#!/usr/bin/env bash
# Independent check of the proved statements with comparator (leanprover/comparator).
#
#   bash tools/comparator_check.sh <evidence-dir> [--nanoda]
#
# For every clause of acceptance/claims.json with a proof, `tools/acceptance.py comparator-inputs`
# writes `AcceptanceChallenge.lean`: the theorem of the proof's name typed by the statement of
# `Dissertation.PaperSpec` (by its negation for a refutation), proved by `sorry`, importing only
# the statements. Comparator then builds
# the challenge and `Dissertation.Acceptance` in a landrun sandbox, exports both with lean4export,
# checks that each proof has the statement of its challenge (every declaration the statement uses
# being the same in both environments) and uses only propext, Classical.choice and Quot.sound, and
# replays the exported proofs into a fresh Lean kernel (and nanoda with --nanoda). The run is bound
# to its inputs in <evidence-dir>/comparator_result.json (`acceptance.py comparator-bind`).
#
# Tools are built from source once into $ACCEPTANCE_TOOLS (default ~/.cache/acceptance-tools):
# comparator and lean4export at the tags matching lean-toolchain, landrun at LANDRUN_REV.
# Comparator requests landrun's best-effort mode, which enforces what the kernel's Landlock ABI
# supports: the filesystem and execution from v2 (on v1 nothing, as the rules use `refer`), TCP
# from v4, abstract UNIX sockets and signals from v6, pathname UNIX sockets from v9; with no
# Landlock it enforces nothing. The run stops unless a write outside the sandbox is refused.
set -euo pipefail
LANDRUN_REV=811cfff51ceaf3d9843708aa6d22e9b84ccac8b4

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
EV="$(mkdir -p "$1" && cd "$1" && pwd)"
NANODA=""
[[ "${2:-}" == "--nanoda" ]] && NANODA="--nanoda"
TOOLS="${ACCEPTANCE_TOOLS:-$HOME/.cache/acceptance-tools}"
export PATH="$HOME/.elan/bin:/usr/local/go/bin:$PATH"
TAG="$(cut -d: -f2 "$ROOT/lean-toolchain")"
mkdir -p "$TOOLS"

if [[ ! -x "$TOOLS/comparator/.lake/build/bin/comparator" ]]; then
  rm -rf "$TOOLS/comparator"
  git clone -q --depth 1 --branch "$TAG" https://github.com/leanprover/comparator "$TOOLS/comparator"
  # --no-cache: build lean4export here rather than download Reservoir's prebuilt archive
  ( cd "$TOOLS/comparator" && lake build --no-cache lean4export comparator )
fi
if [[ ! -x "$TOOLS/landrun" ]]; then
  rm -rf "$TOOLS/landrun-src"
  git init -q "$TOOLS/landrun-src"
  git -C "$TOOLS/landrun-src" fetch -q --depth 1 https://github.com/Zouuup/landrun "$LANDRUN_REV"
  git -C "$TOOLS/landrun-src" checkout -q FETCH_HEAD
  ( cd "$TOOLS/landrun-src" && go build -o "$TOOLS/landrun" ./cmd/landrun )
fi
# landrun's command-line parser consumes a later `--` (lean4export's separator between modules and
# declarations); the wrapper ends landrun's flags with an explicit `--` before the command.
cat > "$TOOLS/landrun-wrap" <<'WRAP'
#!/usr/bin/env bash
valued=" --ro --rox --rw --rwx --unix --bind-tcp --connect-tcp --log-level --env "
flags=()
while [[ $# -gt 0 && "$1" == -* ]]; do
  flags+=("$1")
  if [[ "$valued" == *" $1 "* ]]; then flags+=("$2"); shift; fi
  shift
done
exec "$(dirname "$0")/landrun" "${flags[@]}" -- "$@"
WRAP
chmod +x "$TOOLS/landrun-wrap"
# best effort silently enforces nothing without Landlock: check that the sandbox refuses a write
probe="$(mktemp -d)"
sandbox=("$TOOLS/landrun-wrap" --best-effort --ro / -ldd -add-exec --rwx "$probe/in")
mkdir "$probe/in"
"${sandbox[@]}" touch "$probe/in/ok" || { echo "landrun cannot run a command here" >&2; exit 1; }
if "${sandbox[@]}" touch "$probe/out" 2>/dev/null; then
  echo "landrun does not restrict the filesystem on this kernel (no usable Landlock)" >&2; exit 1
fi
rm -rf "$probe"
LANDLOCK_ABI="$(python3 -c 'import ctypes; l = ctypes.CDLL(None)
print(l.syscall(444, None, ctypes.c_size_t(0), ctypes.c_uint32(1)))')"
{
  echo "comparator $(git -C "$TOOLS/comparator" rev-parse HEAD) ($TAG)"
  echo "landrun $(git -C "$TOOLS/landrun-src" rev-parse HEAD 2>/dev/null || echo prebuilt)"
  echo "landlock ABI $LANDLOCK_ABI ($(uname -r)), uid $(id -u)"
  echo "Dissertation $(git -C "$ROOT" rev-parse HEAD)"
} > "$EV/comparator_versions.txt"

cd "$ROOT"
trap 'rm -f "$ROOT/AcceptanceChallenge.lean"' EXIT
python3 tools/acceptance.py comparator-bind --evidence "$EV" --stage start
python3 tools/acceptance.py comparator-inputs --out "$EV/comparator.json" $NANODA
cp AcceptanceChallenge.lean "$EV/"
# the solution is built before the check, so comparator does not rebuild it
lake build Dissertation.PaperSpec Dissertation.Acceptance > "$EV/comparator_prebuild.log" 2>&1
set +e
COMPARATOR_LANDRUN="$TOOLS/landrun-wrap" \
COMPARATOR_LEAN4EXPORT="$TOOLS/comparator/.lake/packages/lean4export/.lake/build/bin/lean4export" \
  lake env "$TOOLS/comparator/.lake/build/bin/comparator" "$EV/comparator.json" \
  2>&1 | tee "$EV/comparator.log"
status=${PIPESTATUS[0]}
set -e
rm -f AcceptanceChallenge.lean
# the result binds the run to its inputs; release-gate --comparator-result checks the binding
python3 tools/acceptance.py comparator-bind --evidence "$EV" --exit-code "$status"
exit "$status"
