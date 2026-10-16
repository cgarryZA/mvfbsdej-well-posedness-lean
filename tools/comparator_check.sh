#!/usr/bin/env bash
# Independent check of the proved statements with comparator (leanprover/comparator).
#
#   bash tools/comparator_check.sh <evidence-dir> [--nanoda]
#
# For every clause of acceptance/claims.json with a proof, `tools/acceptance.py comparator-inputs`
# writes `AcceptanceChallenge.lean`: the theorem of the proof's name typed by the statement of
# `Dissertation.PaperSpec`, proved by `sorry`, importing only the statements. Comparator then builds
# the challenge and `Dissertation.Acceptance` in a landrun sandbox, exports both with lean4export,
# checks that each proof has the statement of its challenge (every declaration the statement uses
# being the same in both environments) and uses only propext, Classical.choice and Quot.sound, and
# replays the exported proofs into a fresh Lean kernel (and nanoda with --nanoda). The run is bound
# to its inputs in <evidence-dir>/comparator_result.json (`acceptance.py comparator-bind`).
#
# Tools are built once into $ACCEPTANCE_TOOLS (default ~/.cache/acceptance-tools) at the tags
# matching lean-toolchain; landrun from its main branch. On a kernel with Landlock below ABI v9,
# landrun's best-effort mode (which comparator requests) restricts the filesystem only.
set -euo pipefail

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
  ( cd "$TOOLS/comparator" && lake build lean4export comparator )
fi
if [[ ! -x "$TOOLS/landrun" ]]; then
  rm -rf "$TOOLS/landrun-src"
  git clone -q --depth 1 https://github.com/Zouuup/landrun "$TOOLS/landrun-src"
  ( cd "$TOOLS/landrun-src" && go build -o "$TOOLS/landrun" ./cmd/landrun )
fi
# landrun's command-line parser consumes a later `--` (lean4export's separator between modules and
# declarations); the wrapper ends landrun's flags with an explicit `--` before the command.
cat > "$TOOLS/landrun-wrap" <<'WRAP'
#!/usr/bin/env bash
valued=" --ro --rox --rw --rwx --bind-tcp --connect-tcp --log-level --env "
flags=()
while [[ $# -gt 0 && "$1" == -* ]]; do
  flags+=("$1")
  if [[ "$valued" == *" $1 "* ]]; then flags+=("$2"); shift; fi
  shift
done
exec "$(dirname "$0")/landrun" "${flags[@]}" -- "$@"
WRAP
chmod +x "$TOOLS/landrun-wrap"
{
  echo "comparator $(git -C "$TOOLS/comparator" rev-parse HEAD) ($TAG)"
  echo "landrun $(git -C "$TOOLS/landrun-src" rev-parse HEAD 2>/dev/null || echo prebuilt)"
  echo "Dissertation $(git -C "$ROOT" rev-parse HEAD)"
} > "$EV/comparator_versions.txt"

cd "$ROOT"
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
