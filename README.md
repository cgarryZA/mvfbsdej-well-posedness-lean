# Well-posedness of fully coupled McKean–Vlasov FBSDEs with jumps, in Lean

[![MachineChecked][badge]][audit-page]

[badge]: https://machinechecked.org/papers/2608.23203/badge.svg
[audit-page]: https://machinechecked.org/papers/2608.23203/

A Lean 4 + Mathlib formalisation of the paper *Well-posedness of fully coupled McKean–Vlasov
FBSDEs with jumps under full-tuple law dependence* (Chunrong Feng and Christian Garry), in its
revision of [arXiv:2608.23203v1](https://arxiv.org/abs/2608.23203v1) at commit
[`1f67672`](https://github.com/cgarryZA/mvfbsdej-well-posedness/tree/1f67672).

**The audits.** Open the paper with its Lean beside it, in
[MachineChecked](https://github.com/cgarryZA/MachineChecked)'s reader: every claim of the paper,
the Lean statement and proof linked to it, and what is established.

- [The latest manuscript](https://cgarryza.github.io/mvfbsdej-well-posedness-lean/latest/)
  (commit `1f67672`), built from `main`.
- [arXiv v1](https://cgarryza.github.io/mvfbsdej-well-posedness-lean/v1/), built from the branch
  `audit-v1`: the Lean of commit `ba94c06`, frozen, with its audit configuration (the paper's
  published identity and its claims' source regions pinned at arXiv v1).

The `Audit` workflow rebuilds and republishes both after every push to `main` that passes CI.
An audit records what its author linked, checked and reviewed; it is not an independent
certification.

The formalisation is organised in three layers, and only the third decides what counts as proved:

1. `Dissertation/PaperSpec/A/` — each claim of the paper (or each clause of one) as a closed
   proposition, written from the manuscript;
2. the rest of `Dissertation/` — the implementation: coefficients, laws and Wasserstein
   distances (`Law/`), the system and its assumptions, existence, uniqueness and stability
   (`WellPosedness/`), and a topological lemma on continuous injections (`Topology/`);
3. `Dissertation/Acceptance/A/` — for each proved claim, a theorem whose type is exactly the
   proposition of layer 1.

[`ACCEPTANCE.md`](ACCEPTANCE.md) is the generated report: per claim, whether its proposition is
proved, over which axioms, and whether the proposition and every definition it depends on are
reviewed at their current hashes. The policy is [`acceptance/README.md`](acceptance/README.md).
A claim counts as proved only by that report; a proof of a proposition does not by itself show
that the proposition says what the paper says, which is what the reviews record.

The stochastic calculus (Brownian and Poisson integrals, the Itô–Lévy isometry, Lévy drivers and
their filtrations) comes from [`LevyStochCalc`](https://github.com/cgarryZA/LevyStochCalc).

## Build

Requirements: [`elan`](https://github.com/leanprover/elan) (the toolchain is pinned in
`lean-toolchain`), git, and about 10 GB of disk for Mathlib and its build cache.

```sh
git clone https://github.com/cgarryZA/mvfbsdej-well-posedness-lean
cd mvfbsdej-well-posedness-lean
lake exe cache get        # Mathlib's prebuilt cache
lake build
```

Lake fetches the dependencies at the revisions pinned in `lake-manifest.json`: Mathlib and
`LevyStochCalc`. Mathlib's cache does not cover `LevyStochCalc` and the other dependencies, so
this builds them from source, which takes hours; restoring the prebuilt build below takes about
a minute.

### Restoring a prebuilt build

Every push to `main` publishes its build (this project, `LevyStochCalc` and the other
dependencies Mathlib's cache does not supply) to the `build-cache` release of this repository,
with [MachineChecked](https://github.com/cgarryZA/MachineChecked)'s `scripts/lean_cache.py`. To
use it instead of building from source (Linux x86-64):

```sh
curl -sSfLO https://raw.githubusercontent.com/cgarryZA/MachineChecked/2d577fda5c42713980c3dafe6c46560c02e3330d/scripts/lean_cache.py
lake exe cache get
python3 lean_cache.py restore . cgarryZA/mvfbsdej-well-posedness-lean --build
```

Restore takes the archive of the nearest ancestor commit built with the same toolchain,
`lake-manifest.json` and platform, checks its SHA-256 against its manifest and GitHub's record,
and `--build` runs `lake build --rehash`, which rebuilds exactly what changed since. A restored
build is trusted as built; the proofs are re-checked by `tools/comparator_check.sh`.

## Acceptance check

```sh
python3 tools/acceptance.py check                  # consistency check; regenerates nothing
python3 tools/acceptance.py check --write          # regenerate the report, status and alignment
python3 tools/acceptance.py release-gate --comparator-result <dir>/comparator_result.json
bash tools/comparator_check.sh <dir>               # independent kernel replay (comparator)
python3 tools/test_acceptance.py                   # regression tests of the checker
```

The check builds a probe against the built library, so run it after `lake build`. It also checks
the source hash of every claim against the manuscript in `manuscript/paper/`. On every push to
`main`, the `certify` job of the CI workflow runs comparator and the release gate on its own
evidence and publishes the evidence directory as the run's `comparator-evidence` artifact.

## The paper

The paper is by Chunrong Feng and Christian Garry. This repository formalises its revision of
[arXiv:2608.23203v1](https://arxiv.org/abs/2608.23203v1) at commit
[`1f67672`](https://github.com/cgarryZA/mvfbsdej-well-posedness/tree/1f67672) of the manuscript
repository, whose LaTeX source is vendored in `manuscript/paper/` (the main file
`wellposedness.tex` and its sections).

Compiling the manuscript, or an audit that shows it, needs TeX Live with `latexmk` and
`poppler-utils`. On Debian or Ubuntu:

```sh
sudo apt-get update
sudo DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends \
  latexmk texlive-latex-recommended texlive-latex-extra texlive-fonts-recommended lmodern \
  poppler-utils
cd manuscript/paper && latexmk -pdf wellposedness.tex
```

## Layout

| Path | What |
|---|---|
| `Dissertation/PaperSpec/A/` | the statements of the paper, one closed proposition per clause |
| `Dissertation/Acceptance/A/` | their proofs, and witnesses that their hypotheses can be met |
| `Dissertation/Law/` | laws of finite second moment, the 2-Wasserstein distance, law functionals |
| `Dissertation/WellPosedness/` | the system, its assumptions, existence, uniqueness, stability and the examples |
| `Dissertation/Topology/` | continuous injections into spaces of smaller dimension |
| `acceptance/` | the claim inventory (`claims.json`), the reviews (`review/`) and the policy |
| `manuscript/paper/` | the LaTeX source of the manuscript at the pinned revision |
| `tools/` | the acceptance checker, its tests and Lean probe, the claim extractor, the comparator |
| `.github/workflows/` | CI (build, acceptance check, comparator and release gate) and the audit |

## License

Apache 2.0, see [`LICENSE`](LICENSE).
