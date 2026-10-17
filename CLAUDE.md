# mvfbsdej-well-posedness-lean — project instructions

The Lean 4 formalisation of one paper: the well-posedness of fully coupled McKean–Vlasov FBSDEs
with jumps. `README.md` is the overview, `acceptance/README.md` the acceptance policy.

## Rules that do not bend

- **This repository is public.** Nothing of any other, private formalisation goes into it: no
  names, declarations, statements, claim ids, review text, manuscript lines or repository names of
  another project, in files, comments, commit messages, issues or pull requests.
- **Only the paper as written.** This repository formalises the claims of the paper's current
  manuscript and what their proofs need. Results that go beyond the manuscript are not added
  here.
- **The acceptance test is `ACCEPTANCE.md`.** A claim counts as proved only when its frozen
  proposition in `Dissertation/PaperSpec/A/` has a theorem in `Dissertation/Acceptance/A/` whose
  type is exactly that proposition, and the proposition and the definitions it depends on are
  reviewed at their current hashes. Never change a proposition to fit what the implementation
  proves: a false printed claim is refuted beside a corrected one. When in doubt, under-claim.
- **Kernel-checked is not reviewed.** `#print axioms` over `propext`, `Classical.choice`,
  `Quot.sound` certifies the logical trust base, not that a statement says what the paper says.
  Never call a statement verified on the strength of its proof alone.
- A review marker records a reading; never add or update one without doing the reading it
  records.

## Build and check

```sh
lake exe cache get && lake build
python3 tools/acceptance.py check --write    # regenerate ACCEPTANCE.md, acceptance/status.json and
                                             # the alignment of formalization.yaml
python3 tools/test_acceptance.py
```

`lake build` is authoritative. After a change to a statement or a definition it uses, regenerate
the report and review the reopened entries. `tools/acceptance.py hashes NAME` prints the current
hashes for review markers.

## Style

- Docstrings are mathlib-style: one or two sentences on the mathematical object. Do not narrate
  the proof event, the history of a change or audit status ("proved here", "machine-checked",
  "verified", "formerly"). Lines at most 100 columns.
- Prefer version-robust tactics (`gcongr`, `nlinarith`, `linarith`, `omega`, `simp`,
  `field_simp`). For heartbeat timeouts with `set`-introduced constants, `clear_value` them.

## MachineChecked feedback

While using [MachineChecked](https://github.com/cgarryZA/MachineChecked) (audits, `lean_cache.py`
build caches, review markers, exports), raise every bug, problem, missed opportunity or feature you
would have wanted as an issue on its repository: one issue per item, saying what, why, and when it
is done, with a label for its kind (`bug`, `enhancement`, `cleanup`, `docs`). Search its open
issues first and add to an existing one rather than duplicating it. That repository is public:
write each issue generically, with nothing of a private project (no names, declarations,
statements, counts, review text or manuscript lines); show the problem on a synthetic example.
