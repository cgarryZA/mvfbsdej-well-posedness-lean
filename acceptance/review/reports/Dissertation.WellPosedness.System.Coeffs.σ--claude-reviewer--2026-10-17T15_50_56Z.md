### A:abstract, A:ass:integ, A:ass:lip, A:ass:mono, A:conclusion, A:cor:robust, A:eq:coeffint, A:eq:coefmeas, A:eq:forced, A:eq:hborel, A:eq:monomargin, A:eq:monomarginu, A:eq:mvfbsdej, A:ex:brownian, A:ex:concrete, A:ex:dealer, A:ex:fulllaw, A:intro:limin-comparison, A:intro:mvfbsdej, A:lem:cont, A:lem:pert, A:lem:small, A:rem:beta1-dich, A:rem:cwp-class, A:rem:diag-mono, A:rem:freelaw, A:rem:generalrank, A:rem:intrinsic, A:rem:margin, A:rem:regimes, A:rem:uniq-no-integ, A:sec3:margin-paragraph, A:sec3:one-null-set, A:sec4:WP-def, A:sec4:horizon-not-contractive, A:sec5:overview, A:sec:examples, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: Dissertation.WellPosedness.System.Coeffs.σ
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash b8b7ad45d5043ac9ea56b20d79cc8746 (pl-fp-v1:30455c8c6ca273988d7121693932f59237e2030ae00d65d3e28b2f81644de04a)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:50:56Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T15:41:48Z):
Reading for def:Dissertation.WellPosedness.System.Coeffs.σ.

Paper notion: the diffusion coefficient sigma : [0,T] x H x P2(H) -> R^{n x d} (Frobenius norm),
deterministic, jointly Borel.

Faithful Lean: the field sigma, type (time) -> H -> P2W(H) -> (n x d real matrices) with the norm
used in the statements being the Frobenius norm (Mathlib's default matrix norm is not Frobenius:
Matrix has no global norm instance; Matrix.frobeniusNormedAddCommGroup or an explicit sum must be
used). Dimension n x d (forward state, Brownian dimension).
Comparison (verdict recorded 2026-10-17T15:50:04Z):
Comparison for def:Dissertation.WellPosedness.System.Coeffs.σ: field accessor, type
R -> TupleH nu n m d -> P2 (TupleH nu n m d) -> EuclideanSpace R (Fin n x Fin d). Matches
sigma : [0,T] x H x P2(H) -> R^{n x d}: the codomain is the Euclidean space on index pairs (i,j), whose
norm is exactly the Frobenius norm (my reading's concern about Mathlib's matrix norms is avoided).
Dimension n x d. Plus the representation choices of Coeffs. Verdict: faithful with representation
choices.
Witness: —
Verdict: faithful with representation choices — Choices: R^{n x d} realised as EuclideanSpace R (Fin n x Fin d) (Euclidean norm on index pairs =
Frobenius norm); time domain R (only [0,T] used); H realised as the max-norm product TupleH, whose P2
has the same carrier as the paper's P2(H), no metric in the field; measurability imposed separately.
Disagreements with the author's review (shown 2026-10-17T15:50:12Z): No disagreement with a stated position (the author's entry shown is empty). For the record: faithful
with the representation choices of Coeffs (time over R, max-norm product TupleH whose P2 has the
paper's carrier, measurability imposed separately).
