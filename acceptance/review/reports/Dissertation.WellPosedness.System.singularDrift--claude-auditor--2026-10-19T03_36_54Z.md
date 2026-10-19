### A:rem:uniq-no-integ: Dissertation.WellPosedness.System.singularDrift
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash 52bed42bcf81ba997be36c4ad7c8d90e (pl-fp-v1:dbfae93e0a36a23f8e461a320ff2f33adf6b5b22dc32cb961c91fb149a7e2987)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:36:54Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:18:00Z):
Reading of def:Dissertation.WellPosedness.System.singularDrift (Remark 3.4).

Paper notion: the deterministic drift t -> t^{-1/2} on (0,T] (R^n-valued; for n=1 a scalar), which
is in L^1(0,T) but not in L^2(0,T) (int_0^T t^{-1} dt = oo); its antiderivative vanishing at 0
is 2 sqrt t. A faithful Lean definition: t -> t^{-1/2} (e.g. (sqrt t)^{-1} or t^(-1/2)) for t>0;
the value at t=0 (Lean 0^{-1}=0 gives 0) and for t<0 is irrelevant (a Lebesgue-null set / outside
[0,T]). For n>1, a vector multiple (or each coordinate) of t^{-1/2}; for the n=1 instance, the
scalar t^{-1/2}. It must not be truncated/regularised near 0 (that would make it L^2 and defeat
the remark).
Comparison (verdict recorded 2026-10-19T03:34:54Z):
Comparison: def singularDrift t = toLp (fun _ => (Real.sqrt t)^{-1}) : EuclideanSpace R (Fin 1)
(Examples/SingularDrift.lean:82-84).
Reading: t -> t^{-1/2} on (0,T], R^1-valued for the n = 1 instance, value at t <= 0 irrelevant, no
regularisation near 0.
For t > 0, (sqrt t)^{-1} = t^{-1/2}. For t <= 0, Real.sqrt t = 0 and 0^{-1} = 0 (Lean
convention), so the value is 0, at t = 0 (a null set) and outside the horizon. Not truncated, so
it is not L^2 on (0,T), which is the point of the remark. The general vector form t^{-1/2} e is
written inline in rem_uniq_translation. Matches.
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-19T03:36:40Z): none
