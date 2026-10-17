### A:cor:robust, A:eq:forced, A:eq:mvfbsdej, A:ex:brownian, A:ex:concrete, A:intro:mvfbsdej, A:lem:bpbsde, A:lem:cont, A:lem:pert, A:lem:small, A:rem:cwp-class, A:rem:generalrank, A:sec2:prp, A:sec3:one-null-set, A:sec4:WP-def, A:sec4:horizon-not-contractive, A:sec:examples, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: LevyStochCalc.Poisson.Compensated.MarkStep.K
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 69b93339d92d0211761d8983c191e8a4 (pl-fp-v1:7f77191f51572e1e97bc43acfc845a4eca9fd810a8fadad8ab9207db57490ec3)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:01:48Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:35:33Z):
Unit: def:LevyStochCalc.Poisson.Compensated.MarkStep.K (reading locked before any Lean is seen)

Paper notion. A size parameter of the elementary marked integrand (unit 17): the number of mark sets
(or of time slabs) in the finite sum.

What a faithful Lean definition must be.
- A natural-number field of MarkStep indexing the finite family (mark sets B_j, j < K, or slabs).
  No mathematical content beyond indexing; any natural number allowed (K = 0 gives the zero integrand).
Comparison (verdict recorded 2026-10-17T15:01:15Z):
Comparison: def:LevyStochCalc.Poisson.Compensated.MarkStep.K
(Poisson/MarkStepIsometry.lean:75-76.)

- Reading: natural-number count of mark sets; no content; K = 0 gives the zero integrand.
- Lean: K : N, the number of mark sets (B and xi are indexed by Fin K). K = 0 gives empty sums.

Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-17T15:01:27Z): none
