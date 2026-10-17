### A:cor:robust, A:eq:forced, A:eq:mvfbsdej, A:ex:brownian, A:ex:concrete, A:intro:mvfbsdej, A:lem:bpbsde, A:lem:cont, A:lem:pert, A:lem:small, A:rem:cwp-class, A:rem:generalrank, A:sec2:prp, A:sec3:one-null-set, A:sec4:WP-def, A:sec4:horizon-not-contractive, A:sec:examples, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: LevyStochCalc.Poisson.Compensated.TimeGrid.p
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 57d3a20338cbc4687e319ddece66a22f (pl-fp-v1:8fa4560e3373055b50a7df6aad93ecd0f5063f47f88dba927774fa83bef7b195)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:01:49Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:35:34Z):
Unit: def:LevyStochCalc.Poisson.Compensated.TimeGrid.p (reading locked before any Lean is seen)

Paper notion. The grid points t_0..t_N of the time grid (unit 25).

What a faithful Lean definition must be.
- A field of TimeGrid: the points, indexed by Fin (N_0+1) (or N), constrained by the structure to start at
  0 (or be nonnegative) and increase. Faithful iff the structure is.
Comparison (verdict recorded 2026-10-17T15:01:17Z):
Comparison: def:LevyStochCalc.Poisson.Compensated.TimeGrid.p
(Poisson/MarkStepIsometry.lean:34-35.)

- Reading: the grid points, constrained to start at 0 and increase.
- Lean: p : N -> R, constrained by p 0 = 0 and strict increase up to index N_0; values beyond N_0 unused.

Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-17T15:01:28Z): none
