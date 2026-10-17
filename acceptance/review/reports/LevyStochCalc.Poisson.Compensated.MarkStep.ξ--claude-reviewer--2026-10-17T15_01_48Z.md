### A:cor:robust, A:eq:forced, A:eq:mvfbsdej, A:ex:brownian, A:ex:concrete, A:intro:mvfbsdej, A:lem:bpbsde, A:lem:cont, A:lem:pert, A:lem:small, A:rem:cwp-class, A:rem:generalrank, A:sec2:prp, A:sec3:one-null-set, A:sec4:WP-def, A:sec4:horizon-not-contractive, A:sec:examples, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: LevyStochCalc.Poisson.Compensated.MarkStep.ξ
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 0be3e10909ab07b6258c2d3d03a8b983 (pl-fp-v1:4ae1f5b9565d4b28f09b0b0d63f6a4e9657bdbfd1592ed016472dff87a7f3cea)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:01:48Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:35:34Z):
Unit: def:LevyStochCalc.Poisson.Compensated.MarkStep.ξ (reading locked before any Lean is seen)

Paper notion. The random coefficients xi_{k,j} : Omega -> R (or R^m) of the elementary marked integrand
(unit 17); xi_{k,j} is the value on the slab (t_k, t_{k+1}] x B_j, to be F_{t_k}-measurable and square
integrable.

What a faithful Lean definition must be.
- A field of MarkStep: a doubly indexed family (time slab k, mark set j) of real (or vector) random
  variables. Its meaning is fixed by the structure's properties and the Adapted predicate (unit 18);
  faithful iff those are.
Comparison (verdict recorded 2026-10-17T15:01:16Z):
Comparison: def:LevyStochCalc.Poisson.Compensated.MarkStep.ξ
(Poisson/MarkStepIsometry.lean:81-82.)

- Reading: doubly indexed (slab, mark) family of real random variables; meaning fixed by the structure and
  Adapted.
- Lean: xi : N -> Fin K -> Omega -> R (slab index i, mark index k), bounded and measurable by the structure,
  F_{p_i}-measurable under Adapted; entries with i >= N_0 unused.

Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-17T15:01:27Z): none
