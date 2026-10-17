### A:cor:robust, A:eq:forced, A:eq:mvfbsdej, A:ex:brownian, A:ex:concrete, A:intro:mvfbsdej, A:lem:bpbsde, A:lem:cont, A:lem:pert, A:lem:small, A:rem:cwp-class, A:rem:generalrank, A:sec2:prp, A:sec3:one-null-set, A:sec4:WP-def, A:sec4:horizon-not-contractive, A:sec:examples, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: LevyStochCalc.Poisson.Compensated.TimeGrid
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash f743d5d40f14218f0000000000000000 (pl-fp-v1:89a518ee8421801eb0287a20dfddd64cef0961bd9a0a85fb7e17695bf0762204)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:01:48Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:35:34Z):
Unit: def:LevyStochCalc.Poisson.Compensated.TimeGrid (reading locked before any Lean is seen)

Paper notion. Not printed in the paper; the partition of the time interval behind elementary integrands
(unit 17): 0 = t_0 < t_1 < ... < t_N (= T, or any finite endpoint), N >= 1 (or N >= 0).

What a faithful Lean structure must be.
- Data: a number of steps N_0 and grid points p : Fin (N_0+1) -> R (or N -> R) with p_0 = 0 (or >= 0) and
  monotone (strictly or weakly) increasing. Weak monotonicity (repeated points) is harmless: repeated points
  give empty slabs. Points must be >= 0 (the time domain is R_+). An unconstrained sequence of reals would
  allow decreasing slabs (t_k, t_{k+1}] = empty or negative times; harmless only if the slab formula gives
  zero for decreasing pairs and the adaptedness requirement at negative times is meaningful.
- Whether the last point is pinned to T is a convention of use.
Comparison (verdict recorded 2026-10-17T15:01:16Z):
Comparison: def:LevyStochCalc.Poisson.Compensated.TimeGrid
(Poisson/MarkStepIsometry.lean:29-37.)

- Reading: N_0 steps and points p with p_0 = 0 (or >= 0), increasing (strictly or weakly), nonnegative;
  terminal point a convention of use.
- Lean: N_0 : N, p : N -> R, p_zero : p 0 = 0, p_lt : for i < N_0, p i < p (i+1). So 0 = p_0 < p_1 < ...
  < p_{N_0}: a strictly increasing finite partition starting at 0 (all points >= 0). Values of p beyond N_0
  are irrelevant (never used by eval/integral, which sum over i < N_0). No terminal time is fixed. N_0 = 0
  allowed (empty grid). Matches.

Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-17T15:01:28Z): none
