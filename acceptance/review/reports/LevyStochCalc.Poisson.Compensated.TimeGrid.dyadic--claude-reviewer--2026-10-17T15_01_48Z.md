### A:cor:robust, A:eq:forced, A:eq:mvfbsdej, A:ex:brownian, A:ex:concrete, A:intro:mvfbsdej, A:lem:bpbsde, A:lem:cont, A:lem:pert, A:lem:small, A:rem:cwp-class, A:rem:generalrank, A:sec2:prp, A:sec3:one-null-set, A:sec4:WP-def, A:sec4:horizon-not-contractive, A:sec:examples, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: LevyStochCalc.Poisson.Compensated.TimeGrid.dyadic
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 95a28fb6db0dc434182c96d67c581601 (pl-fp-v1:753dd06fdfb06701eeba2ee9a770bcb9764cd9122a29d37e0446dedd02143788)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:01:48Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:35:34Z):
Unit: def:LevyStochCalc.Poisson.Compensated.TimeGrid.dyadic (reading locked before any Lean is seen)

Paper notion. Not printed in the paper; the dyadic partition used to approximate integrands by
elementary ones in the construction of the integral: t_k = k T / 2^n, k = 0..2^n (on [0,T]), or
t_k = k / 2^n.

What a faithful Lean definition must be.
- A TimeGrid with N_0 = 2^n (or n 2^n for an expanding dyadic grid) and points k * T / 2^n (or k / 2^n),
  starting at 0, increasing, ending at T (or the stated endpoint). Requires T >= 0 for monotonicity
  (T > 0 in the paper). Any partition with mesh -> 0 and nested refinements would serve the same role;
  what matters is that it is a valid grid (monotone, starting at 0) for every n and the T in use.
Comparison (verdict recorded 2026-10-17T15:01:17Z):
Comparison: def:LevyStochCalc.Poisson.Compensated.TimeGrid.dyadic
(Poisson/MarkStepIncrement.lean:36-46.)

- Reading: N_0 = 2^n and t_k = k T / 2^n on [0,T], starting at 0, increasing, ending at T; needs T > 0.
- Lean: dyadic T (hT : 0 < T) n has N_0 = 2^n and p i = i * T / 2^n; p 0 = 0 and p_i < p_{i+1} proved
  (the TimeGrid invariants), p_{2^n} = T. Exactly the dyadic grid of level n on [0,T].

Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-17T15:01:28Z): none
