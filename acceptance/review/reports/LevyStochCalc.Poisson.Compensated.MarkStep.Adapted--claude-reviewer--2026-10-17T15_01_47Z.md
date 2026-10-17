### A:cor:robust, A:eq:forced, A:eq:mvfbsdej, A:ex:brownian, A:ex:concrete, A:intro:mvfbsdej, A:lem:bpbsde, A:lem:cont, A:lem:pert, A:lem:small, A:rem:cwp-class, A:rem:generalrank, A:sec2:prp, A:sec3:one-null-set, A:sec4:WP-def, A:sec4:horizon-not-contractive, A:sec:examples, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: LevyStochCalc.Poisson.Compensated.MarkStep.Adapted
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash ecd786abe075b89b145b9c7361973099 (pl-fp-v1:32845f842a2084173305909c7650f5870267f47579c99354b04ee7107df4c6aa)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:01:47Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:35:33Z):
Unit: def:LevyStochCalc.Poisson.Compensated.MarkStep.Adapted (reading locked before any Lean is seen)

Paper notion. Predictability of the elementary marked integrand (unit 17): each coefficient xi_{k,j},
the value on the time slab (t_k, t_{k+1}], must be F_{t_k}-measurable (known at the left endpoint),
w.r.t. the standing filtration (F_t). This makes phi P (x) E-measurable (predictable).

What a faithful Lean definition must be.
- A Prop on a MarkStep and a filtration F: for every k and j, xi_{k,j} is strongly
  measurable/measurable w.r.t. F_{t_k} (the LEFT endpoint p_k of the k-th slab). Measurability w.r.t.
  F_{t_{k+1}} (right endpoint) would be wrong (non-predictable integrand, integral not a martingale).
- May also include integrability (E|xi|^2 < oo); if not, that requirement must be elsewhere.
Comparison (verdict recorded 2026-10-17T15:01:15Z):
Comparison: def:LevyStochCalc.Poisson.Compensated.MarkStep.Adapted
(Poisson/MarkStepIsometry.lean:107-111.)

- Reading: for every slab k and mark j, xi_{k,j} measurable w.r.t. F_{t_k} (LEFT endpoint); right endpoint
  would be wrong; integrability may be elsewhere.
- Lean: for all i < g.N_0 and all k, xi i k is StronglyMeasurable[F (g.p i)] - the left endpoint p_i of the
  slab (p_i, p_{i+1}]. Real-valued, so strong measurability = measurability. Only the relevant slabs
  i < N_0 are constrained. Boundedness (hence integrability) is a field of MarkStep.

Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-17T15:01:27Z): none
