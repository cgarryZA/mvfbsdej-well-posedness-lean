### A:cor:robust, A:eq:forced, A:eq:mvfbsdej, A:ex:brownian, A:ex:concrete, A:intro:mvfbsdej, A:lem:bpbsde, A:lem:cont, A:lem:pert, A:lem:small, A:rem:cwp-class, A:rem:generalrank, A:sec2:prp, A:sec3:one-null-set, A:sec4:WP-def, A:sec4:horizon-not-contractive, A:sec:examples, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: LevyStochCalc.Poisson.Compensated.MarkStep
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash a1ee2ea0e1457b990000000000000000 (pl-fp-v1:ec96f426e17bb3e371b00a0c0b44a9bc491141f2a6bd0fca5d6ba54d931985fe)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:01:47Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:35:33Z):
Unit: def:LevyStochCalc.Poisson.Compensated.MarkStep (reading locked before any Lean is seen)

Paper notion. The paper does not define it; it is the elementary integrand behind the compensated
Poisson integral int int U_s(e) Ntilde(ds,de) of system (1.1), the zero-mean property (2.2) and the
isometry used in Section 4. The standard elementary predictable marked integrand is
   phi(t, omega, e) = sum_{k < K} sum_{j} xi_{k,j}(omega) 1_{(t_k, t_{k+1}]}(t) 1_{B_j}(e),
with a time grid 0 = t_0 < ... < t_K, mark sets B_j in E with nu(B_j) < oo, and coefficients
xi_{k,j} that are F_{t_k}-measurable and square-integrable (often bounded). Its integral is
sum_{k,j} xi_{k,j} Ntilde((t_k ^ t, t_{k+1} ^ t] x B_j). The general integral (for U in H^2_N) is the
L^2 isometric extension.

What a faithful Lean structure must be.
- Data: a time grid (unit 25), a finite family of mark sets B_j (measurable, ideally of finite nu-measure),
  and real coefficients xi_{k,j} : Omega -> R (or R^m-valued).
- Properties (fields or separate predicates such as Adapted, unit 18): measurability of B_j, finite
  nu-measure of B_j (needed for Ntilde(.. x B_j) to be finite), square integrability of xi, and
  F_{t_k}-measurability of xi_{k,j} (adaptedness), the last possibly as a separate predicate.
- If finite nu-measure / measurability are not fields, the Lean must not use the step integrand where
  they fail without them being hypotheses; then the structure is a broader container and acceptable
  provided the integral built from it is only asserted on valid steps.
- Mark sets may be required disjoint or not; either is harmless (sums of indicators).
Comparison (verdict recorded 2026-10-17T15:01:15Z):
Comparison: def:LevyStochCalc.Poisson.Compensated.MarkStep
(Poisson/MarkStepIsometry.lean:70-84; TimeGrid at :29-37; eval :102-105; integral :91-95; Adapted
:107-111; use: Poisson/CompensatedApprox.lean builds the compensated integral from adapted MarkSteps on
dyadic grids.)

- Reading: elementary predictable marked integrand sum_{k,j} xi_{k,j} 1_{(t_k,t_{k+1}]}(t) 1_{B_j}(e) on a
  time grid, mark sets measurable of finite nu-measure, coefficients F_{t_k}-measurable and square
  integrable (often bounded), adaptedness possibly a separate predicate; disjointness of mark sets
  optional.
- Lean: MarkStep Omega E nu g on a TimeGrid g: K mark sets B : Fin K -> Set E with B_measurable and
  B_finite (nu (B k) != oo); coefficients xi : N -> Fin K -> Omega -> R, each bounded (a sure bound) and
  measurable; coefficients with index >= N_0 are irrelevant (eval and integral sum over i < N_0).
  Adaptedness is the separate predicate Adapted (left endpoint). Mark sets need not be disjoint.
- Bounded rather than square-integrable coefficients: the standard elementary class; its L^2 closure is the
  same, so the integral built from it (by L^2 extension) is unaffected.

Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless:
1. Coefficients are bounded (a uniform bound in omega) and ambient-measurable, rather than merely square
   integrable: this is the usual elementary class, dense in the same L^2 space, so the compensated integral
   obtained by L^2 extension is unchanged.
2. Adaptedness (F_{t_i}-measurability at the left endpoint) is a separate predicate (MarkStep.Adapted),
   required wherever the approximants are used (CompensatedApprox requires G.Adapted F).
3. Coefficients are indexed by all i : N and k : Fin K; those with i >= N_0 are ignored by eval and
   integral, so they carry no meaning.
4. Mark sets are not required disjoint; overlapping indicators add, which is still an elementary
   integrand.
5. Scalar (real) coefficients; vector integrands are handled componentwise.
Disagreements with the author's review (shown 2026-10-17T15:01:26Z): No disagreement about the meaning. The author's entry is a bare def-review marker with no recorded comparison, so it does not record the representation choices this review lists (each judged harmless):
1. Coefficients are bounded (a uniform bound in omega) and ambient-measurable, rather than merely square
   integrable: this is the usual elementary class, dense in the same L^2 space, so the compensated integral
   obtained by L^2 extension is unchanged.
2. Adaptedness (F_{t_i}-measurability at the left endpoint) is a separate predicate (MarkStep.Adapted),
   required wherever the approximants are used (CompensatedApprox requires G.Adapted F).
3. Coefficients are indexed by all i : N and k : Fin K; those with i >= N_0 are ignored by eval and
   integral, so they carry no meaning.
4. Mark sets are not required disjoint; overlapping indicators add, which is still an elementary
   integrand.
5. Scalar (real) coefficients; vector integrands are handled componentwise.
