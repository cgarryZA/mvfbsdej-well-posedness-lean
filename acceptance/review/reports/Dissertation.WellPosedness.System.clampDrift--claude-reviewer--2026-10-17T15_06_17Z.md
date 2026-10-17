### A:ex:concrete, A:prop:strict: Dissertation.WellPosedness.System.clampDrift
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash b25f794b96410650c732095ab6aa7055 (pl-fp-v1:e32b25ac97174aad3716d8b466a92ca34ce3f5bb1bb2869a0764faa44ad6817f)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:06:17Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:33:35Z):
Reading for clampDrift (paper Prop 3.8, (3.6); Ex 5.1(i) last paragraph).
b(t,theta,mu) := -beta_1 y + eps g_0(y - m_Y(mu)), g_0(r) = max{-1, min{1, r}},
m_Y(mu) = int_H y mu(dtheta) (Y-marginal mean), with n = m = 1, d >= 1, G = 1, beta_1 > 0, 0 < eps < beta_1
(the definition itself makes sense for any reals beta_1, eps). The drift is a map
[0,T] x H x P_2(H) -> R^n = R, independent of t, x, z, u. Faithful Lean: a drift coefficient with
value -beta_1 * y + eps * clamp(y - m_Y(mu)), with y the (scalar) Y-component of theta and m_Y(mu) the
Bochner mean of the Y-projection under mu (well-defined on P_2). If written for general m = n
(vector y, componentwise clamp), at n = m = 1 it must reduce to the scalar formula. The sign
conventions must be exactly these (minus beta_1 y; plus eps g_0).
Comparison (verdict recorded 2026-10-17T15:03:46Z):
Comparison for clampDrift (ExpectedVsPointwiseModel.lean:106):
clampDrift beta1 eps _t theta mu := -(beta1 . theta.2.1) + eps . clampVec (theta.2.1 - meanY mu), on
TupleH nu 1 1 d (n = m = 1, d arbitrary), with meanY mu := int theta.2.1 d(mu.law) (Bochner mean of the
Y-projection) and clampVec v := toLp (fun i => clamp01 (v i)), clamp01 r := max (-1) (min 1 r).
Against my reading ((3.6): b(t,theta,mu) = -beta_1 y + eps g_0(y - m_Y(mu)), g_0 = max{-1, min{1, r}},
m_Y(mu) = int_H y mu(dtheta), n = m = 1, independent of t, x, z, u): exact match, signs included
(clampDrift_apply in the file reduces the coordinate to the scalar formula). The mean is over a P_2
law, so the Y-projection (1-Lipschitz) is integrable and the Bochner integral is the genuine mean.
beta1, eps are free reals in the definition (the restrictions beta_1 > 0, 0 < eps < beta_1 belong to the
propositions). Values in EuclideanSpace R (Fin 1) = R^n with n = 1.
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-17T15:05:47Z): none (the author's excerpt shown for this unit is a marker and at most a section heading, with no
item-level reading to compare against; my comparison file records the representation choices in
detail).
