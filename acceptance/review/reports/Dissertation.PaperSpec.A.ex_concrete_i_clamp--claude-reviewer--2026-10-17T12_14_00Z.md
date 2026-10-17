### A:ex:concrete: Dissertation.PaperSpec.A.ex_concrete_i_clamp
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash ed839d34f480cba1f386f903a2799dd0 (pl-fp-v1:5022620db86db321279ab8b9bd530d8fefb8c6e7c6a656352bbc7b9855704785)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T12:14:00Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:13:33Z):
# Reading: ex_concrete_i_clamp, clause "(i) with the drift (3.6): the assumptions"

Paper (Ex 5.1(i), last paragraph): "The baseline also realises the example of Proposition 3.7:
replacing its drift -beta1 y by (3.6) leaves (2.7) intact with constants (beta1 - eps, beta2), so
Theorem 3.5 continues to apply." (3.6): b(t, theta, mu) = -beta1 y + eps g0(y - m_Y(mu)),
g0(r) = max{-1, min{1, r}}, m_Y(mu) = int y mu(dtheta), with 0 < eps < beta1 (Prop 3.7).

Faithful formal statement (assumptions part):
- Setting as in Ex 5.1(i): standing basis, n = m = d = 1, G = 1, nu any sigma-finite on a
  countably generated E, T > 0.
- Data: xi0 in L^2(F_0), sigma_c in R, h_c in L^2(nu), beta1 > 0, beta2 > 0, eps with
  0 < eps < beta1 (Prop 3.7's range; the paper's "fix beta1 > 0, every 0 < eps < beta1").
- Coefficients: b = -beta1 y + eps g0(y - m_Y(mu)), sigma = sigma_c - beta1 z,
  h = h_c - beta1 u, f = beta2 x, g = x. m_Y must be the Y-marginal mean of mu in P_2(H)
  (well defined for mu in P_2).
- Conclusion: (2.3), Ass. 2.2, Ass. 2.3 (for some L, e.g. max{beta1 + eps, beta2, 1}; the paper
  prints no value -- an existential L or a stated value are both fine), Ass. 2.4 (G = 1), and
  Ass. 2.5 with G = 1, alpha = 1 and constants (beta1 - eps, beta2) (admissible since
  beta1 - eps > 0). The interior inequality is the expectation (diagonal) form; it is NOT
  pointwise (Prop 3.7 shows pointwise fails), so the Lean must use the diagonal expectation form.
- No added hypothesis (e.g. nu finite, sigma_c = h_c = 0) and no lost case (all eps in
  (0, beta1)).
Comparison (verdict recorded 2026-10-17T12:13:53Z):
# Comparison: ex_concrete_i_clamp

Lean (Sec5.lean:179): setting of ex_concrete_i (every basis with d = 1, any sigma-finite nu, G0
independent; T > 0); for all beta1, beta2 > 0 and 0 < eps < beta1, sigma_c, h_c, xi0 in L^2(F_0):
clampAffineCoeffs beta1 beta2 eps sigma_c h_c = affineCoeffs with b replaced by clampDrift,
b = -(beta1 y) + eps clampVec(y - meanY mu), clampVec = coordinatewise clamp01 = max(-1, min(1, .)),
meanY mu = int theta.2.1 d mu.law (the Y-marginal mean), satisfies JointBorel, Assumption22,
exists L with Assumption23, G = 1 full rank, Assumption25 with G = 1, alpha = 1, (beta1 - eps,
beta2).

Against my reading: setting (n = m = d = 1, G = 1, any sigma-finite nu): yes. Range of eps:
0 < eps < beta1: yes. Coefficients: exactly (3.6) plus the affine sigma, h, f, g: yes (checked
definitions). Conclusion: (2.3), 2.2, 2.3 with some L (paper prints none), 2.4, 2.5 with alpha = 1,
constants (beta1 - eps, beta2) in the diagonal expectation form (Mono27At over diagonalInputs):
yes. Admissible constants are enforced inside Assumption25 (beta1 - eps > 0). No added
hypothesis. Assumption 2.4's c_G is not restated here (it is in ex_concrete_i); harmless as
G = 1 and rank = min 1 1 is the full-rank condition.
Non-vacuity: witness ex_concrete_hypotheses (driver d = 1, nu = dirac 0, G0 = bot, xi0 = 0,
beta's 1, eps = 1/2 < 1).

Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-17T12:13:53Z): none
