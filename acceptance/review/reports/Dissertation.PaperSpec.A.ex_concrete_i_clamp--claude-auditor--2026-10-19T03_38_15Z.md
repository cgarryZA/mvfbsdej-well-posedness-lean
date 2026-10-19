### A:ex:concrete: Dissertation.PaperSpec.A.ex_concrete_i_clamp
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba1f386f903a2799dd0 (pl-fp-v1:5022620db86db321279ab8b9bd530d8fefb8c6e7c6a656352bbc7b9855704785)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:38:15Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:16:44Z):
# Reading: spec ex_concrete_i_clamp (Example 5.1(i) with the drift (3.6): the assumptions)

Example 5.1(i), last paragraph: "replacing its drift -beta1 y by (3.6) leaves (2.7) intact with
constants (beta1 - eps, beta2), so Theorem 3.5 continues to apply."
(3.6): b(t,theta,mu) = -beta1 y + eps g0(y - m_Y(mu)), g0(r) = max{-1,min{1,r}},
m_Y(mu) = int y mu(dtheta), with 0 < eps < beta1 (Prop 3.8's range).
Setting: n=m=d=1, G=1, nu arbitrary sigma-finite, xi0 in L^2(F_0), sigma_c, h_c in L^2(nu),
beta1, beta2 > 0, 0 < eps < beta1; sigma = sigma_c - beta1 z, h = h_c - beta1 u, f = beta2 x, g = x.
A faithful formal statement: for all such data (every basis, T > 0, nu):
* Assumption 2.2 (b(.,0,delta0) = eps g0(0) = 0; others as in 5.1(i));
* Assumption 2.3 with some L (e.g. max{beta1+eps, beta2, 1}; the paper gives no explicit L for
  this variant, so an existential L or an explicit valid one are both fine);
* Assumption 2.4 (G = 1);
* Assumption 2.5 with alpha = 1 and constants (beta1 - eps, beta2) (both > 0, constraints hold);
* Borel measurability if bundled.
The quantifier over eps must be the full range 0 < eps < beta1.
Comparison (verdict recorded 2026-10-19T03:34:12Z):
# Comparison: ex_concrete_i_clamp (Example 5.1(i) with the drift (3.6): the assumptions)

Lean (Sec5.lean): for every standing basis (any sigma-finite nu, d = 1, G0 independent), T > 0,
beta1, beta2 > 0 and every eps with 0 < eps < beta1, sigma_c, h_c in L^2(nu), xi0 strongly
F_0-measurable and square integrable: for clampAffineCoeffs beta1 beta2 eps sigma_c h_c (the affine
system of Example 5.1(i) with b replaced by clampDrift: b(t, theta, mu) = -beta1 y + eps g0(y - m_Y(mu)),
g0 = clamp to [-1,1] (clamp01 = max(-1, min(1, r))), m_Y(mu) = int y dmu): JointBorel, Assumption22
(xi0), EXISTS L with Assumption23, rank(1) = min 1 1, Assumption25 with G = 1, alpha = 1 and
constants (beta1 - eps, beta2).

Against my reading: the setting and the full range 0 < eps < beta1: yes. The drift (3.6) exactly
(m_Y the Y-marginal mean, the clamp g0): yes; other coefficients unchanged (sigma_c - beta1 z,
h_c - beta1 u, beta2 x, g = x): yes. Assumptions 2.2, 2.3 (existential L, which my reading
allowed — the paper gives no explicit L here), 2.4 (G = 1 full rank), 2.5 with alpha = 1 and
(beta1 - eps, beta2) (both > 0, admissible): yes, as conclusions. Standing (2.3): included.
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-19T03:38:10Z): none
