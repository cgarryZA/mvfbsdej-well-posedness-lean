### A:ex:concrete: Dissertation.WellPosedness.Existence.clampAffineCoeffs
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 5dc0669bb7724f483dd7fd8e2ba08292 (pl-fp-v1:460c847baaabd522780f5ab41bda70ccb49e02a682e2b7bf1ef8c601466c03ea)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:04:36Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:34:25Z):
Unit: def Existence.clampAffineCoeffs (used by Example 5.1).
Paper: the last paragraph of Example 5.1(i): "The baseline also realises the example of
Proposition 3.7: replacing its drift -beta1 y by (3.11) leaves (2.7) intact with constants
(beta1 - eps, beta2)". (3.11): b(t,theta,mu) = -beta1 y + eps g0(y - m_Y(mu)),
g0(r) = max{-1, min{1, r}} (the clamp to [-1,1]), m_Y(mu) = int_H y mu(dtheta) the Y-marginal
mean, with n = m = d = 1, 0 < eps < beta1.
So the notion is the affine coefficient system of Example 5.1(i) (sigma = sigma_c - beta1 z,
h = h_c - beta1 u, f = beta2 x, g(x,rho) = x) with only the drift replaced by
-beta1 y + eps * clamp(y - m_Y(mu)). A faithful Lean definition: exactly that (parameters beta1,
beta2, eps, sigma_c, h_c), with m_Y(mu) the genuine mean of the Y-coordinate under mu (mu in
P_2(H), so the mean exists; no junk), clamp = max(-1, min(1, .)), and all other coefficients as
in affineCoeffs. A general-dimension version would need a vector clamp; the n=m=d=1 case is the
paper's.
Comparison (verdict recorded 2026-10-17T12:39:43Z):
clampAffineCoeffs beta1 beta2 eps sigmac hc : Coeffs nu 1 1 d := affineCoeffs beta1 beta2 sigmac hc
with b replaced by clampDrift beta1 eps, where clampDrift beta1 eps t theta mu =
-(beta1 . y) + eps . clampVec (y - meanY mu), clampVec the coordinatewise clamp01 r =
max(-1, min(1, r)) on R^1, meanY mu = Bochner integral of theta.2.1 (the Y coordinate) under
mu.law, mu in P_2(H) (so the mean exists; no junk).
Item by item with the last paragraph of Example 5.1(i) / (3.6): drift -beta1 y + eps g0(y - m_Y(mu))
exactly; sigma = sigmac - beta1 z, h = hc - beta1 u, f = beta2 x, g = x unchanged from affineCoeffs
(reviewed: faithful at n = d = 1). n = m = 1 as in the paper; d is a free parameter (the paper
has d >= 1 in Prop 3.7 and d = 1 in Example 5.1), eps free (0 < eps < beta1 in the statements).
Verdict: broader (free diffusion dimension d), instance d = 1 is the printed system.
Witness: —
Verdict: broader — Instantiation: d := 1, sigmac := (sigma_c) in R^{1 x 1}, hc := h_c in L^2(nu; R^1); then the system
is b = -beta1 y + eps max(-1, min(1, y - m_Y(mu))), sigma = sigma_c - beta1 z, h = h_c - beta1 u,
f = beta2 x, g(x,rho) = x, the paper's modified baseline of Example 5.1(i). (For general d >= 1 it
is also the drift setting of Proposition 3.7 with the remaining coefficients of 5.1(i).)
Disagreements with the author's review (shown 2026-10-17T15:04:20Z): No disagreement on substance, but the author's review is an empty marker (only a section heading at
most): it does not record that the definition is broader than the printed system (general
dimensions) nor the instantiation that gives the printed one (n = d = 1, resp. d = 1), which the
review policy asks for a broader definition.
