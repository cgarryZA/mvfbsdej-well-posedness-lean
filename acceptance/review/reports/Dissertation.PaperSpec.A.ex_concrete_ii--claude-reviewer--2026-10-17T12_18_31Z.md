### A:ex:concrete: Dissertation.PaperSpec.A.ex_concrete_ii
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash ed839d34f480cba1cba84bcbe1866633 (pl-fp-v1:750e750ae4a2ad0cd8e6fb10bafbd8ec220649dc0da17a4d14d01d6ecb45b5e6)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T12:18:31Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:18:09Z):
# Reading: ex_concrete_ii, clause "(ii) the assumptions"

Paper Ex 5.1(ii): n = m = d = 1, G = 1 (kept from (i)), nu any sigma-finite measure ("arbitrary
jump activity", nu(E) = infinity included), T > 0, xi0 in L^2(F_0) (kept from (i)).
m_Psi(mu) = int pi_Psi(theta) mu(dtheta) (marginal means; m_U(mu) in L^2(nu) as a Bochner mean),
b(rho) = int x rho(dx) (barycentre).
Coefficients: b = -2y - m_Y(mu), sigma = -2z - m_Z(mu), h(e) = -2u(e) - m_U(mu)(e),
f = 2x + m_X(mu), g(x, rho) = 2x + b(rho).
Claims: Assumption 2.3 holds with L = 2 (interior along diagonal inputs, terminal); Assumption
2.2 is immediate (b, sigma, h, f vanish at (0, delta_0); xi0 in L^2(F_0)); Assumption 2.5 holds
with alpha = beta1 = beta2 = 2 (G = 1); implicitly (2.3) Borel measurability and Assumption 2.4
(G = 1 full rank).
Faithful statement: for every basis (any sigma-finite nu on countably generated E, d = 1), T > 0,
xi0 in L^2(F_0): the mean-field system satisfies (2.3), 2.2, 2.3 with L = 2 (printed constant),
2.4 (G = 1), 2.5 with G = 1, alpha = beta1 = beta2 = 2. The law arguments must be the paper's
(means of the marginals of mu in P_2(H), barycentre of rho in P_2(R^n)), the monotonicity in the
diagonal expectation form (it is NOT pointwise for the law terms -- the Lean must not
pointwise-ise it). No finiteness of nu.
Comparison (verdict recorded 2026-10-17T12:18:27Z):
# Comparison: ex_concrete_ii

Lean (Sec5.lean:246): every basis (any sigma-finite nu on countably generated E, d = 1, G0
independent), T > 0, xi0 strongly F_0-measurable in L^2: meanFieldCoeffs nu 1 1
(b = -2y - (tupleMean mu).Y, sigma = -2z - (tupleMean mu).Z, h = -2u - (tupleMean mu).U,
f = 2x + (tupleMean mu).X, g = 2x + barycentre rho; tupleMean mu = Bochner mean of mu.law on H,
barycentre rho = Bochner mean of rho) satisfies JointBorel; b, sigma, h, f vanish at (t, 0, delta_0)
for every t; Assumption22; Assumption23 with L = 2; rank 1 = min 1 1; Assumption25 with G = 1,
alpha = beta1 = beta2 = 2.

Against my reading: setting (n = m = d = 1, G = 1, arbitrary sigma-finite nu): yes. Coefficients:
the channels of the mean of mu are the marginal means m_Psi(mu) (the mean of a product-valued
variable is the product of the means; m_U(mu) is the Bochner mean in L^2(nu), the paper's
m_U(mu)(e)); barycentre as printed: yes. Conclusions: (2.3), vanishing at (0, delta_0), 2.2,
2.3 with the printed L = 2, 2.4 (G = 1 full rank), 2.5 with alpha = beta1 = beta2 = 2 in the
diagonal expectation form (Mono27At over diagonalInputs, terminal over F_T-measurable L^2
pairs): yes. No finiteness of nu. c_G not restated (=1, G = 1), harmless.
Non-vacuity: witness ex_concrete_hypotheses.

Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-17T12:18:27Z): none (the displayed author entry for this unit is empty; nothing specific to disagree with).
