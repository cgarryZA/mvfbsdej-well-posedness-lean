### A:ex:dealer: Dissertation.PaperSpec.A.ex_dealer_coeffs
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash ed839d34f480cba1ddb1f9221aa35a6d (pl-fp-v1:b251b3b631080d389b4fb98d125f7858efe5bae1251d633ab7375d2e92d92fd3)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T16:03:52Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T15:47:46Z):
Reading of spec ex_dealer_coeffs ("At epsilon = 0 this is Example 5.1(i) verbatim").

Dealer coefficients (Example 5.5): b = -beta_1 y, sigma = sigma_c - beta_1 z,
h = h_c - beta_1 u - epsilon A_{mu^U}(u), f = beta_2 x, g(x, rho) = x, with mu^U the U-marginal of
the measure argument, n = m = d = 1, G = 1, sigma_c in R, h_c in L^2(nu), beta_1, beta_2 > 0
(the example's parameters), nu sigma-finite.
Example 5.1(i) coefficients: b = -beta_1 y, sigma = sigma_c - beta_1 z, h(e) = h_c(e) -
beta_1 u(e), f = beta_2 x, g(x, rho) = x.
Faithful statement: for every admissible nu, sigma_c, h_c, beta_1, beta_2 (the printed claim
is for the example's parameters; universal quantification over them, beta_i > 0 or arbitrary
reals - broader is fine), the dealer coefficient system with epsilon = 0 equals the Example
5.1(i) coefficient system: equality of all five coefficients as functions of (t, theta, mu)
(and (x, rho) for g). Equality of the whole system (structure) is fine. Since this is a
definitional identity, its meaning rests on the two coefficient definitions (dealer and
concrete), which must be the printed ones; the comparison must be checked against them.
Comparison (verdict recorded 2026-10-17T16:01:28Z):
Comparison, ex_dealer_coeffs (Sec5Dealer.lean:49-55).
ex55Coeffs nu b1 b2 sc hc eps: b = -(b1 . y), sigma = sc - b1 . z, h = hc - b1 . u - eps .
A_{mu^U}(u) with mu^U = mu.margU (push-forward of the law by theta |-> u), f = b2 . x, g x _ = x;
n = m = d = 1. These are the printed dealer coefficients.
affineCoeffs b1 b2 sc hc (Example 5.1(i)): b = -(b1 . y), sigma = sc - b1 . z, h = hc - b1 . u,
f = b2 . x, g x _ = x - the printed Example 5.1(i) coefficients.
Statement: forall sigma-finite nu on countably generated E, forall b1 b2 in R, sc, hc:
ex55Coeffs ... 0 = affineCoeffs ... - equality of the whole coefficient structure at eps = 0.
Quantification over all real b1, b2 (broader than b_i > 0, harmless).
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-17T16:01:35Z): none
