### A:ex:concrete, A:ex:dealer, A:rem:uniq-no-integ, A:sec4:horizon-not-contractive, A:sec5:overview: Dissertation.WellPosedness.Existence.affineCoeffs
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash f17e5fb23dc1dc13867a3e931c8f06af (pl-fp-v1:98a64588a8544358c8238771b6417b1b541ff1b029e2115bb68a25694a05610b)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:50:57Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T15:41:49Z):
Reading for def:Dissertation.WellPosedness.Existence.affineCoeffs (Example 5.1(i)).

Paper notion: the law-free affine coefficients, n = m = d = 1, G = 1, parameters sigma_c in R,
h_c in L^2(nu), beta_1, beta_2 (> 0 in the example):
  b = -beta_1 y,  sigma = sigma_c - beta_1 z,  h(e) = h_c(e) - beta_1 u(e),
  f = beta_2 x,   g(x, rho) = x,
with no dependence on t or on the measure argument.

Faithful Lean: the coefficient system with exactly these components (in 1-d types: R^1 Euclidean,
1 x 1 matrices, L^2(nu;R^1)), parameterised by sigma_c, h_c, beta_1, beta_2. A general-dimension
version (n = m, G = I, matrices) instantiating to this at n=m=d=1 would be a broader representation;
the signs (minus on b, sigma, h; plus beta_2 x for f; g = x) must be exactly the paper's. Edge
cases: identification of R with EuclideanSpace R (Fin 1) and of R^{1x1}; sigma_c may enter as a
1x1 matrix; h_c as an element of L^2(nu;R^1). It should not require beta_1, beta_2 > 0 in the
definition (positivity belongs to the propositions), but it is harmless if it takes them.
Comparison (verdict recorded 2026-10-17T15:50:04Z):
Comparison for def:Dissertation.WellPosedness.Existence.affineCoeffs (Existence/AffineExample.lean:66-75):
affineCoeffs beta1 beta2 sigmac hc : Coeffs nu n n d with
  b _ theta _ = -(beta1 . y), sigma _ theta _ = sigmac - beta1 . z, h _ theta _ = hc - beta1 . u,
  f _ theta _ = beta2 . x, g x _ = x,
for theta = (x, y, z, u) (theta.1 = x, theta.2.1 = y, theta.2.2.1 = z, theta.2.2.2 = u), with
sigmac in R^{n x d}, hc in L^2(nu;R^n), any n = m and d.

Signs and slots: exactly the paper's b = -beta1 y, sigma = sigma_c - beta1 z, h(e) = h_c(e) - beta1 u(e),
f = beta2 x, g(x, rho) = x; no dependence on t or on the law. beta1, beta2 are free reals in the
definition (positivity belongs to the propositions), as my reading allowed. The definition is
broader than the paper's Example 5.1(i), which fixes n = m = d = 1 (G = 1): it is the same affine
system in any dimension n = m and any d (sigma_c an n x d matrix, h_c in L^2(nu;R^n)). The printed
object is the instance n = d = 1, with sigma_c in R identified with a 1x1 matrix (EuclideanSpace R
(Fin 1 x Fin 1)), h_c in L^2(nu;R^1), R identified with EuclideanSpace R (Fin 1). Verdict: broader.
Witness: —
Verdict: broader — The definition is the law-free affine system of Example 5.1(i) in arbitrary dimension n = m and
Brownian dimension d (sigma_c an n x d matrix, h_c in L^2(nu;R^n)); the paper's Example 5.1(i) is the
instance n = d = 1 (so m = 1, G = 1), with sigma_c in R read as the 1x1 matrix in
EuclideanSpace R (Fin 1 x Fin 1), h_c in L^2(nu;R) as Lp (EuclideanSpace R (Fin 1)) 2 nu, and R as
EuclideanSpace R (Fin 1): affineCoeffs (n := 1) (d := 1) beta1 beta2 sigma_c h_c. The components
(b = -beta1 y, sigma = sigma_c - beta1 z, h = h_c - beta1 u, f = beta2 x, g = x) are exactly the paper's.
Disagreements with the author's review (shown 2026-10-17T15:50:12Z): The author's entry shown is only the section heading, so there is no stated position to disagree
with; I classify the definition as broader than the paper's Example 5.1(i): it is the same affine
system for any n = m and d, and the printed object is the instance n = d = 1 (sigma_c a 1x1 matrix,
h_c in L^2(nu;R^1)).
