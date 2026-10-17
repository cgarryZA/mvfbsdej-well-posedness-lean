### A:ex:concrete: Dissertation.PaperSpec.A.ex_concrete_i_ham
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash ed839d34f480cba1cf9f26355b828c6a (pl-fp-v1:8c80bbaef3cfa4fe088b7cd654058531ed81cc400b41b4e80c26d9e363b80ede)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T12:16:01Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:15:30Z):
# Reading: ex_concrete_i_ham, clause "(i) the Hamiltonian and its minimiser"

Paper: with n = m = d = 1, sigma_c in R, h_c in L^2(nu), beta1, beta2 > 0, the Hamiltonian
H(x, y, z, u; a^b, a^sigma, a^h) = a^b y + (sigma_c + a^sigma) z + int (h_c(e) + a^h(e)) u(e) nu(de)
  + beta2/2 |x|^2 + 1/(2 beta1) (|a^b|^2 + |a^sigma|^2 + ||a^h||^2_{L^2(nu)})
"is strictly convex in the controls, with pointwise minimiser a^b* = -beta1 y,
a^sigma* = -beta1 z, a^h*(e) = -beta1 u(e)". Then (via the cited SMP of Tang-Li, not to be
formalised) the optimality system is (1.1) with b = -beta1 y, sigma = sigma_c - beta1 z,
h = h_c - beta1 u, f = d_x H = beta2 x, g(x, rho) = x.

Faithful formal statement:
- For all beta1 > 0, beta2 (> 0, or any real -- beta2 does not affect the control part),
  sigma_c, h_c in L^2(nu) on any sigma-finite nu, and every point theta = (x, y, z, u) in H:
  (a) the map a = (a^b, a^sigma, a^h) in R x R x L^2(nu) -> H(theta; a) is strictly convex
      (on the whole control space, with a^h ranging over L^2(nu) classes);
  (b) a* = (-beta1 y, -beta1 z, -beta1 u) is its (unique) minimiser: H(theta; a*) <= H(theta; a)
      for all a, with equality only at a*;
  (c) possibly: d_x H = beta2 x, and the closed-loop coefficients are those of affineCoeffs
      (b = a^b*, sigma = sigma_c + a^sigma*, h = h_c + a^h*, f = d_x H, g = x).
- The integral int (h_c + a^h) u dnu must be the L^2(nu) inner product (well defined for
  L^2 classes).
- The SMP step (the Pontryagin system is the optimality system) is a cited result; its omission
  is not a defect of this clause.
Comparison (verdict recorded 2026-10-17T12:15:53Z):
# Comparison: ex_concrete_i_ham

Lean (Sec5.lean:75): for every measurable space E and EVERY measure nu on it (no sigma-finiteness),
beta1 > 0, beta2 in R (any sign), sigma_c in R^{1x1}, h_c in L^2(nu; R^1), and every point
(x, y, z, u) of H: with
H(a) = <a^b, y> + <sigma_c + a^sigma, z> + int <h_c(e) + a^h(e), u(e)> nu(de) + beta2/2 |x|^2
       + 1/(2 beta1) (|a^b|^2 + |a^sigma|^2 + ||a^h||^2),
a in R^1 x R^{1x1} x L^2(nu; R^1): StrictConvexOn R univ H, and H(-beta1 y, -beta1 z, -beta1 u)
<= H(a) for all a.

Against my reading:
- (a) strict convexity on the whole control space: yes (StrictConvexOn univ).
- (b) minimiser a* = (-beta1 y, -beta1 z, -beta1 u): yes; uniqueness follows from strict
  convexity (a strictly convex function has at most one minimiser), so "the pointwise
  minimiser" is captured.
- The nu-integral is the Bochner integral of <h_c(e) + a^h(e), u(e)> over representatives, which
  is the L^2(nu) inner product and independent of representatives: correct.
- (c) d_x H = beta2 x and the closed-loop identification with the affine coefficients are not
  stated; the latter depends on the cited SMP (Tang-Li) and the former is elementary. The
  clause is named "the Hamiltonian and its minimiser", so this is not a lost case of this
  clause.
- Generality: nu is any measure and beta2 any real, whereas the example has nu sigma-finite on
  a countably generated E and beta2 > 0. The proposition is therefore broader than printed, in
  parameters that do not affect the claim; the printed claim is the instance nu sigma-finite on
  countably generated E, beta2 > 0.
- Non-vacuity: only hypothesis beta1 > 0; trivially satisfiable (no witness needed).

Verdict: broader.
Witness: —
Verdict: broader — The proposition quantifies over every measure nu on any measurable space E (the example has nu
sigma-finite on a countably generated E) and every beta2 in R (the example has beta2 > 0); the
x-term beta2/2 |x|^2 is constant in the controls, so neither generalisation changes the claim.
The printed claim is the instance with nu sigma-finite on a countably generated E and beta2 > 0
(any beta1 > 0, sigma_c in R, h_c in L^2(nu), point (x, y, z, u) of H). Otherwise the statement is
exactly the printed one: strict convexity on R x R x L^2(nu) and the minimiser
(-beta1 y, -beta1 z, -beta1 u), unique by strict convexity. Not stated (and not required by this
clause): d_x H = beta2 x and the SMP identification of the optimality system with (1.1).
Disagreements with the author's review (shown 2026-10-17T12:15:53Z): Essentially none: the author's verdict line itself records ex_concrete_i_ham as broader (beta2
arbitrary). I would add that nu is also generalised to an arbitrary measure (not sigma-finite,
on any measurable space), which the author's proposition summary says ("for every measure nu")
but the verdict line does not list; both generalisations are harmless and the printed claim is
the instance nu sigma-finite on a countably generated E, beta2 > 0.
