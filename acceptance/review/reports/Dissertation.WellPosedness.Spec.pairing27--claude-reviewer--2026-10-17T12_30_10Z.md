### A:ass:mono, A:cor:robust, A:ex:brownian, A:ex:concrete, A:lem:cont, A:lem:pert, A:rem:diag-mono, A:rem:generalrank, A:rem:intrinsic, A:sec4:horizon-not-contractive, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: Dissertation.WellPosedness.Spec.pairing27
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash ede49a3a3551d3de0749c24d2bf7198b (pl-fp-v1:7ef1c9d19252b431821d610904ff48d1f11792c940c40feb0884a82deb48000e)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T12:30:10Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:29:03Z):
Reading: pairing27 = the integrand of the expectation on the left of (2.7), evaluated at one
time t and two points (theta, mu), (theta', mu') of H x P_2(H) (the expectation is applied by
Assumption 2.5 along diagonal inputs Theta(omega), Law Theta).

With theta = (x,y,z,u), theta' = (x',y',z',u'), G in R^{m x n}, delta b = b(t,theta,mu) -
b(t,theta',mu') in R^n, delta sigma in R^{n x d}, delta f in R^m, delta h = h(t,theta,.,mu) -
h(t,theta',.,mu') in L^2(nu;R^n), delta x = x - x', delta y in R^m, delta z in R^{m x d},
delta u in L^2(nu;R^m):

  pairing = <delta b, G^T delta y>_{R^n} + <delta sigma, G^T delta z>_F
            + <-delta f, G delta x>_{R^m} + int_E <delta h(e), G^T delta u(e)> nu(de)

with G^T delta z the n x d matrix product, <.,.>_F the Frobenius inner product, and the last term
the L^2(nu;R^n) inner product of delta h and G^T delta u (G^T applied pointwise in e, which is a
well-defined element of L^2(nu;R^n)). Real-valued. Signs: minus on the f channel only. All four
coefficients evaluated at the same t; b, sigma, f, h at the non-left-limit points supplied (the
caller supplies Theta or Theta^-). A faithful Lean definition must be exactly this real number
(any equivalent rewriting, e.g. <G delta b... > by adjointness, is fine).
Comparison (verdict recorded 2026-10-17T12:30:03Z):
Comparison for pairing27 G C t theta theta' mu mu'.

TupleH = R^n x R^m x R^{m x d} x L^2(nu;R^m) (EuclideanSpace on Fin n, Fin m, Fin m x Fin d, Lp),
so theta.1 = x, theta.2.1 = y, theta.2.2.1 = z, theta.2.2.2 = u.
- term 1: inner (b(t,theta,mu) - b(t,theta',mu')) (GX G^T (y - y')): GX G^T = x |-> G^T x on
  R^m -> R^n (toEuclideanLin of G^T). = <delta b, G^T delta y>. OK.
- term 2: inner (sigma - sigma') (GZ G^T (z - z')): GZ G^T is the Kronecker G^T (x) I_d on
  coordinates (k,j), i.e. (G^T z)_{ij} = sum_k G_{ki} z_{kj}, the n x d matrix product; the inner
  product on EuclideanSpace (Fin n x Fin d) is the Frobenius one. = <delta sigma, G^T delta z>_F.
- term 3: inner (-(f - f')) (GX G (x - x')) = <-delta f, G delta x>. OK, sign as printed.
- term 4: integral over nu of inner (h(t,theta,mu) e - h(t,theta',mu') e) (G^T (u e - u' e)),
  with pointwise representatives of the Lp classes. The integrand is a.e.-strongly measurable and
  bounded by |delta h(e)| ||G|| |delta u(e)|, a product of two L^2(nu) functions, hence integrable,
  so the Bochner integral is the genuine value (no junk 0), equal to the L^2(nu;R^n) inner product
  <delta h, G^T delta u>; changing representatives changes the integrand only nu-a.e.
- one time t, both points evaluated at the supplied (theta, mu), (theta', mu'). Real-valued.

Exactly the integrand of (2.7). Faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-17T12:30:03Z): No disagreement in substance. The author review shows only a marker (definitions.md:212) and no recorded reading; it should note that the nu-integral of the fourth term is of an integrable function (product of two L^2(nu) functions), so it is the L^2(nu) inner product and never the Bochner junk value.
