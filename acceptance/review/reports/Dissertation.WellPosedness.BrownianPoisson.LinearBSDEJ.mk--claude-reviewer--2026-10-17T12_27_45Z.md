### A:sec4:horizon-not-contractive: Dissertation.WellPosedness.BrownianPoisson.LinearBSDEJ.mk
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash a259997f09ec23780000000000000000 (pl-fp-v1:f0b3e5adde3267ca80b80dd9ffabeb9ce8f05a0ec291d4dd10f24786f96de8a2)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T12:27:45Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:25:42Z):
Unit: def LinearBSDEJ.mk (constructor of the structure LinearBSDEJ, namespace BrownianPoisson).
Used by claim A:sec4:horizon-not-contractive (§4 intro, line 886), which concerns the frozen-
coefficient map Phi_lambda of Lemma 4.2 (lem:small), whose backward half is the "frozen linear
BSDE" (eq:frozenbwd), and whose difference is the linear BSDEJ (eq:dYlin) of Lemma 4.1.

Paper notion (eq:dYlin / eq:frozenbwd): a linear BSDE with jumps on the standing
Brownian-Poisson basis (W d-dim BM, N Poisson random measure with sigma-finite intensity
dt nu(de), filtration = usual augmentation of sigma(W, N, F_0)): data
  * terminal value xi in L^2(Omega, F_T; R^m),
  * driver phi in L^2(Omega x [0,T]; R^m), progressively measurable (an exogenous process,
    the driver does NOT depend on (Y,Z,U) -- that is what "linear"/"frozen" means here),
and a solution triple
  * Y cadlag adapted R^m-valued,
  * Z in H^2_W(0,T; R^{m x d}) predictable, E int |Z|_F^2 < inf,
  * U in H^2_N(0,T; L^2(nu;R^m)) predictable (P x E-measurable representative), 
    E int ||U||^2 dt < inf,
with, a.s. for every t in [0,T],
  Y_t = xi + int_t^T phi_s ds - int_t^T Z_s dW_s - int_t^T int_E U_s(e) Ntilde(ds,de).

A faithful constructor: a structure whose fields are exactly these processes with these
measurability/integrability conditions (relative to the standing filtration), and the
backward identity holding at every t (a.s., null set possibly depending on t is equivalent
because both sides are cadlag), where the stochastic integrals are the Ito integral against
the given W and the compensated Poisson integral against the given N. Lemma 4.1 moreover
concludes Y in S^2, so S^2 need not be a field (it may be one if a hypothesis xi, phi in L^2
is also carried). Junk-value issues to check: the stochastic integrals must be the genuine
L^2 integrals (not 0 by a totality convention) on the integrands supplied; the drift
integral int_t^T phi must be the Lebesgue integral along paths (a.s. integrable); the
filtration must be the standing one.
Comparison (verdict recorded 2026-10-17T12:27:38Z):
Comparison, LinearBSDEJ.mk (the constructor of the Prop-structure LinearBSDEJ, Hypotheses.lean:54).

Reading item -> Lean:
* basis W, N, filtration: D : LevyDriver (d-dim BM W and PRM N with sigma-finite nu, independent);
  the filtration is a parameter F with hFW (each W^j Brownian for F) and hFN (N Poisson for F).
  The paper's filtration is one instance (the spec instantiates enlJoint, reviewed separately).
  Parametric generality in F is fine for a definition.
* xi in L^2(F_T): MemLp xi 2 P; F_T-measurability not required. Harmless: eqn at t = T gives
  Y_T = xi a.s. (integral over Icc T T is 0, integral differences vanish), and Y_T is
  F_T-measurable by Y_adapted, so xi is a.s. equal to an F_T-measurable variable.
* phi in L^2(Omega x [0,T]): jointly measurable, progressive, energy finite, vanishing off [0,T].
  Progressivity is stronger than the paper's bare L^2 in Lemma 4.1, but every driver the paper
  feeds to the linear equation (lambda f(s,Theta_s,mu_s) + q^f, lambda delta f) is progressive.
* Y cadlag adapted: Adapted F Y and every path right-continuous (left limits not asked).
  Harmless: the right side of the equation has a cadlag modification, Y agrees with it a.s.
  at each rational time, and both are right-continuous, so Y is a.s. cadlag.
* Z in H^2_W predictable: coordinates jointly measurable, progressive, finite energy, vanishing off
  [0,T]; Z : Fin d -> R is one row of the R^{m x d} integrand (the equation is scalar; the R^m
  equation is m decoupled scalar ones, as Z dW and U Ntilde act row/coordinatewise).
  Progressive versus predictable is harmless for the continuous Brownian integrator.
* U in H^2_N predictable: a pointwise function Omega x R x E -> R, jointly measurable, marked
  progressive, finite marked energy, vanishing off [0,T]. The compensated integral of the library
  is the L^2 (isometric) integral, determined by the dt x dP x nu class of the integrand, and a
  progressive integrand has a predictable version in that class; the paper itself reads every
  Poisson integral through a P x E-measurable representative (eq:fubiniiso). Harmless.
* Equation: for each t in [0,T], a.s., Y_t = xi + int_{[t,T]} phi - (I^W_T - I^W_t)
  - (I^N_T - I^N_t), with I^W the library's multidimensional Ito integral (sum of coordinate L^2
  integrals) and I^N the library's cadlag compensated Poisson integral, both for F. The null set
  depends on t; equivalent to the paper's form (both sides cadlag up to modification). The
  Bochner drift integral is genuine a.s. because finite energy makes phi(omega,.) in L^1[0,T]
  for a.e. omega. Integral over Icc vs (t,T]: Lebesgue-null difference.
* Vanishing off [0,T] of Z, U, phi: a normalisation; only values on [0,T] enter the equation.
* No S^2 requirement on Y: matches Lemma 4.1, which concludes it.

No junk-value problem found: the stochastic integrals are fed the proofs of their own
hypotheses (derived from vanishing + finite energy), so they are the genuine integrals.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless:
1. Scalar equation (Y real, Z a row Fin d -> R, U real-valued in the mark): the R^m-valued
   linear BSDEJ is m decoupled scalar ones (users quantify over the component k).
2. Filtration is a parameter F with W Brownian and N Poisson for F; the paper's filtration is
   the instance used by the statements.
3. Y adapted with right-continuous paths, left limits not asked: Y equals a.s. at each time a
   cadlag modification of the right side, so it is a.s. cadlag.
4. xi only MemLp 2, not F_T-measurable: the equation at t = T forces xi = Y_T a.s.
5. phi, Z progressive and U marked progressive (pointwise function of the mark), not predictable:
   the library integrals are L^2-isometric integrals of dt x dP (x nu) classes, which contain
   predictable versions; the paper reads Poisson integrals through such representatives.
   phi progressive is stronger than Lemma 4.1's bare L^2 drift, but all drivers the paper uses
   are progressive.
6. Z, U, phi vanish off [0,T]: normalisation, only values on [0,T] enter.
7. Equation a.s. at each t (null set depending on t), equivalent to the a.s.-for-all-t form for
   cadlag sides.
Disagreements with the author's review (shown 2026-10-17T12:27:38Z): The author's review is an empty marker (no text at acceptance/review/definitions.md:400): it
records no comparison. No disagreement on substance; the representation choices listed in my
detail (scalar form, right-continuity only, xi not F_T-measurable, progressive rather than
predictable integrands, vanishing off [0,T]) are not recorded by the author and should be.
