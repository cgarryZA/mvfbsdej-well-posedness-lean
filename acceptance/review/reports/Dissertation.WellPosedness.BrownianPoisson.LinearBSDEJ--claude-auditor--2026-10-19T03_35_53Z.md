### A:sec4:horizon-not-contractive: Dissertation.WellPosedness.BrownianPoisson.LinearBSDEJ
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash 61bb9f1d9c8aba870000000000000000 (pl-fp-v1:b515c3a31d7d6c9d201a61c5e87d42521d3db4eee7db121657e460813f7cf634)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:35:53Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:16:43Z):
# Reading: def WellPosedness.BrownianPoisson.LinearBSDEJ (used by sec4_horizon_not_contractive)

Paper notion: the linear (frozen-driver) BSDE with jumps on the Brownian-Poisson basis, as in
Lemma 4.1 (eq. dYlin) and the frozen backward equation (frozenbwd):
  Y_t = xi + int_t^T phi_s ds - int_t^T Z_s dW_s - int_t^T int_E U_s(e) Ntilde(ds,de),  t in [0,T],
with data xi in L^2(Omega,F_T;R^m) and phi in L^2(Omega x [0,T];R^m) progressive (the driver does
not depend on the unknown), and a solution (Y,Z,U) with Y cadlag adapted, Z in H^2_W (predictable,
E int |Z|_F^2 < oo), U in H^2_N (predictable L^2(nu)-valued / P (x) E-measurable,
E int ||U||^2 dt < oo). In the frozen step it is solved by M_t = E[Xi | F_t] and the PRP.

A faithful Lean structure "LinearBSDEJ" (a solution record of this linear BSDEJ) must carry:
* the processes Y (R^m), Z (R^{m x d}), U (L^2(nu;R^m)-valued or a function of (omega,t,e));
* Y cadlag and adapted to the standing filtration; Z, U predictable w.r.t. the standing
  filtration's predictable sigma-field; square-integrability of Z and U;
* the identity above holding a.s. for every t in [0,T] (or a.s. simultaneously in t), with the
  stochastic integrals the Ito integral against the standing W and the compensated Poisson integral
  against the standing Ntilde; terminal value xi (F_T-measurable, square-integrable) and driver phi
  (square-integrable).
Edge cases: integrals of non-integrable integrands are junk (0) in Lean, so the square-integrability
fields are what make the identity meaningful; "for every t a.s." vs "a.s. for all t" are equivalent
for cadlag processes; the dimension of Y may be generic (m) or fixed.
Comparison (verdict recorded 2026-10-19T03:21:59Z):
# Comparison: def LinearBSDEJ

Lean (WellPosedness/BrownianPoisson/Hypotheses.lean): a structure (Prop) over a Levy driver D, a
filtration F for which each coordinate of W is an F-Brownian motion and N is an F-Poisson random
measure, T, terminal xi : Omega -> R, drift phi : Omega -> R -> R, and (Y, Z, U) with fields
Z_meas, Z_prog (progressive), Z_vanish (0 off [0,T]), Z_sq (E int_0^T |Z|^2 < oo); U_meas, U_prog
(marked progressive), U_vanish, U_sq (E int_0^T int_E |U|^2 nu de dt < oo); phi_meas, phi_prog,
phi_vanish, phi_sq; xi_sq (xi in L^2); Y_adapted (F-adapted at every time); Y_rightCont (every path
right-continuous); eqn: for each t in [0,T], a.s.
  Y_t = xi + int_{[t,T]} phi ds - (int_0^T Z dW - int_0^t Z dW) - (int_0^T int U dNtilde - int_0^t ...),
with the canonical L^2 stochastic integrals of F.

Against my reading:
* Processes and value spaces: scalar Y, Z in R^d, U a function of (omega,s,e); the R^m-valued
  equation is a family of m scalar ones (how it is used). OK.
* Square-integrability of Z, U, phi and xi: yes (energies, MemLp).
* The identity: yes, with int_t^T written as int_0^T - int_0^t, the Ito integral against the
  standing W and the compensated integral against the standing Ntilde.
Representation choices:
1. Z, U are progressive / marked progressive rather than predictable. The integrals are the L^2
   (isometric) extensions, which depend only on the dP x dt (x nu) class of the integrand, and every
   square-integrable progressive (marked progressive) process agrees a.e. with a predictable one;
   so the integrands and integrals are the paper's classes, matching (2.4)'s convention that
   Poisson integrands are read through a P (x) E representative.
2. phi is required progressive, whereas Lemma 4.1 says only phi in L^2(Omega x [0,T]). In every
   use phi is progressive (lambda f along a tuple + q^f), and for any solution with Y adapted,
   int_0^t phi ds = Y_0 - Y_t + (martingale terms) is adapted and continuous, so phi has a
   progressive version a.e.; harmless.
3. Y adapted with right-continuous paths, left limits not required; the equation a.s. at each t.
   Given right-continuity, Y is indistinguishable from the cadlag right-hand side, so this is the
   paper's notion up to indistinguishability.
4. xi only square integrable (F_T-measurability not asked): Y_T = xi a.s. with Y_T F_T-measurable
   and F complete, so xi is F_T-measurable up to a null set.
5. Integrands extended by 0 off [0,T]; adaptedness/right-continuity at times outside [0,T] are free
   (any constant extension works).
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless:
1. Z and U are progressively / marked-progressively measurable instead of predictable; the
   stochastic integrals are the L^2 isometric ones, determined by the a.e. class of the integrand,
   and a square-integrable progressive process agrees dP x dt (x nu)-a.e. with a predictable one, as
   the paper's convention (2.4) on representatives allows.
2. The drift phi is required progressive (Lemma 4.1 says phi in L^2(Omega x [0,T])): every use has
   a progressive phi, and for an adapted solution int_0^t phi ds is adapted and continuous, so phi
   has a progressive version a.e.
3. Y is adapted with right-continuous paths (left limits not required) and the identity holds a.s.
   at each t; Y is then indistinguishable from the cadlag right-hand side.
4. xi is only square integrable; Y_T = xi a.s. with the filtration complete makes it F_T-measurable
   up to a null set.
5. Scalar equation (R^m as m scalar equations); integrands extended by 0 off [0,T].
Disagreements with the author's review (shown 2026-10-19T03:35:46Z): none
