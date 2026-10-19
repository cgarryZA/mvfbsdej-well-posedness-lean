### A:sec4:horizon-not-contractive: Dissertation.WellPosedness.BrownianPoisson.LinearBSDEJ.mk
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash a259997f09ec23780000000000000000 (pl-fp-v1:f0b3e5adde3267ca80b80dd9ffabeb9ce8f05a0ec291d4dd10f24786f96de8a2)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:35:59Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:16:43Z):
# Reading: def WellPosedness.BrownianPoisson.LinearBSDEJ.mk (constructor)

The constructor of the structure LinearBSDEJ. Its meaning is the list of fields: to build a value
one must supply exactly the data and properties of a solution of the linear BSDEJ
  Y_t = xi + int_t^T phi ds - int_t^T Z dW - int_t^T int_E U Ntilde(ds,de):
the processes (Y,Z,U), Y cadlag adapted, Z and U predictable and square-integrable (H^2_W, H^2_N),
the terminal value xi in L^2(F_T) and driver phi in L^2(Omega x [0,T]), and the identity a.s. for
every t in [0,T]. A faithful constructor has argument types matching those fields (see the reading
of LinearBSDEJ); nothing extra that would make the structure uninhabitable by the paper's linear
BSDEJ solutions, and nothing missing that the paper requires.
Comparison (verdict recorded 2026-10-19T03:22:14Z):
# Comparison: def LinearBSDEJ.mk

The constructor takes exactly the fields of LinearBSDEJ, in order: Z_meas, Z_prog, Z_vanish, Z_sq,
U_meas, U_prog, U_vanish, U_sq, phi_meas, phi_prog, phi_vanish, phi_sq, xi_sq, Y_adapted,
Y_rightCont, eqn (the identity a.s. at each t in [0,T], with the canonical Ito and compensated
Poisson integrals of F built from the earlier fields). Nothing else is required, nothing is
missing relative to the structure. Its meaning is that of LinearBSDEJ, with the same
representation choices (progressive instead of predictable integrands, progressive drift,
right-continuous adapted Y, identity a.s. at each t, xi only square integrable, extension by 0 off
[0,T]); see the comparison for LinearBSDEJ.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — The constructor's arguments are exactly the fields of LinearBSDEJ, so it carries the same harmless
representation choices: (1) progressive / marked-progressive Z, U in place of predictable ones
(the L^2 integrals depend only on a.e. classes, which contain predictable representatives);
(2) a progressive drift phi (every use is progressive; an adapted solution forces a progressive
version); (3) Y adapted with right-continuous paths and the identity a.s. at each t (equivalent up
to indistinguishability to the cadlag, all-t form); (4) xi only square integrable (F_T-measurable up
to a null set via Y_T = xi); (5) scalar equation, integrands extended by 0 off [0,T].
Disagreements with the author's review (shown 2026-10-19T03:35:53Z): none
