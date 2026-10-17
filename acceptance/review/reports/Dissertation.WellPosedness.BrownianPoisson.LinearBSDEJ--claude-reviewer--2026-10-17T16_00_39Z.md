### A:sec4:horizon-not-contractive: Dissertation.WellPosedness.BrownianPoisson.LinearBSDEJ
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 61bb9f1d9c8aba870000000000000000 (pl-fp-v1:b515c3a31d7d6c9d201a61c5e87d42521d3db4eee7db121657e460813f7cf634)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T16:00:39Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T15:42:31Z):
Reading for def:Dissertation.WellPosedness.BrownianPoisson.LinearBSDEJ (locked before seeing Lean).

Paper notion: the linear BSDE with jumps of Lemma 4.1 (eq:dYlin), also the frozen BSDE (4.4):
 delta Y_t = xi + int_t^T phi_s ds - int_t^T Z_s dW_s - int_t^T int_E U_s(e) Ntilde(ds,de),
for every t in [0,T], a.s., where Y is cadlag adapted (R^m), Z in H^2_W (predictable,
E int |Z|_F^2 < inf), U in H^2_N (predictable / P(x)E-measurable, E int ||U||^2 < inf),
xi in L^2(F_T), phi in L^2(Omega x [0,T]) progressively measurable. The stochastic integrals are
the L^2 Ito integral against W and the compensated-Poisson integral against Ntilde.

Faithful Lean: a predicate on (Y, Z, U) given (xi, phi) (the data may be hypotheses rather than
part of the predicate) stating the identity a.s. for each t in [0,T] (or indistinguishably),
with the integrals being the genuine L^2 stochastic integrals of the library, and with the
membership/regularity conditions either included or imposed where it is used. Junk: Lean's
Bochner integral of a non-integrable phi is 0; with phi in L^2(Omega x [0,T]) the ds-integral
is genuine for a.e. omega. "int_t^T" = int_0^T - int_0^t is fine.
Comparison (verdict recorded 2026-10-17T15:49:31Z):
Comparison for def:Dissertation.WellPosedness.BrownianPoisson.LinearBSDEJ.

Lean (BrownianPoisson/Hypotheses.lean): structure LinearBSDEJ D F hFW hFN T xi phi Y Z U, scalar Y : R -> Omega -> R,
Z : R -> Omega -> (Fin d -> R) (a row of R^{1 x d}), U : R -> Omega -> E -> R, phi : Omega -> R -> R:
Z jointly measurable, progressive, 0 off [0,T], finite energy E int_0^T |Z|^2; U jointly measurable,
marked progressive, 0 off [0,T], finite marked energy E int_0^T int_E U^2 dnu dt; phi jointly measurable,
progressive, 0 off [0,T], finite energy; xi in L^2; Y adapted, every path right-continuous; and for each
t in [0,T], a.s. Y_t = xi + int_{[t,T]} phi ds - (I^W_T - I^W_t) - (I^N_T - I^N_t), with I^W the
library's multidimensional L^2 Ito integral of Z against D.W and I^N the library's compensated Poisson
L^2 integral of U against D.N (cadlag modification of the L^2 limit of step approximants), over a
filtration F for which W is Brownian and N is Poisson.

Item by item against my reading:
- the identity a.s. at each t in [0,T], with the genuine L^2 stochastic integrals: yes.
- scalar instead of R^m: the vector equation of (4.2)/(4.4) holds iff it holds coordinatewise (the
  equation and the integrability conditions are coordinatewise); the users apply it per coordinate.
  Representation choice.
- Z, U progressive (marked progressive) rather than predictable: broader class. Every progressive
  square-integrable integrand is dt(x)dP(-x nu)-a.e. equal to a predictable one, and the library
  integrals are L^2-isometric (they depend only on the L^2 class), so the integrals are those of
  the predictable versions. Harmless.
- phi progressive in L^2(Omega x [0,T]): yes. The ds-integral is a Bochner integral; finite energy
  makes almost every path integrable on [0,T], so the junk 0 value arises only on a null set of
  omega.
- xi in L^2: F_T-measurability is not required, but Y adapted and the equation at t = T give
  xi = Y_T a.s., so xi is a.s. F_T-measurable; equivalent up to null sets.
- Y cadlag adapted: Lean asks adapted and every path right-continuous, not left limits. Left limits
  follow a.s.: Y is a right-continuous modification of the cadlag process
  xi + int phi - (I_T - I_.) (the library integrals are cadlag), hence indistinguishable from it.
  Requiring every path (not a.s.) right-continuous, and on all of R, is a mild strengthening of
  the version; on the augmented filtrations used a version with every path right-continuous
  always exists. Representation choice.
- extension by 0 off [0,T] for Z, U, phi: a convention, harmless (only [0,T] is used).
- the filtration: any filtration for which W is Brownian and N Poisson, broader than the standing
  augmented one; Lemma 4.1's statement does not use the representation property, so harmless.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices: (1) scalar (one coordinate) form of the R^m-valued linear BSDEJ; the
vector equation is the conjunction of its coordinates; (2) Z and U progressive / marked
progressive instead of predictable: every such square-integrable integrand is a.e. equal to a
predictable one and the library integrals depend only on the L^2 class; (3) integrands and drift
extended by 0 off [0,T]; (4) Y required adapted with every path right-continuous on R, left limits
not required (they hold a.s. since Y is then indistinguishable from the cadlag right-hand side);
(5) xi only square integrable, its F_T-measurability following a.s. from the equation at t = T
and adaptedness; (6) a general filtration for which W is Brownian and N Poisson (the standing one
is an instance).
Disagreements with the author's review (shown 2026-10-17T16:00:30Z): No disagreement on the meaning; points the author's review omits:
(1) the def is scalar (one coordinate), the R^m-valued equation being coordinatewise;
(2) Z and U are only progressive (marked progressive), whereas Lemma 4.1 takes dZ in H^2_W and dU in
    H^2_N predictable: a broader class, harmless because the library integrals depend only on the
    L^2 class and progressive integrands have a.e.-equal predictable versions;
(3) xi is only required square integrable, its F_T-measurability following a.s. from adaptedness
    of Y and the equation at t = T;
(4) Y is required right-continuous on every path but not to have left limits (they hold a.s.
    because Y is then indistinguishable from the cadlag right-hand side);
(5) the filtration is any one for which W is Brownian and N Poisson.
The phrase "in the sense of the paper's S^2 processes except that E sup |Y|^2 is not part of it" is
slightly off: Lemma 4.1 assumes only cadlag adapted Y (S^2 is its conclusion), so the def matches
the lemma's hypothesis, not an S^2 notion with a part removed.
