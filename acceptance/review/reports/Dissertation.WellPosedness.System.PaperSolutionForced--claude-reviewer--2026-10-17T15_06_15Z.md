### A:eq:forced, A:lem:cont, A:lem:small, A:sec4:WP-def: Dissertation.WellPosedness.System.PaperSolutionForced
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 879f49cf215ebc960000000000000000 (pl-fp-v1:fa4a1becfe4d7886db95c94d9b3d6e42d020800e2a5cb485ebff132e098d2088)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:06:15Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:33:34Z):
Reading for PaperSolutionForced (paper §4: solution in HH of the lambda-scaled forced system (4.1)).
Setting as in §2. Given lambda in [0,1], an F_0-measurable initial datum xi_0 (in L^2), and a
square-integrable forcing q = (q^b, q^sigma, q^h, q^f, q^g_T) (q^b, q^sigma, q^f progressively measurable
in L^2(Omega x [0,T]), q^h predictable P(x)calE-measurable square integrable for dP dt nu, q^g_T in
L^2(Omega, F_T; R^m)). A solution is Theta = (X,Y,Z,U) in HH (X, Y cadlag adapted with E sup|.|^2 < inf;
Z in H^2_W, U in H^2_N) such that for every t in [0,T], a.s.:
 X_t = xi_0 + lambda int_0^t b(s,Theta_s,mu_s) ds + lambda int_0^t sigma(s,Theta_s,mu_s) dW_s
       + lambda int_0^t int_E h(s,Theta^-_s,e,mu^-_s) Ntilde(ds,de)
       + int_0^t q^b ds + int_0^t q^sigma dW + int_0^t int_E q^h(e) Ntilde(ds,de),
 Y_t = lambda g(X_T, Law X_T) + lambda int_t^T f(s,Theta_s,mu_s) ds + q^g_T + int_t^T q^f ds
       - int_t^T Z dW - int_t^T int_E U Ntilde.
mu_t = Law(Theta_t), mu^-_t = Law(Theta^-_t). The coefficient integrals must exist (in HH they do under
Ass 2.2-2.3 by (4.2)); WP(lambda) quantifies over every such q and asks for a unique solution in HH.
A faithful Lean definition: same as PaperSolution with the lambda scalings and additive forcings
(lambda multiplying b, sigma, h, g, f but not the forcings, not xi_0, and not Z, U), forcing terms
entering with the signs shown, the HH class (S^2 for X and Y). Lambda = 1, q = 0 must reduce to
PaperSolution.
Comparison (verdict recorded 2026-10-17T12:40:29Z):
Comparison for PaperSolutionForced (System/PaperSolutionForced.lean:111), read with Forcing
(System/Coefficients.lean:196), the PaperSolution encoding (reviewed), and its use in
PaperSpec/A/Setting.lean (ForcedSolution = exists gamma, PaperSolutionForced over enlJoint, plus
every-path left limits; WP quantifies over PredForcing q).
Against my reading:
- HH class for (X, Y, Z, U): identical fields to PaperSolution (adapted, every path right-continuous
  on [0,T), a.s. left limits, E sup |.|^2 < inf; predictable Z, marked predictable U, finite
  energies, vanishing off [0,T]).
- forcing: q is a Forcing: q^b, q^sigma, q^f jointly and progressively measurable, vanishing off
  [0,T], finite energy on [0,T]; q^h jointly measurable, marked progressively measurable, vanishing
  off [0,T], finite marked energy; q^g_T strongly F_T-measurable and in L^2. This is implied by
  PredForcing (the class WP quantifies over), and is a slightly larger class (q^h progressive) for
  the solution predicate itself; harmless.
- Forward identity, a.s. for all t in [0,T]: X_t = xi0 + int_{[0,t]} (lam b + q^b) ds + M_t +
  int_0^t int_E (lam gamma + q^h) Ntilde, M a cadlag version of int (lam sigma + q^sigma) dW. The paper
  writes lam int b + int q^b etc. separately; with both integrands square integrable (b, sigma, h
  along an HH tuple under Ass 2.2-2.3, q by hypothesis) the integrals are linear, so the forms
  agree. lam multiplies b, sigma, h(gamma), not the forcings, not xi0. Matches.
- Backward identity, a.s. for all t: Y_t = lam g(X_T, Law X_T) + q^g + int_{[t,T]} (lam f + q^f) ds
  - (M_T - M_t) - (int_0^T int U Ntilde - int_0^t int U Ntilde), M a cadlag version of int Z dW. lam
  multiplies g and f, not q^g, q^f, Z, U. Matches (4.1).
- Integrability/measurability conditions are asked of the forced integrands lam psi + q^psi; for
  lam /= 0 and q a forcing this is equivalent to the conditions on psi alone, and they hold for any
  paper solution under JointBorel + Ass 2.2-2.3 (assumed in lem:small, lem:cont, sec4 WP). At lam = 0
  they involve only q.
- jump_rep, laws, left limits, the representative gamma: as in PaperSolution.
- lam = 1, q = 0 reduces to PaperSolution (the author proves this in PaperSolutionForcedOne).
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices (harmless), in addition to those of PaperSolution (coordinate encoding,
every-path right continuity with a.s. left limits, Z/U and forcings vanishing off [0,T], exact laws
at every time, uLift junk on a null set, marked-progressive representative gamma, identities on one
null set with cadlag versions of the Brownian integrals):
1. Measurability and finite energy are asked of the forced integrands lam*psi + q^psi rather than of
   psi and q^psi separately; given q square integrable and progressive these are equivalent for
   lam /= 0, and the single integral of the sum equals the paper's sum of integrals by linearity.
2. The forcing field is Forcing (q^h marked progressively measurable, all components vanishing off
   [0,T], q^g_T strongly F_T-measurable): implied by the paper's class (PredForcing, which WP
   quantifies over); the larger class only enlarges what may be plugged in.
3. Finite energy of the forced drift and driver is more than existence of the Lebesgue integrals;
   implied under Ass 2.2-2.3, which every claim using the unit assumes.
Disagreements with the author's review (shown 2026-10-17T15:05:45Z): none (the author's excerpt shown for this unit is a marker and at most a section heading, with no
item-level reading to compare against; my comparison file records the representation choices in
detail).
