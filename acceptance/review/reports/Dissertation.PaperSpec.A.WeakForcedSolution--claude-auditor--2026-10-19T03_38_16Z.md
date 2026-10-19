### A:lem:pert, A:sec4:WP-def: Dissertation.PaperSpec.A.WeakForcedSolution
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash 6d8e8f373c5e26dad42e89a4945d5642 (pl-fp-v1:5f4610c4ad96a71ecde2af741ff414ff5989e20447bb72029b0b044875bf0ab4)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:38:16Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:15:38Z):
Reading (locked before any Lean): def WeakForcedSolution (PaperSpec) - the solution notion of
Lemma 4.3: "Theta solves (4.1) at parameter lambda with F_0-measurable initial datum xi_0 and
forcing q, where X, Y are cadlag adapted with E int_0^T (|X|^2 + |Y|^2) dt < inf and
X_T in L2(Omega, F_T; R^n), Z in H^2_W, U in H^2_N".

Paper notion (4.1) + the weak class. Given a coefficient system (b, sigma, h, f, g), lambda in
[0,1], F_0-measurable xi_0 in R^n, a square-integrable forcing q = (q^b, q^sigma, q^h, q^f,
q^g_T) (q^b, q^sigma, q^f progressively measurable, in L2(Omega x [0,T]); q^h predictable
(P x calE-measurable), in L2(dP dt nu); q^g_T in L2(Omega, F_T; R^m)), a tuple Theta = (X, Y, Z,
U) is a weak forced solution iff
 (a) X (R^n), Y (R^m) cadlag (paths) and adapted, E int_0^T (|X_t|^2 + |Y_t|^2) dt < inf,
     X_T in L2(F_T) (so Law X_T in P_2(R^n));
 (b) Z predictable R^{m x d}-valued with E int |Z|_F^2 < inf; U predictable L2(nu;R^m)-valued
     (P x calE representative) with E int ||U||^2 < inf;
 (c) for every t in [0,T], a.s.,
     X_t = xi_0 + lambda int_0^t b(s, Theta_s, mu_s) ds + lambda int_0^t sigma(s,Theta_s,mu_s) dW_s
           + lambda int_0^t int_E h(s, Theta_s^-, e, mu_s^-) Ntilde(ds,de)
           + int_0^t q^b ds + int_0^t q^sigma dW + int_0^t int_E q^h(e) Ntilde(ds,de),
     Y_t = lambda g(X_T, Law X_T) + lambda int_t^T f(s,Theta_s,mu_s) ds + q^g_T + int_t^T q^f ds
           - int_t^T Z dW - int_t^T int_E U(e) Ntilde(ds,de),
     with mu_s = Law(Theta_s), mu_s^- = Law(Theta_s^-) (Borel representatives, agreeing with the
     true laws for a.e. s), Theta_s^- = (X_{s-}, Y_{s-}, Z_s, U_s);
 (d) implicitly: the integrals exist (the coefficient processes along Theta are integrable /
     square-integrable as needed for the Lebesgue, Ito and compensated Poisson integrals). Under
     Assumption 2.3 alone (no 2.2), these are not automatic for a weak-class Theta, so a formal
     definition must require them (or define the integrals so that a non-integrable integrand
     cannot spuriously satisfy the identity).
A faithful Lean definition: a Prop/structure with exactly these fields, using the genuine
stochastic integrals of the library, adaptedness to the standing filtration, predictability for
Z, U (or the representation used by the library, e.g. predictable P x calE-measurable U), and
not requiring more (e.g. not E sup |X|^2 < inf, not xi_0 in L2), and not less (identities at
every t a.s., or a.s. for all t - the latter is equivalent by the one-null-set argument when both
sides are cadlag). Watch: junk values of Bochner/lintegral/stochastic integrals for
non-integrable integrands, Law of a non-measurable map, the lambda-scaling placement (lambda on
b, sigma, h, f, g, not on forcings), the sign conventions, and whether the forcing measurability
conditions are part of the definition or of the surrounding statement.
Comparison (verdict recorded 2026-10-19T03:32:33Z):
Comparison: def WeakForcedSolution (Setting.lean:98-114) against my locked reading.

Definition: exists gamma, PaperWeakSolutionForcedInt over the standing filtration enlJoint (with
the Brownian and Poisson filtration certificates), and every path of every coordinate of X and Y
has left limits on (0,T].

Item by item against the paper's notion (Lemma 4.3's class, (4.1)):
(a) X, Y: adapted on [0,T], every path right-continuous on [0,T), left limits (a.s. in
    PaperWeakTuple, every path by the extra conjunct), E int_0^T |X|^2, E int_0^T |Y|^2 finite
    (PaperWeakTuple.X_sq, Y_sq), X_T in L2 (XT_sq). Matches "cadlag adapted with
    E int (|X|^2 + |Y|^2) < inf and X_T in L2"; no S^2 bound, as required.
(b) Z predictable, U marked predictable (P x calE), finite energies, vanishing off [0,T]:
    H^2_W, H^2_N. Matches.
(c) Forcing: field `forcing : Forcing` (q^b, q^sigma, q^f jointly and progressively measurable,
    square integrable, vanishing off [0,T]; q^h marked progressive, square integrable; q^g_T
    F_T-measurable in L2). This is slightly more permissive than the paper's forcing class (q^h
    predictable), a harmless widening of the predicate: lem_pert adds PredForcing for both forcings.
(d) Integrals exist: forced drift lambda b + q^b and driver lambda f + q^f jointly and
    progressively measurable with a.s. integrable paths (no finite energy, as Assumption 2.2 is
    not assumed); forced diffusion lambda sigma + q^sigma and jump lambda gamma + q^h (gamma cut to
    [0,T]) with finite energy (L2 stochastic integrals); gamma represents h(s, Theta^-_s, ., mu^-_s)
    in L2(nu) for a.e. s a.s. Since q is square integrable, conditions on the combined integrands
    are equivalent to conditions on lambda psi. For the Brownian channel the L2 requirement loses
    no paper solution (with Assumption 2.3, a.s. local square integrability along an Hweak tuple
    forces sigma(., 0, delta_0) in L2(0,T) and finite energy). For the jump channel it is the
    paper's L2 framework for Poisson integrals.
(e) Identities: X_t = xi0 + int_{[0,t]} (lambda b + q^b) + M_t + int_0^t int_E (lambda gamma + q^h)
    dNtilde, M a cadlag version of int (lambda sigma + q^sigma) dW; Y_t = lambda g(X_T, Law X_T) +
    q^g_T + int_{[t,T]} (lambda f + q^f) - (M_T - M_t) - (int U dNtilde)_t^T, M a cadlag version of
    int Z dW; on one null set for all t in [0,T] (equivalent to a.s. for every t). The lambda
    placement (on b, sigma, h, f, g; forcings unscaled) and the signs are those of (4.1). By
    linearity of the integrals, combining coefficient and forcing integrands is the same as the
    paper's separate integrals.
(f) Law flows: mu_s = lawP2 P Theta_s and mu^-_s = lawP2 P Theta^-_s at every time (Dirac at 0 off
    L2, only on a null set of times for this class), agreeing a.e. with the paper's Borel
    representatives.
(g) xi0: no measurability in the definition; the lemma assumes F_0-measurability separately.
Junk values: integrals are taken only with their integrability certificates; uLift and lawP2
fallbacks occur only on null sets. No junk satisfies the identities spuriously.

Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless:
1. The forced integrands lambda psi + q^psi are combined in single integrals. With q square
   integrable, conditions on them are equivalent to conditions on lambda psi, and the integrals
   split by linearity.
2. Stochastic integrals are L2 integrals (finite energy of the forced diffusion and jump
   integrands), drift and driver pathwise. The L2 requirement loses nothing in the Brownian
   channel under Assumption 2.3 and is the paper's framework for Poisson integrals.
3. The forcing field is the class Forcing, whose q^h is only marked progressive: a widening of the
   paper's predictable class, compensated in Lemma 4.3 by the separate PredForcing hypothesis.
4. Cadlag adapted X, Y: right-continuous every path, left limits every path (a null-set
   modification of any paper solution; the filtration is augmented), adapted on [0,T]; Z, U
   vanish off [0,T].
5. Law flows lawP2 at every time; gamma a marked progressive representative of the predictable
   h(s, Theta^-_s, ., mu^-_s); identities on one null set for all t; the F_0-measurability of xi0
   is left to the statements using the definition.
Disagreements with the author's review (shown 2026-10-19T03:38:06Z): none (I add that the L2 requirement on the forced diffusion integrand loses no paper solution under Assumption 2.3, and that requiring every path to have left limits is a null-set modification of any paper solution; both reviews agree on the verdict)
