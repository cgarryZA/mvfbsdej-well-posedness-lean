### A:lem:pert, A:sec4:WP-def: Dissertation.WellPosedness.System.PaperWeakSolutionForcedInt
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 879f49cf215ebc960000000000000000 (pl-fp-v1:fa4a1becfe4d7886db95c94d9b3d6e42d020800e2a5cb485ebff132e098d2088)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:06:16Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:33:34Z):
Reading for PaperWeakSolutionForcedInt (paper: the solution class of Lemma 4.3, and §4 (4.1)).
Lemma 4.3 class: Theta = (X,Y,Z,U) solving (4.1) at parameter lambda with an F_0-measurable initial datum
xi_0 and forcing q, where X, Y are cadlag adapted with E int_0^T (|X_t|^2 + |Y_t|^2) dt < inf,
X_T in L^2(Omega, F_T; R^n), Z in H^2_W, U in H^2_N. ("Int": the integrals of (4.1) exist along Theta.)
So: the Hweak class plus X_T in L^2; the identities of (4.1) for every t in [0,T] a.s.:
 X_t = xi_0 + lambda int_0^t b ds + lambda int_0^t sigma dW + lambda int_0^t int_E h(s,Theta^-_s,e,mu^-_s) Ntilde
       + int_0^t q^b ds + int_0^t q^sigma dW + int_0^t int_E q^h Ntilde,
 Y_t = lambda g(X_T, Law X_T) + lambda int_t^T f ds + q^g_T + int_t^T q^f ds - int_t^T Z dW - int_t^T int_E U Ntilde,
with mu_t = Law(Theta_t), mu^-_t = Law(Theta^-_t).
For the integrals to make sense, the coefficient processes along Theta must be measurable
(progressive for b, sigma, f, predictable for h) and integrable enough: in the paper's Lemma 4.3 no
origin integrability (Ass 2.2) is assumed, so individual coefficient processes need not be
square-integrable; the paper's class requires only that the integrals exist. A faithful Lean
definition must not require more of Theta than: cadlag adapted X, Y with dt dP-square-integrability,
X_T in L^2, Z, U predictable square-integrable, plus existence (measurability + integrability
sufficient for definition) of the integrals; requiring square-integrable coefficient processes
(sigma, h, for the L^2 Ito/Poisson integrals) is a natural formal reading of "the stochastic
integrals exist" (the paper's Ito integrals are L^2 integrals), but requiring L^2 for the drift
would be extra. Forcing: PredForcing.
Comparison (verdict recorded 2026-10-17T12:40:59Z):
Comparison for PaperWeakSolutionForcedInt (System/PaperWeakSolutionForcedInt.lean:68).
It extends PaperWeakTuple (Hweak: adapted X, Y on [0,T], every path right-continuous on [0,T), a.s.
left limits on (0,T], finite energy E int_0^T X_i^2 < inf etc.; predictable Z, marked predictable U
with finite energies, vanishing off [0,T]) and adds: forcing (Forcing), joint/progressive
measurability of the forced integrands lam psi + q^psi, a.s. integrable paths on [0,T] for the forced
drift and driver (no L^2), finite energy for the forced diffusion and jump integrands (L^2 stochastic
integrals), jump_rep (gamma represents h(s, Theta^-_s, ., mu^-_s) nu-a.e., a.e. s, a.s.), XT_sq (X_T in
L^2), and the two identities of (4.1) (same form as PaperSolutionForced, reviewed).
Against my reading (Lemma 4.3 class): Hweak + X_T in L^2 + Z in H^2_W + U in H^2_N + (4.1) with initial
datum xi0 and forcing q, the integrals existing. Matches: no S^2, no L^2 of the forced drift/driver
(consistent with Lemma 4.3 assuming only Ass 2.3-2.5), xi0 not required in L^2 or F_0-measurable here
(Lemma 4.3 states F_0-measurable data; that is in the proposition). The L^2 requirement on the forced
diffusion and jump integrands is the existence of the L^2 stochastic integrals; with Lipschitz
coefficients and square-integrable forcing, any Hweak tuple along which the integrals exist at all
has it. The author's lemma paperWeakSolutionForcedInt_one_zero_iff shows lam = 1, q = 0 gives
PaperWeakSolutionInt. Remaining encoding choices are those of PaperSolutionForced.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices (harmless): those of PaperSolutionForced (coordinate encoding; every-path
right continuity with a.s. left limits; Z, U, forcings vanishing off [0,T]; Forcing with marked
progressive q^h in the solution predicate; exact laws at every time; uLift junk on a null set;
marked-progressive representative gamma; conditions on the forced integrands lam psi + q^psi rather
than separately; identities on one null set with cadlag versions of the Brownian integrals), with
the forced drift/driver only a.s. path-integrable and X_T in L^2 as a field, as the paper's
Lemma 4.3 class requires. Finite energy of the forced diffusion and jump integrands is the
existence of the L^2 stochastic integrals (implied by Lipschitz coefficients and an L^2 forcing for
any tuple along which the integrals exist).
Disagreements with the author's review (shown 2026-10-17T15:05:45Z): none (the author's excerpt shown for this unit is a marker and at most a section heading, with no
item-level reading to compare against; my comparison file records the representation choices in
detail).
