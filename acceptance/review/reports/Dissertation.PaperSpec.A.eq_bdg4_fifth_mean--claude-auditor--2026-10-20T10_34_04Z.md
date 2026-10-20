### A:eq:bdg4: Dissertation.PaperSpec.A.eq_bdg4_fifth_mean
Pins: manuscript A None; project 6d403c197bfb10fe8808933c6e525ee0ae544fb1; hash ed839d34f480cba153e1a9d9480bd7ff (pl-fp-v1:381b5907259e40c16e782b23e94b49321740f84b772aa0b4e50350cb079fecfd)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-20T10:34:04Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-20T10:21:55Z):
Reading of the clause (proof of Lemma 4.3, Step 1, the fifth stochastic term of (4.17) and its zero mean, asserted in
the paragraph after (4.18); manuscript/paper/sections/04-proof-wellposedness.tex lines 563-578 and 611-622).

Paper: "The fifth has predictable integrand, and by Cauchy-Schwarz E int_0^T int_E |<lambda delta h_t(e) + q^h_t(e),
G^T delta U_t(e)>| nu(de) dt <= ||G|| (E int ||lambda delta h + q^h||^2 dt)^{1/2} (E int ||delta U||^2 dt)^{1/2} < inf.
Hence (2.2) applies, and all five terms have zero expectation." The fifth term of (4.17) is
int_0^T int_E <G(lambda delta h_t + q^h_t)(e), delta U_t(e)> Ntilde(dt,de) = int int <(lambda delta h + q^h)(e),
G^T delta U(e)> Ntilde.

Setting in force (Lemma 4.3): standing basis (section 2), T > 0, n, m, d >= 1, nu sigma-finite on countably generated E;
coefficients b, sigma, h, f, g deterministic jointly Borel; Assumptions 2.2-2.4 (Lipschitz with L, G full rank,
monotonicity with alpha, beta_1, beta_2); underline-lambda in (0,1], lambda in [underline-lambda, 1]; Theta^1, Theta^2
solve the forced system (4.1) at lambda with F_0-measurable initial data and forcings q^k (square integrable;
q^{h,k} predictable P (x) E-measurable); X^k, Y^k cadlag adapted with E int (|X^k|^2 + |Y^k|^2) dt < inf, X^k_T in L^2,
Z^k in H^2_W, U^k in H^2_N, Theta^1 - Theta^2 in S. delta h_t = h(t, Theta^{1,-}_t, ., mu^{1,-}_t) - h(t, Theta^{2,-}_t,
., mu^{2,-}_t) (L^2(nu; R^n)-valued), q^h = q^{h,1} - q^{h,2}, delta U = U^1 - U^2 (P (x) E-measurable).
(Only the Lipschitz bound - to make lambda delta h + q^h square integrable via the computation of (4.9) - and
delta U in H^2_N are used; G's full rank / monotonicity are in force but unused here: dropping them is broader.)

Conclusions:
 (i) lambda delta h + q^h, an L^2(nu)-valued predictable process, has a P (x) E-measurable ("marked predictable")
     representative H (agreeing with it in L^2(nu) for dt (x) dP-a.e. (t, omega)), the reading (2.7) imposes;
 (ii) for every such H, the fifth integrand (t, omega, e) -> <H_t(omega, e), G^T delta U_t(omega, e)> is
     P (x) E-measurable;
 (iii) E int_0^T int_E |<H, G^T delta U>| nu(de) dt < infinity (the printed Cauchy-Schwarz bound);
 (iv) hence (2.2): the compensated integral, which for this L^1 (not L^2) integrand is
     int_{(0,T] x E} <H, G^T dU> N(dt,de) - int_0^T int_E <H, G^T dU> nu(de) dt, has zero expectation; this needs and
     includes E int_{(0,T] x E} |<H, G^T dU>| dN < inf (from the compensation formula (2.1)).
The integral must be against the Poisson random measure N of the standing basis (intensity dt nu). The G must be the
coupling matrix (G^T in the pairing). The mean zero is at T (over [0,T]). A faithful statement quantifies over the
representative H (any representative), or exhibits one and proves the claims for all.
A witness should make the integrand nonzero: delta U != 0 and lambda delta h + q^h != 0 with overlapping support.
Comparison (verdict recorded 2026-10-20T10:33:06Z):
Comparison of Dissertation.PaperSpec.A.eq_bdg4_fifth_mean (Dissertation/PaperSpec/A/Sec4BDG.lean) with my locked
reading.

Setting. Standing basis (Levy driver D: W d-dimensional, N with intensity Leb (x) nu, independent; G_0 independent of the
driver; filtration `enlJoint G_0 D`, the usual augmentation), nu sigma-finite on a countably generated E, n, m, d > 0,
T > 0. [match]

Hypotheses (Lemma 4.3 and the standing (2.3)):
 - `JointBorel T C` ((2.3)); `Assumption23 … L C` (Assumption 2.3, Lipschitz); `G.rank = min m n` (Assumption 2.4, full
   rank); `Assumption25 … G α β₁ β₂ C` (Assumption 2.5, terminal and interior G-monotonicity with admissible constants).
   These are "Assumptions 2.3-2.5" of Lemma 4.3 (my reading wrote the same content with the numbers shifted by one);
   Assumption 2.2 is correctly absent, as in Lemma 4.3. [match]
 - lamLow ∈ (0,1], lam ∈ [lamLow, 1]; xi_1, xi_2 F_0-measurable; two forcings `PredForcing` (q^h marked predictable);
   Theta^1, Theta^2 `WeakForcedSolution` at lam (solve (4.1) in H_weak, X_T ∈ L^2, Poisson integral through a
   representative of h at the predictable tuple); `supSize` of the difference < inf (Theta^1 - Theta^2 ∈ S). [match]
 Only the Lipschitz bound and delta U ∈ H^2_N are used for this step; the others are in force (no more, no fewer).

Conclusions:
 (1) there is H : Fin n → Ω → ℝ → E → ℝ, coordinatewise `MarkedPredictable` for the standing filtration, equal
     P (x) Leb|[0,T] (x) nu-a.e. to lam (coeffJump(Theta^{1,-}) - coeffJump(Theta^{2,-})) + (q^{h,1} - q^{h,2}), where
     coeffJump P T C (leftLimProc X) (leftLimProc Y) Z U is the jointly measurable representative (lpRep) of
     h(s, Theta^-_s(omega), ., Law(Theta^-_s)) cut to [0,T]: delta h at the predictable tuples (Theta^{k,-}, mu^{k,-}), as
     the paper specifies for Lemma 4.3, and q^h = delta q^h. "lambda delta h + q^h has a marked predictable
     representative". [match]
 (2) for every such H: psi = <H, G^T delta U> (`(H_i)_i ⬝ᵥ (Gᵀ *ᵥ delta U)`, delta U = U^1 - U^2 the marked predictable
     versions) is marked predictable; E int_{(0,T] x E} |psi| dN(omega) < inf; E int_{(0,T]} int_E |psi| dnu ds < inf;
     E[ int_{(0,T] x E} psi dN - int_{(0,T]} int_E psi dnu ds ] = 0. [match: "the fifth has predictable integrand ... (2.2)
     applies, and ... zero expectation"; the fifth term of (4.17) is int int <G(lam dh + q^h)(e), dU(e)> Ntilde
     = int int <(lam dh + q^h)(e), G^T dU(e)> Ntilde.]
Points examined: the compensated integral of an integrand that is L^1 but not L^2 is read pathwise as N-integral minus
compensator, the only meaning available and the one (2.2) uses; quantifying over every marked predictable representative
is right, since for two predictable representatives the N-integrals agree a.s. by (2.1) while a non-predictable
modification on a dP dt dnu-null set could change the N-integral; Bochner junk values (non-integrable path) occur only on
a null set because the N-lintegral has finite expectation; Law(Theta^-_s) is `lawP2` at every time (Dirac mass at 0 on
the null set of times where Theta^-_s is not square integrable), a Borel representative of mu^-; `MarkedPredictable` has
no generator at times <= 0 (H constant there), immaterial as the a.e. requirement is on [0,T] and t = 0 is null. The
Cauchy-Schwarz bound of lines 615-620 is not restated here; it is the clause eq_bdg4_fifth.

The mean-zero assertion is exactly what the paper says (not strengthened): zero expectation of the fifth term over
[0,T]; the finiteness of E int |psi| dN is the integrability (2.2) needs, a consequence of (2.1).

Vacuity / witness. Dissertation.Acceptance.A.lem_pert_forced_hypotheses (Dissertation/Acceptance/A/WitnessForced.lean)
meets every hypothesis: Levy driver with d = 1, nu = dirac 0, G_0 trivial, n = m = 1, T = 1, Example 5.1(i) with
beta_1 = beta_2 = 1, sigma_c = h_c = 0 (b = -y, sigma = -z, h = -u, f = x, g = x), G = 1, alpha = beta_1 = beta_2 = 1,
L = 1, lamLow = lam = 1, xi = 0 for both, the zero forcing and the forcing with q^sigma = 1_{(0,1]}, the two solutions
of (4.1) given by WP(1) (proof of Theorem 3.5), their difference in S. It proves only that delta Z or
lam delta sigma + delta q^sigma has nonzero energy. For this unit the relevant objects are not nonzero: both forcings
have q^h = 0 and h = -u, so lam delta h + q^h = -delta U, and the witness establishes nothing about delta U; in fact
delta U = 0 (the solution forced only in the Brownian channel is the Brownian solution with U = 0, by the uniqueness of
WP(1), as is the unforced solution 0), so H = 0 a.e. and the fifth integrand vanishes identically. The hypotheses are met
at an instance the paper intends, so the statement is not vacuous, but the witness exhibits only a trivial fifth term.

Coverage of the claim A:eq:bdg4 (acceptance/claims.json). The passage (lines 579-622) asserts the four BDG bounds of
(4.18) (clauses eq_bdg4_XZ, _sigmaY, _XU, _hY, each with the existence of its local martingale, the finiteness of the
bound and the zero mean from the supremum criterion), the finiteness of E int |lam dsigma + q^sigma|^2_F and
E int ||lam dh + q^h||^2 and the Cauchy-Schwarz integrability bound of the fifth integrand (clause eq_bdg4_fifth), and the
predictability of the fifth integrand with the zero mean by (2.2) (this clause). Together the clauses state every
mathematical assertion of the passage; the identification of the five terms as the stochastic terms of (4.17) belongs to
(4.17), the first BDG link is cited work, and the display at lines 600-605 is the definition of the norm of S at the
hypothesis, as the scope_note says. No clause states something the passage does not claim; the hypotheses are those of
Lemma 4.3 (with the standing (2.3)), no more and no fewer. The scope_note is accurate. Witness: the shared witness
lem_pert_forced_hypotheses makes delta Z or lam delta sigma + delta q^sigma nonzero, but the jump-channel integrands of
the third, fourth and fifth terms are zero there (delta U = 0, lam delta h + q^h = -delta U = 0).
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless: (1) delta h is the difference of `coeffJump` at the left-limit tuples
(Theta^{k,-}, Law(Theta^{k,-}_s)), a jointly measurable representative of h(s, Theta^{k,-}_s, ., mu^{k,-}_s) cut to
[0,T], with Law taken as `lawP2` at every time (Dirac mass at 0 on a null set of times); (2) the paper's reading of the
Poisson integrand through a P (x) E-measurable representative is made explicit: existence of a marked predictable H
equal a.e. to lam delta h + q^h, and the conclusions for every such H; (3) the fifth term, an L^1 (not L^2) compensated
integral, is read pathwise as the N-integral minus the compensator, with the integrability of both stated, the meaning
under which (2.2) is used; (4) processes coordinatewise, the pairing as a vector dot product with G^T delta U; the marked
predictable sigma-algebra has no cells at times <= 0 (a null time). Witness caveat: lem_pert_forced_hypotheses meets the
hypotheses but has q^h = 0 and delta U = 0, so the fifth integrand is identically zero there.
Disagreements with the author's review (shown 2026-10-20T10:33:55Z): Agreement on the verdict and on the readings. One sharpening about the witness: the author says
lem_pert_forced_hypotheses "does not show the fifth integrand nonzero (nothing is stated about delta U or delta h)". It
is in fact zero there: with h = -u, h_c = 0 and q^h = 0 in both forcings, lam delta h + q^h = -delta U, and delta U = 0,
because the unforced solution is 0 and the solution forced only through q^sigma = 1_{(0,1]} is the Brownian solution with
U = 0 (it solves the system with the Poisson channel absent, and WP(1) gives uniqueness). So the fifth integrand is
identically zero at the only witness, as are the integrands of the third and fourth bounds (eq_bdg4_XU, eq_bdg4_hY). A
witness with a forcing in the jump channel (q^h nonzero, so that delta U is nonzero) would exhibit a nontrivial fifth
term.
