### A:lem4.1:M2-infinite-activity: Dissertation.PaperSpec.A.lem41_M1_chain
Pins: manuscript A None; project 53a4ee4fc8767ba8884b5732431dded9772b47df; hash ed839d34f480cba11e7d5cd5bc08d7ae (pl-fp-v1:53de8ffd7c5abac5bf1913dfc2628504a9e7217df86f7718fce0ce7cb60d0d07)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-20T16:50:37Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-20T16:39:43Z):
Reading of spec:Dissertation.PaperSpec.A.lem41_M1_chain (locked before any Lean).

Passage: manuscript/paper/sections/04-proof-wellposedness.tex lines 159-170 (region 139-187 of
claim A:lem4.1:M2-infinite-activity): the four-link chain for E sup |M^1_t| displayed there.
The clause states the links after the first (the first is BDG at p = 1). With the common factor
c_BDG > 0 removed (dividing by it is harmless), the links are:
 (L2) E[(int_0^T int_E e^{2s} |dY_{s-}|^2 |dU_s(e)|^2 N(ds,de))^{1/2}]
        <= e^T (E sup_{t<=T} |dY_t|^2)^{1/2} (E int_0^T int_E |dU_s(e)|^2 N(ds,de))^{1/2}
      (Cauchy-Schwarz in omega after bounding e^{2s} |dY_{s-}|^2 <= e^{2T} sup |dY|^2 under the
      N-integral; the left limit is bounded by the supremum of the cadlag path);
 (L3) E int_0^T int_E |dU_s(e)|^2 N(ds,de) = E int_0^T int_E |dU_s(e)|^2 nu(de) ds, by (2.1)
      (compensation formula for the predictable nonnegative integrand |dU|^2);
 (L4) E int_0^T int_E |dU_s(e)|^2 nu(de) ds = E int_0^T ||dU_s||^2_{L^2(nu)} ds (definition of
      the L^2(nu) norm of the representative; Tonelli).
Hypotheses in force: delta Y cadlag adapted with E sup |dY|^2 < infinity; delta U in H^2_N read
through its P (x) calE-measurable representative. (L2) holds in [0, infinity] even without the
finiteness; (L3) holds in [0, infinity] for every predictable delta U; (L4) for every
measurable representative.

Faithful formal statement. For every setting, T > 0, cadlag adapted delta Y (E sup |dY|^2 <
infinity may be assumed), marked-predictable delta U (E int ||dU||^2 < infinity may be assumed):
(L2), (L3), (L4) as above, with the N-integrals pathwise integrals against the setting's Poisson
random measure over (0, T] x E (or [0, T] x E: N({0} x E) = 0 a.s.), the expectations in
[0, infinity] or as finite reals under the integrability hypotheses, left limit dY_{s-} in (L2).
Constants: e^T exactly; c_BDG removed. If (L2) is stated with dY_s instead of dY_{s-} it is a
different (though also true) inequality; the printed one has the left limit.

Context (all lem41 units). Passage: manuscript/paper/sections/04-proof-wellposedness.tex, region
lines 139-187 (proof of Lemma 4.1, "Zero-mean terms"), read with the statement of Lemma 4.1
(lines 89-102), the "Membership" step (lines 104-113), identity (4.x) eq:itoY2 (lines 126-137),
the conventions of the start of Section 4 (lines 17-37: one universal BDG constant c_BDG valid at
p = 1 and p = 2; the "supremum criterion"; constants C depend only on T, L, |G|, c_G, alpha,
beta_1, beta_2, c_BDG), the standing setting of Section 2 (lines 1-25: filtered space with the
usual conditions, T > 0, n, m, d >= 1, d-dim Brownian motion W, independent Poisson random measure
N on R_+ x E with intensity dt nu(de), nu sigma-finite on countably generated (E, calE), filtration
the usual augmentation of W, N and an independent F_0; compensation formula (2.1) for predictable
psi >= 0 with values in [0, infinity]; zero mean (2.2) under integrability), the spaces of
Section 3 (H^2_W: predictable R^{m x d}-valued, E int |Z|_F^2 < infinity; H^2_N: predictable
L^2(nu; R^m)-valued, E int ||U||^2 < infinity), and the Fubini reading (2.x) eq:fubiniiso:
every Poisson integral and every L^2(nu)-valued predictable integrand in one is read through a
P (x) calE-measurable representative (marked predictable), unique up to dt dP nu-null sets.
Hypotheses in force at line 139: delta Y cadlag adapted R^m-valued, delta Z in H^2_W, delta U in
H^2_N, delta xi in L^2(F_T), phi in L^2(Omega x [0,T]), equation (eq:dYlin) for every t, and, from
the Membership step already done, E sup_{t<=T} |delta Y_t|^2 < infinity (delta Y in S^2).
The three processes on [0, T]:
  M^W_t = int_0^t e^s <delta Y_{s-}, delta Z_s dW_s>  (= sum_{i,j} e^s dY^i_{s-} dZ^{ij}_s dW^j_s),
  M^1_t = int_0^t int_E e^s <delta Y_{s-}, delta U_s(e)> Ntilde(ds, de),
  M^2_t = int_0^t int_E e^s |delta U_s(e)|^2 Ntilde(ds, de).
The printed passage asserts, in order: (a) the stochastic-integral terms of (eq:itoY2) decompose
into these three local martingales; (b) each satisfies E[M_T - M_t] = 0; (c) delta U in H^2_N
gives the quadratic integrand of M^2 no square moments, so the L^2 theory does not reach it;
(d) with nu(E) = infinity, localisation along jump times fails, as they fail to exhaust [0, T];
(e) the compensation formula needs only integrability; (f) the BDG bound for M^W; (g) the BDG
chain for M^1 (four links, the third by (2.1)); (h) the supremum criterion gives
E[M_T - M_t] = 0 for M^W, M^1; (i) the integrand of M^2 is predictable and nonnegative and lies
in L^1(dP ds nu) with the displayed bound by e^T E int ||dU||^2; (j) the Poisson integral and its
compensator are integrable, so the increment splits and E[M^2_T - M^2_t] = 0 (three-line display).
"For every t": the paper uses E[M_T - M_t] = 0 at every t in [0, T] (taken at every t <= T in
line 200).
Comparison (verdict recorded 2026-10-20T16:48:45Z):
Comparison for spec:Dissertation.PaperSpec.A.lem41_M1_chain
(Dissertation/PaperSpec/A/Sec4LocalMartingales.lean, lem41_M1_chain).

Reading (locked): with c_BDG removed, (L2) E[(int_0^T int_E e^{2s} |dY_{s-}|^2 |dU_s(e)|^2
N(ds,de))^{1/2}] <= e^T (E sup |dY|^2)^{1/2} (E int int |dU|^2 N)^{1/2} with the left limit;
(L3) E int int |dU|^2 N = E int int |dU|^2 nu ds by (2.1); (L4) = E int ||dU_s||^2 ds; Poisson
integrals pathwise against the setting's N over (0, T] x E; expectations in [0, infinity].

Lean, item by item.
- Setting and hypotheses: the standing setting and all hypotheses of Lemma 4.1 (in force).
- (L2): lintegral over w of (int_{(0,T] x E} ofReal(e^{2s} (sum_k (dY^k_{s-})^2) (sum_k dU_k^2))
  dN(w))^{1/2} <= ofReal(e^T) (E sup_{t in [0,T]} |dY_t|^2)^{1/2}
  (E int_{(0,T] x E} ofReal(sum_k dU_k^2) dN)^{1/2}. On (0, T] the guard "0 < s" always holds, so
  the left limit dY_{s-} is used, as printed. Matches; e^T exact.
- (L3): E int_{(0,T] x E} sum dU^2 dN = E int_{(0,T]} int_E sum dU^2 nu ds, in [0, infinity].
  Matches (the compensation formula for the predictable nonnegative integrand |dU|^2).
- (L4): E int_{(0,T]} int_E sum dU^2 nu ds = sum_k markedEnergy(dU_k) = E int_0^T ||dU_s||^2 ds
  (markedEnergy integrates over [0, T]; the time 0 is Lebesgue-null). Matches.
- c_BDG: removed from links two to four, as in the reading (a common positive factor).

Verdict: faithful with representation choices.

Witness: Dissertation.Acceptance.A.lem_bpbsde_nonzero_hypotheses: delta U = 1_{(0,1]} with
nu = delta_0 and delta Y = int dZ dW + int int dU dNtilde, so every side of the three links is
positive (E int int |dU|^2 nu ds = 1): nondegenerate and intended.

Shared representation of the setting and of the hypotheses of Lemma 4.1 (checked in
Dissertation/PaperSpec/A/Sec4BrownianPoisson.lean and Sec4LocalMartingales.lean, with the
definitions LevyStochCalc.Driver.LevyDriver, Dissertation.WellPosedness.Enlarged.enlJoint,
LevyStochCalc.Probability.MarkedPredictable / Predictable, Poisson.Compensated.markedEnergy,
Brownian.Ito.energy, Dissertation.WellPosedness.System.leftLimProc,
Dissertation.WellPosedness.Stability.esq):
- Setting: a LevyDriver D (d-dimensional Brownian motion W and Poisson random measure N with
  intensity Lebesgue on [0, infinity) x nu, sigma(W) independent of sigma(N)), nu sigma-finite on a
  countably generated E, an initial sigma-algebra G0 independent of the driver, the filtration
  enlJoint G0 D = usual augmentation (right-continuous version, frozen before 0, P-null sets added)
  of the joint natural filtration joined with G0; 0 < m, 0 < d, T > 0. This is the standing
  setting of Section 2.
- Hypotheses of Lemma 4.1: delta xi : Omega -> R^m, F_T-measurable, MemLp 2 (delta xi in
  L^2(F_T)); phi jointly measurable with finite energy (phi in L^2(Omega x [0, T]); the paper
  requires no adaptedness); delta Y adapted on [0, T], every path right-continuous on [0, T) with
  left limits on (0, T] (cadlag on [0, T]); delta Z componentwise predictable, zero off [0, T],
  finite energy (H^2_W); delta U componentwise marked predictable, zero off [0, T], finite marked
  energy (H^2_N); and (eq:dYlin) for every t in [0, T] almost surely, with int_t^T dZ dW and
  int_t^T int dU dNtilde written as differences of the integrals from 0 (multidimensional Ito
  integral of LevyStochCalc; L^2 compensated integral of LevyStochCalc).
Representation choices (harmless): processes are indexed by R and the integrands are extended by
0 off [0, T]; the marked predictable sigma-algebra is generated by rectangles
F x (r, q] x B with r >= 0, F in F_r and nu(B) < infinity, which by sigma-finiteness of nu is
the paper's P (x) calE on the time half-line (0, infinity), and forces a marked predictable
integrand to be constant on times s <= 0 (with the vanishing off [0, T], the value at the single
time s = 0 is 0: a dt dP nu-null modification, harmless since H^2_N is a space of classes);
L^2 norms and moments of nonnegative quantities are lintegrals in [0, infinity], with
E int ||dU||^2 = sum_k markedEnergy(dU_k) and E int |dZ|_F^2 = sum_{k,j} energy(dZ_{kj}); the left
limit dY_{s-} is Function.leftLim of the path at s in (0, T] (which exists by hypothesis and depends
only on values in (0, s)), and 0 at s <= 0 (a Lebesgue-null time, and N({0} x E) = 0 a.s.).

Coverage (claim A:lem4.1:M2-infinite-activity, region lines 139-187 of
manuscript/paper/sections/04-proof-wellposedness.tex, read in acceptance/claims.json after show).
Its eight clauses (lem41_M2_no_square_moment, lem41_jump_times, lem41_M2_integrand,
lem41_M2_zero_mean, lem41_M2_martingale, lem41_MW, lem41_M1, lem41_M1_chain) state: the
non-implication of lines 149-150 (for nu != 0); the failure of localisation along jump times when
nu(E) = infinity (150-151); the bound, its finiteness and the zero-mean increments of M^W
(153-158, 171-172); the composite bound, finiteness and zero mean of M^1 and links two to four of
its chain (159-172); the integrand of M^2 predictable and nonnegative, its L^1 bound by
e^T E int ||dU||^2, the finiteness of the Poisson integral and of the compensator over (t, T] and
E[M^2_T - M^2_t] = 0 (173-187); and that M^2 is a local martingale (139-147), stated as a
martingale on [0, T]. Not stated by any clause: (i) the first link of the M^1 chain (line 162),
E sup_{t<=T} |M^1_t| <= c_BDG E[(int_0^T int_E e^{2s} |dY_{s-}|^2 |dU_s(e)|^2 N(ds,de))^{1/2}];
the scope note sets it aside as cited work (BDG at p = 1), but it is the paper's assertion about
its own M^1 (BDG in quadratic-variation form combined with Cauchy-Schwarz in R^m), so its absence
is a gap in coverage, mitigated by the composite bound of lem41_M1, which is stated and does not
depend on it; (ii) that the stochastic-integral terms of (eq:itoY2) are -2(M^W_T - M^W_t)
- 2(M^1_T - M^1_t) - (M^2_T - M^2_t) (lines 139-141), assigned by the scope note to A:eq:itoY2,
which I did not check; (iii) the local-martingale property of M^W and M^1, which is carried by
the definitions IsLocalBrownianIntegral / IsLocalCompensatedIntegral (adapted cadlag processes
agreeing, up to stopping times eventually >= T, with L^2 integrals) rather than stated. The
sentence that the compensation formula "asks only for integrability" is methodological and is
embodied in lem41_M2_zero_mean. No clause states something the passage does not claim, except
that lem41_M2_martingale asserts a true martingale where the paper prints "local martingale"
(stronger, recorded in the scope note). Hypotheses: clauses three to eight carry exactly the
hypotheses of Lemma 4.1 in the standing setting, which are those in force at line 139 (the
Membership step's E sup |dY|^2 < infinity is derived, and it appears as the finiteness conclusion
of lem41_MW and lem41_M1); clause one carries the setting with nu != 0, clause two a Levy driver
with nu(E) = infinity.
Witness: —
Verdict: faithful with representation choices — Representation choices: (1) the common factor c_BDG > 0 of the printed chain removed (dividing by
it is an equivalence); (2) Poisson integrals as lintegrals against D.N.N w over (0, T] x E (the
time 0 carries no atom a.s., and the paper's int_0^T is over (0, T]); (3) expectations in
[0, infinity]; (4) |dY_{s-}|^2 |dU_s(e)|^2 as (sum_k (dY^k_{s-})^2)(sum_k dU_k^2), with the left
limit given by Function.leftLim at s in (0, T]; (5) E int ||dU||^2 as sum_k markedEnergy(dU_k);
(6) the shared representation of the setting and of the hypotheses of Lemma 4.1. None changes the
meaning.
Disagreements with the author's review (shown 2026-10-20T16:50:16Z): No disagreement with the verdict (faithful with representation choices). The coverage gap of the claim, recorded in my decision: the first link of the M^1 chain (line 162, E sup |M^1_t| <= c_BDG E[(int int e^{2s} |dY_{s-}|^2 |dU|^2 N)^{1/2}]) is stated by no clause; the scope note treats it as cited work, but it is the paper's assertion about its own M^1, and the decomposition of the stochastic terms of (eq:itoY2) into M^W, M^1, M^2 is left to A:eq:itoY2.
