### A:lem4.1:M2-infinite-activity: Dissertation.PaperSpec.A.lem41_M2_no_square_moment
Pins: manuscript A None; project 53a4ee4fc8767ba8884b5732431dded9772b47df; hash ed839d34f480cba18ac876cdb600252c (pl-fp-v1:ed0fdadbf734b82b40508e53fd2dc332fee10c41364f6557bd59c99a74275670)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-20T16:50:36Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-20T16:39:43Z):
Reading of spec:Dissertation.PaperSpec.A.lem41_M2_no_square_moment (locked before any Lean).

Passage: manuscript/paper/sections/04-proof-wellposedness.tex lines 148-152 (inside the region
139-187 of claim A:lem4.1:M2-infinite-activity): "delta U in H^2_N gives the quadratic integrand
of M^2 no square moments, so the L^2 theory behind the bounds below does not reach it".

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

What is asserted. A negative (non-implication) statement: membership delta U in H^2_N, i.e.
delta U predictable (read as a P (x) calE-measurable function) with
E int_0^T ||delta U_s||^2_{L^2(nu)} ds < infinity, does NOT imply that the integrand
psi_s(e) = e^s |delta U_s(e)|^2 of M^2 has a square moment, i.e. it need not hold that
E int_0^T int_E (e^s |delta U_s(e)|^2)^2 nu(de) ds < infinity (psi need not lie in
L^2(dP ds nu), the space on which the compensated-Poisson isometry / L^2 theory works).
It cannot be the universal statement "for every delta U in H^2_N the fourth moment is infinite"
(false at delta U = 0); it is "there is delta U in H^2_N with infinite square moment of psi".

Faithful formal statement. For the standing setting with T > 0 and nu != 0 (at nu = 0 the
integrand is 0 and the claim is false, so a hypothesis nu != 0, or nu(A) > 0 for some A, is a
legitimate reading of "the integrand has no square moment"), there exists a predictable delta U
(marked predictable for the setting's filtration, P (x) calE-measurable, R^m-valued) with
E int int |delta U|^2 nu ds < infinity and E int int e^{2s} |delta U_s(e)|^4 nu(de) ds = infinity.
Quantifier over settings: the paper speaks of the setting in force, so the faithful form is
"for every setting with nu != 0 (and T > 0), there exists such delta U"; a deterministic
example works in every such setting (delta U_s(e) = s^{-1/3} 1_A(e) v / sqrt(nu(A)) with
0 < nu(A) < infinity, |v| = 1). A form "there exists one setting where it fails" is weaker
(narrower) but still conveys the non-implication; it would be acceptable only if it exhibits an
intended setting. The square moment in question is of the integrand under dP ds nu (not, say,
of M^2_T). Integrability measured in [0, infinity] (lintegral) is the natural rendering of
"= infinity". The lemma's other hypotheses do not restrict delta U (take delta Z = 0, phi = 0,
delta Y_t = int_0^t int delta U Ntilde, delta xi = delta Y_T), so stating the clause about
H^2_N alone loses nothing.
Comparison (verdict recorded 2026-10-20T16:48:45Z):
Comparison for spec:Dissertation.PaperSpec.A.lem41_M2_no_square_moment
(Dissertation/PaperSpec/A/Sec4BrownianPoisson.lean, lem41_M2_no_square_moment).

Reading (locked): for every setting with nu != 0 and T > 0 there is delta U in H^2_N (marked
predictable, E int ||dU||^2 < infinity) with E int_0^T int_E (e^s |dU_s(e)|^2)^2 nu(de) ds =
infinity; universal over settings, existential in delta U.

Lean, item by item.
- Setting: for every Omega, G0, (E, nu) sigma-finite and countably generated, m, d, P, Levy driver
  D, G0 <= the ambient sigma-algebra and independent of the driver, nu != 0, 0 < m, 0 < d,
  T > 0. Matches (nu != 0 is the reading's hypothesis; at nu = 0 the integrand is 0 and the
  non-implication is false).
- Quantifier order: forall setting, forall T > 0, exists delta U. Matches the faithful form (the
  universal-over-settings one, not the weaker "some setting").
- delta U in H^2_N: each component MarkedPredictable for enlJoint G0 D (the setting's filtration),
  zero off [0, T], markedEnergy P nu T (dU_k) != infinity. Matches.
- Conclusion: markedEnergy P nu T (fun w s e => e^s * sum_k dU_k(s,w,e)^2) = infinity, i.e.
  E int_{[0,T]} int_E (e^s |dU_s(e)|^2)^2 nu(de) ds = infinity: the square moment, under
  dP ds nu, of the integrand of M^2. Matches exactly.
- The lemma's other hypotheses are absent; as noted in the reading they do not restrict delta U,
  so nothing is lost.
True in every such setting (deterministic example s^{-1/3} 1_A(e) with 0 < nu(A) < infinity), so
not vacuous; the witness only needs the setting.

Verdict: faithful with representation choices (listed in the detail).

Witness: Dissertation.Acceptance.A.lem41_M2_no_square_moment_hypotheses exhibits a probability
space with a Levy driver, d = 1, nu = delta_0 != 0, G0 = bottom (independent), m = d = 1, T = 1:
an intended setting; since the clause is existential in delta U, nothing else is needed and
nothing is degenerate.

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
Verdict: faithful with representation choices — Representation choices: delta U given componentwise as R^m-valued functions on R x Omega x E,
zero off [0, T] (H^2_N on [0, T]); predictability as measurability for the marked predictable
sigma-algebra of the setting's filtration (generated by F x (r, q] x B, nu(B) < infinity, equal to
P (x) calE on positive times by sigma-finiteness; forces the value 0 at s = 0, a null
modification); the square moment and the energy as lintegrals in [0, infinity] (markedEnergy over
[0, T]); |dU|^2 as sum_k dU_k^2. None changes the meaning of the printed sentence.
Disagreements with the author's review (shown 2026-10-20T16:50:15Z): none
