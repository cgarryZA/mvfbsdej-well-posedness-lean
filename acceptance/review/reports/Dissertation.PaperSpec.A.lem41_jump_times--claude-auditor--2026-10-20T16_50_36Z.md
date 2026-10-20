### A:lem4.1:M2-infinite-activity: Dissertation.PaperSpec.A.lem41_jump_times
Pins: manuscript A None; project 53a4ee4fc8767ba8884b5732431dded9772b47df; hash ed839d34f480cba17f1df52f488747a1 (pl-fp-v1:e067139d1bf4a6441655bb2dd65c129357516501c1ca6d5fd05bbfcadb41e70c)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-20T16:50:36Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-20T16:39:43Z):
Reading of spec:Dissertation.PaperSpec.A.lem41_jump_times (locked before any Lean).

Passage: manuscript/paper/sections/04-proof-wellposedness.tex lines 150-152 (region 139-187 of
claim A:lem4.1:M2-infinite-activity): "nor, with nu(E) = infinity admitted, does localisation along
jump times, which then fail to exhaust [0, T]". Also Section 2 lines 9-11 ("in the
infinite-activity regime N has infinitely many atoms on every nondegenerate time interval").

What is asserted. In the standing setting, if nu(E) = infinity, the jump times of N do not exhaust
[0, T]: the localising sequence one would use (the successive jump times of the counting process
t -> N((0, t] x E)) does not increase to T (or beyond), so it cannot localise on [0, T]. The
mechanism: N((0, t] x E) is a Poisson variable of mean t nu(E) = infinity, hence (Poisson random
measure, sigma-finite nu) equals infinity almost surely for each t > 0, and on a common null set
for all t > 0 by monotonicity in t (rational t suffices). So tau_k := inf{t >= 0 : N((0, t] x E)
>= k}, valued in [0, infinity] with inf of the empty set = infinity, is 0 for every k >= 1 (for
k = 0 it is 0 trivially), almost surely; hence sup_k tau_k = 0 < T.

Faithful formal statement. For every setting of Section 2 (or any Poisson random measure with
intensity dt nu, sigma-finite nu) with nu(E) = infinity, and every T > 0: almost surely,
N((0, t] x E) = infinity for all t > 0, and the jump times tau_k (defined from N as above, in
[0, infinity]) satisfy sup_k tau_k < T (in particular they are all 0). The quantifier "almost
surely" must come before "for every t > 0" (one null set for all t), or at least the conclusion
"sup_k tau_k < T a.s." must be stated; "for each t, a.s." alone would not give the
non-exhaustion. The jump times must be those of the setting's N (not of an arbitrary process).
Other renderings of "fail to exhaust [0, T]" (e.g. P(sup_k tau_k >= T) < 1, or = 0) are
acceptable; the a.s. form with tau_k = 0 is the strongest natural one and is true. The claim
needs T > 0 (the setting has T > 0). No constants are involved.

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
Comparison for spec:Dissertation.PaperSpec.A.lem41_jump_times
(Dissertation/PaperSpec/A/Sec4BrownianPoisson.lean, lem41_jump_times).

Reading (locked): for every setting with nu(E) = infinity and T > 0, almost surely
N((0, t] x E) = infinity for all t > 0, and tau_k = inf{t >= 0 : N((0, t] x E) >= k} in
[0, infinity] (inf of the empty set = infinity) are all 0, so sup_k tau_k < T; one null set for all
t; the jump times of the setting's N.

Lean, item by item.
- Setting: every probability space, every sigma-finite (E, nu) (no countable generation required),
  every d and every Levy driver D, with nu univ = infinity. The standing setting (countably
  generated E, G0, enlJoint) is an instance; G0 and the filtration play no role in the statement.
  So the clause is broader than the printed setting (see detail).
- N: D.N.N w, the setting's Poisson random measure (intensity Lebesgue on [0, infinity) x nu).
- "for ae w" placed before "forall t > 0": one null set for all t. Matches.
- tau_k := infimum over real t with 0 <= t and k <= N((0, t] x univ) of ofReal t, in [0, infinity];
  the infimum of the empty family is infinity. Matches the reading's definition. The clause
  asserts tau_k = 0 for every k in N (k = 0 included, trivially) and, for every T > 0,
  sup_k tau_k < ofReal T. Matches "they fail to exhaust [0, T]".
- Constants: none. "Almost surely" as the reading requires.
Not vacuous: nu(E) = infinity with a Levy driver is realised (witness).

Verdict: broader.

Witness: Dissertation.Acceptance.A.sec2_infinite_activity_hypotheses: Lebesgue measure on R has
infinite mass, and a Levy driver with d = 1 and that intensity exists. This is the intended
infinite-activity regime; nondegenerate (the conclusion is about a genuinely infinite-activity N).

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
Verdict: broader — Broader: the clause holds for every Levy driver with sigma-finite nu(E) = infinity on an arbitrary
mark space, without the standing hypotheses that calE be countably generated and that an
independent initial sigma-algebra G0 enlarge the filtration. Instantiation giving the printed
step: take the setting's (E, nu) (countably generated, sigma-finite, nu(E) = infinity) and its
driver D; G0 and the filtration do not enter the statement, so the conclusion is the printed
non-exhaustion of [0, T] by the jump times of the setting's N, for every T > 0.
Disagreements with the author's review (shown 2026-10-20T16:50:15Z): none
