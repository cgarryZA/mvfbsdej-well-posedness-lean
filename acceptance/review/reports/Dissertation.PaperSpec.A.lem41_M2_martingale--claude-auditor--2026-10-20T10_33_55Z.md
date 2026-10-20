### A:lem4.1:M2-infinite-activity: Dissertation.PaperSpec.A.lem41_M2_martingale
Pins: manuscript A None; project 6d403c197bfb10fe8808933c6e525ee0ae544fb1; hash ed839d34f480cba1983f1a786ecea56b (pl-fp-v1:1005079ef05bc22ae785ab53b27b28ba87c94c3f649c64486d194f6c58a1ce01)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-20T10:33:55Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-20T10:21:55Z):
Reading of the clause (proof of Lemma 4.1, the M^2 term; manuscript/paper/sections/04-proof-wellposedness.tex lines
139-152 and 173-187).

Paper: "The stochastic-integral terms in (4.5) decompose into three local martingales ... M^2_t := int_0^t int_E e^s
|delta U_s(e)|^2 Ntilde(ds,de), each of which we now show satisfies E[M_T - M_t] = 0 ... M^2 is instead handled through
the compensation formula, which asks only for integrability. ... the integrand e^s |delta U_s(e)|^2 is predictable and
nonnegative and, because delta U in H^2_N, lies in L^1(dP ds nu) ... Both the Poisson integral and its compensator are
therefore integrable, so the increment splits under the expectation: E[M^2_T - M^2_t] = ... = 0."

Setting in force: standing basis of section 2 (usual conditions, W, N independent PRM with intensity dt nu, nu
sigma-finite on countably generated E, Ntilde = N - dt nu); T > 0, m, d >= 1; hypotheses of Lemma 4.1: delta Y cadlag
adapted, delta Z in H^2_W, delta U in H^2_N (predictable, P (x) E-measurable representative, E int_0^T ||delta U_s||^2
ds < inf), satisfying (4.4) with delta xi in L^2(F_T), phi in L^2(Omega x [0,T]). Only delta U in H^2_N is used for M^2;
dropping the rest is harmless (broader, the printed one an instance).

What the paper asserts about M^2: (a) M^2 is a local martingale (stated in passing, for all three); (b) the
nonnegative predictable integrand e^s |delta U_s(e)|^2 lies in L^1(dP (x) ds (x) nu) on [0,T]; (c) the Poisson
integral int_{(t,T] x E} e^s|delta U|^2 N(ds,de) and its compensator are integrable; (d) E[M^2_T - M^2_t] = 0 for t <= T,
where M^2 is read as the N-integral minus the compensator (the L^1 compensated integral; the integrand has no second
moment).
A faithful statement: M^2_t := int_{(0,t] x E} e^s |delta U_s(e)|^2 N(ds,de) - int_0^t int_E e^s |delta U_s(e)|^2 nu(de) ds
(pathwise integrals against the random measure N(omega) and against nu (x) Leb), and for every t in [0,T]:
E int_{(0,t]xE} e^s|dU|^2 dN < inf, M^2_t integrable and F_t-measurable (up to a null set, the filtration being
complete), and the zero-mean increment E[M^2_T - M^2_t] = 0 (paper's conclusion). A statement of the martingale
property E[M^2_t | F_s] = M^2_s a.s. for 0 <= s <= t <= T is stronger than the printed E[M_T - M_t] = 0 and than
"local martingale" in the sense of conditional expectations; it is supported by the paper's own tool (the compensation
formula (2.1) for predictable nonnegative psi applied to psi 1_A 1_{(s,t]}, A in F_s, which is predictable), so it is a
faithful strengthening, not a different claim, provided it is about the same M^2 (N-integral minus compensator, with
e^s weight, the same P (x) E-measurable delta U). The N-integral must be the integral against the Poisson random measure
of the standing basis with intensity dt nu (with respect to which F is the filtration). The weight e^s must be present.
A witness should have delta U nonzero (ideally nu(E) = infinity admitted).
Comparison (verdict recorded 2026-10-20T10:31:01Z):
Comparison of Dissertation.PaperSpec.A.lem41_M2_martingale (Dissertation/PaperSpec/A/Sec4BrownianPoisson.lean) with my
locked reading.

Setting. Standing basis: a `LevyDriver` D (W d-dimensional Brownian motion, N Poisson random measure on ℝ x E with
intensity Leb (x) nu, independent), G_0 independent of the driver, filtration `enlJoint G_0 D` (usual augmentation of
F^{W,N} v G_0), nu sigma-finite on a countably generated E (nu(E) = inf admitted), m, d > 0, T > 0. [match]

Hypotheses (Lemma 4.1, all present): delta xi ℝ^m-valued, F_T-measurable, in L^2; phi coordinatewise jointly measurable
with finite energy (phi ∈ L^2(Omega x [0,T]); the paper imposes no adaptedness on phi, nor does the statement);
delta Y adapted on [0,T], every path right-continuous on [0,T) with left limits on (0,T] (cadlag adapted); delta Z
predictable of finite energy (H^2_W), delta U marked predictable of finite marked energy (H^2_N), both vanishing off
[0,T] (normalisation); and (4.4) a.s. at every t ∈ [0,T], written with int_t^T = int_0^T - int_0^t for the Ito and
compensated integrals of the standing basis. Only delta U ∈ H^2_N is used for M^2; the rest is in force. [match]

Conclusion. With M^2_t(omega) := int_{(0,t] x E} e^s sum_k delta U_k(s,omega,e)^2 N(omega)(ds,de)
- int_{(0,t]} int_E e^r sum_k delta U_k(r,omega,e)^2 nu(de) dr (Bochner integrals, pathwise; the integrand is
e^s |delta U_s(e)|^2):
 - for every t ∈ [0,T]: E int_{(0,t] x E} e^s|delta U|^2 dN < inf (as a lintegral, so the Poisson integral has finite
   expectation; hence it is a.s. finite and the Bochner integral is its value a.s., the junk value 0 of a non-integrable
   Bochner integral occurring only on a null set); M^2_t integrable; M^2_t a.e.-strongly measurable for F_t (F_t-
   measurable up to a null set; the filtration is complete anyway);
 - for 0 <= s <= t <= T: E[M^2_t | F_s] = M^2_s a.s. (a martingale on [0,T] for the standing filtration).
Reading of M^2: the paper defines M^2_t := int_0^t int_E e^s|delta U|^2 Ntilde(ds,de), and in lines 179-186 itself splits
it as the N-integral minus the compensator, both integrable, the only meaning available for an integrand in L^1 but not
L^2 (no square moments, lines 148-152). The statement uses exactly that reading. [match]

The strengthening. The paper asserts (lines 139-141) that M^2 is a local martingale and proves (lines 173-187) that
E[M^2_T - M^2_t] = 0 through the compensation formula (2.1) and integrability. The statement asserts the martingale
property on [0,T] instead. It is a faithful strengthening, supported by the paper's own argument: (2.1) is stated for
every predictable psi >= 0, and applied to psi 1_A 1_{(s,t]}(r) e^r|delta U_r(e)|^2 with A ∈ F_s (predictable,
nonnegative, in L^1(dP ds nu) since delta U ∈ H^2_N) it gives E[1_A (M^2_t - M^2_s)] = 0, i.e. the martingale property;
it is also the standard fact that the compensated integral of a predictable integrand in L^1(dP (x) ds (x) nu) is a true
martingale. The printed assertions follow: a martingale on [0,T] is a local martingale (its paths are a.s. cadlag, the
N-integral of a nonnegative integrand being right-continuous where finite and the compensator continuous), and taking
expectations gives E[M^2_T - M^2_t] = 0. It is not a different claim: the same process, the same filtration, the same
integrand, with a stronger (and true, by the same tool) conclusion. Hence verdict `broader` rather than `faithful`.

Vacuity / witness. Dissertation.Acceptance.A.lem_bpbsde_nonzero_hypotheses (Dissertation/Acceptance/A/WitnessLocal.lean):
a Levy driver with d = 1, nu = dirac 0 on ℝ, G_0 trivial, m = 1, T = 1, delta Z = delta U = 1_{(0,1]} (energy 1 each),
phi = 0, delta Y the sum of everywhere-cadlag versions of int delta Z dW and int int delta U Ntilde, delta xi = delta Y_1;
all hypotheses of Lemma 4.1 hold. The relevant object is nonzero: M^2_t = sum over jump times s <= t of e^s - (e^t - 1),
not identically zero. The witness has nu(E) = 1 < inf, so it does not exhibit the infinite-activity regime that the
claim's title emphasises; the statement itself admits nu(E) = inf, and the companion clause lem41_jump_times has an
infinite-activity witness.

Coverage of the claim A:lem4.1:M2-infinite-activity (acceptance/claims.json). The passage (lines 139-187) asserts: the
three local martingales M^W, M^1, M^2 and E[M_T - M_t] = 0 for each (lem41_MW, lem41_M1, lem41_M2_zero_mean, this clause
for the local-martingale property of M^2); delta U ∈ H^2_N gives M^2's integrand no square moments (lem41_M2_no_square
_moment); with nu(E) = inf localisation along jump times fails to exhaust [0,T] (lem41_jump_times); the BDG bounds on
E sup |M^W| and E sup |M^1| and the chain for M^1 (lem41_MW, lem41_M1, lem41_M1_chain, the cited BDG first link not
stated); M^2's integrand predictable and nonnegative (lem41_M2_integrand), in L^1 with the e^T bound, the Poisson integral
and compensator integrable, the zero-mean increment (lem41_M2_zero_mean). Together the clauses state every mathematical
assertion of the passage; the decomposition of the stochastic terms of (4.5) into M^W, M^1, M^2 is assigned to (4.5), and
"the L^2 theory does not reach it"/"asks only for integrability" are methodological remarks. No clause states something
the passage does not claim, except that this clause states a martingale where the paper says local martingale, a
faithful strengthening (above), which the scope_note records ("stated as a martingale on [0, T] (stronger)"). The
hypotheses are those of Lemma 4.1 in force at that point, no more and no fewer (Z, U vanishing off [0,T] is a
normalisation). The scope_note is accurate (line ranges, the treatment of M^W, M^1 as local stochastic integrals, of the
cited BDG link, of the nu = 0 case in the no-square-moment clause). Witnesses: this clause's witness has delta U, hence
M^2, nonzero, with finite nu.
Witness: —
Verdict: broader — Stronger conclusion than printed, a faithful strengthening: the paper says M^2 is a local martingale and proves
E[M^2_T - M^2_t] = 0 via the compensation formula (2.1); the statement asserts the martingale property
E[M^2_t | F_s] = M^2_s on [0,T] (with integrability, F_t-measurability up to null sets, and finite expectation of the
Poisson integral), for the same pathwise M^2 (N-integral minus compensator, the paper's own split in lines 179-186). The
printed claim follows: take expectations in the martingale property for E[M^2_T - M^2_t] = 0, and a martingale on
[0,T] (a.s. cadlag paths) is a local martingale. The strengthening is supported by the paper's tool: (2.1) applied to
the predictable integrand 1_A 1_{(s,t]} e^r |delta U_r(e)|^2, A ∈ F_s, gives the martingale identity.
Disagreements with the author's review (shown 2026-10-20T10:33:47Z): Agreement on substance: M^2 read pathwise (the paper's own split, lines 179-186), the martingale property a faithful
strengthening of the printed "local martingale" supported by the compensation formula applied to 1_A 1_{(s,t]} times the
integrand, adaptedness up to a null set, the filtration. Two points. (1) Label: the author's verdict is "faithful,
stronger than printed"; a proposition that says more than the printed claim, with the printed claim a consequence, is
what `broader` records (with the derivation: take expectations for E[M^2_T - M^2_t] = 0; a martingale on [0,T] is a
local martingale), so I record `broader`. (2) Witness: lem_bpbsde_nonzero_hypotheses makes M^2 nonzero but has
nu = dirac 0, a finite intensity; the claim this clause belongs to is about the infinite-activity regime (its title and
lines 148-152), and no witness of this clause exhibits nu(E) = inf. The statement covers that regime, so this is a
remark on the witness, not on the statement.
