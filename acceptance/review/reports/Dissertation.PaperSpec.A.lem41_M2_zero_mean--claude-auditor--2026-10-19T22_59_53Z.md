### A:lem4.1:M2-infinite-activity: Dissertation.PaperSpec.A.lem41_M2_zero_mean
Pins: manuscript A None; project 6d403c197bfb10fe8808933c6e525ee0ae544fb1; hash ed839d34f480cba15a569c2d7c1d42fd (pl-fp-v1:3e4472679566bcc59baef822f1c2667d8f4afc93e39ecf6aea232ba99b7048a6)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T22:59:53Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T22:48:57Z):
READING (locked before any Lean) -- spec:Dissertation.PaperSpec.A.lem41_M2_zero_mean
Reviewer: claude-auditor (same model family as the statements' author).

Passage (proof of Lemma 4.1, "Zero-mean terms", the M^2 paragraph): "For M^2 the integrand
e^s|dU_s(e)|^2 is predictable and nonnegative and, because dU in H_N, lies in
L^1(dP x ds x nu): E int_0^T int_E e^s|dU_s(e)|^2 nu(de) ds <= e^T E int_0^T ||dU_s||^2 ds < inf.
Both the Poisson integral and its compensator are therefore integrable, so the increment splits
under the expectation: E[M^2_T - M^2_t] = E int_t^T int_E e^s|dU|^2 Ntilde(ds,de)
= E int_t^T int_E e^s|dU|^2 N(ds,de) - E int_t^T int_E e^s|dU|^2 nu(de) ds = 0."
with M^2_t := int_0^t int_E e^s|dU_s(e)|^2 Ntilde(ds,de).

Faithful formal statement must contain:
 - Setting: the standing basis (or any filtered probability space with a PRM N of intensity
   dt x nu, nu sigma-finite, with the compensation formula (2.1) available for predictable
   nonnegative integrands -- i.e. N must be a Poisson random measure relative to the filtration,
   so that the predictable compensator of N is dt x nu). T > 0 (or T >= 0).
 - Hypothesis: dU : Omega x [0,T] x E -> R^m predictable (P x E-measurable) with
   E int_0^T ||dU_s||^2_{L^2(nu)} ds < infinity. (The lemma's other hypotheses -- dY, dZ, dxi, phi,
   the BSDE identity -- are not needed for this step; their absence is not a loss.)
 - Conclusions, for every t in [0,T]:
   (i)  E int_0^T int_E e^s|dU_s(e)|^2 nu(de) ds <= e^T E int_0^T ||dU_s||^2 ds, and this is finite;
   (ii) the Poisson integral E int_(t,T] int_E e^s|dU_s(e)|^2 N(ds,de) < infinity and the
        compensator E int_t^T int_E e^s|dU_s(e)|^2 nu(de) ds < infinity;
   (iii) E[M^2_T - M^2_t] = 0.
 - The definition of M^2 (or of its increment) is critical. The integrand is only L^1, not L^2
   (that is the point of the passage), so M^2_T - M^2_t must be the compensated integral of an L^1
   predictable integrand: pathwise int_(t,T]xE psi dN - int_t^T int_E psi nu(de) ds (both finite
   a.s.), equal to the L^1-limit of the compensated integrals of truncations. If the Lean defines
   M^2 through an L^2 (Ito-isometry) compensated integral, the increment of a non-L^2 integrand
   would be a junk value (e.g. 0) and (iii) would hold trivially -- that would be a mismatched
   definition. If the increment is written explicitly as (N-integral) - (compensator integral),
   that is faithful, and (iii) is then exactly the compensation formula (2.1) at psi 1_{(t,T]}.
 - The N-integral must be the integral against the random measure N(omega) (a lintegral in
   [0,infinity] of a nonnegative integrand); "E" of a real random variable must not be a
   Bochner junk 0 for a non-integrable variable -- integrability is part of (ii).
 - Predictability of psi_s(e) = e^s|dU_s(e)|^2 matters only for the compensation formula; it is
   inherited from dU.
Comparison (verdict recorded 2026-10-19T22:58:40Z):
COMPARISON -- spec:Dissertation.PaperSpec.A.lem41_M2_zero_mean
Reviewer: claude-auditor (same model family as the statements' author).

Lean (Sec4BrownianPoisson.lean:84-146). Hypotheses: the standing setting (LevyDriver D, G0
independent of the driver, filtration enlJoint), 0 < m, 0 < d, T > 0, and all hypotheses of
Lemma 4.1: dZ coordinatewise Predictable, zero off [0,T], finite energy; dU coordinatewise
MarkedPredictable, zero off [0,T], finite markedEnergy; dxi enlJoint_T-measurable and in L^2;
phi jointly measurable with finite energy; dY adapted on [0,T], every path right-continuous on
[0,T) with left limits on (0,T]; and the identity (4.3) for each k and each t in [0,T] a.s., with
the L^2 Ito integral of the row dZ_k against the d-dim W and the (cadlag-version) L^2 compensated
Poisson integral of dU_k. Conclusions:
 (i)  lintegral_w lintegral_{[0,T]} lintegral_E ofReal(e^s sum_k dU_k^2) dnu ds dP
        <= ofReal(e^T) * sum_k markedEnergy(dU_k);
 (ii) that right-hand side < top;
 (iii) for every t in [0,T]: E lintegral_{(t,T] x E} ofReal(e^s sum dU^2) dN(w) < top;
       E lintegral_{(t,T]} lintegral_E ofReal(e^s sum dU^2) dnu ds < top; and
       E[ int_{(t,T] x E} e^s sum dU^2 dN(w) - int_{(t,T]} int_E e^s sum dU^2 dnu ds ] = 0
       (Bochner integrals).

Item by item against my locked reading:
 - Setting: the standing basis with N a PRM for enlJoint (isPoissonFiltration_enlJoint), so the
   compensation formula is available. OK.
 - Hypotheses: those of Lemma 4.1, exactly the ones in force at this point of the printed proof
   (more than this step needs, which is not a loss: they are the lemma's hypotheses, and the
   witness lem_bpbsde_hypotheses shows them met at the backward equation of the solution of
   Example 5.1(i), nu = delta_0, an instance the paper intends). OK.
 - (i), (ii): exactly the display on lines 175-178, as [0, infinity] integrals. OK.
 - (iii) finiteness of the Poisson integral and of the compensator over (t,T] x E: OK.
 - The M^2 increment: written explicitly, pathwise, as (N-integral) - (compensator integral) over
   (t,T] x E. This is the reading my locked reading called faithful: the integrand is only L^1,
   and the Ntilde-integral of a nonnegative L^1 predictable integrand is that difference (it is
   how M^2 arises in (4.4), from splitting int |dU|^2 dN through N = Ntilde + ds nu). No L^2
   isometry integral with a junk value is used.
 - Junk check on the Bochner integrals in the zero-mean conclusion: given the two finiteness
   conclusions, for a.e. w the N-integral and the inner nu-integrals are finite for a.e. s, so the
   Bochner integrals equal the [0, infinity]-integrals' real values off null sets; the outer
   expectation is of an integrable function. So "= 0" is the genuine E[M^2_T - M^2_t] = 0 and is
   not made trivial by a junk 0. OK.
 - "for every t": t in [0,T]. OK.
Representation choices (harmless): coordinates for R^m; time over R with processes vanishing off
[0,T]; energies as lintegrals; the identity (4.3) assumed "for each t, a.s." (weaker than "a.s.
for all t", so the proposition is if anything broader); paths of dY cadlag for every w (the
paper's "cadlag adapted"; on an augmented filtration a null-set modification is harmless); M^2
read pathwise as N-integral minus compensator.

Verdict: faithful with representation choices.

COVERAGE (claim A:lem4.1:M2-infinite-activity, lines 148-152 and 173-187): this clause states the
M^2 paragraph (lines 173-187) except the explicit assertion that the integrand e^s|dU_s(e)|^2 is
predictable and nonnegative (line 173), which no clause states (trivial). The intermediate
equality E[M^2_T - M^2_t] = E int_t^T int_E ... Ntilde(ds,de) is definitional under the pathwise
reading. Across the claim, the jump-times clause does not actually state the "fail to exhaust"
assertion (junk sInf), and the every-setting no-square-moment clause is, in my reading, not the
passage's meaning (its nu != 0 correction is). The hypotheses of this clause are exactly those in
force at this point of the printed proof (Lemma 4.1's), no more, no fewer.
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless: (1) R^m-valued processes as real coordinates, time over R
with processes required to vanish off [0,T]; (2) the L^1 bound and the finiteness statements as
lintegrals in [0, infinity] (no junk); (3) M^2_T - M^2_t read pathwise as the integral against
N(w) over (t,T] x E minus the compensator integral over (t,T] x E -- the correct meaning of a
compensated integral of a nonnegative L^1 predictable integrand, and how M^2 arises in (4.4);
the Bochner integrals in the zero-mean conclusion agree with the [0, infinity] integrals off null
sets because the two finiteness conclusions are stated alongside, so the mean zero is not a junk
value; (4) the identity (4.3) is assumed for each t almost surely (weaker than a.s. for all t, so
the proposition is if anything broader), and dY's paths are cadlag for every w (a null-set
modification on the augmented filtration); (5) the hypotheses are all those of Lemma 4.1, the
ones in force at this point of the proof, witnessed at the backward equation of Example 5.1(i).
Disagreements with the author's review (shown 2026-10-19T22:58:58Z): No disagreement with the author's reading of this clause: M^2_T - M^2_t read pathwise as the
N-integral minus the compensator over (t,T] x E, the L^1 bound and the two finiteness statements
as [0, infinity] integrals, the zero mean as the Bochner expectation of the pathwise difference
(not a junk value, given the finiteness statements), under exactly the hypotheses of Lemma 4.1.
One omission at the level of the claim, not of this proposition: line 173 also asserts that the
integrand e^s|dU_s(e)|^2 is predictable and nonnegative, and no clause of the claim states it
(trivial, but an assertion of the passage).
