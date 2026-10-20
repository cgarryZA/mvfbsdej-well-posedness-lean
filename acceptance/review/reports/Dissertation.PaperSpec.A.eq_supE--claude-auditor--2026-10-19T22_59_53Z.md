### A:eq:supE: Dissertation.PaperSpec.A.eq_supE
Pins: manuscript A None; project 6d403c197bfb10fe8808933c6e525ee0ae544fb1; hash ed839d34f480cba17f3cae8e2942fb86 (pl-fp-v1:e241a26f752408caf91446781f151100334c9ecb1156a6f82b2884312e552502)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T22:59:53Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T22:48:57Z):
READING (locked before any Lean) -- spec:Dissertation.PaperSpec.A.eq_supE
Reviewer: claude-auditor (same model family as the statements' author).

Passage: proof of Lemma 4.1 (lem:bpbsde), after "Taking expectations in (4.4) ...":
 E e^t|dY_t|^2 + E int_t^T e^s(|dZ_s|_F^2+||dU_s||^2) ds <= E e^T|dxi|^2 + E int_t^T e^s|phi_s|^2 ds;
 "Bounding 1 <= e^s <= e^T on both sides leaves, for every t <= T,
   E|dY_t|^2 + E int_t^T (|dZ_s|_F^2 + ||dU_s||^2) ds <= R,  R := e^T(E|dxi|^2 + E int_0^T|phi_s|^2 ds).
 Both terms on the left are nonnegative and R does not depend on t, so each is bounded by R on its
 own, the first uniformly in t and the second at t = 0; adding them,
 (4.6)  sup_{t<=T} E|dY_t|^2 + E int_0^T (|dZ_s|_F^2+||dU_s||^2) ds <= 2R = C_0(E|dxi|^2 +
        E int_0^T |phi_s|^2 ds),  C_0 := 2e^T."

Hypotheses in force at this point (those of Lemma 4.1, in the standing setting):
 - standing basis (T > 0, W d-dim BM, independent PRM N with intensity dt x nu, nu sigma-finite on
   countably generated E, augmented filtration with F_0);
 - dY : cadlag adapted R^m-valued; dZ in H_W (predictable R^{m x d}, E int |dZ|_F^2 < inf);
   dU in H_N (predictable, P x E-measurable, E int ||dU||^2 < inf);
 - dxi in L^2(F_T; R^m); phi in L^2(Omega x [0,T]; R^m) (jointly measurable; adaptedness is not
   stated in the lemma; (4.3) itself forces int_0^t phi ds to be adapted);
 - the identity (4.3): a.s., for every t in [0,T],
   dY_t = dxi + int_t^T phi_s ds - int_t^T dZ_s dW_s - int_t^T int_E dU_s(e) Ntilde(ds,de),
   with the Ito integral and the L^2 compensated-Poisson integral (dZ, dU are L^2, so these are
   the L^2 stochastic integrals).
 - Already derived before this step: dY in S^2 (the "Membership" paragraph). A statement may take
   it as a consequence, not as an extra hypothesis; adding it as a hypothesis would be a harmless
   strengthening only if it is derivable from the others (it is), but strictly it is not a
   hypothesis of the lemma.
No other hypothesis (no assumption on the coefficients; no smallness; no finiteness of nu).

Conclusion: (A) for every t in [0,T]:
   E|dY_t|^2 + E int_t^T (|dZ_s|_F^2 + ||dU_s||^2_{L^2(nu)}) ds <= e^T (E|dxi|^2 + E int_0^T |phi_s|^2 ds);
 (B) sup_{t in [0,T]} E|dY_t|^2 + E int_0^T (|dZ_s|_F^2 + ||dU_s||^2) ds <= 2e^T (E|dxi|^2 +
   E int_0^T |phi_s|^2 ds), i.e. C_0 = 2e^T.
Constants: C_0 = 2e^T exactly (depends on T only), R = e^T(...). The norms: Euclidean on R^m,
Frobenius on R^{m x d}, ||u||^2 = int_E |u(e)|^2 nu(de).
Representation notes: the sup over t of E|dY_t|^2 must be a genuine supremum (in R it must be
bounded above for sSup to be meaningful -- it is, by (A) -- or in [0,infinity]); expectations of
squares should not be Bochner junk (integrability follows from S^2 membership and the L^2
hypotheses). A statement that takes as HYPOTHESIS the expected Ito identity (the display before
"Bounding 1 <= e^s <= e^T") rather than the BSDE (4.3) would be a different (algebraic) claim;
this proposition, as a step of the printed proof, is legitimately the consequence of the lemma's
hypotheses at this point, i.e. (A) and (B) from the BSDE hypotheses.
Comparison (verdict recorded 2026-10-19T22:58:40Z):
COMPARISON -- spec:Dissertation.PaperSpec.A.eq_supE
Reviewer: claude-auditor (same model family as the statements' author).

Lean (Sec4BrownianPoisson.lean:148-207). Hypotheses: identical to lem41_M2_zero_mean, i.e. the
standing setting and all hypotheses of Lemma 4.1 (dZ in H_W, dU in H_N, dxi in L^2(F_T), phi
jointly measurable with finite energy, dY adapted with cadlag paths on [0,T], identity (4.3) for
each t a.s. with the genuine L^2 Ito and compensated Poisson integrals). Conclusions, all in
[0, infinity]:
 (A) for every t in [0,T]:
     E esq(dY_t) + E int_{[t,T]} (sum_k esq(dZ_k s) + sum_k int_E |dU_k(s,e)|^2 dnu) ds
       <= ofReal(e^T) * (E esq(dxi) + sum_k energy(phi_k));
 (B) (sup_{t in [0,T]} E esq(dY_t)) + (sum_{k,j} energy(dZ_kj) + sum_k markedEnergy(dU_k))
       <= ofReal(2 e^T) * (E esq(dxi) + sum_k energy(phi_k)).

Item by item against my locked reading:
 - Setting and hypotheses: exactly those of Lemma 4.1 in the standing setting, nothing added
   (no S^2 membership assumed, no coefficient assumption, no finiteness of nu). OK.
 - (A): esq = squared Euclidean norm; sum_k esq(dZ_k) = |dZ|_F^2; sum_k int |dU_k|^2 dnu =
   ||dU||^2_{L^2(nu)}; energy(phi_k) summed = E int_0^T |phi|^2. R = e^T(...). Exactly the display
   on lines 200-205. OK.
 - (B): the sup over t in [0,T] of E|dY_t|^2, taken in [0, infinity] (genuine supremum, no
   R-valued sSup junk); the Z and U terms over [0,T]; constant C_0 = 2 e^T. Exactly (4.6). OK.
 - Expectations as lintegrals: no Bochner junk. OK.
 - Constants: C_0 = 2e^T, depends on T only. OK.
 - Non-vacuity: witness lem_bpbsde_hypotheses (backward equation of the solution of Theorem 3.5
   for Example 5.1(i), nu = delta_0, m = d = 1, T = 1): an instance the paper intends.
Representation choices (harmless): coordinates; time over R with vanishing off [0,T]; integrals
over Icc t T instead of (t,T] (Lebesgue-null difference); identity (4.3) assumed for each t a.s.;
cadlag for every path; phi only jointly measurable (as the lemma states phi in L^2(Omega x [0,T])).

Verdict: faithful with representation choices.

COVERAGE (claim A:eq:supE; hashed passage lines 208-217, the display (4.6), with R from line 204):
the single clause states (4.6) with C_0 = 2e^T, and in addition the per-time bound of lines
200-205 ("for every t <= T, ... <= R"), which the paper asserts in the sentence introducing
(4.6), so it states nothing the paper does not claim. Every mathematical assertion of the hashed
passage is stated. The hypotheses are exactly those in force at this point of the printed proof
(Lemma 4.1's), no more, no fewer; the intermediate expected Ito identity of lines 193-199 is not
assumed as a hypothesis (it is derived), which is right for a step stated from the lemma's data.
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless: (1) R^m- and R^{m x d}-valued processes as real
coordinates, with |.|^2 written as the coordinate sum esq and the Frobenius and L^2(nu) norms
as coordinate sums of energies; (2) all expectations, integrals and the supremum over t in
[0, infinity], so neither the bound nor the sup can be a junk value; (3) time over R with
processes vanishing off [0,T], and int_t^T read over [t,T] (a Lebesgue-null difference from
(t,T]); (4) the identity (4.3) assumed for each t almost surely (weaker than a.s. for all t),
dY's paths cadlag for every w, phi only jointly measurable (as the lemma states phi in
L^2(Omega x [0,T])); (5) the hypotheses are exactly Lemma 4.1's, witnessed at the backward
equation of Example 5.1(i).
Disagreements with the author's review (shown 2026-10-19T22:58:58Z): none
