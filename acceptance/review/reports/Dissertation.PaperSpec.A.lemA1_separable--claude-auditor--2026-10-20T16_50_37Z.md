### A:lemA1:pettis: Dissertation.PaperSpec.A.lemA1_separable
Pins: manuscript A None; project 53a4ee4fc8767ba8884b5732431dded9772b47df; hash ed839d34f480cba1e132af851a6dd7cf (pl-fp-v1:a8c22137a3ba327069a0c54958da10ca87ad8a11f136b59616a8e23c38afdd98)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-20T16:50:37Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-20T16:39:44Z):
Reading of spec:Dissertation.PaperSpec.A.lemA1_separable (locked before any Lean).

Passage: manuscript/paper/sections/09-appendix.tex line 28 (region 25-51 of claim
A:lemA1:pettis): "and H is separable because L^2(nu) is"; with Section 2 lines 5-7: nu sigma-finite
on a countably generated (E, calE), "so that L^2(nu; R^j) is separable for every j >= 1".

What is asserted. Under the standing hypotheses on (E, calE, nu): calE countably generated, nu
sigma-finite, L^2(nu; R^m) (classes of square-integrable R^m-valued functions, L^2 norm) is a
separable metric space, and consequently H = R^n x R^m x R^{m x d} x L^2(nu; R^m) is separable.
Separability is a property of the topology; the Hilbert norm |theta|_H^2 = sum of squares and the
product (max) norm induce the same topology, so H "with its Hilbert norm" versus the product
topology is immaterial for the conclusion. Both hypotheses are needed in general (counting measure
on R with its Borel sigma-algebra: countably generated but not sigma-finite, l^2(R) not
separable).

Faithful formal statement. For every measurable space (E, calE) that is countably generated and
every sigma-finite measure nu on it, and all n, m, d >= 1 (any naturals is broader and fine):
L^2(nu; R^m) is separable (TopologicalSpace.SeparableSpace, or second countable, which is
equivalent for metric spaces), and H is separable. The clause may be stated for the setting's
(E, nu) or for all such (E, nu) (broader, instantiation to the setting). If it is stated under
stronger hypotheses (e.g. E a standard Borel space, nu finite) it would be narrower than the
printed claim, whose hypotheses are exactly countably generated + sigma-finite. The Euclidean
spaces must be with any norm (separability does not depend on it), R^{m x d} as matrices.

Context (all lemA1 units). Passage: manuscript/paper/sections/09-appendix.tex, region lines 25-51
(proof of Lemma A.1, Step 1, claim A:lemA1:pettis), read with the statement of Lemma A.1 (lines
5-23), Steps 2-3 (lines 53-73, which use Step 1), the standing setting of Section 2 (lines 1-12:
filtered space with the usual conditions, T > 0, n, m, d >= 1; nu sigma-finite on countably
generated (E, calE), "so that L^2(nu; R^j) is separable for every j >= 1"; the filtration the
usual augmentation of W, N, F_0), the Fubini isometry (2.x) eq:fubiniiso (lines 112-123: P the
predictable sigma-field on Omega x [0, T], L^2(P; L^2(nu)) = L^2(P (x) calE)), and the state space
H = R^n x R^m x R^{m x d} x L^2(nu; R^m) with |theta|_H^2 = |x|^2 + |y|^2 + |z|_F^2 + ||u||^2
(introduction lines 17-31).
Hypotheses of Lemma A.1 (in force throughout Step 1): X (R^n-valued), Y (R^m-valued) cadlag
adapted; Z (R^{m x d}-valued) and U (R^m-valued function of (t, omega, e)) fixed predictable
versions (Z P-measurable, U P (x) calE-measurable); and
  E int_0^T (|X_t|^2 + |Y_t|^2 + |Z_t|_F^2 + int_E |U_t(e)|^2 nu(de)) dt < infinity.
Theta^-_t = (X_{t-}, Y_{t-}, Z_t, U_t) with U_t read as the element U_t(omega, .) of L^2(nu)
(through the representative supplied in Step 1).
The printed Step 1 asserts, in order: (a) X_-, Y_- predictable; (b) they agree with X, Y
dt dP-a.e. as cadlag paths jump at countably many times, so int_0^T 1{X_{t-} != X_t} dt = 0 a.s.;
(c) the hypothesis on X, Y passes to X_-, Y_-; (d) H separable because L^2(nu) is; (e) Z
predictable and square integrable; (f) U in L^2([0,T] x Omega x E) = L^2([0,T] x Omega; L^2(nu))
by the integrability hypothesis and (2.x), so (t, omega) -> U_t(omega, .) admits a predictable
strongly measurable L^2(nu)-valued representative; (g) Theta^- is a predictable, hence jointly
measurable, H-valued field with E int ||Theta^-_t||_H^2 dt < infinity, i.e. Theta^- in
L^2([0,T] x Omega; H); (h) the Fubini isometry L^2([0,T] x Omega; H) = L^2(0,T; L^2(Omega; H))
of [HNVW, Prop. 1.2.24] supplies a strongly measurable L^2(Omega; H)-valued representative of
t -> Theta^-_t; (i) by Pettis that map takes values in a separable closed subspace off a null set
of times, and therefore admits a Borel version agreeing with it for a.e. t.
Comparison (verdict recorded 2026-10-20T16:50:11Z):
Comparison for spec:Dissertation.PaperSpec.A.lemA1_separable
(Dissertation/PaperSpec/A/AppASteps.lean, lemA1_separable).

Reading (locked): for every countably generated (E, calE) and sigma-finite nu (both needed), and
n, m, d: L^2(nu; R^m) is separable, and so is H; the norm on H is immaterial for separability.

Lean, item by item.
- Hypotheses: MeasurableSpace.CountablyGenerated E and SigmaFinite nu, for every E, nu, n, m, d.
  Exactly the standing hypotheses on (E, nu); n, m, d any naturals (including 0, a trivial
  generalisation of n, m, d >= 1).
- Conclusions: SeparableSpace (Lp (EuclideanSpace R (Fin m)) 2 nu), i.e. L^2(nu; R^m) with its
  norm; SeparableSpace (TupleL2 R^n R^m R^{m x d} L^2(nu; R^m)), H with its Hilbert norm (iterated
  L^2 product), the matrix channel EuclideanSpace R (Fin m x Fin d) with the Frobenius norm.
  Matches.

Verdict: faithful.

Witness: Dissertation.Acceptance.A.lemA1_polish_hypotheses: Lebesgue measure on R, sigma-finite on
a countably generated space, of infinite mass (L^2(nu) infinite-dimensional): an intended,
nondegenerate instance (the separability is not a finite-dimensional triviality there).

Coverage (claim A:lemA1:pettis, region lines 25-51 of manuscript/paper/sections/09-appendix.tex,
read in acceptance/claims.json after show). Its seven clauses (lemA1_leftlim, lemA1_separable,
lemA1_U, lemA1_pred, lemA1_L2, lemA1_fubini, lemA1_pettis) state every mathematical assertion of
Step 1: X_-, Y_- predictable and equal to X, Y dt dP-a.e., with countable jump sets,
int_0^T 1{X_{t-} != X_t} dt = 0 and the integrability passing to them (lines 25-28); H separable
because L^2(nu) is (line 28); U in L^2([0, T] x Omega x E) with a predictable strongly measurable
L^2(nu)-valued representative (lines 29-36); Theta^- predictable, jointly measurable and in
L^2([0, T] x Omega; H) (lines 36-42); the Fubini isometry, the strongly measurable
L^2(Omega; H)-valued representative of t -> Theta^-_t, its separable range and the Borel version
agreeing for a.e. t (lines 43-51). The sentence that the Z-coordinate is predictable and square
integrable (lines 28-29) restates the hypothesis (CadlagPredTuple) and is reasonably not stated;
the isometry (2.4) invoked at line 31 is assigned to A:eq:fubiniiso and its conclusion for U is
lemA1_U. No clause states something the passage does not claim; lemA1_pred, lemA1_L2 and
lemA1_pettis use the canonical lift of U_t(w, .) rather than an unspecified representative, a
particular choice of "the" representative which makes those clauses slightly stronger, not
different. Hypotheses: those of Lemma A.1, over an arbitrary filtration on R rather than the
setting's (broader; instantiation in the shared block). Witnesses: lemA1_coin_hypotheses and
lemA1_hypotheses (Bool with the uniform law, X = Y a fair sign revealed at t = 1/2, Z = U =
1_{(0,1]}, nu = delta_0, T = 1, with the filtration generated by the sign, resp. the full one) are
nondegenerate: the left limit differs from the value at the jump time, X_1 is not a.s. constant
and U does not vanish; they lie outside the Brownian-Poisson setting, which the broader clauses do
not require, and the setting itself plainly meets the hypotheses. lemA1_fubini_hypotheses and
lemA1_polish_hypotheses exhibit the data of the general clauses (nu = delta_0, resp. Lebesgue
measure on R with infinite-dimensional L^2(nu)).
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-20T16:50:16Z): A difference of label only: I record "faithful" rather than "faithful with representation
choices". The clause's hypotheses are exactly the standing ones (calE countably generated, nu
sigma-finite). The only representational features are H with its Hilbert norm (separability does
not depend on the norm) and n, m, d ranging over all naturals (a trivial generalisation). Neither
changes the statement, so I see no representation choice to record. There is no substantive
disagreement.
