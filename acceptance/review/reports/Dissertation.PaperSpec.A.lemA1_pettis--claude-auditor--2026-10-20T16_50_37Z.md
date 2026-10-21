### A:lemA1:pettis: Dissertation.PaperSpec.A.lemA1_pettis
Pins: manuscript A None; project 53a4ee4fc8767ba8884b5732431dded9772b47df; hash ed839d34f480cba176ccc2a6aaf99d7c (pl-fp-v1:9aaf53a77ade3938e572bca7bb0c4b878d9bcedf03920b1fe533274be51bc6f0)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-20T16:50:37Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-20T16:39:44Z):
Reading of spec:Dissertation.PaperSpec.A.lemA1_pettis (locked before any Lean).

Passage: manuscript/paper/sections/09-appendix.tex lines 46-51 (region 25-51 of claim
A:lemA1:pettis): the Fubini isometry "supplies a strongly measurable L^2(Omega; H)-valued
representative of t -> Theta^-_t; by the Pettis measurability theorem, that map takes values in a
separable closed subspace of L^2(Omega; H) off a Lebesgue-null set of times, and therefore admits
a Borel version, agreeing with it for a.e. t."

What is asserted (hypotheses of Lemma A.1; Theta^- = (X_-, Y_-, Z, V) with V the predictable
representative of U): there is F : [0, T] -> L^2(Omega, P; H) such that
 (a) F is strongly measurable (Lebesgue/Borel on [0, T]);
 (b) F takes values in a closed separable subspace of L^2(Omega; H) (off a null set of times, for
     the representative; everywhere for the version);
 (c) F is Borel measurable (for the Borel sigma-algebra of the norm topology of L^2(Omega; H)),
     which is what Step 2 composes with the law map;
 (d) F(t) = [Theta^-_t] in L^2(Omega; H) for a.e. t in [0, T] (in particular, for a.e. t, the
     section omega -> Theta^-_t(omega) is in L^2(Omega; H)).
Faithful formal statement. For every setting, T > 0, X, Y cadlag adapted, Z predictable, U
P (x) calE-measurable with the integrability hypothesis, V the predictable L^2(nu)-valued
representative of U: there exists F with (a)-(d). The domain [0, T] with Lebesgue measure (a
function on R measured with Lebesgue restricted to [0, T] is fine); Borel measurability with
respect to the Borel sigma-algebra of the norm topology of L^2(Omega, F, P; H) (not a weaker
sigma-algebra). "for a.e. t" w.r.t. Lebesgue on [0, T]. The closed separable subspace may be
stated as separability of the range (TopologicalSpace.IsSeparable of range F) or as the existence
of a closed separable subspace containing the range; strong measurability (finite-valued
approximation) already implies separability of the range (Pettis), so (b) is a consequence of
(a), and (c) of (a) as well. The Borel version must agree with Theta^- for a.e. t, as printed.

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
Comparison for spec:Dissertation.PaperSpec.A.lemA1_pettis
(Dissertation/PaperSpec/A/AppASteps.lean, lemA1_pettis).

Reading (locked): under Lemma A.1's hypotheses there is F : [0, T] -> L^2(Omega, P; H) with
(a) F strongly measurable; (b) values in a closed separable subspace; (c) Borel measurable for the
norm-Borel sigma-algebra of L^2(Omega; H); (d) F(t) = [Theta^-_t] in L^2(Omega; H) for a.e. t in
[0, T] (in particular Theta^-_t in L^2(Omega; H) for a.e. t).

Lean, item by item.
- Hypothesis: CadlagPredTuple.
- exists F : R -> Lp H 2 P with: (a) StronglyMeasurable F (Borel on R); (b) a closed, separable
  submodule V of Lp H 2 P containing F t for every t; (c) Measurable F for borel of Lp H 2 P (the
  norm-Borel sigma-algebra, written explicitly); (d) for Lebesgue-a.e. t in [0, T] there is a
  proof h that w -> Theta^-_t(w) is in L^2(P; H) and F t = h.toLp. Matches (a)-(d), the domain R
  measured on [0, T] being harmless.
- Theta^- with the canonical lift in the U-channel, as in lemA1_pred.

Verdict: broader.

Witness: Dissertation.Acceptance.A.lemA1_hypotheses (fair sign on Bool, full filtration, X = Y
jumping at 1/2, Z = U = 1_{(0,1]}, nu = delta_0, T = 1): Theta^-_t is a nonconstant element of
L^2(Omega; H) for t in (1/2, 1]: nondegenerate.

Shared representation of the hypotheses of Lemma A.1 (checked in
Dissertation/PaperSpec/A/AppASteps.lean and the structure
Dissertation.WellPosedness.System.CadlagPredTuple in
Dissertation/WellPosedness/System/LawFlow.lean; tupleAt, uLift in
Dissertation/WellPosedness/System/Tuple.lean; TupleL2, toL2 in
Dissertation/WellPosedness/System/HilbertW2.lean; Predictable / predictableSigma and
MarkedPredictable in LevyStochCalc):
- The clauses quantify over every probability space, every filtration F indexed by R (no usual
  conditions, no Brownian-Poisson structure), every sigma-finite nu on a countably generated E,
  all n, m, d and every real T. CadlagPredTuple: X, Y adapted at every t in R, every path
  right-continuous with left limits at every t in R; Z componentwise Predictable (strongly
  measurable for the predictable sigma-algebra on R x Omega generated by (-inf, 0] x A, A in F_0,
  and (r, inf) x A, A in F_r, which restricted to [0, T] x Omega is the usual predictable
  sigma-field generated by {0} x F_0 and (r, q] x F_r); U componentwise MarkedPredictable; and
  energy(X_i), energy(Y_k), energy(Z_kj), markedEnergy(U_k) finite over [0, T], which is the
  integrability hypothesis of Lemma A.1 coordinatewise.
- Theta^-_t(w) = toL2(tupleAt nu X_- Y_- Z U t w): the tuple (X_{t-}, Y_{t-}, Z_t, U_t(w, .)) in
  H = R^n x R^m x R^{m x d} x L^2(nu; R^m) with the Hilbert norm (iterated L^2 product, Frobenius
  norm on the matrix channel), the U-channel being the canonical lift uLift: the L^2(nu) class of
  e -> U_t(w, e) when it is square integrable, 0 otherwise (a dt dP-null set of (t, w) in
  [0, T] x Omega under the hypothesis). X_- = leftLimProc X is the actual left limit at every t
  (it exists at every t by hypothesis).
Instantiation giving the paper's Lemma A.1: take F the setting's filtration extended to t < 0 by
F_0 (the paper's filtration enlJoint is frozen before 0 in exactly this way); extend X, Y by X_0,
Y_0 before 0 and by X_T, Y_T after T (still cadlag and adapted, and then X_{0-} = X_0, the paper's
convention); extend Z, U by 0 outside [0, T] (for U also at the single time 0, a dt dP nu-null
modification forced by the marked predictable sigma-algebra and harmless since Lemma A.1's U is a
version fixed up to such null sets). The conclusions restricted to [0, T] are the printed ones.

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
Verdict: broader — Broader: every filtration on R, every real T and n, m, d, under CadlagPredTuple; F defined on R
(its values off [0, T] are unconstrained except by the measurability and range conditions); the
U-channel of Theta^- is the canonical lift. Instantiation giving the printed step: the setting's
filtration frozen before 0 and the processes extended to R as for the other Step 1 clauses,
T > 0; restricting F to [0, T] gives the Borel version of t -> Theta^-_t of lines 46-51, strongly
measurable, separably valued, agreeing with Theta^-_t in L^2(Omega; H) for a.e. t.
Disagreements with the author's review (shown 2026-10-20T16:50:16Z): none
