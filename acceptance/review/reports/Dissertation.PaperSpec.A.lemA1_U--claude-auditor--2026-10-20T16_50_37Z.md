### A:lemA1:pettis: Dissertation.PaperSpec.A.lemA1_U
Pins: manuscript A None; project 53a4ee4fc8767ba8884b5732431dded9772b47df; hash ed839d34f480cba1019406c1cc1330d9 (pl-fp-v1:92ae8f42b45561a8d8cafe9ed3467a7b1d76bc2a3236e3481a9c98e01ea0ba7d)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-20T16:50:37Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-20T16:39:44Z):
Reading of spec:Dissertation.PaperSpec.A.lemA1_U (locked before any Lean).

Passage: manuscript/paper/sections/09-appendix.tex lines 29-36 (region 25-51 of claim
A:lemA1:pettis): "For the U-coordinate, the integrability hypothesis and the Fubini isometry (2.x)
give U in L^2([0,T] x Omega x E) = L^2([0,T] x Omega; L^2(nu)), so the induced map
(t, omega) -> U_t(omega, .) admits a predictable, strongly measurable L^2(nu)-valued
representative."

What is asserted (hypotheses: U a fixed predictable version, i.e. P (x) calE-measurable
R^m-valued function on [0, T] x Omega x E, with E int_0^T int_E |U_t(e)|^2 nu(de) dt < infinity;
standing (E, calE, nu): countably generated, sigma-finite; the setting's filtration):
 (a) U belongs to L^2([0, T] x Omega x E; R^m) for dt dP nu (measurable, square integrable);
 (b) there is V : [0, T] x Omega -> L^2(nu; R^m), strongly measurable for the predictable
     sigma-field P, square integrable (E int_0^T ||V_t||^2 dt < infinity, in fact equal to
     E int int |U|^2 nu dt, by the isometry), with V_t(omega) = [U_t(omega, .)] in L^2(nu) for
     dt dP-a.e. (t, omega), i.e. V_t(omega)(e) = U_t(omega, e) for nu-a.e. e, for dt dP-a.e.
     (t, omega).
The identification "=" (isometric isomorphism of L^2(P (x) calE) with L^2(P; L^2(nu))) is the
cited (2.x); the step uses it to get the representative.

Faithful formal statement. For every setting, T > 0, every P (x) calE-measurable U with
E int int |U|^2 nu dt < infinity: (a) and (b). The predictable sigma-field must be the setting's
(on [0, T] x Omega or R_+ x Omega restricted). "a.e." w.r.t. Lebesgue (restricted to [0, T]) x P,
and nu-a.e. inside. Stating the norm identity of V is optional (square integrability is what the
paper uses next). Hypothesis "predictable" on U must be P (x) calE-measurability (not merely
B x F x calE-measurability, which would make the predictable conclusion false in general).

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
Comparison for spec:Dissertation.PaperSpec.A.lemA1_U
(Dissertation/PaperSpec/A/AppASteps.lean, lemA1_U).

Reading (locked): for U P (x) calE-measurable with E int int |U|^2 nu dt < infinity: (a) U in
L^2([0, T] x Omega x E; R^m) for dt dP nu; (b) there is V : [0, T] x Omega -> L^2(nu; R^m),
strongly measurable for the predictable sigma-field, square integrable, with V_t(w) = U_t(w, .)
nu-a.e. for dt dP-a.e. (t, w); hypothesis "predictable" = P (x) calE-measurability.

Lean, item by item (hypothesis CadlagPredTuple; U_pred is marked predictability, i.e.
measurability for the marked predictable sigma-algebra, which is P (x) calE on positive times,
as the reading requires; U_sq the integrability):
- (a) MemLp of (t, w, e) -> (U_k(t, w, e))_k in EuclideanSpace R (Fin m), exponent 2, for
  ((Lebesgue on [0, T]) x P) x nu. Matches.
- (b) exists V : Omega -> R -> Lp (EuclideanSpace R (Fin m)) 2 nu, Predictable F V (strongly
  measurable for the predictable sigma-algebra), MemLp of (t, w) -> V_t(w) exponent 2 for
  Lebesgue on [0, T] x P, and for a.e. (t, w) the coercion of V_t(w) equals
  e -> (U_k(t, w, e))_k nu-a.e. Matches.
- The isometric identification itself is not restated (it is the clause of A:eq:fubiniiso); the
  step's conclusion is.

Verdict: broader.

Witness: Dissertation.Acceptance.A.lemA1_coin_hypotheses: U = 1_{(0,1]} with nu = delta_0, T = 1,
U does not vanish: nondegenerate.

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
Verdict: broader — Broader: the clause holds for every filtration on R (no usual conditions), every real T and
n, m, d, under CadlagPredTuple. Instantiation giving the printed step: the setting's filtration
frozen at F_0 before 0, the processes extended as described (U by 0 outside [0, T] and at time 0,
a null modification), T > 0; then (a) and (b) are the printed conclusion of lines 29-36 with the
predictable sigma-field of the setting.
Disagreements with the author's review (shown 2026-10-20T16:50:16Z): none
