### A:lemA1:pettis: Dissertation.PaperSpec.A.lemA1_pred
Pins: manuscript A None; project 53a4ee4fc8767ba8884b5732431dded9772b47df; hash ed839d34f480cba136b795f0b638d045 (pl-fp-v1:e0770011789fa86d2d2a5d439a57dcece8ee52edefa3b10081fedbd54f66388f)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-20T16:50:37Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-20T16:39:44Z):
Reading of spec:Dissertation.PaperSpec.A.lemA1_pred (locked before any Lean).

Passage: manuscript/paper/sections/09-appendix.tex lines 36-37 (region 25-51 of claim
A:lemA1:pettis): "Theta^- is therefore a predictable, hence jointly measurable, H-valued field".

What is asserted (all hypotheses of Lemma A.1 in force; U-coordinate read through the
predictable representative V of the previous sentence): the map
(t, omega) -> Theta^-_t(omega) = (X_{t-}(omega), Y_{t-}(omega), Z_t(omega), V_t(omega)) in H is
measurable (equivalently, as H is separable, strongly measurable) for the predictable
sigma-field P of the setting's filtration (on [0, T] x Omega).

Faithful formal statement. For every setting, T > 0, X, Y cadlag adapted, Z predictable, U
P (x) calE-measurable with the integrability hypothesis of Lemma A.1, and V a (or the)
predictable strongly measurable L^2(nu)-valued representative of U (either quantified "for every
such representative V" or "there is a representative V such that"; the first is stronger and
also true, since predictability of Theta^- then follows coordinatewise): the H-valued map is
strongly measurable for P. H with its Hilbert norm vs. the product norm: same topology, same
Borel sets, same strong measurability. Coordinates X_-, Y_- with the left-limit convention at 0
as in the paper (X_{0-} = X_0). The integrability hypothesis is not needed for this conclusion,
except that V is the representative it produces; a clause without it is broader.

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
Comparison for spec:Dissertation.PaperSpec.A.lemA1_pred
(Dissertation/PaperSpec/A/AppASteps.lean, lemA1_pred).

Reading (locked): under Lemma A.1's hypotheses, (t, w) -> (X_{t-}, Y_{t-}, Z_t, V_t)(w) in H is
strongly measurable for the predictable sigma-field, V a (or the) predictable representative of
U; the Hilbert vs product norm immaterial; left-limit convention at 0.

Lean, item by item.
- Hypothesis: CadlagPredTuple (Lemma A.1's hypotheses, see the shared block).
- Conclusion: Predictable F (fun w t => toL2 (tupleAt nu X_- Y_- Z U t w)): strongly measurable
  for the predictable sigma-algebra on R x Omega, valued in H with its Hilbert norm.
- U-channel: the canonical lift of e -> U_t(w, e) (its L^2(nu) class where square integrable,
  0 elsewhere). This is one particular representative V; the paper says the field built with "the"
  predictable representative is predictable. The clause therefore asserts predictability for a
  specific, canonical representative, which is slightly stronger than "for some representative"
  and true (the set where U_t(w, .) is square integrable is predictable by Tonelli, and on it the
  lift is weakly, hence, L^2(nu) being separable, strongly measurable). It agrees dt dP-a.e. with
  any representative of lemA1_U.
- Coordinates X_-, Y_- as in lemA1_leftlim, Z rows forming the Frobenius channel. Matches.

Verdict: broader.

Witness: Dissertation.Acceptance.A.lemA1_coin_hypotheses: nonzero, jumping X, Y and nonzero U:
nondegenerate.

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
Verdict: broader — Broader: (1) every filtration on R, every real T, every n, m, d; instantiation as for the other
Step 1 clauses (the setting's filtration frozen before 0, processes extended to R, U set to 0
outside (0, T]); (2) the U-channel is the canonical L^2(nu)-lift of U_t(w, .) (0 where not square
integrable), a particular representative, so the clause asserts predictability of the field built
with that representative, which yields the printed statement (the field with "the" predictable
representative is predictable) directly, the canonical lift being itself a predictable
representative (lemA1_U's V may be taken to be it). H with its Hilbert norm as printed.
Disagreements with the author's review (shown 2026-10-20T16:50:16Z): none
