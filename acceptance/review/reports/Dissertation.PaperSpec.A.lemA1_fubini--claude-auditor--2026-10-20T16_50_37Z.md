### A:lemA1:pettis: Dissertation.PaperSpec.A.lemA1_fubini
Pins: manuscript A None; project 53a4ee4fc8767ba8884b5732431dded9772b47df; hash ed839d34f480cba18bb7bf3a9a35bb91 (pl-fp-v1:21affc96cb4c8611e3f5aa34d8b24cb0fdaa743607613dd42246afce452628bc)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-20T16:50:37Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-20T16:39:44Z):
Reading of spec:Dissertation.PaperSpec.A.lemA1_fubini (locked before any Lean).

Passage: manuscript/paper/sections/09-appendix.tex lines 43-48 (region 25-51 of claim
A:lemA1:pettis): "The Fubini isometry of [HNVW, Proposition 1.2.24],
L^2([0,T] x Omega; H) = L^2(0,T; L^2(Omega; H)), supplies a strongly measurable
L^2(Omega; H)-valued representative of t -> Theta^-_t".

What is asserted. The cited Fubini isometry: there is a (linear) isometric isomorphism
Phi : L^2([0, T] x Omega, dt dP; H) -> L^2([0, T], dt; L^2(Omega, P; H)) such that for every f,
for a.e. t in [0, T] the section f(t, .) is in L^2(Omega; H) and Phi(f)(t) = [f(t, .)]. This is a
general fact (any sigma-finite measure spaces, any Banach space H, p in [1, infinity)); the step
uses it for H the state space and the probability space of the setting.

Faithful formal statement. For the setting's (Omega, F, P), T > 0, and H (or broader: for every
sigma-finite pair of measure spaces and every Banach/Hilbert space H, instantiation to Lebesgue on
[0, T], P, H): there is a linear isometric equivalence (bijective, norm preserving; "=" in the
paper) Phi between the two L^2 spaces with Phi(f)(t) = f(t, .) in L^2(Omega; H) for a.e. t. An
isometric linear map that is not stated to be onto would be narrower than the printed "=" (the
step uses only the forward direction, so the loss would be of a printed clause the step does not
need). The measure on [0, T] must be Lebesgue restricted to [0, T] (or to (0, T), same), the
product measure dt x P; L^2(Omega; H) with P and the Borel/strong measurability of H-valued maps
(F-measurable, not F_t). The a.e. description is needed: an abstract isometric isomorphism
without it carries no content (any two separable Hilbert spaces of the same dimension are
isometric; here the spaces may be non-separable, still the description is what makes Phi(f) a
representative of t -> f(t, .)).

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
Comparison for spec:Dissertation.PaperSpec.A.lemA1_fubini
(Dissertation/PaperSpec/A/AppASteps.lean, lemA1_fubini).

Reading (locked): a linear isometric isomorphism Phi : L^2([0, T] x Omega, dt dP; H) ->
L^2([0, T], dt; L^2(Omega, P; H)), bijective, with Phi(f)(t) = [f(t, .)] for a.e. t; for the
setting's (Omega, P) and H, or broader (instantiation to Lebesgue on [0, T], P, H); the a.e.
description is required.

Lean, item by item.
- Quantifiers: every probability space (Omega, P), every sigma-finite nu on a countably generated
  E, every n, m, d, every real T; then exists Phi.
- Phi : Lp H 2 ((Lebesgue on [0, T]) x P) to Lp (Lp H 2 P) 2 (Lebesgue on [0, T]) as a linear
  isometric equivalence over R (bijective and norm preserving), H = TupleL2 ... with the Hilbert
  norm. Matches "=" in the paper.
- For every f and Lebesgue-a.e. t in [0, T], the representative of Phi f at t, as a function on
  Omega, equals w -> f(t, w) P-a.e. Matches the required a.e. description.

Verdict: broader.

Witness: Dissertation.Acceptance.A.lemA1_fubini_hypotheses (the uniform law on Bool, nu = delta_0
!= 0 sigma-finite on R, countably generated): the clause has no hypotheses beyond these data, so
any instance is nondegenerate; a probability space of the setting would equally serve.

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
Verdict: broader — Broader: the isometry is asserted for every probability space (Omega, P), every real T and every
n, m, d (with the paper's hypotheses on (E, nu)), not only for the probability space of the
standing setting. Instantiation giving the printed step: take (Omega, F, P) the setting's
probability space, the setting's (E, nu) and n, m, d, and T > 0 its horizon; the conclusion is the
cited Fubini isometry L^2([0, T] x Omega; H) = L^2(0, T; L^2(Omega; H)) with its a.e. description.
Disagreements with the author's review (shown 2026-10-20T16:50:16Z): none
