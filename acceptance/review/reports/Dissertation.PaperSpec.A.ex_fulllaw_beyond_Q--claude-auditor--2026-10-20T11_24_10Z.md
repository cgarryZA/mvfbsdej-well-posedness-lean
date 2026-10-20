### A:ex:fulllaw: Dissertation.PaperSpec.A.ex_fulllaw_beyond_Q
Pins: manuscript A None; project d3e594defeeeb94a6d05c33c666bcb870d584302; hash ed839d34f480cba12be9f13eb8df21c1 (pl-fp-v1:77391c424ac867b33c84ccb47f92f2979db03059f85ddcadebf00bcf5fe4dbae)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-20T11:24:10Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-20T11:09:25Z):
# Reading: ex_fulllaw_beyond_Q — Example 5.4: "the cylindrical term is no expectation functional
# when Q is not affine on the attained range of the features"

Common data of Example 5.4 (05-examples.tex, ex:fulllaw), current text. Section 5 preamble:
"In Examples 5.4 and 5.5, we take nu != 0." Data: mu_0 in P_2(H), Lambda_0 in P_2(L^2(nu))
(L^2(nu) = L^2(nu; R^m), the U-fibre of H), epsilon > 0, q, qtilde, qhat : R_+ -> R, Q : R^J -> R,
features phi_1..phi_J : L^2(nu) -> R, all bounded and Lipschitz; w_0, w_1 in R^m, v_0 in R^n,
hhat in L^2(nu; R^n). R^J and R^j carry Euclidean norms (Section 1: "|.| is the Euclidean norm
on any R^j"), so Lip(Q) is the Euclidean Lipschitz constant. mu^U is the U-marginal of mu.
Statistics: radial F_0(mu) = q(W_2(mu, mu_0)); U-marginal Ftilde(mu) = qtilde(W_2(mu^U, Lambda_0)),
Fhat(mu) = qhat(W_2(mu^U, Lambda_0)); cylindrical F_Q(mu) = Q(int phi_1 dmu^U, ..., int phi_J dmu^U).
Perturbations (independent of t and theta): p_f(mu) = eps q(W_2(mu,mu_0)) w_0 + eps F_Q(mu) w_1,
p_b(mu) = eps qtilde(W_2(mu^U, Lambda_0)) v_0, p_h(mu)(e) = eps qhat(W_2(mu^U, Lambda_0)) hhat(e),
p_sigma = 0. L_Q := Lip(Q) (sum_j Lip(phi_j)^2)^{1/2};
L_p := eps(|w_0| Lip(q) + |v_0| Lip(qtilde) + |w_1| L_Q + ||hhat|| Lip(qhat)).
Baseline (b_0, sigma_0, h_0, f_0, g) "as in Corollary 3.4": m = n, G full rank (invertible),
Assumptions 2.2-2.5 hold (with constants L, alpha, beta_1, beta_2 and initial datum xi_0), margin
c_diss > 0 in the unweighted form (2.13); law-free baseline: b_0(t, theta), sigma_0(t, theta),
h_0(t, theta, e), f_0(t, theta); g : R^n x P_2(R^n) -> R^m as in Section 2, unchanged by the
perturbation. The example says a law-dependent baseline "works identically", so a statement
allowing a law-dependent baseline is a harmless broadening.
"Expectation functional" (the class the example says it goes beyond): the Example 5.3 class,
mu |-> int_H phibar(theta') mu(dtheta') with phibar measurable and Lipschitz (at each fixed
(t, theta) of a kernel phibar(t, theta, theta')), including the two-point-kernel jump-integrand
(Nemytskii) form and the mean-field marginal means of Example 5.1(ii); all are affine under
mixtures of measures.

Claim: Let phi_1..phi_J : L^2(nu) -> R be bounded Lipschitz (measurable) and Q : R^J -> R
(bounded Lipschitz in the example). Let A := { (int phi_1 dmu^U, ..., int phi_J dmu^U) :
mu in P_2(H) } be the attained range of the feature vector (= the set of feature vectors of
lambda in P_2(L^2(nu)), every such lambda being a U-marginal). If Q is non-affine on A, i.e.
there are no a in R, c in R^J with Q(s) = a + sum_j c_j s_j for all s in A, then
mu |-> Q(int phi_1 dmu^U, ..., int phi_J dmu^U) is not an expectation functional of mu (no
Example 5.3 kernel phibar -- measurable Lipschitz H -> R; excluding all measurable integrable
kernels is stronger and acceptable -- with Q(...) = int phibar dmu for all mu in P_2(H)).
(True since the feature map is affine under mixtures and A is convex; an affine-under-mixtures
composite forces Q affine along segments of the convex set A, hence affine on A.)
Quantifiers: for all J, phi, Q satisfying the hypotheses. Narrower would be a different notion
of "affine on the range" (e.g. affine on all of R^J -- then the hypothesis "not affine on R^J"
is weaker and the conclusion would be a stronger, possibly false, claim; or "not affine on A"
replaced by something stronger like "Q non-affine on a neighbourhood"), or a smaller class of
excluded kernels. "Attained range" must be over mu in P_2(H) (or equivalently P_2(L^2(nu))).
Comparison (verdict recorded 2026-10-20T11:23:08Z):
# Decision: spec:Dissertation.PaperSpec.A.ex_fulllaw_beyond_Q (Dissertation/PaperSpec/A/Sec5.lean)

Verdict: broader.

Comparison with the locked reading.
- Setting: every σ-finite ν on a countably generated space, every n, m, d, J.
- Q : EuclideanSpace ℝ (Fin J) -> ℝ, Lipschitz for the Euclidean norm (some LQ); boundedness of Q
  not assumed (broader). Features φ_j : L^2(ν; R^m) -> ℝ Lipschitz (K_j) and bounded (B), as
  printed ("bounded-Lipschitz features").
- Hypothesis "Q non-affine on the attained range": ¬ ∃ a ∈ ℝ, c ∈ ℝ^J such that for every
  μ ∈ P_2(H), Q((∫ φ_j dμ^U)_j) = a + Σ_j c_j ∫ φ_j dμ^U. This is the negation of the printed
  "Q(s) = a + Σ_j c_j s_j there", "there" being the attained range
  {(∫ φ_j dμ^U)_j : μ ∈ P_2(H)} of the feature vector -- exactly the range the passage names
  (not all of R^J).
- Conclusion: for every φ' : H -> ℝ integrable against every P_2 law, some μ ∈ P_2(H) has
  Q((∫ φ_j dμ^U)_j) ≠ ∫ φ' dμ: the cylindrical term is no expectation functional. Excluded class
  larger than the Example 5.3 kernels (stronger conclusion), as for beyond_radial.
Broader than printed: unbounded Q allowed, larger excluded class. The printed claim is the
instance in the detail file.

Current text. Read at 1f67672 (Example 5.4: "The cylindrical term does so when Q is non-affine on
the attained range of the feature vector (∫ φ_1 dμ^U, ..., ∫ φ_J dμ^U): if Q(s) = a + Σ_j c_j s_j
there, the Q-term equals ∫_H (a + Σ_j c_j φ_j(u')) μ(dθ'), an expectation functional already
covered by Example 5.3"). I have not seen the earlier text, so I cannot say what changed; the
"attained range" formulation of the current text is exactly the proposition's hypothesis.

Witness. `Dissertation.Acceptance.A.ex_fulllaw_beyond_Q_hypotheses` (Dissertation/Acceptance/A/
Witness.lean): ν = δ_0, J = 1, Q(s) = min(|s₁|, 1/2) (1-Lipschitz), φ₁(u) = min(||u||, 1)
(1-Lipschitz, bounded by 1), and Q is shown non-affine on the attained range (Dirac laws at
t e₁ give features min(|t|, 1) covering [0, 1], on which min(·, 1/2) is not affine). An instance
the paper intends (nonlinear Q, nonconstant bounded Lipschitz feature).

Coverage (claim A:ex:fulllaw, seven clauses: lip, pert, wp, beyond_radial, beyond_U_corr,
beyond_Q, affineQ). The mathematical assertions of Example 5.4 at this revision are: the three
statistics are W_2-Lipschitz with Lip(q), Lip(qtilde), Lip(qhat) and L_Q (lip); the perturbations
satisfy origin integrability, are θ-independent, satisfy (3.5) with L_p and hence Assumption 2.3,
and (3.4) with c_pert = ||G|| L_p (pert); under (5.1) the perturbed system is well-posed with
margin c_diss - ||G|| L_p (wp); for nonconstant profiles the radial statistics are not expectation
functionals (beyond_radial for the full tuple law, beyond_U_corr for the U-marginal ones, covering
both qtilde and qhat); the cylindrical term is not one when Q is non-affine on the attained range
(beyond_Q) and is the expectation functional of Example 5.3 when Q is affine there (affineQ). Two
further sentences carry content: "Example 5.1(i) supplies such a baseline" (a cross-reference
whose content -- Example 5.1(i) meets Assumptions 2.2-2.5 with an unweighted margin -- is
Example 5.1's own claim; the witness ex_fulllaw_hypotheses also exhibits it) and "a law-dependent
dissipative baseline works identically" (covered: pert and wp allow any baseline, law-dependent
or not). "Beyond the linear jump-integrand expectations of the cited models" is a comparison with
the literature, subsumed by the no-expectation-functional clauses; the closing sentence on the
weak-coupling route is exposition. No clause states something the passage does not claim. The
hypotheses in force: the statements drop boundedness of the profiles, of Q and of the features
where it is not needed and do not assume ν ≠ 0 except where it is needed (beyond_U_corr), which
only broadens them; m = n is assumed where the passage's baseline needs it (pert, wp).
Witnesses: ex_fulllaw_hypotheses (lip, pert, wp) is Example 5.1(i) with β₁ = β₂ = 2 at ν = δ_0 ≠ 0,
G = 1, margin c_diss = 1, with ε = 1/4, q = qtilde = qhat = min(|r|, 1), Q(s) = min(|s|, 1),
φ₁(u) = min(||u||, 1), w₀ = w₁ = v₀ = e₁ but hhat = 0: the jump-coefficient perturbation, which the
passage singles out ("the latter entering the jump coefficient itself"), is zero in the witness.
The hypotheses are met and every other object is nonzero; a choice such as ε = 1/8 with
hhat = e₁ (then L_p = 1/2 < 1) would exhibit the intended instance with all four directions
nonzero.
Witness: —
Verdict: broader — Broader than the printed claim: Q need not be bounded, and the conclusion excludes every
φ' : H -> ℝ integrable against every P_2 law, a class containing the Example 5.3 kernels. The
printed claim is the instance with the paper's bounded Lipschitz Q (Euclidean norm on R^J) and
bounded Lipschitz features φ_j, Q non-affine on the attained range {(∫ φ_j dμ^U)_j : μ ∈ P_2(H)}
(the hypothesis is literally the negation of "Q(s) = a + Σ_j c_j s_j there"), and φ' any
Example 5.3 kernel at fixed (t, θ): the cylindrical term then differs from ∫ φ' dμ at some μ.
Disagreements with the author's review (shown 2026-10-20T11:23:29Z): none
