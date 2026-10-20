### A:ex:fulllaw: Dissertation.PaperSpec.A.ex_fulllaw_affineQ
Pins: manuscript A None; project d3e594defeeeb94a6d05c33c666bcb870d584302; hash ed839d34f480cba1b7c4d4b7307e74ea (pl-fp-v1:c1c56b7f113beceffc7bfe8c4338c5fe843f308fd8210ce9945992e3b56f615b)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-20T11:24:10Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-20T11:09:25Z):
# Reading: ex_fulllaw_affineQ — Example 5.4: "Q affine on the attained range of the features: the
# cylindrical term is an expectation functional of Example 5.3"

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

Claim: Let phi_1..phi_J : L^2(nu) -> R be bounded Lipschitz (bounded measurable suffices for the
identity), Q : R^J -> R, A the attained range as above. If Q(s) = a + sum_j c_j s_j for all s in
A (some a in R, c in R^J), then for every mu in P_2(H)
   Q(int phi_1 dmu^U, ..., int phi_J dmu^U) = int_H ( a + sum_j c_j phi_j(u') ) mu(dtheta'),
and this is an expectation functional "already covered by Example 5.3": the kernel
theta' |-> a + sum_j c_j phi_j(u') is measurable and Lipschitz on H (constant <= sum_j |c_j|
Lip(phi_j), and bounded), so it is in the Example 5.3 class (with no dependence on (t, theta)).
A faithful statement must give the identity for all mu in P_2(H) (with the integral over H of the
kernel composed with the U-projection, or equivalently over L^2(nu) against mu^U); the "covered
by Example 5.3" part asks that the kernel be in that class (Lipschitz) -- a statement giving only
the identity omits that part (narrow omission, to be judged). Hypothesis "affine on A" must be
the attained range over P_2(H) (affine on all of R^J would be a stronger hypothesis, i.e. a
narrower claim).
Comparison (verdict recorded 2026-10-20T11:23:08Z):
# Decision: spec:Dissertation.PaperSpec.A.ex_fulllaw_affineQ (Dissertation/PaperSpec/A/Sec5.lean)

Verdict: broader.

Comparison with the locked reading.
- Setting: every σ-finite ν on a countably generated space, every n, m, d, J.
- Data: Q : R^J -> ℝ arbitrary (no regularity needed); features φ_j Lipschitz with constants K_j
  (boundedness not assumed: broader; Lipschitz continuity makes them Borel and integrable against
  the P_2 law μ^U); a ∈ ℝ, c ∈ ℝ^J.
- Hypothesis "Q affine on the attained range": for every μ ∈ P_2(H),
  Q((∫ φ_j dμ^U)_j) = a + Σ_j c_j ∫ φ_j dμ^U -- i.e. Q(s) = a + Σ_j c_j s_j at every attained s,
  the printed "if Q(s) = a + Σ_j c_j s_j there".
- Conclusion: for every μ ∈ P_2(H),
  Q((∫ φ_j dμ^U)_j) = ∫_H (a + Σ_j c_j φ_j(θ'.2.2.2)) μ(dθ'), with θ'.2.2.2 = u' the U-channel:
  the printed identity, an integral over H against μ of the explicit kernel.
- "An expectation functional already covered by Example 5.3": the proposition gives the kernel
  θ' |-> a + Σ_j c_j φ_j(u') explicitly; its membership in the Example 5.3 class (measurable,
  Lipschitz in θ', uniformly in t, with no dependence on (t, θ)) is not a separate conjunct. It is
  immediate from the hypothesis on the features: |Σ_j c_j (φ_j(u') - φ_j(u''))| <=
  (Σ_j |c_j| K_j) ||u' - u''|| <= (Σ_j |c_j| K_j) |θ' - θ''|_H, and Lipschitz maps are Borel. I
  count this as a harmless omission of a one-line consequence of a displayed hypothesis, not a
  lost claim.
Broader than printed: unbounded features allowed, Q unrestricted. The printed claim is the
instance in the detail file.

Current text. Read at 1f67672 (Example 5.4: "if Q(s) = a + Σ_j c_j s_j there, the Q-term equals
∫_H (a + Σ_j c_j φ_j(u')) μ(dθ'), an expectation functional already covered by Example 5.3"). I
have not seen the earlier text, so I cannot say what changed; the proposition matches the current
sentence ("there" = the attained range of the feature vector).

Witness. `Dissertation.Acceptance.A.ex_fulllaw_affineQ_hypotheses` (Dissertation/Acceptance/A/
Witness.lean): ν = δ_0, J = 1, φ₁(u) = min(||u||, 1) (1-Lipschitz), Q(s) = s₁, a = 0, c = 1: Q is
affine on all of R^1, so in particular on the attained range. An intended instance (affine Q,
nonzero feature), though it uses an everywhere-affine Q rather than one affine only on the
attained range; that is enough to show the hypotheses can be met.

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
Verdict: broader — Broader than the printed claim: the features need only be Lipschitz (not bounded) and Q is
unrestricted. The printed claim is the instance with the paper's bounded Lipschitz features φ_j and
Q affine on the attained range, Q(s) = a + Σ_j c_j s_j for every s = (∫ φ_j dμ^U)_j, μ ∈ P_2(H):
the conclusion is the printed identity Q((∫ φ_j dμ^U)_j) = ∫_H (a + Σ_j c_j φ_j(u')) μ(dθ'). The
"covered by Example 5.3" part -- the kernel θ' |-> a + Σ_j c_j φ_j(u') is measurable and Lipschitz
on H, with constant Σ_j |c_j| Lip(φ_j) -- is not a separate conjunct; it follows in one line from
the displayed Lipschitz hypothesis on the features.
Disagreements with the author's review (shown 2026-10-20T11:23:29Z): none (on the verdict). A note: the "already covered by Example 5.3" part of the clause -- that the
kernel θ' |-> a + Σ_j c_j φ_j(u') is measurable and Lipschitz on H -- is not a separate conjunct of
the proposition; it follows in one line from the displayed Lipschitz hypothesis on the features
(constant Σ_j |c_j| K_j), so I counted it as harmless.
