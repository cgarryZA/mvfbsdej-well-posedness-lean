### A:ex:fulllaw: Dissertation.PaperSpec.A.ex_fulllaw_lip
Pins: manuscript A None; project d3e594defeeeb94a6d05c33c666bcb870d584302; hash ed839d34f480cba11fea7903ed24f9f8 (pl-fp-v1:f433d41570cd71df2b9a2bfa8964bef9e00b0be9d22b3e2c192d36bfa0be4008)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-20T11:24:09Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-20T11:09:24Z):
# Reading: ex_fulllaw_lip — Example 5.4, "the law statistics are W_2-Lipschitz, with the
# constants Lip(q), Lip(qtilde), Lip(qhat), L_Q"

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

Claim: for all mu, mu' in P_2(H),
 (a) |q(W_2(mu,mu_0)) - q(W_2(mu',mu_0))| <= Lip(q) W_2(mu,mu')   [triangle inequality for W_2];
 (b) |qtilde(W_2(mu^U,Lambda_0)) - qtilde(W_2(mu'^U,Lambda_0))| <= Lip(qtilde) W_2(mu,mu'), and
     the same with qhat and Lip(qhat)   [via (2.11)];
 (c) |F_Q(mu) - F_Q(mu')| <= L_Q W_2(mu,mu'), L_Q = Lip(Q)(sum_j Lip(phi_j)^2)^{1/2}, Lip(Q)
     for the EUCLIDEAN norm on R^J   [via (2.10) per feature, then l2-combination].
Hypotheses: mu_0 in P_2(H), Lambda_0 in P_2(L^2(nu)); q, qtilde, qhat Lipschitz on R_+; Q
Lipschitz on R^J (Euclidean); phi_j Lipschitz (bounded, measurable) on L^2(nu). Boundedness and
epsilon are irrelevant to this clause (dropping them is a harmless broadening). nu != 0 is not
needed for this clause.
Faithfulness points: the constants exactly as printed (any valid Lipschitz constant in place of
the best one is equivalent); R^J with the Euclidean norm (a sup norm on R^J changes Lip(Q) and
makes the bound with the printed L_Q formula a different statement); q defined on R_+
(a Lean q : R -> R Lipschitz on R is a harmless representation, as any Lipschitz function on
R_+ extends with the same constant); W_2 genuine (no junk) on P_2(H) and P_2(L^2(nu)); the
marginal is the U-projection; integrals of the features against mu^U genuine (bounded measurable
features).
Comparison (verdict recorded 2026-10-20T11:23:08Z):
# Decision: spec:Dissertation.PaperSpec.A.ex_fulllaw_lip (Dissertation/PaperSpec/A/Sec5.lean)

Verdict: broader.

Numbering note on my locked reading: "Corollary 3.4" there denotes the robustness corollary
cor:robust, numbered Corollary 3.6 in the paper (shared theorem counter).

Comparison with the locked reading.
- Setting: every σ-finite ν on a countably generated space, every n, m, d, J; H = TupleH with
  W_2 on P_2(H) the Hilbert-norm `w2H`; the U-fibre L^2(ν; R^m) with `w2P` of its norm; μ^U is
  `μ.margU`.
- Profiles q, qb (= qtilde), qh (= qhat) : ℝ → ℝ with Lipschitz constants Lq, Lqb, Lqh >= 0 on all
  of ℝ. The paper's profiles are R_+ -> R; every Lipschitz function on R_+ extends to ℝ with the
  same constant (e.g. r |-> q(max r 0)), and the statistics evaluate only at W_2-values >= 0, so
  this is a representation. Boundedness is not assumed: dropped, not needed for this clause.
- Q : EuclideanSpace ℝ (Fin J) -> ℝ with |Q v - Q v'| <= LQ ‖v - v'‖, the Euclidean norm on R^J,
  as the paper's Lip(Q) (Section 1: Euclidean norm on every R^j); boundedness dropped.
- Features φ_j : L^2(ν; R^m) -> ℝ with Lipschitz constants K_j; boundedness dropped. They are
  continuous, hence Borel, and integrable against the P_2 law μ^U, so the integrals
  ∫ φ_j dμ^U are genuine.
- Reference laws μ₀ ∈ P_2(H), Λ₀ ∈ P_2(L^2(ν; R^m)), arbitrary.
- Conclusions, for all μ, μ' ∈ P_2(H):
  |q(W_2(μ, μ₀)) - q(W_2(μ', μ₀))| <= Lq W_2(μ, μ');
  |qtilde(W_2(μ^U, Λ₀)) - qtilde(W_2(μ'^U, Λ₀))| <= Lqb W_2(μ, μ'); same with qhat and Lqh;
  |Q((∫ φ_j dμ^U)_j) - Q((∫ φ_j dμ'^U)_j)| <= LQ (Σ_j K_j^2)^{1/2} W_2(μ, μ'),
  i.e. the constants Lip(q), Lip(qtilde), Lip(qhat) and L_Q = Lip(Q)(Σ_j Lip(φ_j)^2)^{1/2} as
  printed (any valid Lipschitz constants, equivalently the best ones).
Broader than the printed claim: boundedness of the profiles, Q and the features, m = n and ν ≠ 0
are not assumed, and the profiles are given on ℝ (an extension of the paper's R_+-profiles).
The printed claim is the instance in the detail file.

Current text. Read at 1f67672 (Example 5.4: "All three are W_2-Lipschitz in μ. The radial
statistic has constant Lip(q), by the triangle inequality for W_2. The U-marginal statistics have
constants Lip(qtilde) and Lip(qhat), since marginal projection is 1-Lipschitz for W_2 by (2.11).
Each cylindrical feature is the Bochner mean of the kernel θ' |-> φ_j(u'), so (2.10) applies and
the Q-term has constant L_Q := Lip(Q)(Σ_j Lip(φ_j)^2)^{1/2}"). I have not seen the earlier text,
so I cannot say what changed; the proposition states these constants exactly as the current
passage prints them, L_Q with the l^2 combination and the Euclidean Lip(Q).

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
Verdict: broader — Broader than the printed claim: the profiles q, qtilde, qhat, the outer function Q and the
features φ_j need not be bounded, and n, m, d, ν are unrestricted (no m = n, no ν ≠ 0). The
printed claim is the instance: given the paper's bounded Lipschitz q, qtilde, qhat : R_+ -> R,
take their extensions r |-> q(max r 0) etc. to ℝ (same Lipschitz constants), Lq = Lip(q),
Lqb = Lip(qtilde), Lqh = Lip(qhat), LQ = Lip(Q) for the Euclidean norm of R^J, K_j = Lip(φ_j), and
the paper's μ₀ ∈ P_2(H), Λ₀ ∈ P_2(L^2(ν)); the four conclusions are then the printed Lipschitz
bounds with constants Lip(q), Lip(qtilde), Lip(qhat) and L_Q = Lip(Q)(Σ_j Lip(φ_j)^2)^{1/2}, the
statistics evaluating the extended profiles only at W_2-values >= 0, where they agree with the
paper's.
Disagreements with the author's review (shown 2026-10-20T11:23:29Z): none (on the verdict). One note on the witness for this claim's clauses, which I could not check
against the earlier review's text: ex_fulllaw_hypotheses takes hhat = 0, so the perturbation of the
jump coefficient, which Example 5.4 singles out ("the latter entering the jump coefficient
itself"), is zero there; the hypotheses are met and the other objects are nonzero, and a choice
such as ε = 1/8 with hhat = e₁ (L_p = 1/2 < c_diss = 1) would exhibit the intended instance with all
four directions nonzero.
