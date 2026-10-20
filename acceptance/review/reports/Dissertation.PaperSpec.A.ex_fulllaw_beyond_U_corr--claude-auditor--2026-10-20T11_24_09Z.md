### A:ex:fulllaw, A:sec5:overview: Dissertation.PaperSpec.A.ex_fulllaw_beyond_U_corr
Pins: manuscript A None; project d3e594defeeeb94a6d05c33c666bcb870d584302; hash ed839d34f480cba193f328d7c8c243ea (pl-fp-v1:22af2162ff7a9dc3738d459ea4684b8119c137c19dfd0e9d5933ec4b647475a6)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-20T11:24:09Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-20T11:09:25Z):
# Reading: ex_fulllaw_beyond_U_corr — Example 5.4 / Section 5 overview: "the U-marginal radial
# statistics are no expectation functionals, with L^2(nu) != 0"

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

Claim: with nu != 0 (in force in Example 5.4 by the Section 5 preamble; equivalently, nu
sigma-finite, L^2(nu; R^m) != {0}), for every Lambda_0 in P_2(L^2(nu)) and every nonconstant
bounded Lipschitz qtilde : R_+ -> R (and likewise qhat), the map mu |-> qtilde(W_2(mu^U, Lambda_0))
on P_2(H) is not an expectation functional (no phibar in the Example 5.3 class, measurable
Lipschitz H -> R, a fortiori if all measurable integrable kernels are excluded, with
qtilde(W_2(mu^U, Lambda_0)) = int phibar dmu for all mu in P_2(H)).
The hypothesis L^2(nu) != 0 is NOT an extra restriction relative to the current text: the
Section 5 preamble says "In Examples 5.4 and 5.5, we take nu != 0", and for nu = 0 the claim is
false (P_2(L^2(nu)) = {delta_0}, the statistic is the constant qtilde(0)). Both qtilde and qhat
are covered by one statement about a generic nonconstant function. Quantifiers: for all
Lambda_0, for all such qtilde; mu ranges over all of P_2(H). Narrower would be: specific
Lambda_0 / qtilde, a smaller class of excluded kernels, or an added hypothesis beyond nu != 0.
Vector-valued versions (qhat(.) hhat in the jump coefficient) reduce to the scalar statistic.
Comparison (verdict recorded 2026-10-20T11:23:08Z):
# Decision: spec:Dissertation.PaperSpec.A.ex_fulllaw_beyond_U_corr (Dissertation/PaperSpec/A/Sec5.lean)

Verdict: broader.

Comparison with the locked reading.
- Setting: every σ-finite ν on a countably generated space and n, m, d, with the hypothesis
  `∃ u : Lp (EuclideanSpace ℝ (Fin m)) 2 ν, u ≠ 0`, i.e. L^2(ν; R^m) ≠ {0}. For the standing
  m >= 1 and σ-finite ν this is equivalent to ν ≠ 0, which the current text puts in force for
  Example 5.4 (§5 preamble: "In Examples 5.4 and 5.5, we take ν ≠ 0"). It is needed: for ν = 0,
  P_2(L^2(ν)) = {δ₀} and the statistic is the constant qtilde(0), an expectation functional.
- Profile q : ℝ → ℝ bounded, Lipschitz, not constant on [0, ∞) -- the paper's qtilde (and,
  by the same statement, qhat), extended from R_+ as in beyond_radial.
- Reference law: every Λ₀ ∈ P_2(L^2(ν; R^m)).
- Conclusion: for every φ : H -> ℝ integrable against every law of P_2(H), some μ ∈ P_2(H) has
  q(W_2(μ^U, Λ₀)) ≠ ∫ φ dμ, with μ^U = `μ.margU` and W_2 = `w2P` on P_2(L^2(ν; R^m)).
- Excluded class: as in beyond_radial, larger than the Example 5.3 class (stronger conclusion).
- The vector-valued occurrences (ε qtilde(·) v₀ in b, ε qhat(·) hhat in h) reduce to the scalar
  statistic, which is what the passage calls "the radial statistics".
Broader than printed only by the larger excluded class and the profile on ℝ; the hypothesis
L^2(ν) ≠ 0 is the passage's own ν ≠ 0, not an added restriction.

Current text. Read at 1f67672 (Example 5.4 as quoted for beyond_radial, for qtilde and qhat; §5
preamble "In Examples 5.4 and 5.5, we take ν ≠ 0"; §5 overview "and of the jump integrand"). I have
not seen the earlier text. If the earlier text did not put ν ≠ 0 in force for Example 5.4, the
printed claim was false at ν = 0, and this is why the clause carries L^2(ν) ≠ 0 (its name ends in
_corr); at the current text, which takes ν ≠ 0, the hypothesis is the paper's and the proposition
says what the passage says.

Witness. `Dissertation.Acceptance.A.ex_fulllaw_beyond_hypotheses`: at ν = δ_0, L^2(ν; R^1)
contains the nonzero constant e₁; q = min(|r|, 1) bounded, 1-Lipschitz, not constant on [0, ∞);
the kernel 0 is integrable against every P_2 law. An intended instance with ν and the U-fibre
nonzero.

Coverage (claims A:ex:fulllaw and A:sec5:overview): this clause states the U-marginal
("jump integrand") half of the overview's "genuinely nonlinear functionals of the full tuple and
of the jump integrand" and the qtilde/qhat half of Example 5.4's radial assertion.

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
Verdict: broader — Broader than the printed claim: it excludes every φ : H -> ℝ integrable against every P_2 law
(containing the Example 5.3 kernels), and the profile is given on ℝ. The printed claim is the
instance: the standing m >= 1 and ν ≠ 0 (in force for Example 5.4 by the §5 preamble), which give
some u ≠ 0 in L^2(ν; R^m) (an indicator of a set of finite positive ν-measure times e₁); the
paper's Λ₀ ∈ P_2(L^2(ν)); q = qtilde (or qhat) : R_+ -> R bounded Lipschitz nonconstant, extended
by r |-> q(max r 0); and φ any Example 5.3 kernel at fixed (t, θ). The hypothesis L^2(ν) ≠ 0 is
the paper's ν ≠ 0, not an addition.
Disagreements with the author's review (shown 2026-10-20T11:23:29Z): none
