### A:ex:fulllaw, A:rem:regimes, A:sec5:overview: Dissertation.PaperSpec.A.ex_fulllaw_beyond_radial
Pins: manuscript A None; project d3e594defeeeb94a6d05c33c666bcb870d584302; hash ed839d34f480cba1fc87ff54d30df5ad (pl-fp-v1:bd2ddc0359d2a5b2d4c03423f40aa608755e4946bbbc872ba727421245fc5f80)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-20T11:24:09Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-20T11:09:25Z):
# Reading: ex_fulllaw_beyond_radial — Example 5.4: "the radial statistic of the full tuple law is
# no expectation functional"; "a nonlinear law dependence, no expectation functional"; Section 5
# overview: "a nonlinear functional of the full tuple"

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

Claim (printed: "For nonconstant q, qtilde, qhat, the radial statistics lie beyond the
expectation and two-point-kernel jump-integrand interactions of the preceding examples, and beyond
the linear jump-integrand expectations of the cited models"; Section 5 overview: Example 5.4
carries the law dependence "to genuinely nonlinear functionals of the full tuple"). For this
unit, the full-tuple radial statistic:
 For every mu_0 in P_2(H) and every q : R_+ -> R bounded, Lipschitz and NONCONSTANT, the map
 mu |-> q(W_2(mu, mu_0)) on P_2(H) is not an expectation functional: there is no kernel
 phibar : H -> R (in the Example 5.3 class: measurable, Lipschitz; a statement excluding every
 measurable mu-integrable phibar is stronger and acceptable) with q(W_2(mu, mu_0)) =
 int_H phibar dmu for all mu in P_2(H). ("Nonlinear law dependence" = not affine in mu; a
 statement "not affine under mixtures" implies "no expectation functional" and is acceptable
 as stronger, if it is the paper's sense of nonlinear.)
Quantifiers: for ALL mu_0 in P_2(H) (the example fixes an arbitrary one), all nonconstant
bounded Lipschitz q. Narrower would be: a specific mu_0 (e.g. a Dirac mass), a specific q, an
existential over q or mu_0, or a class of excluded kernels smaller than the Example 5.3 class
(e.g. only kernels depending on finitely many coordinates, or only affine kernels). Hypotheses
needed for truth: H != {0} holds (n >= 1). Note q is vector-scaled in f (eps q(.) w_0) -- the
statistic itself is the object of the claim. The exclusion of "two-point-kernel" and "linear
jump-integrand expectations of the cited models" is subsumed: these are all of the form
int K(theta, theta') mu(dtheta') at fixed (t, theta), i.e. expectation functionals of mu.
Comparison (verdict recorded 2026-10-20T11:23:08Z):
# Decision: spec:Dissertation.PaperSpec.A.ex_fulllaw_beyond_radial (Dissertation/PaperSpec/A/Sec5.lean)

Verdict: broader.

Comparison with the locked reading.
- Setting: every σ-finite ν on a countably generated space, n >= 1 (the standing n >= 1, which
  makes H ≠ {0}), every m, d; H = TupleH, W_2 the Hilbert-norm `w2H`.
- Profile: q : ℝ → ℝ, Lipschitz (some Lq), bounded (some B), and not constant on [0, ∞)
  (∃ a, b >= 0 with q a ≠ q b). The paper's q : R_+ -> R bounded Lipschitz nonconstant; its
  extension r |-> q(max r 0) satisfies all three, and the statistic only evaluates q on [0, ∞).
- Reference law: every μ₀ ∈ P_2(H) (the example fixes an arbitrary one), as required.
- Conclusion: for every φ : H -> ℝ integrable against every law of P_2(H), some μ ∈ P_2(H) has
  q(W_2(μ, μ₀)) ≠ ∫ φ dμ: the radial statistic is not an expectation functional μ |-> ∫ φ dμ.
- The excluded class. The paper's "expectation and two-point-kernel jump-integrand interactions of
  the preceding examples" are, at each fixed (t, θ), maps μ |-> ∫ K(θ') μ(dθ') with K measurable
  and Lipschitz (Example 5.3, its Nemytskii form, the marginal means of Example 5.1(ii)); every
  such K is integrable against every P_2 law. The proposition excludes all φ integrable against
  every P_2 law, a larger class, so its conclusion is stronger than the printed one and implies
  it (the radial term does not depend on θ, so a representation at one (t, θ) would already give
  such a φ). Non-integrable φ define no expectation functional (the Bochner integral would be a
  junk 0), so nothing meaningful is lost by requiring integrability.
- "Nonlinear law dependence" (Remark 5.7) and "a nonlinear functional of the full tuple" (§5
  overview) are, in the paper, this contrast with the expectation functionals; the proposition
  states that contrast.
Broader than printed: a stronger conclusion (a larger excluded class) and profiles given on ℝ.
The printed claim is the instance in the detail file.

Current text. Read at 1f67672 (Example 5.4: "For nonconstant q, qtilde, qhat, the radial statistics
lie beyond the expectation and two-point-kernel jump-integrand interactions of the preceding
examples, and beyond the linear jump-integrand expectations of the cited models"; Remark 5.7; §5
overview "to genuinely nonlinear functionals of the full tuple"). I have not seen the earlier
text, so I cannot say what changed; the proposition matches the current text, with the
boundedness and Lipschitz hypotheses the current data list imposes ("with q, qtilde, qhat, Q and
the features φ_j bounded and Lipschitz") -- boundedness matters, since q(r) = r^2 (unbounded,
not Lipschitz) with μ₀ = δ₀ gives the expectation functional ∫|θ|^2 dμ.

Witness. `Dissertation.Acceptance.A.ex_fulllaw_beyond_hypotheses` (Dissertation/Acceptance/A/
Witness.lean): at ν = δ_0, n = m = d = 1, q = min(|r|, 1) is bounded, 1-Lipschitz and not constant
on [0, ∞) (q 0 ≠ q 1), and the kernel 0 is integrable against every P_2 law (so the universally
quantified φ ranges over a nonempty set). μ₀ is arbitrary in the statement (e.g. a Dirac mass).
An instance the paper intends (a nonconstant bounded Lipschitz profile).

Coverage (claims A:ex:fulllaw, A:rem:regimes, A:sec5:overview). For A:rem:regimes and
A:sec5:overview, the Example 5.4 assertions ("arbitrary nonlinear full-tuple law dependence can be
added below the margin"; "genuinely nonlinear functionals of the full tuple and of the jump
integrand") are stated by this clause with pert, wp (rem:regimes) and beyond_U_corr (overview, the
jump-integrand part); the other clauses of those claims concern Examples 5.1-5.3 and 5.5.

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
Verdict: broader — Broader than the printed claim: it excludes every φ : H -> ℝ integrable against every law of
P_2(H), a class containing the Example 5.3 kernels (measurable Lipschitz, hence integrable against
every P_2 law) and the two-point-kernel and marginal-mean interactions; and the profile is given on
ℝ. The printed claim is the instance: n >= 1, the paper's μ₀ ∈ P_2(H) and bounded Lipschitz
nonconstant q : R_+ -> R extended to ℝ by r |-> q(max r 0) (still bounded, Lipschitz and not
constant on [0, ∞)), and φ any Example 5.3 kernel at fixed (t, θ): then
q(W_2(μ, μ₀)) ≠ ∫ φ dμ for some μ, i.e. the radial statistic is no expectation functional.
Disagreements with the author's review (shown 2026-10-20T11:23:29Z): none
