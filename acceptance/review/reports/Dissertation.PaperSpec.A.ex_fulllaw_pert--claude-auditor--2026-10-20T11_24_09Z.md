### A:ex:fulllaw, A:rem:regimes: Dissertation.PaperSpec.A.ex_fulllaw_pert
Pins: manuscript A None; project d3e594defeeeb94a6d05c33c666bcb870d584302; hash ed839d34f480cba1e9dade95deb0a071 (pl-fp-v1:0c1f0ffc43ee1ab122f03515095b53fec6c6e995b39e950ff671058469ff8b2f)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-20T11:24:09Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-20T11:09:24Z):
# Reading: ex_fulllaw_pert — Example 5.4: "the perturbation: origin integrability, (3.5) with
# L_p, Assumption 2.3, and (3.4) with c_pert = ||G|| L_p"; Remark 5.7: "the full-tuple law
# perturbation satisfies (3.4) with c_pert = ||G|| L_p"

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

Claim (the perturbation part of Example 5.4), under the data above (m = n per Corollary 3.4; G
full rank; nu sigma-finite, nu != 0 in force but not needed for these clauses):
 (i) origin integrability (the perturbation part of Assumption 2.2): p_b(., 0, delta_0) in
     L^2(0,T; R^n), p_sigma = 0, p_h(., 0, ., delta_0) in L^2(0,T; L^2(nu; R^n)),
     p_f(., 0, delta_0) in L^2(0,T; R^m) (constants in t on a finite horizon);
 (ii) (3.5) with constant L_p: for a.e. t and all diagonal pairs (Theta,mu),(Theta',mu') in D_t,
     |dp_b| + |dp_sigma|_F + ||dp_h|| + |dp_f| <= L_p W_2(mu, mu') (in fact for all mu, mu');
     the perturbations are independent of theta;
 (iii) the diagonal Lipschitz condition of Assumption 2.3 for the perturbations (with constant
     L_p, nothing on g since g is unchanged);
 (iv) (3.4) with c_pert = ||G|| L_p: for a.e. t and all diagonal pairs,
     E[<dp_b, G^T dY> + <dp_sigma, G^T dZ>_F + <-dp_f, G dX> + int_E <dp_h(e), G^T dU(e)> nu(de)]
       <= ||G|| L_p E[|dX|^2 + |dY|^2 + |dZ|_F^2 + ||dU||^2].
||G|| = operator norm (spectral) of G; |.| Euclidean on R^n, R^m; L_p and L_Q exactly as printed.
Diagonal pairs are F_t-measurable square-integrable tuples with their own laws on the standing
space. Measurability of the perturbation coefficients (the standing joint Borel measurability,
including (2.3) for p_h) is part of "the perturbations are admissible coefficients"; a statement
omitting it is acceptable only if it does not rely on it.
Faithfulness points: all four clauses present; constants exactly as printed (or valid
Lipschitz constants equivalently); the pairing is the genuine expectation along diagonal inputs;
not a free-real abstraction.
Comparison (verdict recorded 2026-10-20T11:23:08Z):
# Decision: spec:Dissertation.PaperSpec.A.ex_fulllaw_pert (Dissertation/PaperSpec/A/Sec5.lean)

Verdict: broader.

Numbering note on my locked reading: "Corollary 3.4" there denotes cor:robust (Corollary 3.6).

Comparison with the locked reading.
- Setting: the standing basis (Lévy driver, independent 𝒢₀, filtration `enlJoint`), ν σ-finite on
  a countably generated space, n >= 1, m = n (the perturbation lives in `Coeffs ν n n d`), d >= 1,
  T > 0. G ∈ R^{n x n} arbitrary (no full-rank hypothesis -- not needed here).
- Data: ε > 0; q, qb, qh : ℝ → ℝ Lipschitz (Lq, Lqb, Lqh >= 0); Q Lipschitz for the Euclidean norm
  of R^J (LQ >= 0); features φ_j Lipschitz (K_j); μ₀ ∈ P_2(H), Λ₀ ∈ P_2(L^2(ν; R^n));
  w₀, w₁, v₀ ∈ R^n; hhat ∈ L^2(ν; R^n). Boundedness of the profiles, Q and the features is not
  assumed (only broadens); profiles on ℝ represent the paper's R_+-profiles (Lipschitz extension).
- The perturbation `ex54Pert` (same file): p_b = ε qtilde(W_2(μ^U, Λ₀)) v₀, p_σ = 0,
  p_h = ε qhat(W_2(μ^U, Λ₀)) hhat, p_f = ε q(W_2(μ, μ₀)) w₀ + ε Q((∫ φ_j dμ^U)_j) w₁, independent
  of t and θ, with W_2 the Hilbert-norm `w2H` on P_2(H) and `w2P` on P_2(L^2(ν)): exactly the
  printed perturbation (f = f₀ + p_f, b = b₀ + p_b, h = h₀ + p_h via `Coeffs.perturb`).
- Conclusions:
  (i) `TupleIndep`: the perturbations are independent of θ, as printed;
  (ii) `OriginValues T`: p_b(·, 0, δ₀), p_σ, p_h(·, 0, ·, δ₀), p_f(·, 0, δ₀) in L^2(0, T), the
       origin-integrability part of Assumption 2.2, as printed;
  (iii) `LawLip35 … L_p` with L_p = ε(|w₀| Lq + |v₀| Lqb + |w₁| LQ (Σ K_j^2)^{1/2} + ||hhat|| Lqh):
       (3.5) for a.e. t and all pairs of diagonal inputs, almost surely,
       |δp_b| + |δp_σ|_F + ||δp_h|| + |δp_f| <= L_p W_2(μ, μ'), with the printed L_p;
  (iv) `LipInterior … L_p`: the interior bound of Assumption 2.3 for the perturbation with the
       same constant ("hence the diagonal Lipschitz condition of Assumption 2.3 as well");
  (v) `PairingBound34 … G (‖GX G‖ L_p)`: (3.4) for a.e. t and all pairs of diagonal inputs, pairing
       integrable, E[⟨δp_b, Gᵀ δY⟩ + ⟨δp_σ, Gᵀ δZ⟩_F + ⟨-δp_f, G δX⟩ + ∫⟨δp_h, Gᵀ δU⟩ dν]
       <= ||G|| L_p E[|δX|^2 + |δY|^2 + |δZ|_F^2 + ||δU||^2], with ||G|| = ‖GX G‖ the operator
       (spectral) norm of x |-> G x on Euclidean R^n.
All four printed clauses are present with the printed constants. Broader than printed in dropping
boundedness and the full rank of G (and ν ≠ 0, irrelevant here); the printed claim is the instance
in the detail file. Measurability of the perturbation is not asserted here; the passage does not
assert it in this clause either (it is asserted, for the perturbed system, in the wp clause).

Current text. Read at 1f67672 (Example 5.4: "The perturbations are bounded multiples of the fixed
vectors ... so they satisfy the origin-integrability condition of Assumption 2.2. They are
independent of θ and satisfy the W_2-Lipschitz bound (3.5) with constant L_p := ε(...), hence the
diagonal Lipschitz condition of Assumption 2.3 as well. By (3.5) and Corollary 3.6, (3.4) holds
with c_pert = ||G|| L_p"; Remark 5.7 for the second clause). I have not seen the earlier text, so I
cannot say what changed; the proposition says what the current passage says.

Remark 5.7 clause ("Example 5.4: the full-tuple law perturbation satisfies (3.4) with
c_pert = ||G|| L_p"): conclusion (v). Coverage of claim A:rem:regimes: its Example 5.4 part
("arbitrary nonlinear full-tuple law dependence can be added when it is smaller than the
dissipativity margin") is stated by pert, wp and beyond_radial together; its Example 5.5 part is
covered by the dealer clauses (not in this chunk).

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
Verdict: broader — Broader than the printed claim: G need not have full rank, and the profiles q, qtilde, qhat, Q
and the features φ_j need not be bounded (ν ≠ 0 is not assumed either). The printed clause is the
instance with the standing basis, m = n >= 1, d >= 1, T > 0, the paper's full-rank G, ε > 0, the
paper's bounded Lipschitz data with the profiles extended from R_+ to ℝ by r |-> q(max r 0)
(same constants), Lq = Lip(q), Lqb = Lip(qtilde), Lqh = Lip(qhat), LQ = Lip(Q) (Euclidean),
K_j = Lip(φ_j): then L_p is the printed ε(|w₀| Lip(q) + |v₀| Lip(qtilde) + |w₁| L_Q
+ ||hhat|| Lip(qhat)), and the five conclusions are θ-independence, origin integrability, (3.5)
with L_p, the interior bound of Assumption 2.3 with L_p, and (3.4) with c_pert = ||G|| L_p.
Disagreements with the author's review (shown 2026-10-20T11:23:29Z): none (on the verdict). Same witness note as for ex_fulllaw_lip: ex_fulllaw_hypotheses takes
hhat = 0, so the jump-coefficient perturbation is zero at the witness; e.g. ε = 1/8 and hhat = e₁
would keep (5.1) (L_p = 1/2 < 1) with every direction nonzero.
