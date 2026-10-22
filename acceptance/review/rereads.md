# Readings of widened passages

The pinned passages of the claims below were widened to cover the hypotheses, definitions,
notation or conclusion printed around them. Each proposition or definition had been reviewed
independently at the narrower passage; the reviewer `claude-auditor` (a model of the same
family as the author) then read the added lines with the earlier report and the Lean
declaration, not blind, and recorded whether they change the reading. Each entry below
records a reading that stands at the widened passage; its marker carries that passage's
digest.

## `A:abstract` (paper/wellposedness.tex, lines 30–48)

* `MVFBSDEJ.PaperSpec.ex_dealer_active` (added: lines 31–48). Lines 46-47 ('in an explicit
  specialisation, active along the solution') are conjunct (b) of ex_dealer_active. At the
  specialisation of Example 5.5 (beta1 = 1, beta2 = 1/2, sigma_c = 1, xi0 = 0, c = (2 - rho)/2, h_c
  = side*q, h_x = q), for every eps > 0 every solution has E int_0^T ||eps A_{Law U_t}(U_t)||^2 dt >
  0. Conjunct (a) is the non-Dirac law of U at eps = 0. The other added lines do not bear on this
  clause. The earlier verdict, faithful, stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.ex_dealer_active ed839d34f480cba1a2ecf4542b86cf40 by=claude-auditor source=A:abstract@4698dc07f7b17ef066bf70072b872f20edb0da7f972ce4c1a8edc13f34c35ab3 -->

* `MVFBSDEJ.PaperSpec.ex_dealer_marks` (added: lines 31–48). Line 48, 'its mark measure has
  infinite activity', is the conjunct nu(E) = infinity of ex_dealer_marks. There E = {-1,+1} x (0,1]
  and nu = c_side q^(-1-rho) dq, for all c_{-1}, c_{+1} > 0 and 0 < rho < 2. The other conjuncts are
  the finiteness of the integral of q^2 and h_c in L2(nu), printed in Example 5.5. The other added
  lines describe the setting, the main theorems and the dealer interaction, none of which bears on
  this clause. The earlier verdict, faithful with representation choices, stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.ex_dealer_marks ed839d34f480cba140a65f520ffefa33 by=claude-auditor source=A:abstract@4698dc07f7b17ef066bf70072b872f20edb0da7f972ce4c1a8edc13f34c35ab3 -->

* `MVFBSDEJ.PaperSpec.ex_dealer_mono` (added: lines 31–48). Lines 45-47: 'A mean-field
  dealer-market example realises the U-law dependence non-perturbatively: its interaction between
  valuation curves is monotone at every interaction strength'. This is ex_dealer_mono: crowding
  monotonicity along the diagonal, and Assumption 2.5 with G = 1, alpha = 1 and beta1, beta2 for
  every eps >= 0, with constants that do not depend on eps. 'Its mark measure has infinite activity'
  is the clause ex_dealer_marks. The earlier verdict, broader, stands: nu is any sigma-finite
  measure, nu = 0 included. The instance nu != 0, of which the infinite-activity dealer marks are
  one, gives the printed claim.
  <!-- spec-review: MVFBSDEJ.PaperSpec.ex_dealer_mono ed839d34f480cba18bebeea12a1b6e30 by=claude-auditor source=A:abstract@4698dc07f7b17ef066bf70072b872f20edb0da7f972ce4c1a8edc13f34c35ab3 -->

* `MVFBSDEJ.PaperSpec.ex_dealer_wp` (added: lines 31–48). Lines 45-47 say the dealer example
  realises the U-law dependence 'non-perturbatively', monotone 'at every interaction strength'. That
  is the content of ex_dealer_wp: for every eps >= 0 and every h_x, with no smallness condition, the
  dealer system has a solution in the strong space, and it is unique. The infinite-activity mark
  measure (line 48) is ex_dealer_marks. The earlier verdict, broader, stands: any sigma-finite nu,
  nu = 0 included, with the instance nu != 0.
  <!-- spec-review: MVFBSDEJ.PaperSpec.ex_dealer_wp ed839d34f480cba1169a2b8090bb4149 by=claude-auditor source=A:abstract@4698dc07f7b17ef066bf70072b872f20edb0da7f972ce4c1a8edc13f34c35ab3 -->

* `MVFBSDEJ.PaperSpec.prop_strict` (added: lines 31–48). The added lines 39-40 ('expected
  diagonal monotonicity is strictly weaker than pointwise monotonicity') are Proposition 3.8 as
  prop_strict states it. The drift (3.6) is free-measure W2-Lipschitz with constant beta1 + eps, and
  is expected-diagonal monotone with constant beta1 - eps along all square-integrable tuples with
  their laws. For every beta >= 0 there are free points and laws, the points in the supports, at
  which the pointwise bound fails. The other added lines describe the setting, the main theorems and
  the dealer example. The earlier verdict, faithful with representation choices, stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.prop_strict ed839d34f480cba1ac9d315442ee6c22 by=claude-auditor source=A:abstract@4698dc07f7b17ef066bf70072b872f20edb0da7f972ce4c1a8edc13f34c35ab3 -->

* `MVFBSDEJ.PaperSpec.rem_diag_mono` (added: lines 31–48). The added lines 38-40 read: 'Both
  the Lipschitz and monotonicity hypotheses are imposed only along diagonal tuple-law pairs; we show
  that expected diagonal monotonicity is strictly weaker than pointwise monotonicity.' The 'weaker'
  half is this clause: pointwise (2.7) at free points and laws, for a.e. t, gives the expected
  interior inequality along the diagonal. Strictness is carried by prop_strict and
  rem_diag_mono_converse. The remaining added lines (setting, the main theorems, the dealer example)
  do not bear on this clause. The earlier verdict, faithful with representation choices, stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.rem_diag_mono ed839d34f480cba16dbf12782c23a6c7 by=claude-auditor source=A:abstract@4698dc07f7b17ef066bf70072b872f20edb0da7f972ce4c1a8edc13f34c35ab3 -->

* `MVFBSDEJ.PaperSpec.rem_diag_mono_converse` (added: lines 31–48). The added lines 39-40
  assert strictness ('strictly weaker than pointwise monotonicity'). rem_diag_mono_converse states
  it: for every standing basis and every T > 0 there is a system satisfying (2.3), Assumption 2.3
  and the full Assumption 2.5 with G = 1, for which the pointwise inequality of (2.7) fails for
  every beta >= 0 and every beta'. The rest of the added text is setting, the main theorems and the
  dealer example, none of which bears on this clause. The earlier verdict, faithful, stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.rem_diag_mono_converse ed839d34f480cba194f9b4ec1a6ab33d by=claude-auditor source=A:abstract@4698dc07f7b17ef066bf70072b872f20edb0da7f972ce4c1a8edc13f34c35ab3 -->

* `MVFBSDEJ.PaperSpec.thm_cwp` (added: lines 31–48). For this clause the added lines say
  'existence on every prescribed finite horizon'. thm_cwp states this for every T > 0, under (2.3)
  and Assumptions 2.2-2.5, with existence and uniqueness in the strong space. The latest earlier
  report read the whole abstract, these lines included. It recorded that the setting descriptions
  (full-tuple W2 law dependence with the law of U, sigma-finite nu, diagonal expected
  G-monotonicity) are visible in the hypotheses, and that the continuation route describes the
  proof. The verdict, faithful with representation choices, stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.thm_cwp ed839d34f480cba12370b493940a6d61 by=claude-auditor source=A:abstract@4698dc07f7b17ef066bf70072b872f20edb0da7f972ce4c1a8edc13f34c35ab3 -->

* `MVFBSDEJ.PaperSpec.thm_stab` (added: lines 31–48). The added lines 31-48 complete the
  abstract. For this clause they say: 'under a jump-extended G-monotonicity condition we establish
  an a priori continuous-dependence estimate'. That is Theorem 3.1 as thm_stab states it: system 1
  under (2.3) and Assumptions 2.2-2.5, system 2 under (2.3) and Assumptions 2.2-2.3, and C_stab a
  function of (T, L, ||G||, c_G, alpha, beta1, beta2) chosen first. Lines 31-37 and 38-39 describe
  the setting and the hypotheses: W2-Lipschitz dependence of b, sigma, h, f on the law of the full
  tuple (U included), a terminal function of X_T and its law, a Brownian motion with an independent
  compensated Poisson random measure of sigma-finite intensity, and Lipschitz and monotonicity
  hypotheses imposed only along diagonal pairs. The proposition already carries all of this: Coeffs
  on H x P2(H) with the L2(nu) channel, g on R^n x P2(R^n), any sigma-finite nu, and
  Assumption23/Assumption25 along the diagonal. The scope note names these lines as exposition, and
  'by monotone continuation ...' as a description of the proof. The earlier verdict, faithful with
  representation choices, stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.thm_stab ed839d34f480cba14815ce65dd3b146f by=claude-auditor source=A:abstract@4698dc07f7b17ef066bf70072b872f20edb0da7f972ce4c1a8edc13f34c35ab3 -->

* `MVFBSDEJ.PaperSpec.thm_uniq` (added: lines 31–48). For this clause the added lines say
  'uniqueness' under the jump-extended G-monotonicity condition. That is Theorem 3.3 as thm_uniq
  states it: (2.3) and Assumptions 2.3-2.5 with no Assumption 2.2; two solutions in H_weak with the
  same initial datum coincide, and their difference lies in the strong space. Lines 31-37 and 38-39
  describe the setting and the hypotheses: W2-Lipschitz dependence of b, sigma, h, f on the law of
  the full tuple (U included), a terminal function of X_T and its law, a Brownian motion with an
  independent compensated Poisson random measure of sigma-finite intensity, and Lipschitz and
  monotonicity hypotheses imposed only along diagonal pairs. The proposition already carries all of
  this: Coeffs on H x P2(H) with the L2(nu) channel, g on R^n x P2(R^n), any sigma-finite nu, and
  Assumption23/Assumption25 along the diagonal. The scope note names these lines as exposition, and
  'by monotone continuation ...' as a description of the proof. The earlier verdict, faithful with
  representation choices, stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.thm_uniq ed839d34f480cba1c0edbd81a0b01a9e by=claude-auditor source=A:abstract@4698dc07f7b17ef066bf70072b872f20edb0da7f972ce4c1a8edc13f34c35ab3 -->

## `A:conclusion` (paper/sections/06-conclusion.tex, lines 3–16)

* `MVFBSDEJ.PaperSpec.cor_robust_wp` (added: lines 4–16). Lines 6–7 say that by Corollary 3.6
  the well-posedness is robust, at m = n, under full-tuple-law perturbations below the dissipativity
  margin. That is what the proposition states. It has m = n in its types, and the perturbation p is
  itself a coefficient record whose law argument lies in P₂(H), the full-tuple law. It assumes
  c_pert < c_diss and concludes existence, uniqueness in ℍ_weak and the stability estimate (3.1) for
  the perturbed system. The other added lines concern other clauses, the diagonal form of the
  hypotheses, exposition and open questions. The earlier verdict (faithful with representation
  choices) stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.cor_robust_wp ed839d34f480cba1617ff136058ce573 by=claude-auditor source=A:conclusion@730a6134cc7015b366900c995805b60c092012e31b44602037a39984c2a91da5 -->

* `MVFBSDEJ.PaperSpec.prop_strict` (added: lines 4–16). Lines 9–10, 'Proposition 3.8 shows
  that expected diagonal G-monotonicity is strictly weaker than its pointwise form', are the summary
  the earlier report already matched to this proposition. The proposition gives the drift (3.6) at n
  = m = 1, G = 1, which is free-measure W₂-Lipschitz, satisfies (3.7) along all diagonal inputs, and
  fails the pointwise bound for every β ≥ 0 at points in the supports. The full-system form is the
  separate clause rem_diag_mono_converse. The other added lines are other clauses or are named in
  the scope note. The verdict (faithful with representation choices) stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.prop_strict ed839d34f480cba1ac9d315442ee6c22 by=claude-auditor source=A:conclusion@730a6134cc7015b366900c995805b60c092012e31b44602037a39984c2a91da5 -->

* `MVFBSDEJ.PaperSpec.rem_beta1_dich` (added: lines 4–16). Lines 10–12 state that in the m < n
  regime with ν ≠ 0, Assumption 2.5 forces strictly U-dissipative jump feedback (Remark 2.10). That
  is what the proposition states, with ν ≠ 0: the reduced inequality 𝔼∫⟨δh, GᵀδU⟩dν ≤ −β₁𝔼‖GᵀδU‖²
  along 𝒟_t and, if m < n, β₁ > 0 with h not of the additive form. 'Still coercive' is exposition.
  Lines 12–16 name open questions, per the scope note. The inadmissibility of additive h when m < n,
  implied by their wording, is the third conjunct of this proposition. The earlier verdict
  (faithful) stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.rem_beta1_dich ed839d34f480cba15923d378afdb7162 by=claude-auditor source=A:conclusion@730a6134cc7015b366900c995805b60c092012e31b44602037a39984c2a91da5 -->

* `MVFBSDEJ.PaperSpec.rem_diag_mono` (added: lines 4–16). Lines 7–10 say that the hypotheses
  are imposed only along diagonal inputs, and that expected diagonal G-monotonicity is strictly
  weaker than its pointwise form (Proposition 3.8, Remark 2.8). The 'weaker' half, pointwise (2.7)
  giving (2.7) in expectation along 𝒟_t, is what this proposition states; the earlier report found
  the interior-only conclusion right. The strictness half is stated by prop_strict and
  rem_diag_mono_converse. The other added lines are other clauses or are named in the scope note.
  The earlier verdict (faithful with representation choices) stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.rem_diag_mono ed839d34f480cba16dbf12782c23a6c7 by=claude-auditor source=A:conclusion@730a6134cc7015b366900c995805b60c092012e31b44602037a39984c2a91da5 -->

* `MVFBSDEJ.PaperSpec.rem_diag_mono_converse` (added: lines 4–16). Lines 9–10 state that
  expected diagonal G-monotonicity is strictly weaker than its pointwise form (Proposition 3.8,
  Remark 2.8). On every standing basis and horizon, the proposition gives a coefficient system that
  satisfies (2.3), Assumption 2.3 and Assumption 2.5 at G = 1, while the pointwise inequality of
  (2.7) fails for every β ≥ 0 and every β′. That is the strictness, for a full system. The other
  added lines are other clauses or are named in the scope note. The earlier verdict (faithful)
  stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.rem_diag_mono_converse ed839d34f480cba194f9b4ec1a6ab33d by=claude-auditor source=A:conclusion@730a6134cc7015b366900c995805b60c092012e31b44602037a39984c2a91da5 -->

* `MVFBSDEJ.PaperSpec.thm_cwp` (added: lines 4–16). The added lines 4–5 complete the sentence
  on Theorems 3.1, 3.3 and 3.5. Global well-posedness for every horizon, for the system whose
  coefficients depend through W₂ on the law of the whole tuple (U included), at arbitrary σ-finite
  activity, is the setting of the proposition: every T > 0, law argument on P₂(H) with the L²(ν)
  channel, SigmaFinite ν only, hypotheses imposed along 𝒟_t only. The rest of the added lines are
  other clauses of the claim or are named in the scope note as a description of the hypotheses,
  exposition and open questions. The earlier verdict (faithful with representation choices) stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.thm_cwp ed839d34f480cba12370b493940a6d61 by=claude-auditor source=A:conclusion@730a6134cc7015b366900c995805b60c092012e31b44602037a39984c2a91da5 -->

* `MVFBSDEJ.PaperSpec.thm_stab` (added: lines 4–16). The added lines 4–5 complete the sentence
  on Theorems 3.1, 3.3 and 3.5: W₂-dependence on the law of the whole tuple, the L²(ν)-valued
  integrand included, at arbitrary σ-finite activity. The proposition already has this setting. Its
  coefficients take their law argument in P₂(H) with the L²(ν) channel, its Lipschitz hypothesis
  uses W₂ on P₂(H), ν is only σ-finite, and C_stab is chosen before ν, the dimensions and system 2.
  Lines 6–16 are either the other clauses of the claim (Corollary 3.6, Remark 2.8, Proposition 3.8,
  Remark 2.10) or, as the scope note says, a description of the hypotheses, exposition and open
  questions; none of them bears on (3.1). The earlier verdict (faithful with representation choices)
  stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.thm_stab ed839d34f480cba14815ce65dd3b146f by=claude-auditor source=A:conclusion@730a6134cc7015b366900c995805b60c092012e31b44602037a39984c2a91da5 -->

* `MVFBSDEJ.PaperSpec.thm_uniq` (added: lines 4–16). The added lines complete the summary
  sentence: global well-posedness for the full-tuple-law system at arbitrary σ-finite activity. The
  proposition already has that setting: law argument on P₂(H) with the L²(ν) channel, ν only
  σ-finite, every T > 0. The other added lines are other clauses of the claim, the diagonal-only
  form of the hypotheses (which Assumption23 and Assumption25 have), exposition and open questions,
  all named in the scope note. Nothing in them bears on uniqueness in ℍ_weak under Assumptions
  2.3–2.5. The earlier verdict (faithful with representation choices) stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.thm_uniq ed839d34f480cba1c0edbd81a0b01a9e by=claude-auditor source=A:conclusion@730a6134cc7015b366900c995805b60c092012e31b44602037a39984c2a91da5 -->

## `A:eq:Gid` (paper/sections/04-proof-wellposedness.tex, lines 624–632)

* `MVFBSDEJ.PaperSpec.eq_Gid` (added: lines 624–625). The added lines 624-625 read 'Taking
  expectations and dropping the left limits in the drift multipliers (the dt-integral convention
  above) reduces (4.17) to'. This names the step from the pathwise identity and the convention. The
  earlier report compared the proposition, which uses dX_s and dY_s rather than left limits in the
  drift multipliers, with exactly this convention. The earlier verdict, faithful with representation
  choices, stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.eq_Gid ed839d34f480cba1be665c86f064628a by=claude-auditor source=A:eq:Gid@e3e59eed648d77453dd17511b3b546a6abb04d571b7f574138b426e7b411f9ce -->

## `A:eq:bwddiff` (paper/sections/04-proof-wellposedness.tex, lines 391–424)

* `MVFBSDEJ.PaperSpec.eq_bwddiff` (added: lines 423–424). Lines 423–424 name the
  justifications of the links of (4.12): the second link by (4.11) and (4.9), the fourth by (4.10),
  and the last by λ⁴ ≤ λ² for λ ∈ [0, 1]. The proposition states every link with the printed
  constants and assumes λ ∈ [0, 1]. The earlier report's reading listed these justifications, and
  its coverage noted that 'lines 423–424 name justifications'. The verdict (faithful with
  representation choices) stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.eq_bwddiff ed839d34f480cba18579ef83ba51d72e by=claude-auditor source=A:eq:bwddiff@ca58096655e5e6b70fd088ebf4b2b03e622b17d584f98ab52e438e1f35e7dfaa -->

* `MVFBSDEJ.PaperSpec.eq_bwddiff_identity` (added: lines 423–424). Lines 423–424 justify links
  of (4.12): the second by (4.11) and (4.9), the fourth by (4.10), the last by λ⁴ ≤ λ² on [0, 1].
  They belong to the clause eq_bwddiff and say nothing about the backward difference identity of
  lines 391–397, which this proposition states with the same λ ∈ [0, 1] and the same forcing for
  both trials. The verdict (faithful with representation choices) stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.eq_bwddiff_identity ed839d34f480cba1a9d0fef012ee5fb2 by=claude-auditor source=A:eq:bwddiff@ca58096655e5e6b70fd088ebf4b2b03e622b17d584f98ab52e438e1f35e7dfaa -->

## `A:eq:bwdito` (paper/sections/04-proof-wellposedness.tex, lines 716–725)

* `MVFBSDEJ.PaperSpec.eq_bwdito` (added: lines 716–717). The added lines 716-717 read 'Step 4
  (backward estimate). Ito's formula applied to e^{kappa t}|dY_t|^2 gives, for kappa > 0,'. This is
  the justification and the quantifier kappa > 0. The earlier reading took both from this sentence,
  and the proposition states the inequality for every kappa > 0 and every t in [0,T]. The earlier
  verdict, faithful with representation choices, stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.eq_bwdito ed839d34f480cba1de984de67bb05da2 by=claude-auditor source=A:eq:bwdito@d6302cd9ce59f4a74c314e331a8684638c6d9c76831a024f322a74d59192785e -->

## `A:eq:coeffdiff` (paper/sections/04-proof-wellposedness.tex, lines 312–348)

* `MVFBSDEJ.PaperSpec.eq_coeffdiff` (added: lines 312–324). Lines 312-323 print the set-up of
  the contraction step: trials Theta^1, Theta^2 in the solution space, barTheta^k =
  Phi_lambda(Theta^k), delta psi_s along each trial with its own law, the component differences, and
  the cancellation of xi0 and q. The latest earlier reading used exactly these (S_s with delta psi
  at (Theta^k_s, Law Theta^k_s), trials in the solution space, lambda and q absent from (4.9)). The
  earlier verdict (faithful with representation choices) stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.eq_coeffdiff ed839d34f480cba1a61551fba1a5d143 by=claude-auditor source=A:eq:coeffdiff@dbfe072b5d719a544ec43b251110f77f32c3ceb9a4d075f5cbdefe4a901196bd -->

* `MVFBSDEJ.PaperSpec.eq_coeffdiff_ae` (added: lines 312–324). The added lines 312-324 define
  the trials and delta psi_s at (Theta^k_s, mu^{Theta^k}_s), with h at Theta_s rather than the
  left-limit tuple, which the earlier reading already took from line 316; barTheta^k and the
  cancellation of xi0 and q do not enter the bound at a.e. s. The earlier verdict (faithful with
  representation choices) stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.eq_coeffdiff_ae ed839d34f480cba1b00489a3e8ac9b0a by=claude-auditor source=A:eq:coeffdiff@dbfe072b5d719a544ec43b251110f77f32c3ceb9a4d075f5cbdefe4a901196bd -->

## `A:eq:coeffint` (paper/sections/04-proof-wellposedness.tex, lines 72–81)

* `MVFBSDEJ.PaperSpec.eq_coeffint` (added: lines 72–74 and 80–81). Lines 72-74 give the
  hypotheses and the claim that the coefficient processes along any Theta of the solution space are
  square-integrable; lines 80-81 give the justification (the Lipschitz bound with (2.8) at mu' =
  delta_0) and the start of (4.3). The earlier reading quoted all of this; the proposition (K(L),
  the interior Lipschitz bound only, Theta_t in L2(F_t) for a.e. t, four inequalities in [0,
  infinity]) gives the square-integrability once Assumption 2.2 and membership of the solution space
  make the right side finite. The earlier verdict (broader) stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.eq_coeffint ed839d34f480cba133ce0e119f63091f by=claude-auditor source=A:eq:coeffint@c5122bd0c06b75cd49a895770b87c8f3418f7a1732d074261410c61a8a9d5aaf -->

## `A:eq:coefmeas` (paper/sections/02-model-assumptions.tex, lines 123–134)

* `MVFBSDEJ.PaperSpec.eq_coefmeas` (added: line 123 and 132–134). Line 123 ends the reading
  convention of (2.4) and opens (2.5) with 'Consequently, along any diagonal input'. Lines 132–134
  defer to Lemma A.1 the well-definedness of the law flows and the independence from the
  representatives of Z, U; the scope note pins this as the standing reading of μ and μ⁻. Lemma A.1's
  tuples (càdlàg adapted X, Y and predictable Z, U, of finite energy) lie in the proposition's class
  of progressive tuples. Along those tuples the proposition asserts that b, σ and f are
  progressively measurable, at the exact law at every time, which equals the Borel flow for a.e.
  time. The added lines narrow nothing. The verdict (broader) stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.eq_coefmeas ed839d34f480cba1c9dc5757782364d2 by=claude-auditor source=A:eq:coefmeas@0109d50802d3c1896c48e997eef1423f9bb8bba68e798c4721fae63f388eccb2 -->

* `MVFBSDEJ.PaperSpec.eq_coefmeas_jump` (added: line 123 and 132–134). The earlier report read
  lines 112–134, which include the added lines. Line 123 introduces (2.5) along diagonal inputs.
  Lines 132–134 defer the Borel law flows μ, μ⁻ to Lemma A.1, and the proposition takes an arbitrary
  Borel flow ρ and an arbitrary predictable tuple, instantiated at Θ⁻ and μ⁻. The verdict (broader)
  stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.eq_coefmeas_jump ed839d34f480cba16b26e31f5be9d0e8 by=claude-auditor source=A:eq:coefmeas@0109d50802d3c1896c48e997eef1423f9bb8bba68e798c4721fae63f388eccb2 -->

## `A:eq:compid` (paper/sections/02-model-assumptions.tex, lines 14–25)

* `MVFBSDEJ.PaperSpec.eq_compid` (added: lines 14–15 and 20–25). Lines 14–15 end the
  definition of Ñ and state the hypothesis of (2.1), 'for predictable ψ ≥ 0'. The proposition has
  it: ψ is nonnegative and [0, ∞]-valued, measurable for the marked predictable σ-algebra of the
  standing filtration. Lines 20–25 are (2.2), the claim A:eq:zeromean, as the scope note says. The
  verdict (faithful with representation choices) stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.eq_compid ed839d34f480cba19bf140186b2d4c13 by=claude-auditor source=A:eq:compid@aafacd95e4ac38766dd8830cdd75ad754721232a5283759a5c9383f2d22943cd -->

## `A:eq:dX` (paper/sections/04-proof-wellposedness.tex, lines 511–533)

* `MVFBSDEJ.PaperSpec.eq_dX` (added: lines 511–527). Lines 511–527 fix the notation of the
  proof of Lemma 4.3 that the earlier reading already used. They set q := δq, define the data
  quantity P, and take δψ along (Θ^k_t, Law Θ^k_t), with δh at the predictable tuples. They also
  remark that (Θ^k_t, μ^k_t) is a diagonal input for a.e. t, which the scope note treats as a step
  of the proof, with Lemma A.1. The proposition states (4.15) with these differences and adds no
  hypothesis. The verdict (faithful with representation choices) stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.eq_dX ed839d34f480cba138350f5aeac5a8fc by=claude-auditor source=A:eq:dX@9dd172cef01f1026aa495e51fb68721f4460fd5f4d55467771aae4ff86cab79b -->

## `A:eq:dY` (paper/sections/04-proof-wellposedness.tex, lines 511–533)

* `MVFBSDEJ.PaperSpec.eq_dY` (added: lines 511–527). Lines 511-527 print the set-up of the
  proof of Lemma 4.3 (q := delta q, the data quantity P, delta psi_t with mu^k_t = Law(Theta^k_t),
  delta g_T, delta h at the predictable tuples, the a.e.-t diagonal inputs); the earlier reading
  used this notation for (4.16) (delta f at (Theta^k_s, Law Theta^k_s), delta g_T at the induced
  terminal laws, q = delta q), and P does not enter (4.16). The earlier verdict (faithful with
  representation choices) stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.eq_dY ed839d34f480cba186644af7b4929391 by=claude-auditor source=A:eq:dY@9dd172cef01f1026aa495e51fb68721f4460fd5f4d55467771aae4ff86cab79b -->

## `A:eq:forced` (paper/sections/04-proof-wellposedness.tex, lines 39–65)

* `MVFBSDEJ.PaperSpec.ForcedSolution` (added: lines 39–53). Lines 39–53 print λ ∈ [0, 1] and
  the forcing class: q^b, q^σ, q^f progressively measurable, q^h predictable and 𝒫 ⊗ ℰ-measurable,
  all square integrable, and q^g_T ∈ L²(ℱ_T). The earlier report read lines 37–68 and recorded two
  points. First, the definition carries the forcing as the class Forcing, in which q^h need only be
  marked progressive; WP restricts to the printed predictable class through PredForcing, as the
  scope note says. Second, λ ranges over all reals. On the printed forcings and λ ∈ [0, 1] the
  definition is the printed notion of a solution of (4.1) in ℍ. The verdict (faithful with
  representation choices) stands.
  <!-- def-review: MVFBSDEJ.PaperSpec.ForcedSolution bde81c401c9ac909f447baae21c89992 by=claude-auditor source=A:eq:forced@6e95d16ec0d43e3e59ac4b392a3ff8d5d36e8ba90636e0d6c6af2f8419322135 -->

## `A:eq:frozenbwd` (paper/sections/04-proof-wellposedness.tex, lines 287–310)

* `MVFBSDEJ.PaperSpec.eq_frozenbwd` (added: lines 287–304 and line 310). The latest earlier
  report read lines 287-310 in full (Xi in L2(F_T), the representation of M_t = E[Xi | F_t], barY =
  M - int (lambda f + q^f), barY in S2, barTheta in the solution space, Phi_lambda well defined);
  the added lines are those steps, which the scope note records as steps of the proof of the clause.
  The earlier verdict (faithful with representation choices) stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.eq_frozenbwd ed839d34f480cba158f65f076daf91ac by=claude-auditor source=A:eq:frozenbwd@ef8aee719aa929ad43ce7610eae6de7be530924d8737e8c03fff1f1112349d65 -->

## `A:eq:frozenfwd` (paper/sections/04-proof-wellposedness.tex, lines 258–285)

* `MVFBSDEJ.PaperSpec.eq_frozenfwd` (added: lines 258–265 and 272–285). The earlier report
  read lines 257–285, the whole widened region. It covers the set-up (λ ∈ [0, 1], the forcing, Θ ∈
  ℍ, μ^Θ, μ^{Θ,−}, Φ_λ), the left-limit remark citing Lemma A.1, the integrability display, the
  measurability sentence, and existence and uniqueness in S². The report recorded the predictability
  of the jump integrand as not stated; the scope note now names it as (2.5), the claim
  A:eq:coefmeas. The verdict (faithful with representation choices) stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.eq_frozenfwd ed839d34f480cba17566150acd92b890 by=claude-auditor source=A:eq:frozenfwd@a72c0729408b846798089067eac3f1966ae9f7df239c8d2e944157592fc2390a -->

## `A:eq:fubiniiso` (paper/sections/02-model-assumptions.tex, lines 112–123)

* `MVFBSDEJ.PaperSpec.eq_fubiniiso` (added: line 112 and 117–123). The earlier report read
  lines 112–123. Line 112 introduces the isometry for predictable processes. Lines 117–119 assert
  the 𝒫 ⊗ ℰ-measurable representative and its uniqueness up to dt ⊗ dP ⊗ ν-null sets, which are the
  second and third conjuncts of the proposition. Lines 119–123 are the reading convention pinned by
  the scope note. The verdict (broader: any σ-finite base (X, μ), instantiated at the predictable
  σ-field with dt ⊗ dP) stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.eq_fubiniiso ed839d34f480cba1f8905adfcaf41890 by=claude-auditor source=A:eq:fubiniiso@afa161dc6583c6a35e577920f56a78d2ffa2160398278a7afcd025eaeee73dfd -->

## `A:eq:hborel` (paper/sections/02-model-assumptions.tex, lines 86–106)

* `MVFBSDEJ.WellPosedness.Spec.JointBorel` (added: lines 86–101). The added lines 86-101 say the
  coefficients are deterministic and give the signatures: b, sigma, h, f on [0,T] x H x P2(H) into
  R^n, R^{n x d}, L2(nu; R^n), R^m, and g on R^n x P2(R^n). They also say all coefficients are
  jointly Borel. JointBorel requires exactly this: Borel measurability of b, sigma, h (into L2(nu;
  R^n)) and f on [0,T] x H x P2(H) with the W2 topology, and of g on R^n x P2(R^n), for the
  deterministic Coeffs. The forcings of Section 4 and the omega-random coefficients of cited work
  are not part of it. The earlier reading quoted this sentence; its verdict, faithful, stands.
  <!-- def-review: MVFBSDEJ.WellPosedness.Spec.JointBorel 6f73c7a1734b55b30000000000000000 by=claude-auditor source=A:eq:hborel@f3d81f78d89578cf0708f975cb8c81d7c791427d8c9187ffca569edf249c1840 -->

## `A:eq:intmono` (paper/sections/04-proof-wellposedness.tex, lines 634–646)

* `MVFBSDEJ.PaperSpec.eq_intmono` (added: lines 634–638). Lines 634–638 open Step 2. They say
  that δh at the predictable tuples agrees with δh at (Θ^k_t, μ^k_t) for dt-a.e. t, by Lemma A.1,
  and that Assumption 2.5 applied at the common input pair bounds the integrand. The earlier report
  read this sentence and found it absorbed into the proposition: the left side is taken at the
  predictable tuples, for a.e. t, with the integrability stated. The verdict (faithful with
  representation choices) stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.eq_intmono ed839d34f480cba1448a1399ac43f935 by=claude-auditor source=A:eq:intmono@9d221f3b9e56232ce7594196244b4b7c26ce6508017ae6136ed16c7526aae86e -->

## `A:eq:monomargin` (paper/sections/02-model-assumptions.tex, lines 289–297)

* `MVFBSDEJ.PaperSpec.Margin212` (added: line 289). Line 289 adds 'Say that (2.7) holds with
  margin c > 0 if', the phrase the earlier reading took as its starting point: (2.12) inherits the
  quantifiers of (2.7) (a.e. t, all diagonal pairs), which Margin212 has, and the positivity of c is
  a separate hypothesis of the statements using it, as the scope note says. The earlier verdict
  (faithful with representation choices) stands.
  <!-- def-review: MVFBSDEJ.PaperSpec.Margin212 a0fc1ba9071e126ca6e512bffcfb0a22 by=claude-auditor source=A:eq:monomargin@93d5988c3689252f9d5fece5709d721eb8ab08c6b2ef6c2ef46c7da2598c2099 -->

## `A:eq:monomarginu` (paper/sections/02-model-assumptions.tex, lines 306–316)

* `MVFBSDEJ.WellPosedness.Spec.Margin213` (added: lines 306–308). The added lines 306-308 read:
  'A margin c in (2.12) therefore yields the margin c/c_G, which is smaller than c when c_G > 1, in
  the unweighted form, which with margin c > 0 reads'. The first part is the content of
  A:rem:margin, as the scope note says. The positivity c > 0 is a separate hypothesis of the
  statements that use a margin, which the earlier report already recorded (c > 0 is not built into
  Margin213). The display (2.13) is unchanged. The earlier verdict, faithful with representation
  choices, stands.
  <!-- def-review: MVFBSDEJ.WellPosedness.Spec.Margin213 a0fc1ba9071e126c345eefe1f9893670 by=claude-auditor source=A:eq:monomarginu@7a54aa98ecce9d453337bd582ab01fa94492a3ede87c7f372e4197062861568b -->

## `A:eq:mvfbsdej` (paper/sections/01-introduction.tex, lines 3–48)

* `MVFBSDEJ.PaperSpec.Solution` (added: lines 3–5 and 14–48). Lines 3-5 announce the results
  (content of Theorems 3.1, 3.3 and 3.5). Lines 14-48 print the standing setting: W and an
  independent compensated Poisson random measure with sigma-finite nu, nu(E) = infinity admitted; H
  with its Euclidean, Frobenius and L2(nu) norms; Theta; the predictable tuple Theta^- = (X_{t-},
  Y_{t-}, Z_t, U_t) at which h is evaluated; and mu_t = Law(Theta_t), mu_t^- = Law(Theta_t^-) in
  P2(H). They end with the W2-Lipschitz, diagonal-only hypotheses. The earlier reading of Solution
  already used this setting: a driver with independent W and N, any sigma-finite nu, a
  representative of h at the predictable tuple and its law, and exact laws that agree with the
  paper's law flows for a.e. t. The Lipschitz and monotonicity sentences concern Assumptions 2.3 and
  2.5, not the solution notion. The earlier verdict, faithful with representation choices, stands.
  <!-- def-review: MVFBSDEJ.PaperSpec.Solution 3220c6ff72b9eb8278fda8b917b2b13b by=claude-auditor source=A:eq:mvfbsdej@5eb480b379a74b6cf3448b228b60d1dcb3f707265f25c5b1cbe6f82b684e917a -->

## `A:eq:supE` (paper/sections/04-proof-wellposedness.tex, lines 188–246)

* `MVFBSDEJ.PaperSpec.eq_supE` (added: lines 218–246). The added lines 218-246 upgrade sup_t
  E|dY_t|^2 to E sup_t |dY_t|^2 using the forward form, Cauchy-Schwarz, BDG and (4.6). They end by
  defining C_BP := C_0(5 + 4c_BDG) + 4T, 'depending only on T and c_BDG'. They use (4.6) but add no
  hypothesis to it and change neither its conclusion nor C_0 = 2e^T. The scope note assigns them to
  the conclusion of Lemma 4.1 (a separate claim) and pins the definition of C_BP here. The earlier
  verdict, faithful with representation choices, stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.eq_supE ed839d34f480cba130fc02b504932bac by=claude-auditor source=A:eq:supE@69066031ecb004372ea47f44623161352a6f6ead47cb3d38fdb991579e47bd8f -->

* `MVFBSDEJ.PaperSpec.eq_supE_weighted` (added: lines 218–246). The added lines 218-246 come
  after (4.6): the upgrade to E sup_t |dY_t|^2 and the definition C_BP := C_0(5 + 4c_BDG) + 4T. The
  scope note assigns them to the conclusion of Lemma 4.1 and to the definition of C_BP pinned here.
  They do not touch the weighted inequality of lines 193-199, which this clause states for every t
  under the hypotheses of Lemma 4.1. The earlier verdict, faithful with representation choices,
  stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.eq_supE_weighted ed839d34f480cba1842c940f112b9666 by=claude-auditor source=A:eq:supE@69066031ecb004372ea47f44623161352a6f6ead47cb3d38fdb991579e47bd8f -->

## `A:eq:terdiff` (paper/sections/04-proof-wellposedness.tex, lines 376–389)

* `MVFBSDEJ.PaperSpec.eq_terdiff` (added: lines 376–380 and line 389). The added lines 376-380
  define dxi-bar = lambda[g(Xbar^1_T, Law Xbar^1_T) - g(Xbar^2_T, Law Xbar^2_T)], and line 389 names
  the justifications (first step by (2.6), last by (2.9)). The earlier report read both. The
  proposition's dxi is this dxi-bar at X_k = Xbar^k_T, and its only hypothesis is (2.6). The earlier
  verdict, broader, stands: any filtered space, real lambda and L, and any two F_T-measurable
  square-integrable terminal values.
  <!-- spec-review: MVFBSDEJ.PaperSpec.eq_terdiff ed839d34f480cba1e42e4445110ef5d2 by=claude-auditor source=A:eq:terdiff@116673203b4e630139746461480f29ec99df5f9a0b1c2b65182172d52b7c6663 -->

## `A:eq:termg` (paper/sections/04-proof-wellposedness.tex, lines 81–85)

* `MVFBSDEJ.PaperSpec.eq_termg` (added: line 81 and line 85). The added line 81 ends the
  sentence of (4.2) ('... at mu' = delta_0. For the terminal function the analogous bound'), and
  line 85 reads 'follows in the same way from (2.6) and (2.9)'. Both are justifications. The earlier
  reading derived C from (2.6) at X'_T = 0 and from (2.9), as printed, and the proposition assumes
  only (2.6). The earlier verdict, broader, stands: g need not be Borel and the filtered space is
  arbitrary; the instance is the standing basis with C := K(L).
  <!-- spec-review: MVFBSDEJ.PaperSpec.eq_termg ed839d34f480cba12450d1561dfcb469 by=claude-auditor source=A:eq:termg@e5e65b5b630e579811ef01eae876fb0b8d2a6a7e480cc1b1489922be38a78fc2 -->

## `A:eq:termmono` (paper/sections/04-proof-wellposedness.tex, lines 648–656)

* `MVFBSDEJ.PaperSpec.eq_termmono` (added: lines 648–649). Lines 648-649 name the
  justification of (4.21), the terminal monotonicity of Assumption 2.5, which is a hypothesis of the
  proposition (the terminal half of Assumption25) and was read as such earlier. The earlier verdict
  (faithful with representation choices) stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.eq_termmono ed839d34f480cba1333d2c440bae1c71 by=claude-auditor source=A:eq:termmono@1ff3c48770a8bbe244b9a0a64dc92f938b6ba1357952a47e23573c7ccccdf7c1 -->

## `A:eq:uniq-bwd` (paper/sections/03-main-results.tex, lines 158–174)

* `MVFBSDEJ.PaperSpec.eq_uniq_bwd` (added: lines 173–174). The added lines 173-174 read
  'therefore dY in S^2(R^m). By (3.2) and (3.3) we have dTheta in the strong space.' The first is
  the finiteness that (3.3) already asserts: the proposition states the right side < infinity, and
  dY is cadlag and adapted by the solution notion. The second is the membership Theta^1 - Theta^2 in
  the strong space, which the scope note assigns to the fifth clause, rem_uniq_lip_mem. Neither adds
  a hypothesis, nor changes (3.3) or the dependence of C_BP on T alone. The earlier verdict,
  faithful with representation choices, stands, and so does its remark on the degenerate witness.
  <!-- spec-review: MVFBSDEJ.PaperSpec.eq_uniq_bwd ed839d34f480cba135b52d27f248f550 by=claude-auditor source=A:eq:uniq-bwd@2299c84c37bf6e6d07e5bf1079800d77af7ce8de795c426b59b69acde29e973a -->

* `MVFBSDEJ.PaperSpec.eq_uniq_bwd_eq` (added: lines 173–174). The added lines 173-174 come
  after (3.3). They state that dY is in S^2 and that dTheta is in the strong space; the first is the
  finiteness of (3.3), the second the fifth clause. They do not touch the backward difference
  identity of lines 158-163, which this clause states. The earlier verdict, broader, stands:
  Assumptions 2.4-2.5 are dropped, and the printed step is the instance with them added.
  <!-- spec-review: MVFBSDEJ.PaperSpec.eq_uniq_bwd_eq ed839d34f480cba192eaf1aadb749ed7 by=claude-auditor source=A:eq:uniq-bwd@2299c84c37bf6e6d07e5bf1079800d77af7ce8de795c426b59b69acde29e973a -->

* `MVFBSDEJ.PaperSpec.eq_uniq_bwd_lip` (added: the clause is new to this claim: read the whole
  passage). No lines were added: the widened region (lines 158-174) is the region read. Within it,
  (3.3) with its '< infinity' and the sentence 'therefore dY in S^2' are this clause's inequality
  and finiteness conjunct. The clause states them under (2.3) and Assumption 2.3 alone, so it is
  broader than the step in the proof of Theorem 3.3 (instance: add Assumptions 2.4-2.5). The earlier
  report and the scope note record this. 'dTheta in the strong space' is the clause
  rem_uniq_lip_mem.
  <!-- spec-review: MVFBSDEJ.PaperSpec.eq_uniq_bwd_lip ed839d34f480cba1e8f6ceb6d82ac63e by=claude-auditor source=A:eq:uniq-bwd@2299c84c37bf6e6d07e5bf1079800d77af7ce8de795c426b59b69acde29e973a -->

* `MVFBSDEJ.PaperSpec.eq_uniq_bwd_terminal` (added: lines 173–174). The added lines 173-174
  (dY in S^2, dTheta in the strong space) come after (3.3) and concern its finiteness and the
  membership clause. They do not touch the terminal bound of lines 163-166 (X^k_T in L2, E|dg_T|^2
  <= C E|dX_T|^2 < infinity), which this clause states. The earlier verdict, broader, stands: only
  (2.3) and Assumption 2.3 are assumed, and the printed step is the instance with Assumptions
  2.4-2.5 added.
  <!-- spec-review: MVFBSDEJ.PaperSpec.eq_uniq_bwd_terminal ed839d34f480cba132f1ce11a6edfb1c by=claude-auditor source=A:eq:uniq-bwd@2299c84c37bf6e6d07e5bf1079800d77af7ce8de795c426b59b69acde29e973a -->

* `MVFBSDEJ.PaperSpec.rem_uniq_lip_mem` (added: lines 173–174 (the clause is new to this
  claim: its auditor marker records a reading of A:rem:uniq-no-integ only, so the whole passage
  158–174 needs a reading)). The added line 'By (3.2) and (3.3) we have dTheta in the strong space'
  prints exactly this clause's conclusion: the norm of Theta^1 - Theta^2 in the strong space (sup
  norms on X and Y, energies of Z and U) is finite, which is supSize < infinity. The passage lies
  inside the proof of Theorem 3.3, where Assumptions 2.3-2.5 are in force; the proposition assumes
  only (2.3) and Assumption 2.3, as the scope note says. So the proposition is broader than this
  line, which is its instance with Assumptions 2.4-2.5 added. The earlier report recorded exactly
  this for the 'Furthermore' clause of Theorem 3.3, which these lines prove. Its reading and its
  representation choices stand.
  <!-- spec-review: MVFBSDEJ.PaperSpec.rem_uniq_lip_mem ed839d34f480cba1cd99b18fe79eeef0 by=claude-auditor source=A:eq:uniq-bwd@2299c84c37bf6e6d07e5bf1079800d77af7ce8de795c426b59b69acde29e973a -->

## `A:eq:uniq-coeff` (paper/sections/03-main-results.tex, lines 110–156)

* `MVFBSDEJ.PaperSpec.eq_uniq_coeff` (added: lines 143–156). The added lines 143–156 are the
  next step of the proof of Theorem 3.3: the forward difference equation, 𝔼 sup|δX|² ≤ C_T 𝔼∫(|δb|²
  + |δσ|²_F + ‖δh‖²) < ∞ by (3.2), hence δX ∈ S². As the scope note says, this step is the claim's
  fourth clause, eq_uniq_fwd. The lines print no new hypothesis; they use the same initial datum,
  already a hypothesis here. They do not alter (3.2), which this clause states under the hypotheses
  of Theorem 3.3 with δh at the predictable tuples. The earlier report's remark that the region is
  (3.2) alone is superseded by the four-clause coverage. The verdict (faithful with representation
  choices) stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.eq_uniq_coeff ed839d34f480cba14f8e0a069ba79654 by=claude-auditor source=A:eq:uniq-coeff@c5e7dae7414c6edbeb2afd8a9b9973a719f095ba7998511de1e2ebcb347197cb -->

* `MVFBSDEJ.PaperSpec.eq_uniq_coeff_ae` (added: lines 143–156). The added lines 143–156 are
  the forward step that follows (3.2): the forward difference equation and the bound on 𝔼 sup|δX|²
  giving δX ∈ S². They are stated by the clause eq_uniq_fwd, print no hypothesis, and do not touch
  the bound 𝔼[|δb_t|² + |δσ_t|²_F + ‖δh_t‖² + |δf_t|²] ≤ C 𝔼|δΘ_t|²_H at a.e. t that this
  proposition states. The verdict (broader: (2.3) and Assumption 2.3 only, and C = K(L) chosen
  first; the printed step is its instance) stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.eq_uniq_coeff_ae ed839d34f480cba104f29a2c26ce0258 by=claude-auditor source=A:eq:uniq-coeff@c5e7dae7414c6edbeb2afd8a9b9973a719f095ba7998511de1e2ebcb347197cb -->

* `MVFBSDEJ.PaperSpec.eq_uniq_coeff_lip` (added: lines 143–156 (the clause is new to this
  claim: its auditor marker records a reading of A:rem:uniq-no-integ only, so the whole passage
  110–156 needs a reading)). The earlier independent report read this proposition for Remark 3.4, as
  (3.2) under (2.3) and Assumption 2.3 alone. At this claim the passage is the proof of Theorem 3.3,
  with Assumptions 2.3–2.5 in force. As the scope note says, and as the earlier report also
  recorded, the proposition is that step under the Lipschitz control alone, and the printed (3.2) is
  its instance with 2.4–2.5 added. Against this passage it is therefore broader, with the same
  meaning. The added lines 143–156 (the forward step to δX ∈ S²) are the clause eq_uniq_fwd, print
  no new hypothesis, and do not change the reading of (3.2).
  <!-- spec-review: MVFBSDEJ.PaperSpec.eq_uniq_coeff_lip ed839d34f480cba12dd6d5b53696ba1a by=claude-auditor source=A:eq:uniq-coeff@c5e7dae7414c6edbeb2afd8a9b9973a719f095ba7998511de1e2ebcb347197cb -->

* `MVFBSDEJ.PaperSpec.eq_uniq_fwd` (added: lines 143–156 (the clause is new to this claim: its
  auditor marker records a reading of A:rem:uniq-no-integ only, so the whole passage 110–156 needs a
  reading)). The added lines 143–156 are exactly the step this proposition states, and the earlier
  independent report, recorded for Remark 3.4, read those lines. It found three things faithful.
  First, the forward difference identity holds for every t, almost surely, with δh at the
  predictable tuples. Second, 𝔼 sup|δX_t|² ≤ K(T) 𝔼∫(|δb|² + |δσ|²_F + ‖δh‖²), with K a function of
  T chosen first. Third, the right side is finite. At this claim the step sits in the proof of
  Theorem 3.3, with 2.3–2.5 in force, and the proposition drops 2.4–2.5, the passage being its
  instance. The scope note states this, and the earlier report recorded it ('broader than the step
  in the proof'). Against this passage the label is therefore broader; the reading stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.eq_uniq_fwd ed839d34f480cba157d3ed036c939145 by=claude-auditor source=A:eq:uniq-coeff@c5e7dae7414c6edbeb2afd8a9b9973a719f095ba7998511de1e2ebcb347197cb -->

## `A:eq:zeromean` (paper/sections/02-model-assumptions.tex, lines 13–25)

* `MVFBSDEJ.PaperSpec.eq_zeromean` (added: lines 13–20). Lines 13-20 add the definition Ntilde
  = N - dt nu and the compensation formula (2.1); the earlier reading already used both (the
  compensated integral of an L1 integrand as int psi dN - int int psi dnu ds, its integrability by
  (2.1)). The earlier verdict (faithful with representation choices) stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.eq_zeromean ed839d34f480cba1ab4a0cb1d17ec7d1 by=claude-auditor source=A:eq:zeromean@4a8de4ef68a42a19524cd25d158243c45a32a31e55ce45fb91402f26631627ea -->

## `A:intro:contributions` (paper/sections/01-introduction.tex, lines 101–116)

* `MVFBSDEJ.PaperSpec.cor_robust_wp` (added: lines 101–116 (a new formal claim: the whole
  passage, the contribution list)). The whole region (lines 101-116) is new. Item (iv) (lines
  111-113) reads 'robustness: well-posedness survives full-tuple-law perturbations below the
  dissipativity margin at equal forward and backward dimension (Corollary 3.6; ...)'. This is what
  cor_robust_wp states: - Equal dimension: m = n, built into the types. - The baseline: it satisfies
  (2.3) and Assumptions 2.2-2.5 with the unweighted margin (2.13), c_diss > 0, so it is well-posed
  with a margin. - 'Full-tuple-law perturbations': p perturbs b, sigma, h, f, with g unchanged, and
  its arguments are the tuple and the law of the full tuple in P_2(H). - 'Below the dissipativity
  margin': p has origin values and the interior Lipschitz bound, and satisfies (3.4) with c_pert <
  c_diss. - 'Survives': the perturbed system has a solution in H, is unique in H_weak and satisfies
  (3.1). This is the sense 'well-posed by Theorems 3.1, 3.3 and 3.5' of Corollary 3.6. I also
  considered reading 'full-tuple-law perturbations' as the tuple-independent perturbations of (3.5),
  with 'below the margin' meaning ||G|| L_p < c_diss. Under that reading the item would be an
  instance of this proposition, with (3.4) supplied by the second part of Corollary 3.6
  (cor_robust_lip). But the item states the size condition through the margin, which is c_pert <
  c_diss in (3.4), and mentions no W_2-Lipschitz constant. The first reading is therefore the
  printed one: the item is the first part of the corollary, and Section 6 uses the same words for
  it. The item drops no hypothesis and adds no conclusion. The earlier verdict, faithful with
  representation choices, stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.cor_robust_wp ed839d34f480cba1617ff136058ce573 by=claude-auditor source=A:intro:contributions@6ee0736683d48f72fd199cb331cad8e2e8968f67f97c9826bccbcb140867b8df -->

* `MVFBSDEJ.PaperSpec.prop_strict` (added: lines 101–116 (a new formal claim: the whole
  passage, the contribution list)). The whole region (lines 101-116) is new. Item (v) (lines
  114-115) cites Proposition 3.8 for the strictness, and prop_strict states that proposition in
  full. For n = m = 1, every d >= 1, G = 1, beta_1 > 0 and 0 < eps < beta_1, the drift (3.6)
  satisfies the expected diagonal bound (3.7) along all diagonal inputs. Yet the pointwise bound
  <db, dy> <= -beta |dy|^2 fails for every beta >= 0 at free inputs in the supports. The proposition
  also gives the free-measure Lipschitz constant beta_1 + eps. What the item asserts of Proposition
  3.8 is that the expected diagonal bound holds where its pointwise form fails, and this is that
  statement. The Lipschitz conjunct is part of Proposition 3.8, which the note records. The item
  drops none of the proposition's hypotheses (n = m = 1, G = 1, eps < beta_1), because it states the
  strictness as the existence of such an instance. For a full coefficient system the strictness is
  carried by the separate clause rem_diag_mono_converse. The earlier verdict, faithful with
  representation choices, stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.prop_strict ed839d34f480cba1ac9d315442ee6c22 by=claude-auditor source=A:intro:contributions@6ee0736683d48f72fd199cb331cad8e2e8968f67f97c9826bccbcb140867b8df -->

* `MVFBSDEJ.PaperSpec.rem_diag_mono` (added: lines 101–116 (a new formal claim: the whole
  passage, the contribution list)). The whole region (lines 101-116) is new. Item (v) (lines
  114-115) reads 'expected diagonal monotonicity is strictly weaker than its pointwise form
  (Proposition 3.8)'. It contains the implication that the pointwise form gives the expected one,
  which is Remark 2.8 and is what rem_diag_mono states. Under (2.3), suppose the inequality of (2.7)
  holds without expectations, for a.e. t, at all points theta, theta' and all free laws mu, mu'.
  Then for a.e. t and all pairs in D_t the expected (2.7) holds, in the extended sense. When
  Assumption 2.3, one of the stated L^2 assumptions, supplies the integrability, it also holds in
  the Lean form Mono27At. 'Its pointwise form' is the pointwise condition as Remark 2.8 defines it,
  namely the inequality of (2.7), so a conclusion about the interior inequality only is right. The
  item adds no hypothesis and no conclusion beyond the remark, which the note records for this half
  of the strictness. The earlier verdict, faithful with representation choices, stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.rem_diag_mono ed839d34f480cba16dbf12782c23a6c7 by=claude-auditor source=A:intro:contributions@6ee0736683d48f72fd199cb331cad8e2e8968f67f97c9826bccbcb140867b8df -->

* `MVFBSDEJ.PaperSpec.rem_diag_mono_converse` (added: lines 101–116 (a new formal claim: the
  whole passage, the contribution list)). The whole region (lines 101-116) is new. The strictness in
  item (v) (lines 114-115) is the failure of the converse of Remark 2.8, and rem_diag_mono_converse
  states it for a full coefficient system. On every standing basis with n = m = d = 1 and for every
  T > 0, some coefficients satisfy (2.3), Assumption 2.3 and Assumption 2.5 (expected along D_t,
  terminal and interior, with G = 1 and admissible constants). For these coefficients the inequality
  of (2.7) without expectations fails at free points and laws, for every beta >= 0 and every beta'.
  The item claims no generality in the dimensions: strictness is the existence of an instance, as in
  Remark 2.8's 'the converse fails' and in Proposition 3.8, which has n = m = 1. A counterexample at
  d = 1 on every basis therefore states it, and prop_strict covers every d >= 1 for the drift
  pairing. Nothing is dropped or added. The earlier verdict, faithful, stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.rem_diag_mono_converse ed839d34f480cba194f9b4ec1a6ab33d by=claude-auditor source=A:intro:contributions@6ee0736683d48f72fd199cb331cad8e2e8968f67f97c9826bccbcb140867b8df -->

* `MVFBSDEJ.PaperSpec.rem_generalrank_wp` (added: lines 101–116 (a new formal claim: the whole
  passage, the contribution list)). The whole region (lines 101-116) is new. 'Remark 3.7 for general
  rank' in item (iv) (line 113) is what rem_generalrank_wp states. The setting is arbitrary n, m >=
  1 and a full-rank G in R^{m x n}. The baseline satisfies (2.3) and Assumptions 2.2-2.5 with the
  weighted margin (2.12), c_diss > 0. The perturbation has origin values and the interior Lipschitz
  bound, and satisfies (3.4) in the weighted quantity of (2.12) with c_pert < c_diss. Then the
  perturbed system has a solution in H, is unique in H_weak and satisfies (3.1). For general rank
  the item leaves the form of 'below the dissipativity margin' to Remark 3.7, which records both the
  margin and (3.4) in the weighted quantities, and the proposition takes exactly these. So the item
  drops no hypothesis and adds no conclusion. The earlier verdict, faithful with representation
  choices, stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.rem_generalrank_wp ed839d34f480cba1e559b01e430dcbd3 by=claude-auditor source=A:intro:contributions@6ee0736683d48f72fd199cb331cad8e2e8968f67f97c9826bccbcb140867b8df -->

* `MVFBSDEJ.PaperSpec.thm_cwp` (added: lines 101–116 (a new formal claim: the whole passage,
  the contribution list)). The whole region (lines 101-116) is new. Two passages bear on this
  proposition: 'We prove well-posedness under the stated L^2 and monotonicity assumptions' (lines
  102-103), and item (iii) (lines 109-110), 'global existence by monotone continuation from a
  small-coupling base case (Theorem 3.5)'. Both are what thm_cwp states, with thm_stab for the
  continuous dependence: for every horizon T > 0, with no smallness condition, under (2.3) and
  Assumptions 2.2-2.5, (1.1) has a solution in H, and any two solutions are equal in H. Here
  Assumptions 2.2-2.3 are the L^2 assumptions and 2.4-2.5 the monotonicity assumptions. 'Global'
  means existence on every finite horizon, the quantifier over all T > 0; the opening sentence of
  the introduction and the abstract say 'on every fixed/prescribed finite horizon', so this is not a
  claim about an infinite horizon. 'By global-in-time monotone continuation' and 'from a
  small-coupling base case' describe the proof, which the note names (Section 4.5, Lemmas 4.2 and
  4.4). The passage drops no hypothesis of Theorem 3.5 and asserts nothing the proposition lacks.
  The uniqueness conjunct is part of 'well-posedness' in lines 102-103. The earlier verdict,
  faithful with representation choices (latest report), stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.thm_cwp ed839d34f480cba12370b493940a6d61 by=claude-auditor source=A:intro:contributions@6ee0736683d48f72fd199cb331cad8e2e8968f67f97c9826bccbcb140867b8df -->

* `MVFBSDEJ.PaperSpec.thm_stab` (added: lines 101–116 (a new formal claim: the whole passage,
  the contribution list)). The whole region (lines 101-116, the contribution list of the
  introduction) is new. Item (i) (lines 106-107), 'an a priori stability estimate: the full
  difference of two solutions is controlled by the differences of their coefficients and data
  (Theorem 3.1)', together with the continuous dependence that 'well-posedness' carries in lines
  102-103, is what thm_stab states. Take two systems with solutions in H, system 1 under (2.3) and
  Assumptions 2.2-2.5 and system 2 under (2.3) and Assumptions 2.2-2.3, both within 'the stated L^2
  and monotonicity assumptions'. Then supSize of all four components of Theta^1 - Theta^2 (the full
  difference, in the norm of H) is at most C_stab times dataSize. The terms of dataSize are the
  differences of the initial data, of the terminal functions at X^2_T and of the four interior
  coefficients along solution 2: these are the differences of coefficients and data, in the notation
  the note pins in A:sec3:two-system-notation. The item drops no hypothesis of Theorem 3.1 and adds
  no conclusion. The constant dependence the proposition carries is that of Theorem 3.1, which the
  note records as item (i). The earlier verdict, faithful with representation choices, stands.
  Entry-level coverage. The eight clauses together state every mathematical assertion of lines
  101-116, and the note names the rest correctly. - Lines 101-102 describe cited work. The contrast
  they imply, that the present results are restricted on none of the three axes, is carried by the
  hypotheses of thm_cwp and thm_stab: the coefficients take the law of the full tuple in P_2(H),
  U-marginal included; nu is only sigma-finite; and no smallness of the coupling is assumed. -
  'Well-posedness under the stated L^2 and monotonicity assumptions' (lines 102-103) is thm_cwp
  under (2.3) and Assumptions 2.2-2.5, with thm_stab for the continuous dependence. - 'By
  global-in-time monotone continuation' and 'by monotone continuation from a small-coupling base
  case' describe the proof: Section 4.5 and Lemmas 4.2 (small-coupling base case) and 4.4
  (continuation), which the note numbers correctly. - Items (i)-(v) are attributed as printed. -
  Item (iv) cites Corollary 3.6 as a whole but asserts only its well-posedness part. The corollary's
  second part, that (3.5) gives (3.4) with c_pert = ||G|| L_p (cor_robust_lip), is not asserted by
  the item, so it is right that no clause carries it. - Item (v), 'strictly weaker', is the
  implication of Remark 2.8 (rem_diag_mono) together with the failure of its converse. That failure
  is stated for the drift pairing (prop_strict) and for a full coefficient system
  (rem_diag_mono_converse).
  <!-- spec-review: MVFBSDEJ.PaperSpec.thm_stab ed839d34f480cba14815ce65dd3b146f by=claude-auditor source=A:intro:contributions@6ee0736683d48f72fd199cb331cad8e2e8968f67f97c9826bccbcb140867b8df -->

* `MVFBSDEJ.PaperSpec.thm_uniq` (added: lines 101–116 (a new formal claim: the whole passage,
  the contribution list)). The whole region (lines 101-116) is new. Item (ii) (line 108),
  'uniqueness in the natural class (Theorem 3.3)', is what thm_uniq states. Under (2.3) and
  Assumptions 2.3-2.5, two tuples of H_weak that satisfy (1.1) with the same initial datum have
  indistinguishable X and Y on [0, T] and zero energy of the Z- and U-differences, and their
  difference lies in H. These hypotheses are part of 'the stated L^2 and monotonicity assumptions'
  of lines 102-103; Assumption 2.2 is not needed, as Remark 3.4 says. The passage does not define
  'the natural class'. Read as H_weak, the class in which Theorem 3.3 compares two tuples, it is the
  class of the proposition. Read as H, the solution space of Section 3, uniqueness there is an
  instance of the proposition, since H is contained in H_weak. Either way the proposition states the
  item. Its further conclusion, that Theta^1 - Theta^2 lies in H, is part of Theorem 3.3, which the
  note records as item (ii); the note pins the class itself in A:sec3:HH-banach. The earlier
  verdict, faithful with representation choices, stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.thm_uniq ed839d34f480cba1c0edbd81a0b01a9e by=claude-auditor source=A:intro:contributions@6ee0736683d48f72fd199cb331cad8e2e8968f67f97c9826bccbcb140867b8df -->

## `A:intro:limin-comparison` (paper/sections/01-introduction.tex, lines 58–66)

* `MVFBSDEJ.PaperSpec.ex_expfunc_limin` (added: lines 59–66). The added lines describe the
  cited interaction class: expectation-functional (independent-copy) type, a jump integrand that
  enters pointwise, and finite total jump mass. They end with 'Example 5.3 details the embedding of
  their interaction class' (line 66), which is this clause. ex_expfunc_limin states the
  finite-activity embedding of independent-copy kernels, consistent with that description: nu
  finite, psi-bar block-Lipschitz, phi-bar finite and independent of the representatives, and
  Lipschitz on H x H with constant Lip(psi-bar) max{nu(E), nu(E)^(1/2)}. The earlier verdict,
  broader, stands: measurability and time-square-integrability of psi-bar are dropped.
  <!-- spec-review: MVFBSDEJ.PaperSpec.ex_expfunc_limin ed839d34f480cba1f28bceb8fea3e945 by=claude-auditor source=A:intro:limin-comparison@28e759aa0429025c3c31ed5e4adc1fdd423b38202635e9fa80e52cc98bb13998 -->

* `MVFBSDEJ.PaperSpec.thm_cwp` (added: lines 59–66). Lines 59-63 describe the theorem of Li
  and Min; the scope note treats them as a statement about cited work. Lines 63-66 say the present
  theorem allows W2 dependence on the full tuple law, the law of U included, at arbitrary
  sigma-finite activity, under the expected G-monotonicity condition. thm_cwp shows all of this in
  its hypotheses: Coeffs on H x P2(H) with the L2(nu) channel and the Hilbert-norm W2, SigmaFinite
  nu only, and Assumption25 in expectation along the diagonal. The latest earlier report already
  read this paragraph to line 66. The verdict, faithful with representation choices, stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.thm_cwp ed839d34f480cba12370b493940a6d61 by=claude-auditor source=A:intro:limin-comparison@28e759aa0429025c3c31ed5e4adc1fdd423b38202635e9fa80e52cc98bb13998 -->

## `A:intro:mvfbsdej` (paper/sections/01-introduction.tex, lines 3–48)

* `MVFBSDEJ.PaperSpec.Solution` (added: lines 3–5 and 14–48). Lines 3-5 announce the results
  (content of Theorems 3.1, 3.3 and 3.5). Lines 14-48 print the standing setting: W and an
  independent compensated Poisson random measure with sigma-finite nu, nu(E) = infinity admitted; H
  with its Euclidean, Frobenius and L2(nu) norms; Theta; the predictable tuple Theta^- = (X_{t-},
  Y_{t-}, Z_t, U_t) at which h is evaluated; and mu_t = Law(Theta_t), mu_t^- = Law(Theta_t^-) in
  P2(H). They end with the W2-Lipschitz, diagonal-only hypotheses. The earlier reading of Solution
  already used this setting: a driver with independent W and N, any sigma-finite nu, a
  representative of h at the predictable tuple and its law, and exact laws that agree with the
  paper's law flows for a.e. t. The Lipschitz and monotonicity sentences concern Assumptions 2.3 and
  2.5, not the solution notion. The earlier verdict, faithful with representation choices, stands.
  <!-- def-review: MVFBSDEJ.PaperSpec.Solution 3220c6ff72b9eb8278fda8b917b2b13b by=claude-auditor source=A:intro:mvfbsdej@5eb480b379a74b6cf3448b228b60d1dcb3f707265f25c5b1cbe6f82b684e917a -->

## `A:lemA1:polish` (paper/sections/09-appendix.tex, lines 53–56)

* `MVFBSDEJ.PaperSpec.eq_coupling` (added: lines 53–54 and line 56). Lines 53-54 and 56
  complete the sentence: by (2.8) the law map Theta -> Law(Theta) is 1-Lipschitz from L2(Omega; H)
  into (P2(H), W2), and the next sentence begins (Lemma A.1's own content per the scope note). The
  latest earlier report already read step 2 of the proof of Lemma A.1 and found this the same
  inequality as (2.8), which the proposition states for every pair of square-integrable random
  tuples. The earlier verdict (broader) stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.eq_coupling ed839d34f480cba1bace4ab391e97c18 by=claude-auditor source=A:lemA1:polish@4468f51e4d8fb85e1f6e3d35f1ed7799fb3dbe79faddc1003ff88fca9dc30d5d -->

* `MVFBSDEJ.PaperSpec.lemA1_polish` (added: lines 53–54 and line 56). The latest earlier
  report read lines 53-56 in full ('the law map ... is 1-Lipschitz ... into (P2(H), W2), which
  inherits Polishness from H'); the added lines hold the coupling clause and the start of the next
  sentence, outside this clause. The earlier verdict (faithful with representation choices) stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.lemA1_polish ed839d34f480cba1ad7506f0b0fa0df4 by=claude-auditor source=A:lemA1:polish@4468f51e4d8fb85e1f6e3d35f1ed7799fb3dbe79faddc1003ff88fca9dc30d5d -->

## `A:sec2:difference-notation` (paper/sections/02-model-assumptions.tex, lines 69–84)

* `MVFBSDEJ.Law.lawP2` (added: lines 69–84 (a definition claim rescoped from expository: the
  whole passage)). The whole region (lines 69-84) is new. lawP2 encodes "Law" in the items of the
  passage: the measure component mu = Law(Theta) of a diagonal input (membership in diagonalInputs
  sets it to lawP2 P Theta) and the induced terminal laws rho := Law(X_T), rho' := Law(X'_T) in
  P_2(R^n) (lines 80-81), which LipTerminal and the terminal field of Assumption25 write as lawP2 P
  XT, lawP2 P XT'. Every random element whose law the passage takes is square integrable there
  (Theta in L^2(Omega, F_t; H), X_T in L^2(Omega, F_T; R^n)), and the definitions carry those L^2
  hypotheses, so lawP2 is the image measure P o Theta^{-1} and its junk value delta_0 off L^2 is
  never reached. The earlier verdict, faithful with representation choices (a total function with
  junk off L^2), stands.
  <!-- def-review: MVFBSDEJ.Law.lawP2 ed84cd1114f294f90f45b5f95750d4cf by=claude-auditor source=A:sec2:difference-notation@cc7023eaeddb4fce3219878053990aa52a93f791b1237a293424f653545642ca -->

* `MVFBSDEJ.WellPosedness.Spec.Assumption23` (added: lines 69–84 (a definition claim rescoped
  from expository: the whole passage)). The whole region (lines 69-84) is new; it fixes the notation
  of Assumption 2.3. Assumption23 encodes the assembly of the items Assumption 2.3 uses: L >= 0, the
  interior bound LipInteriorAt for a.e. t in [0, T] (two diagonal inputs at the same t on the
  standing space, delta X and the other channel differences of Theta - Theta', delta psi = psi(t,
  Theta, mu) - psi(t, Theta', mu') for psi in {b, sigma, h, f} with mu, mu' the laws of the inputs),
  and the terminal bound LipTerminal (delta g_T = g(X_T, rho) - g(X'_T, rho') with the induced laws
  rho = Law(X_T), rho' = Law(X'_T)), one L for both. No field varies a measure argument
  independently of its tuple, which is what "all hypotheses below are imposed along D_t only" (lines
  69-70) requires; the theta/Theta convention of lines 70-71 is typographical and is followed
  (coefficients take points, inputs are maps from Omega). The added lines spell out the objects the
  earlier report already read in Assumption 2.3; the earlier verdict, faithful with representation
  choices (L a parameter with the field 0 <= L), stands.
  <!-- def-review: MVFBSDEJ.WellPosedness.Spec.Assumption23 5ad9199da021d4760000000000000000 by=claude-auditor source=A:sec2:difference-notation@cc7023eaeddb4fce3219878053990aa52a93f791b1237a293424f653545642ca -->

* `MVFBSDEJ.WellPosedness.Spec.Assumption25` (added: lines 69–84 (a definition claim rescoped
  from expository: the whole passage)). The whole region (lines 69-84) is new; it fixes the notation
  of Assumption 2.5. Assumption25 encodes the items as Assumption 2.5 uses them: in the field
  terminal, delta g_T = C.g (XT w) (lawP2 P XT) - C.g (XT' w) (lawP2 P XT'), the measure argument of
  g being the induced law rho = Law(X_T) of its own state argument (never free), and delta X_T = XT
  - XT', over all F_T-measurable square-integrable X_T, X'_T as the assumption quantifies them; in
  the field interior, Mono27At for a.e. t in [0, T], i.e. two diagonal inputs at the same t on the
  same space with delta psi and the channel differences of Theta - Theta' through pairing27.
  Constants (and the separate G) involve no measure argument, so the "imposed along D_t only"
  sentence (lines 69-70) is respected; the theta/Theta convention of lines 70-71 is typographical.
  The added lines define exactly the objects the earlier report already compared; its verdict,
  faithful with representation choices (integrability conjuncts, G and the constants as parameters,
  a.e. t for Lebesgue on [0, T]), stands.
  <!-- def-review: MVFBSDEJ.WellPosedness.Spec.Assumption25 a0fc1ba9071e126c0000000000000000 by=claude-auditor source=A:sec2:difference-notation@cc7023eaeddb4fce3219878053990aa52a93f791b1237a293424f653545642ca -->

* `MVFBSDEJ.WellPosedness.Spec.LipInteriorAt` (added: lines 69–84 (a definition claim rescoped
  from expository: the whole passage)). The whole region (lines 69-84) is new. LipInteriorAt encodes
  the items "two diagonal inputs (Theta, mu), (Theta', mu') at the same time t on the same
  probability space" (both p, p' range over diagonalInputs at the one t on the one (Omega, F, P), so
  mu = lawP2 P Theta and mu' = lawP2 P Theta', never free), "delta X := X - X'" with delta Y, delta
  Z, delta U the other channels of Theta(w) - Theta'(w), and "delta psi := psi(t, Theta, mu) -
  psi(t, Theta', mu'), psi in {b, sigma, h, f}" as the random variable w -> C.psi t (Theta w) mu -
  C.psi t (Theta' w) mu', delta h the difference in L^2(nu; R^n) of the values of C.h. Lines 69-71
  (hypotheses only along D_t; lower-case theta a point, upper-case Theta a random tuple) state the
  diagonal quantification and the convention the earlier report already found in the definition.
  Nothing added contradicts or extends the reading; the earlier verdict, faithful, stands.
  <!-- def-review: MVFBSDEJ.WellPosedness.Spec.LipInteriorAt 5ad9199da021d476f2be26fbc20e44ad by=claude-auditor source=A:sec2:difference-notation@cc7023eaeddb4fce3219878053990aa52a93f791b1237a293424f653545642ca -->

* `MVFBSDEJ.WellPosedness.Spec.LipTerminal` (added: lines 69–84 (a definition claim rescoped
  from expository: the whole passage)). The whole region (lines 69-84) is new. LipTerminal encodes
  the items "the induced terminal laws rho := Law(X_T), rho' := Law(X'_T)" and "delta g_T := g(X_T,
  rho) - g(X'_T, rho')" (lines 80-84): its left side is g (XT w) (lawP2 P XT) - g (XT' w) (lawP2 P
  XT'), the law argument always the law in P_2(R^n) of the state argument itself (the L^2 hypotheses
  keep lawP2 off its junk value), so the terminal condition is diagonal as lines 69-70 require. The
  passage introduces X_T, X'_T without a quantifier; Assumption 2.3 quantifies them over L^2(Omega,
  F_T; R^n), which is what the definition takes (strongly F_T-measurable square-integrable maps),
  and the earlier report already read that quantifier. The added lines change nothing; the earlier
  verdict, faithful, stands.
  <!-- def-review: MVFBSDEJ.WellPosedness.Spec.LipTerminal ba56bc4929aee90fc20042d257c95726 by=claude-auditor source=A:sec2:difference-notation@cc7023eaeddb4fce3219878053990aa52a93f791b1237a293424f653545642ca -->

* `MVFBSDEJ.WellPosedness.Spec.Mono27At` (added: lines 69–84 (a definition claim rescoped from
  expository: the whole passage)). The whole region (lines 69-84) is new. Mono27At encodes the items
  "two diagonal inputs (Theta, mu), (Theta', mu') at the same time t on the same probability space"
  (p, p' range over diagonalInputs at one t on one (Omega, F, P), so the measure arguments are the
  laws lawP2 P Theta, lawP2 P Theta', never varied independently, as lines 69-70 require) and the
  differences delta X, delta Y, delta Z, delta U and delta psi, psi in {b, sigma, h, f}, through
  pairing27 evaluated at theta = Theta(w), theta' = Theta'(w) with those laws, and through the
  channel differences in the quadratic terms. The theta/Theta convention of lines 70-71 is followed.
  The added lines define the objects the earlier report already compared in (2.7); its verdict,
  faithful with representation choices (the explicit integrability conjunct of the pairing), stands.
  <!-- def-review: MVFBSDEJ.WellPosedness.Spec.Mono27At f8eb12ff2eed71b8d19f4b54d2691948 by=claude-auditor source=A:sec2:difference-notation@cc7023eaeddb4fce3219878053990aa52a93f791b1237a293424f653545642ca -->

* `MVFBSDEJ.WellPosedness.Spec.pairing27` (added: lines 69–84 (a definition claim rescoped from
  expository: the whole passage)). The whole region (lines 69-84) is new. pairing27 encodes the
  items "delta X := X - X'" (with delta Y, delta Z, delta U the other channels) and "delta psi :=
  psi(t, Theta, mu) - psi(t, Theta', mu'), psi in {b, sigma, h, f}" at two points theta, theta' of H
  with laws mu, mu' at one time t: each term is C.psi t theta mu - C.psi t theta' mu', and the mark
  integral takes delta h(e) and delta U(e) through representatives, which changes the integrand only
  on nu-null sets, so the integral is the L^2(nu) pairing. That it takes points theta (lower case)
  is the convention of lines 70-71; that its laws are free arguments does not vary a measure
  independently in any hypothesis, because its use in (2.7), Mono27At, evaluates it at Theta(w),
  Theta'(w) with mu, mu' the laws of diagonal inputs (lines 69-70). The earlier report read it
  pointwise in exactly this way; its verdict, faithful, stands.
  <!-- def-review: MVFBSDEJ.WellPosedness.Spec.pairing27 3951ca541ad316db35cf5a08ab3dce91 by=claude-auditor source=A:sec2:difference-notation@cc7023eaeddb4fce3219878053990aa52a93f791b1237a293424f653545642ca -->

## `A:sec2:hborel-derivation` (paper/sections/02-model-assumptions.tex, lines 107–110)

* `MVFBSDEJ.PaperSpec.sec2_hborel` (added: lines 108–110). Lines 108–110 complete the sentence
  that the earlier report read (lines 100–110). The hypothesis is joint pointwise measurability of
  (t, θ, e, μ) ↦ h(t, θ, e, μ), the conclusion is (2.3), and Tonelli followed by Pettis is the proof
  route. The proposition takes a jointly measurable H on ([0,T] × H × P₂(H)) × E whose sections
  represent h, and concludes Borel measurability into L²(ν; ℝⁿ). The verdict (faithful with
  representation choices) stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.sec2_hborel ed839d34f480cba15aaf107e33c090c4 by=claude-auditor source=A:sec2:hborel-derivation@8974ddb463b86c2b7de75d6a70740d5ae4b014aeb8b7b59208d0238e8cd4c9f3 -->

## `A:sec2:infinite-activity-atoms` (paper/sections/02-model-assumptions.tex, lines 9–11)

* `MVFBSDEJ.PaperSpec.sec2_infinite_activity` (added: line 9 and line 11). Lines 9 and 11
  frame the relative clause: nu need not be finite, the infinite-activity regime is admitted
  throughout, and nu(E) < infinity is a special instance. This is the standing admission of every
  sigma-finite nu, named by the scope note, and the earlier reading already covered lines 9-11. The
  proposition (nu(E) = infinity implies a.s. N((s, t] x E) = infinity for all 0 <= s < t) is
  unaffected; the earlier verdict (faithful) stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.sec2_infinite_activity ed839d34f480cba13a9f48f6bc72d40f by=claude-auditor source=A:sec2:infinite-activity-atoms@ab13f63a3a45ffb0e21a5d101e35ead9f9fda21d3710c6d5fc3aa9a01a636835 -->

## `A:sec2:prp` (paper/sections/02-model-assumptions.tex, lines 47–56)

* `MVFBSDEJ.PaperSpec.sec2_prp` (added: lines 48–56). The added lines 48-56 complete the
  sentence on the predictable representation property. They give the citations, the passage to the
  initial enlargement by F_0, and the representation M_t = M_0 + int Z dW + int int U dN~ for every
  t in [0,T], with M_0 F_0-measurable and (Z, U) predictable and square integrable, the pair unique
  up to null sets. The earlier reading was of lines 47-56 and compared exactly this, existence and
  uniqueness over the augmented enlarged filtration. The verdict, faithful with representation
  choices, stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.sec2_prp ed839d34f480cba188dfff65b0dcd4e4 by=claude-auditor source=A:sec2:prp@db17ef09e29aaba5ae130b07f16da1d350bfcff9cfd551c68b79000b5b09063d -->

## `A:sec2:separable-L2nu` (paper/sections/02-model-assumptions.tex, lines 2–8)

* `MVFBSDEJ.PaperSpec.sec2_separable` (added: lines 2–5 and 7–8). The added lines 2–5 and 7–8
  print the standing setting: the filtered space with the usual conditions, T, n, m, d, W, and N
  with intensity dt ν(de), together with the augmented filtration. The scope note pins this as the
  setting of every statement, not a claim. The separability of L²(ν; ℝʲ) depends only on ν being
  σ-finite on a countably generated (E, ℰ) and on j ≥ 1, which are exactly the proposition's
  hypotheses. The verdict (faithful) stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.sec2_separable ed839d34f480cba1673cfd9d331f5aa6 by=claude-auditor source=A:sec2:separable-L2nu@90cbae8104b2345566337d2982f21d3bb10b2f024139bb058c19423bb1296d42 -->

## `A:sec2:tuple-notation` (paper/sections/02-model-assumptions.tex, lines 27–45)

* `MVFBSDEJ.Law.lawP2` (added: lines 27–45 (a new definition claim: the whole passage)). The
  whole region (lines 27-45) is new. lawP2 encodes mu_t = Law(Theta_t) and mu_t^- = Law(Theta_t^-)
  (lines 27 and 37), applied to tupleAt of the tuple and of the left-limit tuple. Lines 41-43 add
  that mu and mu^- denote the Borel representatives fixed in Lemma A.1, which agree with the laws
  for a.e. t. The Lean takes lawP2 of the tuple at every time: the image measure when Theta_s is
  square integrable, and the Dirac junk otherwise. That flow is one of the representatives the lemma
  provides. The proposition of Lemma A.1 (lem_lawflow), which has a proof in the acceptance layer,
  states that it is Borel into (P_2(H), W_2) and equals the image measure for a.e. s in [0, T]. Its
  companion lem_lawflow_invariant states that coefficient evaluations do not depend on the
  representative up to dt x dP-null sets. Lines 43-45 (claims are only dt-a.e. or time-integrated)
  are the condition under which the earlier report judged the junk branch harmless. The added lines
  confirm the reading. The verdict, faithful with representation choices, stands.
  <!-- def-review: MVFBSDEJ.Law.lawP2 ed84cd1114f294f90f45b5f95750d4cf by=claude-auditor source=A:sec2:tuple-notation@ab7fbc983e17a5b9235886da443a4e1a98f9283a09fcfb891dc85e6b092fc256 -->

* `MVFBSDEJ.WellPosedness.Existence.coeffJump` (added: lines 27–45 (a new definition claim: the
  whole passage)). The whole region (lines 27-45) is new. coeffJump encodes the jump terms
  "evaluated at the predictable tuple Theta_t^- = (X_{t-}, Y_{t-}, Z_t, U_t), mu_t^- =
  Law(Theta_t^-)" of lines 35-38. coeffJump is generic in the tuple. Applied to (leftLimProc X,
  leftLimProc Y, Z, U), as every proposition passes it (the earlier report checked this, and the
  solution predicate's jump_rep uses the same left-limit tuple), it is a jointly measurable
  representative of h(s, Theta_s^-, ., mu_s^-) at every s in [0, T]. Here mu_s^- is lawP2 of the
  left-limit tuple, a Borel representative of Lemma A.1 (lem_lawflow) as lines 41-43 require. Lines
  43-45 confirm that only a.e. and time-integrated uses matter, so the junk values (uLift 0, the
  Dirac law) are harmless. The verdict, faithful with representation choices, stands.
  <!-- def-review: MVFBSDEJ.WellPosedness.Existence.coeffJump 18400ae9b3362bfb78e13212c01211ec by=claude-auditor source=A:sec2:tuple-notation@ab7fbc983e17a5b9235886da443a4e1a98f9283a09fcfb891dc85e6b092fc256 -->

* `MVFBSDEJ.WellPosedness.System.TupleH` (added: lines 27–45 (a new definition claim: the whole
  passage)). The whole region (lines 27-45) is new. The item TupleH encodes is lines 29-34: Theta_t
  takes values in the Hilbert space H, componentwise X_t in R^n, Y_t in R^m, Z_t in R^{m x d}, U_t
  in L^2(nu; R^m). TupleH is exactly that product in that order (Z on Fin m x Fin d with the
  Euclidean, i.e. Frobenius, norm; U in Lp of R^m-valued maps). "Hilbert" refers to the norm
  |theta|_H^2 = |x|^2 + |y|^2 + |z|_F^2 + ||u||^2 fixed in the introduction. The earlier report
  already read that norm and recorded that TupleH carries the max of the channel norms, with the
  Hilbert norm entering through toL2/w2H and the explicit channel sums where it is used. The passage
  adds nothing about the norm. The other lines (Theta^-, mu, mu^-, the every-t convention) concern
  other definitions. The earlier verdict, faithful with representation choices, stands.
  <!-- def-review: MVFBSDEJ.WellPosedness.System.TupleH fd49e3c7112f415532925681da98a93f by=claude-auditor source=A:sec2:tuple-notation@ab7fbc983e17a5b9235886da443a4e1a98f9283a09fcfb891dc85e6b092fc256 -->

* `MVFBSDEJ.WellPosedness.System.diffusionProc` (added: lines 27–45 (a new definition claim: the
  whole passage)). The whole region (lines 27-45) is new. diffusionProc encodes the expression
  sigma(t, Theta_t, mu_t), one of the "expressions such as b(t, Theta_t, mu_t)" of line 43. It is
  sigma evaluated at every s at tupleAt of the current-time tuple and at lawP2 of that tuple (a
  Borel representative of Lemma A.1 by lem_lawflow), entry (i, j), cut off to 0 off [0, T]. Lines
  44-45 (claims only dt-a.e. or time-integrated) match the earlier finding that only its dt x dP
  class enters. The verdict, faithful with representation choices, stands.
  <!-- def-review: MVFBSDEJ.WellPosedness.System.diffusionProc 2b164a230bfa865bab8693203c4b1ee8 by=claude-auditor source=A:sec2:tuple-notation@ab7fbc983e17a5b9235886da443a4e1a98f9283a09fcfb891dc85e6b092fc256 -->

* `MVFBSDEJ.WellPosedness.System.driftProc` (added: lines 27–45 (a new definition claim: the
  whole passage)). The whole region (lines 27-45) is new. driftProc encodes the expression b(t,
  Theta_t, mu_t) of line 43, "defined at every t". It is b evaluated at every s at tupleAt of the
  current-time tuple (no left limits, as printed) and at lawP2 of that tuple, cut off to 0 off [0,
  T]. That law flow is a Borel representative of Lemma A.1 (lem_lawflow), as lines 41-43 require.
  The convention of lines 44-45, that every claim about such expressions is dt-a.e. or
  time-integrated, is what the earlier report relied on: the process enters only through its dt x dP
  class. The verdict, faithful with representation choices, stands.
  <!-- def-review: MVFBSDEJ.WellPosedness.System.driftProc fb883e117d3ab2fe2788affb6a069047 by=claude-auditor source=A:sec2:tuple-notation@ab7fbc983e17a5b9235886da443a4e1a98f9283a09fcfb891dc85e6b092fc256 -->

* `MVFBSDEJ.WellPosedness.System.driverProc` (added: lines 27–45 (a new definition claim: the
  whole passage)). The whole region (lines 27-45) is new. driverProc encodes the expression f(t,
  Theta_t, mu_t), one of the "expressions such as b(t, Theta_t, mu_t)" of line 43. It is f evaluated
  at every s at tupleAt of the current-time tuple and at lawP2 of that tuple (a Borel representative
  of Lemma A.1 by lem_lawflow), coordinate k, cut off to 0 off [0, T]. Lines 44-45 (claims only
  dt-a.e. or time-integrated) match the earlier finding that only its dt x dP class enters. The
  verdict, faithful with representation choices, stands.
  <!-- def-review: MVFBSDEJ.WellPosedness.System.driverProc 73a119504de32e3e6e17c4225604f734 by=claude-auditor source=A:sec2:tuple-notation@ab7fbc983e17a5b9235886da443a4e1a98f9283a09fcfb891dc85e6b092fc256 -->

* `MVFBSDEJ.WellPosedness.System.leftLimProc` (added: lines 27–45 (a new definition claim: the
  whole passage)). The whole region (lines 27-45) is new. leftLimProc encodes the left limits
  X_{t-}, Y_{t-} in the predictable tuple of lines 35-40. It is the left limit along s < t of each
  path (Function.leftLim), applied to X and Y only, while Z_t and U_t enter tupleAt unchanged ("the
  integrands Z_t, U_t, already predictable, are left untouched"). The passage does not fix X_{0-}.
  The earlier report's points (a fallback value on paths without left limits, and the value at the
  single time 0) concern a Lebesgue-null set of times, and lines 44-45 confirm that the paper reads
  such expressions only dt-a.e. or time-integrated. The verdict, faithful with representation
  choices, stands.
  <!-- def-review: MVFBSDEJ.WellPosedness.System.leftLimProc 9171262935c3b1fde4f555261cd0b9ba by=claude-auditor source=A:sec2:tuple-notation@ab7fbc983e17a5b9235886da443a4e1a98f9283a09fcfb891dc85e6b092fc256 -->

* `MVFBSDEJ.WellPosedness.System.tupleAt` (added: lines 27–45 (a new definition claim: the whole
  passage)). The whole region (lines 27-45) is new. tupleAt encodes the tuple Theta_t = (X_t, Y_t,
  Z_t, U_t) of lines 27 and 29-34: it packs the coordinate processes at the current time s in the
  order x, y, z, u into H, with U_s the L^2(nu) class of e -> U_s(omega, e) (uLift, which is 0 only
  where that map is not square integrable, a dt x dP-null set for finite-energy U). The predictable
  tuple of lines 35-40, Theta_t^- = (X_{t-}, Y_{t-}, Z_t, U_t), is tupleAt applied to (leftLimProc
  X, leftLimProc Y, Z, U), which leaves the Z and U slots untouched as the passage says. Nothing in
  the added lines contradicts the earlier reading. The verdict, faithful with representation
  choices, stands.
  <!-- def-review: MVFBSDEJ.WellPosedness.System.tupleAt 5c7223a86c8e2dcd94922741f04aaf78 by=claude-auditor source=A:sec2:tuple-notation@ab7fbc983e17a5b9235886da443a4e1a98f9283a09fcfb891dc85e6b092fc256 -->

## `A:sec3:HH-banach` (paper/sections/03-main-results.tex, lines 5–32)

* `MVFBSDEJ.PaperSpec.sec3_HH_complete` (added: lines 5–29 and 31–32). The added lines print
  the definitions of S2, H2_W, H2_N, the solution space, its norm and the identification, which the
  earlier locked reading listed item by item and checked against the Lean (adapted cadlag X, Y;
  predictable Z; marked predictable U; supSize); completeness is stated on representatives, the
  identification being the kernel of the seminorm. The earlier verdict (faithful with representation
  choices) stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.sec3_HH_complete ed839d34f480cba105a40fd50a78c129 by=claude-auditor source=A:sec3:HH-banach@551286dac540371b521169b6e6a0e861b596438fd0ab4b196a659438efe4df1d -->

* `MVFBSDEJ.PaperSpec.sec3_HH_definite` (added: lines 5–29 and 31–32). The added lines define
  the spaces, the norm of the solution space and the identification (indistinguishable cadlag
  components, Z equal dt x dP-a.e., U equal dt x dP x nu-a.e.), which the earlier reading used
  verbatim: the proposition says the norm vanishes iff X, Y are indistinguishable from 0 on [0, T],
  Z = 0 dt x dP-a.e. and U = 0 dt x dP x nu-a.e., for every tuple of the weak class. The earlier
  verdict (broader, the solution space being the instance) stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.sec3_HH_definite ed839d34f480cba1ea08606483b8ce0f by=claude-auditor source=A:sec3:HH-banach@551286dac540371b521169b6e6a0e861b596438fd0ab4b196a659438efe4df1d -->

* `MVFBSDEJ.PaperSpec.sec3_HH_inclusion` (added: lines 5–29 and 31–32). Lines 5-29 and 31-32
  print the definitions of L2_ad, S2, H2_W, H2_N, the solution space, the weak class, the norm and
  the identification, and the inclusion sentence itself; the earlier reading already used exactly
  these definitions (X, Y of the weak class cadlag adapted with E int |.|^2 < infinity) and found E
  int |V|^2 <= T E sup |V|^2 and the finite energy of each coordinate stated. The earlier verdict
  (faithful) stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.sec3_HH_inclusion ed839d34f480cba13d9a37898844e038 by=claude-auditor source=A:sec3:HH-banach@551286dac540371b521169b6e6a0e861b596438fd0ab4b196a659438efe4df1d -->

* `MVFBSDEJ.PaperSpec.sec3_HH_norm` (added: lines 5–29 and 31–32). The earlier reading already
  covered lines 4-32; the added lines are the definitions of the spaces, of the norm (Euclidean,
  Frobenius and L2(nu) norms in an l2 combination) and of the identification, all matched by supSize
  and PaperWeakTuple. The earlier verdict (broader: the weak class as domain, an extended-valued
  norm) stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.sec3_HH_norm ed839d34f480cba1982fd9e7618d6f99 by=claude-auditor source=A:sec3:HH-banach@551286dac540371b521169b6e6a0e861b596438fd0ab4b196a659438efe4df1d -->

## `A:sec3:margin-paragraph` (paper/sections/03-main-results.tex, lines 280–290)

* `MVFBSDEJ.PaperSpec.cor_margin_additive` (added: lines 281–290). Lines 282–283, 'When ν ≠ 0,
  an additive h₀ = h₀(t,x,e) therefore cannot serve as a baseline', are this clause: with ν ≠ 0 and
  h depending on (t, x) only, (2.13) fails for every β₁ ≥ 0, every β₂ and every c > 0. The other
  added lines are the remaining clauses of the claim, or examples named in the scope note. The
  earlier report read the same sentences, and its verdict (broader; instantiation m = n, G of full
  rank, β₁, β₂ ≥ 0) stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.cor_margin_additive ed839d34f480cba1f6b25342c98f12fe by=claude-auditor source=A:sec3:margin-paragraph@23dc0984d55a23cd584d56a864ed5056b9fb123935603b3cc75fbe8fccdf422d -->

* `MVFBSDEJ.PaperSpec.cor_margin_channels` (added: lines 281–290). The added lines 281–290
  complete the paragraph after Corollary 3.6, which the earlier report read in full. Lines 280–282
  (a margin in (2.13) forces every channel of the baseline to be strictly dissipative) are this
  clause, stated for all four channels with the full right-hand side. 'A margin then needs feedback
  dissipative on the whole of L²(ν)' is its jump-channel conjunct. Lines 282–290 are otherwise the
  other clauses of the claim, and the example references are named in the scope note. The verdict
  (broader; instantiation c > 0, β₁, β₂ ≥ 0, m = n, G of full rank) stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.cor_margin_channels ed839d34f480cba1ad6475a2826a7556 by=claude-auditor source=A:sec3:margin-paragraph@23dc0984d55a23cd584d56a864ed5056b9fb123935603b3cc75fbe8fccdf422d -->

* `MVFBSDEJ.PaperSpec.cor_margin_continuous` (added: lines 281–290). Lines 283–288 are the
  sentence the earlier report read, in its general reading: with L²(ν) infinite-dimensional, jump
  feedback entering through finitely many continuous, possibly nonlinear, functionals of u, with any
  law dependence, supplies no margin. The proposition states this as ¬(2.13) for all β₁ ≥ 0, all β₂
  and all c > 0. The other added lines are the remaining clauses or are named in the scope note. The
  verdict (broader; instantiation m = n, G of full rank, β₁, β₂ ≥ 0, F_t independent of t) stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.cor_margin_continuous ed839d34f480cba1bb8184bafca01d3f by=claude-auditor source=A:sec3:margin-paragraph@23dc0984d55a23cd584d56a864ed5056b9fb123935603b3cc75fbe8fccdf422d -->

* `MVFBSDEJ.PaperSpec.cor_margin_findim` (added: lines 281–290). Lines 288–290, 'if L²(ν) is
  finite-dimensional, finitely many functionals can determine u and the second obstruction
  disappears', are this clause, which the earlier report read. The proposition gives an injective
  linear ℓ and the system of Example 5.1(i) satisfying (2.13) with margin c, for every such ν. 'As
  when ν is carried by finitely many atoms' is an example of its hypothesis, named in the scope
  note. The other added lines are the remaining clauses. The verdict (faithful) stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.cor_margin_findim ed839d34f480cba1271f1706f481bec3 by=claude-auditor source=A:sec3:margin-paragraph@23dc0984d55a23cd584d56a864ed5056b9fb123935603b3cc75fbe8fccdf422d -->

* `MVFBSDEJ.PaperSpec.cor_margin_finite` (added: lines 281–290). Lines 283–288 are the
  sentence the earlier report read: with L²(ν) infinite-dimensional, feedback through finitely many
  functionals of u supplies no margin, since finitely many continuous functionals cannot separate
  points, and a margin then needs feedback dissipative on the whole of L²(ν). This clause is its
  linear reading. The nonlinear, law-dependent reading is cor_margin_continuous, the separation fact
  is cor_margin_separate, and the 'whole of L²(ν)' consequence is the jump-channel conjunct of
  cor_margin_channels. The other added lines are the remaining clauses or are named in the scope
  note. The verdict (broader than the linear, law-free reading) stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.cor_margin_finite ed839d34f480cba1e2a2c92114efd4a4 by=claude-auditor source=A:sec3:margin-paragraph@23dc0984d55a23cd584d56a864ed5056b9fb123935603b3cc75fbe8fccdf422d -->

* `MVFBSDEJ.PaperSpec.cor_margin_separate` (added: lines 281–290). Lines 285–286, 'finitely
  many continuous functionals cannot separate the points of an infinite-dimensional space', are this
  proposition: every continuous F : H → ℝᵏ on an infinite-dimensional real normed space fails to be
  injective. The earlier report read the paragraph through its end. The other added lines are the
  remaining clauses or examples named in the scope note. The verdict (faithful) stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.cor_margin_separate ed839d34f480cba1b90f9a7b02bff832 by=claude-auditor source=A:sec3:margin-paragraph@23dc0984d55a23cd584d56a864ed5056b9fb123935603b3cc75fbe8fccdf422d -->

## `A:sec3:one-null-set` (paper/sections/03-main-results.tex, lines 34–37)

* `MVFBSDEJ.PaperSpec.sec3_cadlag_versions` (added: lines 34–36). The added lines 34-36 print
  the definition of a solution: a tuple of the strong space satisfying both identities of (1.1) a.s.
  for every t, with h at the predictable tuple. The scope note pins it here, and the earlier reading
  already quoted it and used it as the instance. The proposition gives adapted, every-path cadlag
  versions of the four stochastic integrals of (1.1) along any H_weak tuple whose integrals exist,
  with arbitrary coefficients. The earlier verdict, broader (instance: a solution), stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.sec3_cadlag_versions ed839d34f480cba1dfafad3c01dd9c62 by=claude-auditor source=A:sec3:one-null-set@50a645fe0ae55998cb3c0ee4547c990dc06667c7e43810173776909d6022b341 -->

* `MVFBSDEJ.PaperSpec.sec3_one_null_set` (added: lines 34–36). The added lines 34-36 print the
  solution notion (a tuple of the strong space, both identities a.s. for every t, h at the
  predictable tuple). The scope note pins it here, and the earlier reading already took it as the
  setting of the clause. The proposition's equivalence ('for every t, a.s.' iff 'a.s., for all t')
  covers that setting as an instance. The earlier verdict, broader, stands: H_weak tuples with the
  integrals existing, any coefficients, and any a.s. right-continuous M in place of the cadlag
  version of the Ito integral.
  <!-- spec-review: MVFBSDEJ.PaperSpec.sec3_one_null_set ed839d34f480cba138f9fd9e89c0b6c3 by=claude-auditor source=A:sec3:one-null-set@50a645fe0ae55998cb3c0ee4547c990dc06667c7e43810173776909d6022b341 -->

## `A:sec3:two-system-notation` (paper/sections/03-main-results.tex, lines 39–49)

* `MVFBSDEJ.Law.lawP2` (added: lines 39–49 (a new definition claim: the whole passage)). The
  whole region (lines 39-49) is new. lawP2 encodes mu^k_t := Law(Theta^k_t) (line 41), the law
  mu^{2,-}_t of the predictable tuple (line 46) and Law(X^2_T) in the hat-delta g_T (line 47). Each
  is lawP2 of the corresponding tupleAt or of X^2_T. That is the image measure for square-integrable
  arguments, which holds for a.e. t and at T for solutions in H, and the flow in t is a Borel
  representative of Lemma A.1 (lem_lawflow), so it agrees with the section 2 reading of mu. The
  verdict, faithful with representation choices, stands.
  <!-- def-review: MVFBSDEJ.Law.lawP2 ed84cd1114f294f90f45b5f95750d4cf by=claude-auditor source=A:sec3:two-system-notation@a3362603389cfff07f713ce49fedd731d218672220d998b1975cf2bdc3a128d6 -->

* `MVFBSDEJ.WellPosedness.Existence.coeffJump` (added: lines 39–49 (a new definition claim: the
  whole passage)). The whole region (lines 39-49) is new. coeffJump encodes the terms of (delta
  h)(t) := h^1(t, Theta^{2,-}_t, ., mu^{2,-}_t) - h^2(t, Theta^{2,-}_t, ., mu^{2,-}_t) (line 46).
  The propositions take coeffJump of system k at (leftLimProc X^2, leftLimProc Y^2, Z^2, U^2) for k
  = 1, 2. That is a jointly measurable representative of h^k at the predictable tuple of solution 2
  and at its law lawP2 = mu^{2,-}_s, the same argument for both systems, as printed. The L^2(nu)
  class of the difference of the two representatives is h^1 - h^2 at that point. Lines 39-40 are
  exposition. The verdict, faithful with representation choices, stands.
  <!-- def-review: MVFBSDEJ.WellPosedness.Existence.coeffJump 18400ae9b3362bfb78e13212c01211ec by=claude-auditor source=A:sec3:two-system-notation@a3362603389cfff07f713ce49fedd731d218672220d998b1975cf2bdc3a128d6 -->

* `MVFBSDEJ.WellPosedness.System.diffusionProc` (added: lines 39–49 (a new definition claim: the
  whole passage)). The whole region (lines 39-49) is new. diffusionProc encodes the terms of (delta
  sigma)(t) := sigma^1(t, Theta^2_t, mu^2_t) - sigma^2(t, Theta^2_t, mu^2_t) (line 44, psi = sigma).
  The propositions take diffusionProc of system 1 minus that of system 2, both at the coordinates of
  solution 2. Each is sigma^k at tupleAt of Theta^2 and its law lawP2 = mu^2_s (line 41). The
  Frobenius norm of the difference is taken in the propositions. Lines 39-40 are exposition. The
  verdict, faithful with representation choices, stands.
  <!-- def-review: MVFBSDEJ.WellPosedness.System.diffusionProc 2b164a230bfa865bab8693203c4b1ee8 by=claude-auditor source=A:sec3:two-system-notation@a3362603389cfff07f713ce49fedd731d218672220d998b1975cf2bdc3a128d6 -->

* `MVFBSDEJ.WellPosedness.System.driftProc` (added: lines 39–49 (a new definition claim: the
  whole passage)). The whole region (lines 39-49) is new. driftProc encodes the terms of (delta
  psi)(t) := psi^1(t, Theta^2_t, mu^2_t) - psi^2(t, Theta^2_t, mu^2_t) for psi = b (line 44). The
  propositions take driftProc of system 1 minus driftProc of system 2, both at the coordinates of
  solution 2. Each is b^k evaluated at tupleAt of Theta^2 at time s and at lawP2 of that tuple,
  which is mu^2_s := Law(Theta^2_s) (line 41). So both systems are evaluated at the same point of
  solution 2, as printed. Lines 39-40 are exposition and do not bear on the definition. The verdict,
  faithful with representation choices, stands.
  <!-- def-review: MVFBSDEJ.WellPosedness.System.driftProc fb883e117d3ab2fe2788affb6a069047 by=claude-auditor source=A:sec3:two-system-notation@a3362603389cfff07f713ce49fedd731d218672220d998b1975cf2bdc3a128d6 -->

* `MVFBSDEJ.WellPosedness.System.driverProc` (added: lines 39–49 (a new definition claim: the
  whole passage)). The whole region (lines 39-49) is new. driverProc encodes the terms of (delta
  f)(t) := f^1(t, Theta^2_t, mu^2_t) - f^2(t, Theta^2_t, mu^2_t) (line 44, psi = f). The
  propositions take driverProc of system 1 minus that of system 2, both at the coordinates of
  solution 2. Each is f^k at tupleAt of Theta^2 and its law lawP2 = mu^2_s (line 41). Lines 39-40
  are exposition. The verdict, faithful with representation choices, stands.
  <!-- def-review: MVFBSDEJ.WellPosedness.System.driverProc 73a119504de32e3e6e17c4225604f734 by=claude-auditor source=A:sec3:two-system-notation@a3362603389cfff07f713ce49fedd731d218672220d998b1975cf2bdc3a128d6 -->

* `MVFBSDEJ.WellPosedness.System.jumpProc` (added: lines 39–49 (a new definition claim: the
  whole passage)). The whole region (lines 39-49) is new. jumpProc is the cut-off to [0, T] of a
  supplied pointwise jump integrand. In this notation it wraps the two representatives coeffJump of
  systems 1 and 2 at the predictable tuple of solution 2. The propositions' difference of the two
  jumpProc terms is therefore, on [0, T], a representative of (delta h)(t) = h^1(t, Theta^{2,-}_t,
  ., mu^{2,-}_t) - h^2(t, Theta^{2,-}_t, ., mu^{2,-}_t) of line 46, and 0 off [0, T], where (3.1)
  does not look. The evaluation point is supplied by the argument, as the earlier report found. The
  verdict, faithful with representation choices, stands.
  <!-- def-review: MVFBSDEJ.WellPosedness.System.jumpProc bfa4317d32adaf7b2cab0921e18838d1 by=claude-auditor source=A:sec3:two-system-notation@a3362603389cfff07f713ce49fedd731d218672220d998b1975cf2bdc3a128d6 -->

* `MVFBSDEJ.WellPosedness.System.leftLimProc` (added: lines 39–49 (a new definition claim: the
  whole passage)). The whole region (lines 39-49) is new. leftLimProc encodes the left limits
  X^2_{t-}, Y^2_{t-} in the predictable tuple Theta^{2,-}_t at which delta h is evaluated (line 46).
  The propositions pass leftLimProc X^2 and leftLimProc Y^2 with Z^2, U^2 unchanged to coeffJump of
  both systems. The earlier report's remarks (the value at the single time 0, the fallback on paths
  without left limits) concern a Lebesgue-null set of times, which the time-integrated delta h term
  does not see. The verdict, faithful with representation choices, stands.
  <!-- def-review: MVFBSDEJ.WellPosedness.System.leftLimProc 9171262935c3b1fde4f555261cd0b9ba by=claude-auditor source=A:sec3:two-system-notation@a3362603389cfff07f713ce49fedd731d218672220d998b1975cf2bdc3a128d6 -->

* `MVFBSDEJ.WellPosedness.System.terminalVal` (added: lines 39–49 (a new definition claim: the
  whole passage)). The whole region (lines 39-49) is new. terminalVal encodes the terms of the
  hat-delta g_T := g^1(X^2_T, Law(X^2_T)) - g^2(X^2_T, Law(X^2_T)) of line 47. The propositions take
  terminalVal of system 1 minus that of system 2, both at X^2. Each is g^k at the value of X^2 at
  the horizon T and at lawP2 of X^2_T, the induced law of solution 2's terminal state. The same
  argument enters for both systems, as printed. The junk law is reached only if X^2_T is not square
  integrable, which solutions in the space H exclude. The verdict, faithful with representation
  choices, stands.
  <!-- def-review: MVFBSDEJ.WellPosedness.System.terminalVal 0c1ad34f7c8c5cdbe0cc1f1dfea8adf8 by=claude-auditor source=A:sec3:two-system-notation@a3362603389cfff07f713ce49fedd731d218672220d998b1975cf2bdc3a128d6 -->

* `MVFBSDEJ.WellPosedness.System.tupleAt` (added: lines 39–49 (a new definition claim: the whole
  passage)). The whole region (lines 39-49) is new. tupleAt encodes the tuples Theta^2_t (line 44)
  and Theta^{2,-}_t (line 46) of solution 2, and Theta^k_t in mu^k_t := Law(Theta^k_t) (line 41).
  The propositions use tupleAt of solution 2's coordinates at time s, and tupleAt of (leftLimProc
  X^2, leftLimProc Y^2, Z^2, U^2) for the predictable tuple, inside driftProc, diffusionProc,
  driverProc and coeffJump. This is the tuple and the predictable tuple as fixed in section 2. The
  verdict, faithful with representation choices, stands.
  <!-- def-review: MVFBSDEJ.WellPosedness.System.tupleAt 5c7223a86c8e2dcd94922741f04aaf78 by=claude-auditor source=A:sec3:two-system-notation@a3362603389cfff07f713ce49fedd731d218672220d998b1975cf2bdc3a128d6 -->

## `A:sec4:WP-def` (paper/sections/04-proof-wellposedness.tex, lines 39–70)

* `MVFBSDEJ.PaperSpec.WP` (added: lines 39–65 and 67–70). Lines 39-65 print the forcing class
  (q^b, q^sigma, q^f progressive, q^h predictable and P x E-measurable, all square-integrable, q^g_T
  in L2(F_T)) and the lambda-forced system (4.1); lines 67-70 finish the definition and give the
  plan of the proof (scope note). The earlier reading compared WP against exactly that forcing class
  and the identification of the solution space. The earlier verdict (faithful with representation
  choices) stands.
  <!-- def-review: MVFBSDEJ.PaperSpec.WP 839d627ccda37855ed1ac20fb346a349 by=claude-auditor source=A:sec4:WP-def@7a46d2596d9c1ba2c84b823eceaf0f8c0f3e90b8af99f5f252c9fad34e87413c -->

* `MVFBSDEJ.PaperSpec.WeakForcedSolution` (added: lines 39–65 and 67–70). The added lines
  print (4.1), with lambda on b, sigma, h, f, g, the forcings unscaled and h at the predictable
  tuple, and the forcing class; the earlier reading compared the definition with that display term
  by term, including its forcing field whose q^h is only marked progressive (predictability is
  supplied by PredForcing where WP and Lemma 4.3 quantify). The earlier verdict (faithful with
  representation choices) stands.
  <!-- def-review: MVFBSDEJ.PaperSpec.WeakForcedSolution bde81c401c9ac90991383a009c3a500d by=claude-auditor source=A:sec4:WP-def@7a46d2596d9c1ba2c84b823eceaf0f8c0f3e90b8af99f5f252c9fad34e87413c -->

## `A:sec4:coeffint` (paper/sections/04-proof-wellposedness.tex, lines 72–85)

* `MVFBSDEJ.PaperSpec.eq_coeffint` (added: line 72 and 74–85). The added lines are the rest of
  the passage that the earlier report quoted. Line 72 reads 'By Assumptions 2.2–2.3, the coefficient
  processes (2.5) along any Θ ∈ ℍ', and old line 73 continues 'are square-integrable'. The lines
  then print (4.2), with its justification (the Lipschitz bound and (2.8) at μ′ = δ₀), and (4.3),
  the clause eq_termg. The proposition states (4.2) with K(L) chosen first, under the interior
  Lipschitz bound only. At the instance (Θ ∈ ℍ, origin values in L² by Assumption 2.2) the right
  side of (4.2) is finite, which gives the square integrability the colon introduces, as the earlier
  report recorded. The verdict (broader) stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.eq_coeffint ed839d34f480cba133ce0e119f63091f by=claude-auditor source=A:sec4:coeffint@9b4835a09d4a96730317d9a3f110c73d021c07f2818d46167bfef20bf557a734 -->

* `MVFBSDEJ.PaperSpec.eq_termg` (added: line 72 and 74–85). The added lines 81–85 print (4.3)
  and its justification ((2.6) with (2.9)), the content the earlier report compared. The proposition
  states 𝔼|g(X_T, Law X_T)|² ≤ K(L)(𝔼|X_T|² + |g(0, δ₀)|²) for every ℱ_T-measurable,
  square-integrable X_T under the terminal bound (2.6), with K(L) chosen first, which is within the
  constant convention of §4. The added lines before it are (4.2), the clause eq_coeffint. The
  verdict (broader: g not required Borel, any filtered space) stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.eq_termg ed839d34f480cba12450d1561dfcb469 by=claude-auditor source=A:sec4:coeffint@9b4835a09d4a96730317d9a3f110c73d021c07f2818d46167bfef20bf557a734 -->

## `A:sec4:horizon-not-contractive` (paper/sections/04-proof-wellposedness.tex, lines 12–15)

* `MVFBSDEJ.PaperSpec.sec4_horizon_not_contractive` (added: line 12 and 14–15). Line 12 ends
  the sentence on the mixed G-energy identity (exposition) and says the continuation is in the
  coupling strength, a description of the proof; lines 14-15 give the reason ('the (z,u)-dependence
  ... no T-factor'), which the scope note records as explanation and the earlier reading already
  read as motivation. The proposition (on every horizon, an Example 5.1(i) system satisfying the
  assumptions whose frozen map at lambda = 1 does not decrease the distance of a trial from 0) is
  unaffected; the earlier verdict (faithful with representation choices) stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.sec4_horizon_not_contractive ed839d34f480cba13e2b5c030bd07fe9 by=claude-auditor source=A:sec4:horizon-not-contractive@db97ce8829bc98255bc1f6086bcedce457887bbe8d9dadbdf18ce129991aa390 -->

## `A:sec4:proof-thm35` (paper/sections/04-proof-wellposedness.tex, lines 942–951)

* `MVFBSDEJ.PaperSpec.sec45_proof_thm35` (added: lines 942–947 and 949–951). The added lines
  942-947 and 949-951 complete the proof in Section 4.5: WP on [0, lambda*] by Lemma 4.2; lambda_k =
  min{lambda* + k zeta0, 1} with lambda_0 = lambda*, lambda_{k+1} - lambda_k <= zeta0 and lambda_k =
  1 from ceil((1 - lambda*)/zeta0) on; Lemma 4.4 carrying WP(lambda_k) to WP(lambda_{k+1}); WP(1);
  and q = 0 giving a unique solution in the strong space. The earlier report read lines 939-952 and
  compared each conjunct, the last through thm_cwp. The verdict, faithful with representation
  choices, stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.sec45_proof_thm35 ed839d34f480cba18b94aa7805f1b2b0 by=claude-auditor source=A:sec4:proof-thm35@b2ec171b301f7adcfcd1839bdf9f892a2d35c3e631135d347dc9506cdf473a56 -->

* `MVFBSDEJ.PaperSpec.thm_cwp` (added: lines 942–947 and 949–951). The added line 950-951
  ('taking q = 0 there gives a unique solution of (1.1) in the strong space') is exactly what
  thm_cwp concludes, under the hypotheses of Theorem 3.5 that are in force in Section 4.5. The other
  added lines are the continuation steps of the clause sec45_proof_thm35. The latest earlier report
  read Section 4.5, this sentence included. The verdict, faithful with representation choices,
  stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.thm_cwp ed839d34f480cba12370b493940a6d61 by=claude-auditor source=A:sec4:proof-thm35@b2ec171b301f7adcfcd1839bdf9f892a2d35c3e631135d347dc9506cdf473a56 -->

## `A:sec4:supremum-criterion` (paper/sections/04-proof-wellposedness.tex, lines 17–37)

* `MVFBSDEJ.PaperSpec.sec4_supremum_criterion` (added: lines 17–34). The added lines 17-34 are
  the standing conventions of Section 4: X_t, Y_t are not distinguished from their left limits
  inside dt-integrals; the convention on constants; Ito's formula is cited; BDG at p = 1 and p = 2
  with one universal c_BDG, valid for cadlag local martingales. The scope note names each as a
  convention or cited work, and none enters the criterion. The criterion states that a cadlag local
  martingale with integrable running supremum has zero-mean increments. The earlier verdict,
  faithful with representation choices, stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.sec4_supremum_criterion ed839d34f480cba1f588c2071f5242ff by=claude-auditor source=A:sec4:supremum-criterion@dfbd28b0a591b82703f11cc1929876e5b2383e0b09afa7d4ae6331ec55b792a3 -->

## `A:sec4:uniqueness-along-homotopy` (paper/sections/04-proof-wellposedness.tex, lines 875–878)

* `MVFBSDEJ.PaperSpec.sec4_uniq_homotopy` (added: lines 876–878). Lines 876–878 complete the
  sentence that the earlier report read in full (lines 875–878). Lemma 4.3 at lower bound λ* gives
  uniqueness at each λ ∈ [λ*, 1], and Lemma 4.2 gives it on [0, λ*]. 'It remains to prove existence
  up to λ = 1' is exposition, as the scope note says. The proposition states uniqueness on both
  intervals under (2.3) and Assumptions 2.2–2.5, with λ* = λ*(T, L) ∈ (0, 1]. The verdict (faithful
  with representation choices) stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.sec4_uniq_homotopy ed839d34f480cba1f816b3d41c1d4166 by=claude-auditor source=A:sec4:uniqueness-along-homotopy@c905216fdc8aa89607a10094617e291d697687be2ee987671adc2fdfc0e4c6a0 -->

## `A:sec5:overview` (paper/sections/05-examples.tex, lines 9–22)

* `MVFBSDEJ.PaperSpec.ex_brownian` (added: line 9 and 11–22). Lines 13-14 print the sentence
  the earlier reading already took for this clause ('Examples 5.2 and 5.3 recover the Brownian and
  the expectation-functional subclasses as special cases'); its identification with the class of
  [BYZ] is a statement about cited work by the scope note. The rest of the added lines concern
  exposition, other examples, or nu != 0 for Examples 5.4-5.5 (Example 5.2 is the case nu = 0). The
  earlier verdict (faithful with representation choices: the nu = 0 identifications of the
  filtration, the fibre and W2, and the m < n rank branch) stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.ex_brownian ed839d34f480cba1549e88774dfe4a71 by=claude-auditor source=A:sec5:overview@8e465cf926145c437fd799ed11d7a0aaaa89f28e2b5f5562f8ceedf17465af52 -->

* `MVFBSDEJ.PaperSpec.ex_brownian_reduction` (added: line 9 and 11–22). Lines 13-14 add the
  overview sentence that Example 5.2 recovers the Brownian subclass as a special case. The
  proposition states that at nu = 0 Assumptions 2.3 and 2.5 and the solution notions (in the
  solution space and in the weak class) are equivalent to their Brownian forms, which is that class
  inclusion; the attribution to [BYZ] is cited work per the scope note. Nothing else in lines 9 and
  11-22 bears on Example 5.2. The earlier verdict (faithful with representation choices) stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.ex_brownian_reduction ed839d34f480cba160cc15ad2ee3a619 by=claude-auditor source=A:sec5:overview@8e465cf926145c437fd799ed11d7a0aaaa89f28e2b5f5562f8ceedf17465af52 -->

* `MVFBSDEJ.PaperSpec.ex_concrete_i` (added: line 9 and 11–22). Lines 9 and 11-22 add the
  expository opening sentence, the overview of Examples 5.2-5.5 and the standing nu != 0 of Examples
  5.4-5.5 (which does not bind Example 5.1). The lines bearing on this clause, 11-12, call Example
  5.1(i) a law-free affine dissipative model 'meeting every assumption exactly, ... at arbitrary
  jump activity', which is what the proposition states: (2.3) and Assumptions 2.2-2.5 for the affine
  coefficients, with L = max{beta1, beta2, 1}, G = 1, alpha = 1, for every sigma-finite nu.
  'Exactly' reads as 'directly, not perturbatively' (the remark on expected diagonal monotonicity in
  section 2 contrasts Example 5.1(i), which verifies Assumption 2.5 exactly, with Example 5.4, which
  does so perturbatively); the equality of the pairings is a clause of Example 5.1 itself
  (ex_concrete_i_pairing), not of this overview. The earlier verdict (faithful) stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.ex_concrete_i ed839d34f480cba18c5c46dad71ae633 by=claude-auditor source=A:sec5:overview@8e465cf926145c437fd799ed11d7a0aaaa89f28e2b5f5562f8ceedf17465af52 -->

* `MVFBSDEJ.PaperSpec.ex_concrete_ii` (added: line 9 and 11–22). Lines 11-12 say that Example
  5.1(ii), the mean-field model, meets every assumption exactly at arbitrary jump activity; the
  proposition states (2.3), the vanishing origin values and Assumptions 2.2-2.5 with L = 2, G = 1,
  alpha = beta1 = beta2 = 2, for every sigma-finite nu. Its interior pairing is strictly below the
  bound (extra mean-square terms), so 'exactly' can only mean 'directly, not through a
  perturbation', which is what the proposition gives. The other added lines concern exposition,
  other examples, or the nu != 0 of Examples 5.4-5.5. The earlier verdict (faithful) stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.ex_concrete_ii ed839d34f480cba15cf7f3328c0ad0e6 by=claude-auditor source=A:sec5:overview@8e465cf926145c437fd799ed11d7a0aaaa89f28e2b5f5562f8ceedf17465af52 -->

* `MVFBSDEJ.PaperSpec.ex_dealer_active` (added: line 9 and 11–22). Line 21 ('in an explicit
  specialisation the interaction is active along the solution') is what the proposition states at
  the printed specialisation (beta1 = 1, beta2 = 1/2, sigma_c = 1, xi0 = 0, the dealer marks with
  nu(E) = infinity, h_c = sign*size, h_x = size): the crowding correction is nonzero with positive
  probability along the eps = 0 solution, and E int ||eps A||^2 dt > 0 for every solution at eps >
  0. That specialisation has nu != 0, as line 22 requires. The earlier verdict (faithful) stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.ex_dealer_active ed839d34f480cba1a2ecf4542b86cf40 by=claude-auditor source=A:sec5:overview@8e465cf926145c437fd799ed11d7a0aaaa89f28e2b5f5562f8ceedf17465af52 -->

* `MVFBSDEJ.PaperSpec.ex_dealer_mono` (added: line 9 and 11–22). Lines 17-21 describe Example
  5.5 as a non-perturbative full U-law dealer market whose U-law enters the jump response 'through a
  monotone crowding operator, so that well-posedness holds at every interaction strength', and line
  22 takes nu != 0. The proposition states the crowding monotonicity along diagonal pairs and
  Assumption 2.5 with alpha = 1, beta1, beta2 for every eps >= 0 (no smallness, the
  'non-perturbative' content), for every sigma-finite nu, nu != 0 being the instance the earlier
  report already recorded. The market description (population law on valuation curves) is modelling
  per the scope note. The earlier verdict (broader) stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.ex_dealer_mono ed839d34f480cba18bebeea12a1b6e30 by=claude-auditor source=A:sec5:overview@8e465cf926145c437fd799ed11d7a0aaaa89f28e2b5f5562f8ceedf17465af52 -->

* `MVFBSDEJ.PaperSpec.ex_dealer_wp` (added: line 9 and 11–22). Lines 17-21 add 'well-posedness
  holds at every interaction strength', which is the proposition (existence and uniqueness in the
  solution space for every eps >= 0 and every h_x); line 22's nu != 0 is the instantiation the
  earlier report recorded (the proposition allows every sigma-finite nu). The rest is modelling
  (scope note) or other examples. The earlier verdict (broader) stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.ex_dealer_wp ed839d34f480cba1169a2b8090bb4149 by=claude-auditor source=A:sec5:overview@8e465cf926145c437fd799ed11d7a0aaaa89f28e2b5f5562f8ceedf17465af52 -->

* `MVFBSDEJ.PaperSpec.ex_expfunc` (added: line 9 and 11–22). Lines 13-14 add the overview
  sentence that Example 5.3 recovers the expectation-functional subclass as a special case, the
  sentence the earlier reading already took for this clause. The proposition states that mu -> int
  phibar(t, theta, theta') mu(dtheta') with phibar Lipschitz satisfies the law component of
  Assumption 2.3 with constant Lip(phibar), i.e. the class lies inside the theory; the
  identification with the class of [LiMin] is cited work per the scope note. The earlier verdict
  (faithful with representation choices) stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.ex_expfunc ed839d34f480cba15a6f123acd31afd5 by=claude-auditor source=A:sec5:overview@8e465cf926145c437fd799ed11d7a0aaaa89f28e2b5f5562f8ceedf17465af52 -->

* `MVFBSDEJ.PaperSpec.ex_expfunc_limin` (added: line 9 and 11–22). Lines 13-14 add that
  Example 5.3 recovers the expectation-functional subclass of [LiMin] as a special case. The
  proposition states the embedding of the finite-activity two-point kernels psibar of their drift,
  diffusion and driver (integrability, the Lipschitz bound with constant Lip(psibar) max{nu(E),
  nu(E)^{1/2}}, independence of representatives), which is that inclusion; the identification with
  their subclass is cited work per the scope note, and the added lines impose nothing the (broader)
  proposition lacks. The earlier verdict (broader) stands. Observation: the Nemytskii embedding of
  their jump coefficient is a separate clause of Example 5.3 (ex_expfunc_jump) not listed under this
  overview; under the scope note it falls within the cited-work identification.
  <!-- spec-review: MVFBSDEJ.PaperSpec.ex_expfunc_limin ed839d34f480cba1f28bceb8fea3e945 by=claude-auditor source=A:sec5:overview@8e465cf926145c437fd799ed11d7a0aaaa89f28e2b5f5562f8ceedf17465af52 -->

* `MVFBSDEJ.PaperSpec.ex_fulllaw_beyond_U_corr` (added: line 9 and 11–22). The latest earlier
  report already read lines 15-16 and line 22. The hypothesis L2(nu; R^m) != {0} is exactly the nu
  != 0 that line 22 puts in force for Example 5.4 (m >= 1, nu sigma-finite), and the conclusion,
  that the U-marginal radial statistics are no expectation functionals, is the 'of the jump
  integrand' half of lines 15-16. The earlier verdict (broader) stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.ex_fulllaw_beyond_U_corr ed839d34f480cba10f66e794dcb439f4 by=claude-auditor source=A:sec5:overview@8e465cf926145c437fd799ed11d7a0aaaa89f28e2b5f5562f8ceedf17465af52 -->

* `MVFBSDEJ.PaperSpec.ex_fulllaw_beyond_radial` (added: line 9 and 11–22). Lines 15-16
  ('carries the law dependence beyond those subclasses, to genuinely nonlinear functionals of the
  full tuple and of the jump integrand') and line 22 (nu != 0 in Examples 5.4-5.5) were already
  quoted and read in the latest earlier report. The proposition states that the full-tuple radial
  statistic q(W2(mu, mu0)) is no expectation functional, for every sigma-finite nu (nu != 0 being an
  instance); the jump-integrand half is the companion clause ex_fulllaw_beyond_U_corr. The earlier
  verdict (broader) stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.ex_fulllaw_beyond_radial ed839d34f480cba1e35b736319ec8895 by=claude-auditor source=A:sec5:overview@8e465cf926145c437fd799ed11d7a0aaaa89f28e2b5f5562f8ceedf17465af52 -->

## `A:sec:examples` (paper/sections/05-examples.tex, lines 3–7)

* `MVFBSDEJ.PaperSpec.sec5_limin` (added: lines 3–5 and line 7). Lines 3-5 add that Theorem
  3.5 permits broad law dependence and that the dissipativity of Assumption 2.5 cannot be traded for
  Lipschitz continuity alone; line 7 gives the horizon T = 3pi/4. The first is exposition and the
  second is the inference the clause supports (a Lipschitz system satisfying (2.3) and Assumptions
  2.2-2.3 with no solution at T = 3pi/4), as the scope note says; the earlier reading already quoted
  'no adapted solution on T = 3pi/4'. The earlier verdict (broader) stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.sec5_limin ed839d34f480cba139dd24c614ab7445 by=claude-auditor source=A:sec:examples@a71b654121931b92f4fc2ddf7dcec26355f85753fd5105d1715986bc59313a76 -->

## `A:thm3.1:companion` (paper/sections/03-main-results.tex, lines 75–81)

* `MVFBSDEJ.PaperSpec.thm_stab_companion` (added: line 75 and 77–81). Lines 75 and 77 complete
  the sentence the clause states ('If system 2 also satisfies Assumptions 2.4-2.5 ... the
  differences evaluated along solution 1 and the constant built from system 2's data'), which the
  earlier reading quoted in full; lines 78-81 are the companion clauses (b) and (c). The
  proposition, with system 2 under (2.3) and Assumptions 2.2-2.5 and C_stab evaluated at system 2's
  constants, matches. The earlier verdict (broader: system 1 needs only Assumptions 2.2-2.3) stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.thm_stab_companion ed839d34f480cba1c07a514f459f590c by=claude-auditor source=A:thm3.1:companion@29dc4c0964f38ec55444454a5131c89d80201b311710e24619a2f05e533a8b3b -->

* `MVFBSDEJ.PaperSpec.thm_stab_data` (added: line 75 and 77–81). Lines 78-79 ('When the two
  systems share the four interior coefficients, the bound gives continuous dependence on the initial
  and terminal data') are the sentence the earlier reading quoted and compared (the data-only form
  of (3.1) under the hypotheses of Theorem 3.1); the other added lines are the companion and minimal
  clauses. The earlier verdict (faithful with representation choices) stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.thm_stab_data ed839d34f480cba104333be660b0803f by=claude-auditor source=A:thm3.1:companion@29dc4c0964f38ec55444454a5131c89d80201b311710e24619a2f05e533a8b3b -->

* `MVFBSDEJ.PaperSpec.thm_stab_minimal` (added: line 75 and 77–81). Lines 79-81 ('the
  hypotheses on system 2 serve only to make the right-hand side of (3.1) finite: the estimate holds
  whenever the displayed differences are square-integrable') are what the earlier reading quoted and
  compared (system 2 under (2.3) only, (3.1) read in [0, infinity]); the other added lines are the
  companion and data clauses. The earlier verdict (faithful with representation choices) stands.
  <!-- spec-review: MVFBSDEJ.PaperSpec.thm_stab_minimal ed839d34f480cba1a1fc76e8097d81f2 by=claude-auditor source=A:thm3.1:companion@29dc4c0964f38ec55444454a5131c89d80201b311710e24619a2f05e533a8b3b -->
