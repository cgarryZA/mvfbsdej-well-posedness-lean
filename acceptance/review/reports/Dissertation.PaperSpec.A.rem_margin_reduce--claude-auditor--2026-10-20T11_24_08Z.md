### A:rem:margin: Dissertation.PaperSpec.A.rem_margin_reduce
Pins: manuscript A None; project d3e594defeeeb94a6d05c33c666bcb870d584302; hash ed839d34f480cba15843e0ffe4756126 (pl-fp-v1:06376446ea6c52f808cb95f81e4a08000ee9375a67c1ee52d32b2eb68afe740f)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-20T11:24:08Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-20T11:09:24Z):
# Reading: rem_margin_reduce — Remark 2.11, first assertion

Passage (02-model-assumptions.tex, Remark 2.11, "Suppose the interior pairing has been bounded
with constants betabar_1, betabar_2. For every 0 < c < min{betabar_1, betabar_2} the same bound
is (2.12) with the reduced constants beta_i := betabar_i - c and margin c").

Setting: the standing setting of Section 2 (coefficients b, sigma, h, f with the Section 2
signatures, G in R^{m x n}, diagonal inputs D_t). "Bounded with constants betabar_1, betabar_2"
means the interior inequality (2.5) holds with betabar_1, betabar_2 in place of beta_1, beta_2
(for a.e. t and all pairs of diagonal inputs at t).

Hypotheses: betabar_1, betabar_2 real; 0 < c < min{betabar_1, betabar_2}; (2.5) with
(betabar_1, betabar_2).
Conclusion: (2.12) holds with beta_i = betabar_i - c and margin c, for a.e. t and all diagonal
pairs:
  E[pairing] <= -(betabar_1 - c) E[|G^T dY|^2 + |G^T dZ|_F^2 + ||G^T dU||^2]
                - (betabar_2 - c) E|G dX|^2
                - c E[|G^T dY|^2 + |G^T dZ|_F^2 + ||G^T dU||^2 + |G dX|^2].
Implicit and harmless: the reduced constants are > 0 (from c < min), so they are admissible
constants of Assumption 2.5 as far as beta_1, beta_2 >= 0 goes.

This is an algebraic identity of the right-hand sides; a formal statement made pointwise on one
pair of diagonal inputs, or abstracted to real numbers standing for the expectations (with the
four squared-norm expectations as free reals), is broader and acceptable provided the instance
with the genuine expectations of Assumption 2.5 is the printed claim. The quantifier structure
must be: for each pair / a.e. t, hypothesis with betabar implies conclusion with betabar - c, c
(constants not depending on the pair). The trailing "slack" sentence is exposition.
Comparison (verdict recorded 2026-10-20T11:23:00Z):
# Decision: spec:Dissertation.PaperSpec.A.rem_margin_reduce (Dissertation/PaperSpec/A/Sec2Remarks.lean)

Verdict: broader.

Numbering note on my locked reading: "(2.5)" there denotes the interior inequality eq:mono, (2.7)
in the paper's numbering.

Comparison with the locked reading.
- Setting: the standing basis (Lévy driver, independent 𝒢₀, filtration `enlJoint`), ν σ-finite
  on a countably generated space, coefficients `C : Coeffs ν n m d`, an arbitrary matrix
  G ∈ R^{m x n}, an arbitrary horizon T.
- Hypothesis "the interior pairing has been bounded with constants β̄₁, β̄₂":
  `∀ᵐ t ∂(volume.restrict [0,T]), Mono27At … t G β₁ β₂ C` -- (2.7) with (β̄₁, β̄₂) for a.e. t and
  all pairs of diagonal inputs, the pairing integrable (Dissertation/WellPosedness/Spec/
  Assumptions.lean). The Lean names β₁, β₂ play the role of β̄₁, β̄₂.
- Quantifier: for every c with 0 < c < min{β̄₁, β̄₂}.
- Conclusion: `Margin212 … T G (β₁ - c) (β₂ - c) c C`, defined in the same file as the
  proposition: for a.e. t and all pairs of diagonal inputs, the pairing is integrable and
  E[pairing] <= -(β̄₁ - c) E[|Gᵀ δY|^2 + |Gᵀ δZ|_F^2 + ||Gᵀ δU||^2] - (β̄₂ - c) E|G δX|^2
  - c E[|Gᵀ δY|^2 + |Gᵀ δZ|_F^2 + ||Gᵀ δU||^2 + |G δX|^2], which is (2.12) as printed with the
  reduced constants and margin c (GX Gᵀ, GZ Gᵀ, GU Gᵀ ν are Gᵀ acting on R^m, R^{m x d} and
  L^2(ν; R^m); GX G is G on R^n).
- Constants are fixed before the pairs (no dependence on the inputs), as printed. The positivity
  of the reduced constants is implicit (from c < min), as in the paper.
Broader than the printed claim only in dropping standing hypotheses that the identity does not
use: G need not have full rank and n, m, d, T are unrestricted; the printed claim is the instance
with the standing n, m, d >= 1, T > 0, G of full rank. The trailing "slack" sentence is a separate
clause (rem_margin_slack), not this one.

Current text. Read at 1f67672 (Remark 2.11: "Suppose the interior pairing has been bounded with
constants β̄₁, β̄₂. For every 0 < c < min{β̄₁, β̄₂} the same bound is (2.12) with the reduced
constants β_i := β̄_i - c and margin c"). I have not seen the earlier text, so I cannot say what
changed; the proposition states exactly this sentence.

Witness. `Dissertation.Acceptance.A.rem_affine_hypotheses` (Dissertation/Acceptance/A/
Sec2Remarks.lean): Example 5.1(i) with β₁ = β₂ = 1, G = 1, ν = δ_0 ≠ 0, T = 1, satisfies
Assumption 2.5 (hence the a.e. Mono27At hypothesis) and 0 < 1/2 < min{1, 1}. An instance the
paper intends (Example 5.1(i) is the paper's own source of a margin), with positive constants and
margin.

Coverage (claim A:rem:margin: clauses rem_margin_reduce, rem_margin_unweighted, rem_margin_smaller,
rem_margin_slack). Remark 2.11 defines "(2.7) with margin c" (a definition, encoded by
`Margin212`) and asserts: the reduction β_i := β̄_i - c (this clause); the slack of the weaker
constants absorbs a perturbation raising the pairing by at most the margin (rem_margin_slack); for
m = n the channel bounds of Assumption 2.4 turn a weighted margin c into the unweighted margin
c / c_G (rem_margin_unweighted); c / c_G < c when c_G > 1 (rem_margin_smaller). The four clauses
state every mathematical assertion of the passage at this revision; I see none that states more
than the passage, and the hypotheses are those in force (standing setting, m = n where the
passage says so).
Witness: —
Verdict: broader — Broader than the printed claim only by dropping standing hypotheses the algebra does not use:
the matrix G is arbitrary (no full-rank hypothesis) and n, m, d, T are unrestricted. The printed
claim is the instance with the standing n, m, d >= 1, T > 0 and G of full rank (Assumption 2.4):
there, if (2.7) holds with (β̄₁, β̄₂) for a.e. t (Mono27At, β̄ written β₁, β₂ in the Lean), then for
every 0 < c < min{β̄₁, β̄₂}, (2.12) holds with β̄₁ - c, β̄₂ - c and margin c (Margin212).
Disagreements with the author's review (shown 2026-10-20T11:23:28Z): Disagreement in the verdict label only. The earlier review records "faithful"; I record "broader",
because the proposition does not assume the standing full rank of G (nor n, m, d >= 1, T > 0),
which the algebraic reduction does not use; the printed claim is the instance with the standing
hypotheses. Substance agrees: Mono27At with (β̄₁, β̄₂) for a.e. t implies Margin212 with
β̄₁ - c, β̄₂ - c and margin c for every 0 < c < min{β̄₁, β̄₂}, as the current Remark 2.11 prints.
