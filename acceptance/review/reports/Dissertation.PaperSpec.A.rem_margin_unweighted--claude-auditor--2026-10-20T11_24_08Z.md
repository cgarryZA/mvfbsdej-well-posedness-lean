### A:rem:margin: Dissertation.PaperSpec.A.rem_margin_unweighted
Pins: manuscript A None; project d3e594defeeeb94a6d05c33c666bcb870d584302; hash ed839d34f480cba1ba4163c9b3d796bd (pl-fp-v1:604c2f8d9a4cd6515bd432ddbef03bd8d40f767692a90ae2016bccf0a124b152)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-20T11:24:08Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-20T11:09:24Z):
# Reading: rem_margin_unweighted — Remark 2.11, second assertion

Passage (Remark 2.11: "When m = n both G and G^T are injective, so the bounds of Assumption 2.4,
applied channel by channel, give c(|G^T dY|^2 + |G^T dZ|_F^2 + ||G^T dU||^2 + |G dX|^2)
>= (c/c_G)(|dY|^2 + |dZ|_F^2 + ||dU||^2 + |dX|^2). A margin c in (2.12) therefore yields the
margin c/c_G, which is smaller than c when c_G > 1, in the unweighted form (2.13)").

Setting: standing setting; m = n; G in R^{n x n} of full rank (invertible); c_G := s_min(G)^{-2}
(smallest singular value). Coefficients b, sigma, h, f; constants beta_1, beta_2.

Hypotheses: m = n, G full rank, c > 0, and (2.12) holds with (beta_1, beta_2, c) [for a.e. t,
all diagonal pairs].
Conclusion: (2.13) holds with the same beta_1, beta_2 and margin c / c_G [for a.e. t, all diagonal
pairs]:
  E[pairing] <= -beta_1 E[|G^T dY|^2+|G^T dZ|_F^2+||G^T dU||^2] - beta_2 E|G dX|^2
                - (c/c_G) E[|dY|^2 + |dZ|_F^2 + ||dU||^2 + |dX|^2].
Sub-claims also printed: the pointwise channel inequality above (Assumption 2.4 bounds
|x|^2 <= c_G |Gx|^2, |y|^2 <= c_G|G^T y|^2, |Z|_F^2 <= c_G |G^T Z|_F^2,
||U||^2 <= c_G ||G^T U||^2), and the side remark c/c_G < c when c_G > 1 (trivial for c > 0).

Faithfulness points: c_G must be s_min(G)^{-2} (equivalently ||G^{-1}||^2 for invertible G), not
another constant; the margin is c/c_G (not c * c_G or c / ||G||^2); the matrix norm is
Frobenius, the L^2(nu) norm the genuine one; the quantifiers as in (2.12)/(2.13). A pointwise
(per pair) or a real-number abstraction with the four expectations as free reals plus the
channel inequalities as hypotheses would NOT be acceptable unless the channel inequalities are
proved from G's rank (they are part of the claim); a version for a single pair of diagonal
inputs is broader and acceptable. A stronger version without m = n (e.g. requiring only the
relevant injectivity) would be broader.
Comparison (verdict recorded 2026-10-20T11:23:01Z):
# Decision: spec:Dissertation.PaperSpec.A.rem_margin_unweighted (Dissertation/PaperSpec/A/Sec2Remarks.lean)

Verdict: faithful with representation choices.

Comparison with the locked reading.
- Setting: the standing basis, ν σ-finite on a countably generated space, n >= 1, m = n
  (coefficients `Coeffs ν n n d`, G ∈ R^{n x n}), arbitrary d, T.
- Hypotheses: `G.rank = min n n` (full rank, so G invertible), `0 < c`, and
  `Margin212 … T G β₁ β₂ c C` ((2.12) with β₁, β₂ and margin c, for a.e. t and all pairs of
  diagonal inputs, pairing integrable).
- c_G: the proposition writes the margin as `c / (sMin G ^ 2)⁻¹`. `sMin G`
  (Dissertation/WellPosedness/System/FullRank.lean) is the square root of the least eigenvalue of
  Gᵀ G (n <= m) or G Gᵀ (m < n), i.e. the smallest singular value s_min(G); so
  (sMin G ^ 2)⁻¹ = s_min(G)^{-2} = c_G of Assumption 2.4. For G of full rank with n >= 1,
  s_min(G) > 0 (`sMin_pos`), so no `0⁻¹ = 0` junk arises.
- Conclusion: `Margin213 … T G β₁ β₂ (c / c_G) C` (Dissertation/WellPosedness/Spec/
  CorollaryHyps.lean): for a.e. t and all pairs of diagonal inputs, the pairing is integrable and
  E[pairing] <= -β₁ E[|Gᵀ δY|^2+|Gᵀ δZ|_F^2+||Gᵀ δU||^2] - β₂ E|G δX|^2
  - (c/c_G) E[|δY|^2 + |δZ|_F^2 + ||δU||^2 + |δX|^2], which is (2.13) as printed with the same
  β₁, β₂ and margin c/c_G.
- The printed intermediate channel inequality (Assumption 2.4's bounds applied channel by channel)
  is a step of the argument; the claim proper is "a margin c in (2.12) yields the margin c/c_G in
  (2.13)", which the proposition states. The side remark "smaller than c when c_G > 1" is the
  separate clause rem_margin_smaller.
- No sign hypotheses on β₁, β₂ are needed (the step only lowers the c-term), and none is imposed:
  a harmless generality.
Representation choices: c_G spelled `(sMin G ^ 2)⁻¹`; the inequalities (2.12) and (2.13) encoded
by `Margin212` and `Margin213` with integrability of the pairing part of each (as in the
repository's reading of Assumption 2.5, where the expectation is required to exist).

Current text. Read at 1f67672 (Remark 2.11: "When m = n both G and Gᵀ are injective, so the
bounds of Assumption 2.4, applied channel by channel, give ... A margin c in (2.12) therefore
yields the margin c/c_G, which is smaller than c when c_G > 1, in the unweighted form"). I have
not seen the earlier text, so I cannot say what changed; the proposition says what the current
passage says.

Witness. `Dissertation.Acceptance.A.rem_margin_hypotheses` (Dissertation/Acceptance/A/
Sec2Remarks.lean): Example 5.1(i) (β₁ = β₂ = 1, ν = δ_0 ≠ 0, d = 1, T = 1) with G = 1 of full rank
satisfies (2.12) with constants 1/2, 1/2 and margin 1/2 > 0. An intended instance with positive
margin. It has c_G = 1, so it does not exercise the constant c_G (c/c_G = c there); an instance
with G ≠ I (as in rem_margin_smaller_hypotheses, G = 1/2) would, but that is not needed for the
hypotheses to be shown satisfiable.

Coverage (claim A:rem:margin): as in the rem_margin_reduce decision -- the four clauses state the
reduction, the slack, the unweighted margin c/c_G and the comparison c/c_G < c, which are all the
mathematical assertions of Remark 2.11 at this revision, with the hypotheses in force (m = n for
the unweighted form).
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless:
1. c_G is written `(sMin G ^ 2)⁻¹`, with `sMin G` the smallest singular value (square root of the
   least eigenvalue of Gᵀ G or G Gᵀ); positive for G of full rank and n >= 1, so the inverse is
   genuine.
2. (2.12) and (2.13) are the predicates `Margin212`, `Margin213`, which quantify over a.e. t in
   [0, T] and all pairs of diagonal inputs and require the pairing's expectation to exist (the
   repository's reading of the printed expectation, carried from hypothesis to conclusion).
3. β₁, β₂ carry no sign hypothesis; the passage's step does not use one, so this only broadens.
Disagreements with the author's review (shown 2026-10-20T11:23:28Z): Disagreement in the verdict label only. The earlier review records "faithful"; I record "faithful
with representation choices": c_G is spelled (sMin G ^ 2)⁻¹ (the smallest singular value, positive
for G of full rank and n >= 1, so no 0⁻¹ junk), (2.12) and (2.13) are the predicates Margin212 and
Margin213 carrying the integrability of the pairing, and β₁, β₂ carry no sign hypothesis. I agree
the proposition says what the current Remark 2.11 says (m = n, margin c in (2.12) gives margin
c / c_G in (2.13)). A minor note on the witness: rem_margin_hypotheses has G = 1, so c_G = 1 and it
does not exercise the constant c_G; it suffices to show the hypotheses can be met.
