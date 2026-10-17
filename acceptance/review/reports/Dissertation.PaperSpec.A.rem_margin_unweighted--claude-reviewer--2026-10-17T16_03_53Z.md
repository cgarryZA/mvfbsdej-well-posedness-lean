### A:rem:margin: Dissertation.PaperSpec.A.rem_margin_unweighted
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash ed839d34f480cba1ba4163c9b3d796bd (pl-fp-v1:604c2f8d9a4cd6515bd432ddbef03bd8d40f767692a90ae2016bccf0a124b152)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T16:03:53Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T15:47:47Z):
Reading of spec rem_margin_unweighted (Remark 2.11: "When m = n the margin may instead be
recorded in the unweighted form (2.13)").

Setting: m = n, G in R^{n x n} full rank (invertible), c_G = s_min(G)^{-2}, coefficient system,
diagonal pairs.
Meaning: at m = n the slack can be expressed with the unweighted quantities |dY|^2 + |dZ|_F^2 +
|dU|^2 + |dX|^2 instead of the G-weighted ones. Since |v|^2 <= c_G |G^T v|^2 and |x|^2 <=
c_G |G x|^2 (Assumption 2.5 at m = n), a weighted margin c gives an unweighted margin c/c_G
(= c s_min(G)^2) with the same beta's; or from a bound with betabar_i: (2.13) with beta_i =
betabar_i - c c_G and margin c for 0 < c < min betabar_i / c_G. The paper does not state the
constant; it does NOT claim the same c (that would be false unless s_min(G) >= 1; cf.
Example 5.1(i) "unweighted here because G = 1").
Faithful statement: for m = n and full-rank G: if the interior pairing satisfies (2.12) with
margin c > 0 (or a bound with betabar_i > 0), then it satisfies (2.13) with some margin c' > 0
(explicitly e.g. c' = c / c_G) and constants beta_1, beta_2 >= 0, for a.e. t and all diagonal
pairs. If the Lean claims the same margin c with no rescaling it would be false or need G
orthogonal-type hypotheses (narrower). If it fixes c' as a function of c and G - fine.
Comparison (verdict recorded 2026-10-17T16:01:29Z):
Comparison, rem_margin_unweighted (Sec2Remarks.lean:227-239).
Setting: standing, m = n >= 1 (C : Coeffs nu n n d, G : n x n), G.rank = n (full rank), c > 0,
any b1, b2, T.
Hypothesis: Margin212 with b1, b2 and margin c (weighted margin (2.12)).
Conclusion: Margin213 with the same b1, b2 and margin c / (sMin G ^ 2)^{-1} = c s_min(G)^2 =
c / c_G, the unweighted form (2.13). sMin G = sqrt of the least eigenvalue of G^T G (n <= n
branch), the smallest singular value; c_G = s_min^{-2} as in Assumption 2.4. My reading: the
margin is re-recorded in unweighted form with the rescaled constant c / c_G (not the same c,
which would be false unless s_min >= 1). Matches; the explicit constant is the natural one.
Witness rem_margin_hypotheses: Example 5.1(i) with G = 1, margin 1/2 - intended instance.
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-17T16:01:36Z): none
