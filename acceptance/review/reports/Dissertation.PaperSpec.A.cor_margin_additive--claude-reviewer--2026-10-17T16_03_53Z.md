### A:sec3:margin-paragraph: Dissertation.PaperSpec.A.cor_margin_additive
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash ed839d34f480cba19075028a95edf84d (pl-fp-v1:b73e058908da190df52e8ee42186266e119383b4a9479d6ec61efd78518efa20)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T16:03:53Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T15:47:47Z):
Reading of spec cor_margin_additive: "an additive h_0 cannot serve as a baseline, with
nu != 0".

Faithful corrected statement: for every sigma-finite nu != 0 on a countably generated E (no
other restriction), m = n, every G (full rank or arbitrary), horizon T > 0, every baseline
(b_0, sigma_0, f_0 arbitrary, h_0 additive: h_0(t, theta, e, mu) = h_0(t, x, e)), every
beta_1, beta_2 >= 0 and every c > 0, the margin condition (2.13) does NOT hold for a.e. t in
[0,T] and all diagonal pairs (i.e. the baseline cannot satisfy Corollary 3.6's margin
hypothesis). Mechanism: inputs with dX = dY = dZ = 0 and deterministic dU = u_0 != 0 (needs
L^2(nu) != 0, which for sigma-finite nu is nu != 0) at a positive-measure set of times.
Only the correction nu != 0 may be added. Narrower would be: requiring G = 1, specific
b_0/sigma_0/f_0, beta_1 > 0, finite nu, law-free baseline. A conclusion "the baseline fails
Assumption 2.7 with beta_1 > 0" alone is different (weaker/other) than failing the margin.
If "additive" is encoded more broadly (e.g. allowing law dependence h_0(t, x, mu)), the claim
is broader and needs random zero-mean dU (available for t > 0) - still fine if true.
Comparison (verdict recorded 2026-10-17T16:01:29Z):
Comparison, cor_margin_additive (Sec3Margin.lean:83-95), corrected (nu != 0).
As the printed version with the extra hypothesis nu != 0 (the correction; for sigma-finite nu
equivalent to L^2(nu) != 0 given m >= 1). Same scope: any n, m >= 1, G : m x n arbitrary,
b1 >= 0, b2 any real, c > 0, T > 0, h depending on (t, x) only; conclusion not Margin213.
Nothing narrower than printed plus correction; broader in scope as the printed version (no
m = n, no full rank, no other baseline assumptions, b2 unrestricted).
Instantiation: m = n, G full rank, baseline satisfying Assumptions 2.2-2.5, b2 >= 0, nu != 0 gives
"an additive h_0 cannot serve as a baseline of Corollary 3.6".
Witness cor_margin_additive_hypotheses: nu = delta_0 != 0, Example 5.1(i) with b1 = 0 (h = h_c,
additive) - the hypotheses are met at an intended instance.
Verdict: broader.
Witness: —
Verdict: broader — Broader than printed-plus-correction. With the correction nu != 0, the Lean asserts the failure of
(2.13) for any G : m x n, any n, m >= 1, b1 >= 0, any b2, c > 0 and any coefficient system whose h
depends on (t, x) only; the printed corrected claim is the instance m = n, G of full rank, the
baseline satisfying Assumptions 2.2-2.5 and b2 >= 0. Nothing beyond nu != 0 is added.
Disagreements with the author's review (shown 2026-10-17T16:01:36Z): The author's review recorded for this unit is empty (its text is attached to an adjacent review marker of a unit outside this chunk and was not shown), so there is nothing to compare point by point. My verdict: broader - with the correction nu != 0, the proposition holds for any G : m x n, any n, m >= 1, any real b2 and any coefficient system with h depending on (t, x) only; Corollary 3.6's context is an instance. Nothing beyond nu != 0 is added.
