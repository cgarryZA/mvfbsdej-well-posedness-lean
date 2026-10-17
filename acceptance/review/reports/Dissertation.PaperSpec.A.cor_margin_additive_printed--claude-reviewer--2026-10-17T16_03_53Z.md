### A:sec3:margin-paragraph: Dissertation.PaperSpec.A.cor_margin_additive_printed
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash ed839d34f480cba173b44fe7fdcea16b (pl-fp-v1:aeda6f85efb1d3d773799503a105ed66ca385ed984655403461ce0d022a36cf1)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T16:03:53Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T15:47:47Z):
Reading of spec cor_margin_additive_printed (paragraph after Cor 3.6: "by the reduction of
Remark 2.10, a margin in (2.13) forces every channel of the baseline to be strictly
dissipative. An additive h_0 = h_0(t,x,e) can therefore never serve as a baseline"), as printed,
every sigma-finite nu.

Setting: m = n (Corollary 3.6), G full rank, standing basis with horizon T > 0, sigma-finite nu
on a countably generated E (nu = 0 not excluded).
"Additive": h_0(t, theta, e, mu) = h_0(t, x, e): depends only on t, the forward state x and the
mark (no y, z, u, no law).
"Cannot serve as a baseline": the baseline system (b_0, sigma_0, h_0, f_0, g) with such h_0
does not satisfy the hypotheses of Corollary 3.6, specifically the margin condition (2.13)
with some c_diss > 0 (and beta_1, beta_2 >= 0) for a.e. t and all diagonal pairs.
Printed proposition: for every sigma-finite nu, every G, b_0, sigma_0, f_0 (arbitrary), every
additive h_0, every beta_1, beta_2 >= 0 and c > 0: the margin condition (2.13) fails (not for
a.e. t all pairs). Mechanism: take dX = dY = dZ = 0, dU != 0 (deterministic U = u_0, U' = 0):
pairing = 0 > -beta_1|G^T u_0|^2 - c|u_0|^2.
Expected refutation: nu = 0 => L^2(nu) = {0}, dU = 0 always, and Example 5.1(i) (law-free,
h_0 = h_c - beta_1 u = 0 on the trivial fibre, additive) has a margin, so an additive h_0 serves
as a baseline. nu = 0 is in the standing setting (sigma-finite; not excluded) - valid
refutation if built that way. The proposition must be no stronger than printed: e.g. must not
claim failure of Assumption 2.7 itself (beta_1 = 0 is allowed for additive h) - only the margin.
Comparison (verdict recorded 2026-10-17T16:01:29Z):
Comparison, cor_margin_additive_printed (AsPrinted.lean:94-107), printed reading, refuted.
Setting: standing (driver, G0 independent, enlJoint), every sigma-finite nu on countably
generated E (as printed, no nontriviality), any n, m with 0 < m (standing m >= 1), T > 0.
Statement: for all b1 >= 0, b2 (any real), c > 0, G : m x n (any), C with h(t, theta, mu) =
h(t, theta', mu') whenever theta.1 = theta'.1 (h depends on t and x only: the additive h_0 =
h_0(t,x,e), no u, y, z or law), not Margin213 ... G b1 b2 c C: the margin (2.13) fails.
Relative to the printed claim ("an additive h_0 can never serve as a baseline" of Corollary 3.6):
the Lean drops the corollary's context m = n, full-rank G and the other baseline assumptions
(2.2-2.5), and allows any real b2; it asserts directly that the margin fails, which is the
paper's own reason ("a margin in (2.13) forces every channel ... strictly dissipative"). So the
proposition is somewhat stronger in scope than the printed claim (broader): the printed claim is
its instance m = n, G full rank, baseline satisfying Assumptions 2.2-2.5, b2 >= 0.
Refutation cor_margin_additive_printed_false: nu = 0 on PUnit, n = m = d = 1, G = 1, Example
5.1(i) with b1 = b2 = 1 satisfying (2.13) with constants 0, 0 and margin 1; L^2(0) = {0} makes
every h additive. This instance lies inside the printed scope (m = n = 1, G = 1 of full rank,
Example 5.1(i) satisfies Assumptions 2.2-2.5, constants >= 0), and nu = 0 is admitted by the
standing setting. So the counterexample refutes the printed claim itself, not only the broader
proposition. Valid.
Verdict: broader (refutation valid; its counterexample lies within the printed scope).
Witness: —
Verdict: broader — Broader than printed (the printed reading of a refuted claim). The proposition asserts that a jump
coefficient depending on (t, x) only is incompatible with the margin (2.13) for every G : m x n,
every n, m >= 1, every b1 >= 0, b2 in R, c > 0, over every sigma-finite nu; the printed claim is
its instance in Corollary 3.6's context (m = n, G of full rank, baseline satisfying Assumptions
2.2-2.5, b2 >= 0). The extra breadth is not exploited by the refutation: its counterexample
(nu = 0 on a point, n = m = d = 1, G = 1, Example 5.1(i) with b1 = b2 = 1, margin 1 with
constants 0, 0) lies in the printed scope and nu = 0 is admitted by the standing setting, so the
printed claim itself is false as printed. Refutation valid.
Disagreements with the author's review (shown 2026-10-17T16:01:36Z): The author's review recorded for this unit is empty (its text is attached to an adjacent review marker of a unit outside this chunk and was not shown), so there is nothing to compare point by point. My verdict: broader - the printed reading is stated for any G : m x n, any n, m >= 1 and any real b2, outside Corollary 3.6's context (m = n, full-rank G, Assumptions 2.2-2.5); the refutation's counterexample (nu = 0, n = m = d = 1, G = 1, Example 5.1(i)) lies inside the printed scope, so the refutation is valid for the printed claim.
