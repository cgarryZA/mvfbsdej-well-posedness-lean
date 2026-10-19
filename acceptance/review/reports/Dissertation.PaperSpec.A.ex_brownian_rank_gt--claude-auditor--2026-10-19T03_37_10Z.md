### A:rem:beta1-dich, A:ex:brownian: Dissertation.PaperSpec.A.ex_brownian_rank_gt
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba154d947c79143fab0 (pl-fp-v1:beb395452b9e6d6ab9f8ec015b6c9c917f43f2a67e1e8b8fb5fcff43f4da2e03)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:37:10Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:16:44Z):
# Reading: spec ex_brownian_rank_gt (Remark 2.10 / Example 5.2: at nu = 0 both rank branches are available — the branch m > n)

Remark 2.10: with nu != 0, a jump coefficient of additive form forces beta1 = 0, hence m >= n with
alpha, beta2 > 0; the m < n case needs U-dissipative h. "When nu = 0 the fibre L^2(nu) is trivial,
dU = 0 identically, and the restriction disappears: this is the Brownian case of Example 5.2, in
which both rank branches remain available." Example 5.2: "With no jump channel the
U-dissipativity constraint ... is vacuous, so both rank branches of Assumption 2.5 are available."
"Available" = the branch can actually be realised: there are systems satisfying the assumptions in
that branch. This clause is the branch m > n (Assumption 2.5 then requires alpha, beta2 > 0).
A faithful formal statement: at nu = 0 (the Brownian case: standing basis with nu = 0, or the
Brownian reduction), there EXIST dimensions with m > n (ideally: for every n < m, any d), a
full-rank G in R^{m x n}, constants alpha, beta2 > 0, beta1 >= 0 meeting the constraints, xi0, and
a coefficient system (b,sigma,h,f,g) satisfying Assumptions 2.2-2.5 with these. A single instance
witnesses availability; a "for all m > n" version is stronger and fine. The instance must be a
genuine m > n system (G rectangular m x n with m > n) and must satisfy ALL the assumptions
(non-vacuity), at nu = 0. It need not involve an additive h (at nu = 0, h takes values in the
trivial fibre).
Comparison (verdict recorded 2026-10-19T03:29:04Z):
# Comparison: ex_brownian_rank_gt (Remark 2.10 / Example 5.2: at nu = 0 the branch m > n is available)

Lean (Sec5Brownian.lean): for every basis with intensity nu = 0 (any countably generated E, any
d, G0 independent), all n, m with 1 <= n < m, d >= 1, T > 0 and xi0 strongly F_0-measurable and
square integrable, there EXIST G in R^{m x n} with rank G = min m n (full rank), coefficients C
on H at nu = 0 and constants L, alpha, beta1, beta2 with JointBorel (2.3), Assumption 2.2 (with
xi0), Assumption 2.3 (L), Assumption 2.5 (G, alpha, beta1, beta2 — including the admissible
constants, which for m > n force alpha, beta2 > 0) and beta2 > 0.

Against my reading: at nu = 0 (the Brownian case): yes. A genuine m > n system with a full-rank
rectangular G satisfying ALL the assumptions: yes, as conclusions (no vacuity), for EVERY n < m
and every d >= 1, T > 0, xi0 — stronger than one instance, which my reading allowed. The branch
constraint alpha, beta2 > 0 comes from Constants (rank_gt) and beta2 > 0 is restated. h is
unconstrained (its fibre is trivial at nu = 0), as my reading noted.
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-19T03:37:01Z): Classification only. The reviewer records "faithful with representation choices"; I record
"faithful": the proposition asserts, at nu = 0 and for every 1 <= n < m, d >= 1, T > 0 and xi0, a
full-rank G and a coefficient system satisfying all of Assumptions 2.2-2.5 (and (2.3)) with
beta2 > 0, which is the printed availability claim (in a stronger, for-all-dimensions form). I see
no representation choice that needs recording beyond those of the shared assumption predicates; no
disagreement about the mathematics.
