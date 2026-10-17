### A:ex:fulllaw, A:rem:regimes, A:sec5:overview: Dissertation.PaperSpec.A.ex_fulllaw_beyond_radial
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash ed839d34f480cba1fc87ff54d30df5ad (pl-fp-v1:bd2ddc0359d2a5b2d4c03423f40aa608755e4946bbbc872ba727421245fc5f80)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T16:03:52Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T15:47:46Z):
Reading of spec ex_fulllaw_beyond_radial (Example 5.4: "(i) q(W_2(mu, mu_0)), a nonlinear
radial statistic of the full tuple law ... All three lie beyond the expectation and
two-point-kernel jump-integrand interactions of the preceding examples"; Section 5 overview:
"Example 5.4 carries the law dependence beyond those subclasses, to genuinely nonlinear
functionals of the full tuple"; Remark 5.7: "arbitrary nonlinear full-tuple law dependence").

Setting: standing H = R^n x R^m x R^{m x d} x L^2(nu;R^m), any n,m,d >= 1, any sigma-finite
nu (nu = 0 included: H is still unbounded through R^n). mu_0 in P_2(H), q : R_+ -> R bounded
and Lipschitz, w_0 in R^m (the driver perturbation direction), epsilon > 0.
"Expectation functional" (the preceding examples' classes): a law dependence of the form
mu |-> int_H phibar(theta, theta') mu(dtheta') (Example 5.3, phibar Lipschitz, possibly with t),
including means (Example 5.1(ii)). Any such map is affine under mixtures of laws.
"Nonlinear": q must be non-degenerate - a constant q gives a constant (hence expectation)
statistic, so the printed "arbitrary bounded Lipschitz q" cannot be meant literally; the
word "nonlinear" carries the nondegeneracy (q not constant on the attained range [0, inf) of
W_2(., mu_0)).
Faithful statement: for all n,m,d, nu, mu_0 in P_2(H), and bounded Lipschitz q that is not
constant (on [0, infinity)), the radial statistic mu |-> q(W_2(mu, mu_0)) (times w_0 != 0,
epsilon > 0, if the vector term is used) is not an expectation functional: there is no kernel
phibar (Lipschitz, or merely integrable) with q(W_2(mu,mu_0)) = int phibar dmu for all mu in
P_2(H) (a "not affine under mixtures" conclusion is stronger and fine). It is a functional of
the full tuple law mu on H.
An existential version (there exist q, mu_0 such that ...) shows only that type (i) as a class
leaves the expectation class; it loses the per-instance content - I would count it narrower
unless the paper's sentence is read as a class statement (possible reading: "lie beyond" =
"is not contained in"). A version adding hypotheses beyond non-constancy (e.g. specific mu_0 =
delta_0, specific q, nu != 0) is narrower.
Comparison (verdict recorded 2026-10-17T16:01:28Z):
Comparison, ex_fulllaw_beyond_radial (Sec5.lean:583-594).
Setting: sigma-finite nu on countably generated E, any n m d with 0 < n (standing n >= 1).
q : R -> R with |q r - q r'| <= Lq |r - r'| and |q r| <= B (bounded Lipschitz), and exists
a, b >= 0 with q a != q b (not constant on [0, infinity)) - the nondegeneracy I identified as
carried by "nonlinear". mu0 in P2(TupleH).
Conclusion: for every phi : H -> R integrable against every P2 law, exists mu in P2 with
q(w2H mu mu0) != int phi dmu: the radial statistic of the full law, with W_2 of the Hilbert
norm, is not an expectation functional. Since the statistic does not depend on theta, this also
excludes the two-point-kernel class int phibar(theta, theta') mu(dtheta') (fix theta), and means.
The vector factor epsilon w_0 is dropped (scalar statistic) - equivalent for epsilon w_0 != 0.
Per-instance universal statement (not merely existential) - my preferred reading.
Restriction "integrable against every P2 law" on phi is the meaning of "int phi dmu defined
for every mu" (avoids Bochner junk), and holds for the Lipschitz kernels of the preceding
examples.
Witness ex_fulllaw_beyond_hypotheses: q = min(|r|,1) bounded, 1-Lipschitz, non-constant - fine.
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-17T16:01:36Z): The author's review recorded for this unit is empty (its text is attached to an adjacent review marker of a unit outside this chunk and was not shown), so there is nothing to compare point by point. My verdict: faithful (see comparison); no disagreement can be recorded against an empty review.
