### A:ex:fulllaw, A:sec5:overview: Dissertation.PaperSpec.A.ex_fulllaw_beyond_U
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash ed839d34f480cba1e06f855614a9b4c6 (pl-fp-v1:bdd2c1463c8eaee2882e02050fc9a8fb04a05f4b4af1875b5bdda20d325fb797)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T16:03:52Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T15:47:46Z):
Reading of spec ex_fulllaw_beyond_U, as printed (every sigma-finite nu): Example 5.4 (ii)
"qtilde(W_2(mu^U, Lambda_0)) and qhat(W_2(mu^U, Lambda_0)), the same for the U-marginal, the
latter entering the jump coefficient itself ... All three lie beyond the expectation and
two-point-kernel jump-integrand interactions".

Printed proposition: for every sigma-finite nu on a countably generated E, all n,m,d, every
Lambda_0 in P_2(L^2(nu)) and bounded Lipschitz qtilde, qhat (non-degenerate: not constant, as
in the radial clause - the same nondegeneracy that the companion radial clause uses), the
U-marginal statistics mu |-> qtilde(W_2(mu^U, Lambda_0)) (and qhat(...), times v_0 / hhat)
are not expectation functionals of mu (not of the form int phibar dmu; or not affine).
Quantification "as printed": every sigma-finite nu, no nontriviality of L^2(nu).
Expected refutation: nu = 0 => L^2(nu) = {0}, P_2(L^2) = {delta_0}, mu^U = delta_0 = Lambda_0
for every mu, so the statistic is the constant q(0): an expectation functional (of a constant
kernel). nu = 0 is in the standing setting (sigma-finite, not excluded). Valid if the
proposition's nondegeneracy hypothesis on q is something a q can meet while the statistic
is constant at nu = 0 (e.g. "q not constant on [0,infinity)"); if the proposition's
nondegeneracy were "not constant on the attained range", then at nu = 0 the hypothesis would
fail and the refutation could not go through nu = 0.
The proposition must be no stronger than printed (e.g. not claim non-affinity of a specific
combination the paper does not state), and its form should mirror the radial clause.
Comparison (verdict recorded 2026-10-17T16:01:28Z):
Comparison, ex_fulllaw_beyond_U (Sec5.lean:596-608), printed reading, refuted.
Same shape as the radial clause, with the U-marginal: 0 < m (standing m >= 1), q bounded
Lipschitz not constant on [0, infinity), Lambda0 in P2(L^2(nu;R^m)), every phi : H -> R
integrable against every P2 law; exists mu in P2 with q(w2P mu^U Lambda0) != int phi dmu. W_2 on
P2(L^2(nu;R^m)) with the L^2 norm. Quantified over every sigma-finite nu on countably generated
E, as printed. One scalar statistic covers both qtilde (drift) and qhat (jump coefficient):
they are the same law functional, multiplied by v0 resp. hhat. Not stronger than printed (same
nondegeneracy as the radial clause).
Refutation ex_fulllaw_beyond_U_false: E = PUnit, nu = 0, q = min(|r|,1) (bounded, 1-Lipschitz,
q 0 != q 1), Lambda0 = delta_0, phi = const q(0): every U-marginal is delta_0, so the statistic is
q(0) = int phi dmu. nu = 0 is a sigma-finite measure on a countably generated space, admitted by
the standing setting; the hypothesis on q is met. Valid.
Verdict: faithful (refutation valid).
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-17T16:01:36Z): The author's review recorded for this unit is empty (its text is attached to an adjacent review marker of a unit outside this chunk and was not shown), so there is nothing to compare point by point. My verdict: faithful (see comparison); no disagreement can be recorded against an empty review.
