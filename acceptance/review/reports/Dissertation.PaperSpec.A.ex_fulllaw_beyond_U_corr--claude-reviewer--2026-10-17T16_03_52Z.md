### A:ex:fulllaw, A:sec5:overview: Dissertation.PaperSpec.A.ex_fulllaw_beyond_U_corr
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash ed839d34f480cba193f328d7c8c243ea (pl-fp-v1:22af2162ff7a9dc3738d459ea4684b8119c137c19dfd0e9d5933ec4b647475a6)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T16:03:52Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T15:47:46Z):
Reading of spec ex_fulllaw_beyond_U_corr: the U-marginal radial statistics are no expectation
functionals, with the correction L^2(nu) != 0.

Faithful corrected statement: for every sigma-finite nu (countably generated E) with
L^2(nu;R^m) != 0 (equivalently nu != 0), all n,m,d, every Lambda_0 in P_2(L^2(nu)), every
bounded Lipschitz qtilde (resp. qhat) non-constant on [0, infinity) (the same nondegeneracy as
the radial clause and the printed version), the statistic mu |-> qtilde(W_2(mu^U, Lambda_0))
(the drift term with v_0, and the jump term qhat(...) hhat) is not an expectation functional
of mu in P_2(H). Both the drift and jump statistics are covered by the clause ("statistics",
plural; the jump one "entering the jump coefficient itself").
Only the correction L^2(nu) != 0 may be added; e.g. requiring Lambda_0 = delta_0, finite nu,
or a stronger nondegeneracy than the printed version's would be narrower.
Truth check: with L^2 != 0, W_2(., Lambda_0) attains all of [0, infinity) on P_2(L^2), and
for Lambda_0 = delta_0 the mixture argument (mu_s = (1-s)delta_0 + s delta_u gives
q(sqrt(s)|u|) = (1-s)q(0) + s q(|u|), forcing q(r) = q(0) + a r^2, bounded => constant) shows
non-affinity; the general Lambda_0 case is plausible, to be checked against the proof.
Comparison (verdict recorded 2026-10-17T16:01:28Z):
Comparison, ex_fulllaw_beyond_U_corr (Sec5.lean:610-621).
As ex_fulllaw_beyond_U with "0 < m" replaced by (exists u != 0 in L^2(nu;R^m)) - the correction
L^2(nu) != 0 (which implies m >= 1 and nu != 0). Nothing else added: same q nondegeneracy, any
Lambda0 in P2(L^2), any n, d. Conclusion as before.
Witness ex_fulllaw_beyond_hypotheses: nu = delta_0 with a nonzero vector, q = min(|r|,1) -
intended instance.
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-17T16:01:36Z): The author's review recorded for this unit is empty (its text is attached to an adjacent review marker of a unit outside this chunk and was not shown), so there is nothing to compare point by point. My verdict: faithful (see comparison); no disagreement can be recorded against an empty review.
