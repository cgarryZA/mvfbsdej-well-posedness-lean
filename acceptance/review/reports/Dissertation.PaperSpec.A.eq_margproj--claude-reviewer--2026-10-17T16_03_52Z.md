### A:remark-2.6: Dissertation.PaperSpec.A.eq_margproj
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash ed839d34f480cba1c19abbad6d02050c (pl-fp-v1:add2ab479c715c283f0abfd1c91ccd82e4d32f1549b9881808c8e64365d6745b)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T16:03:52Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T15:47:46Z):
Reading of spec eq_margproj ((2.11): "Marginal projection P_2(H) -> P_2(L^2(nu)) is 1-Lipschitz
for W_2: W_2(mu^U, mu'^U)^2 <= int |u-u'|^2 dpi <= int |theta-theta'|_H^2 dpi <= W_2(mu,mu')^2").

Setting: H = R^n x R^m x R^{m x d} x L^2(nu;R^m) with |theta|_H^2 = |x|^2+|y|^2+|z|_F^2+|u|^2,
for all dimensions n, m, d >= 1 and every sigma-finite nu on a countably generated E (nu = 0
included). mu^U := push-forward of mu by theta |-> u. P_2(.) = Borel probability measures
with finite second moment. W_2 = quadratic Wasserstein distance (inf over couplings).
Faithful statement: for all mu, mu' in P_2(H): W_2(mu^U, mu'^U) <= W_2(mu, mu') (or the
squared form). Also implicitly mu^U in P_2(L^2(nu)) (the marginal of a P_2 law is P_2). The
paper's proof uses an optimal coupling; the statement does not depend on its existence.
Constant: exactly 1. No other hypotheses.
Encoding checks: the H norm must be the Euclidean (l^2) product norm, not the sup norm
(Lean's default on products is the sup norm!) - for the U-marginal bound
|u - u'| <= |theta - theta'|_H holds in both norms, so the inequality would remain true with
the sup norm, but W_2 on P_2(H) must be the one of the paper's |.|_H to be the printed
statement (a sup-norm W_2 on H is smaller, so a sup-norm statement W_2^U <= W_2^{sup}(mu,mu')
would be STRONGER than printed, still fine logically as broader... actually it implies the
printed one since W_2^{sup} <= W_2^{l2}). W_2 as ENNReal vs real: with P_2 measures, finite.
A statement over a general product with a 1-Lipschitz projection is broader and fine.
Comparison (verdict recorded 2026-10-17T16:01:28Z):
Comparison, eq_margproj (Sec2.lean:45-51).
forall sigma-finite nu on countably generated E, forall n m d, forall mu, mu' in P2(TupleH):
w2P mu.margU mu'.margU <= w2H mu mu'.
TupleH carries the max norm, but the right side is w2H: the 2-Wasserstein distance of the
images under toL2 into WithLp 2 (x, WithLp 2 (y, WithLp 2 (z, u))), i.e. for the Hilbert norm
(|x|^2+|y|^2+|z|_F^2+|u|^2)^{1/2} - the paper's W_2 on P_2(H). The left side is the W_2 on
P2(L^2(nu;R^m)) for the L^2 norm. margU = push-forward by the projection onto the u channel -
mu^U. Constant 1. Both distances finite for P2 laws (no toReal junk).
Dimensions n, m, d in N (including 0) - broader, harmless.
Witness eq_margproj_hypotheses: two laws with distinct U-marginals at nu = delta_0 - fine.
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-17T16:01:35Z): none
