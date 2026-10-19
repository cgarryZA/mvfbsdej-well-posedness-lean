### A:abstract, A:ass:G, A:conclusion, A:cor:robust, A:ex:concrete, A:ex:dealer, A:lem:cont, A:lem:pert, A:rem:generalrank, A:rem:margin, A:sec5:overview, A:thm3.1:companion, A:thm:cwp, A:thm:stab: Dissertation.WellPosedness.System.sMin
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash 42b2e53d2f710588e25de988c32456ea (pl-fp-v1:fcf19e010490b279eed58d7e622bfc124e060dec69d83048df6ca7c72ab17c40)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:27:24Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:13:12Z):
Reading for def:Dissertation.WellPosedness.System.sMin (locked before any Lean is shown).

Paper notion (Assumption 2.4 ass:G): for G in R^{m x n} of full rank, s_min(G) > 0 is its smallest
singular value, i.e. the smallest of the min(m,n) singular values (square roots of the eigenvalues
of G^T G if m >= n, of G G^T if n >= m); c_G := s_min(G)^{-2}. Then
  |x|^2 <= c_G |G x|^2 (m >= n),   |y|^2 <= c_G |G^T y|^2 (n >= m),
equivalently s_min(G) = inf_{|x|=1} |Gx| when m >= n, = inf_{|y|=1} |G^T y| when n >= m.
A faithful Lean definition must give exactly this number for every full-rank G (both rank
branches, m > n, m < n, m = n). Acceptable forms: sqrt of the least eigenvalue of G^T G (m >= n) /
G G^T (n >= m); the max of inf_{|x|=1}|Gx| and inf_{|y|=1}|G^T y| (for m != n one of them is 0);
NOT the min of the two infima (that is 0 when m != n), and NOT the least eigenvalue of G^T G when
m < n (that is 0 since G^T G is n x n of rank m < n). For non-full-rank G any value (0) is junk
and harmless if every use assumes full rank; note c_G = s_min^{-2} would then be 0^{-1} = 0 in
Lean, so statements must carry full rank. Norm conventions: Euclidean (operator 2-norm) on R^n,
R^m.
Comparison (verdict recorded 2026-10-19T03:25:28Z):
Comparison for def:Dissertation.WellPosedness.System.sMin.

Lean: sMin G = sqrt (if n <= m then inf_i eigenvalues(G^H G) else inf_i eigenvalues(G G^H)), G in
R^{m x n} (Matrix (Fin m) (Fin n)), G^H = G^T over R. G^T G is n x n, G G^T is m x m.
- n <= m (m >= n): sqrt of the least eigenvalue of G^T G = the smallest of the n = min(m,n) singular
  values. Correct.
- m < n: sqrt of the least eigenvalue of the m x m matrix G G^T = the smallest of the m = min(m,n)
  singular values. Correct.
- n = m: G^T G (same spectrum as G G^T). Correct.
These are exactly the acceptable forms of my reading; it avoids the wrong variants (least eigenvalue
of G^T G when m < n, which is 0). Eigenvalues of these PSD Hermitian matrices are >= 0, so the
sqrt is of a nonnegative number (sMin_sq_of_le/ge). Junk: n = 0 or m = 0 makes the inf over an empty
index 0 (sInf empty = 0); the paper has n, m >= 1 and the consumers assume 0 < n, 0 < m. Non-full-rank
G gives 0 and c_G = (sMin G ^ 2)^{-1} = 0 in Lean; consumers carry G.rank = min m n.
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-19T03:25:40Z): none
