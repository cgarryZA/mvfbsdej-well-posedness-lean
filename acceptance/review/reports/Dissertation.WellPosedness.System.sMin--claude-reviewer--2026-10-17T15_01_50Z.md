### A:ass:G, A:cor:robust, A:ex:concrete, A:lem:cont, A:lem:pert, A:rem:generalrank, A:thm3.1:companion, A:thm:cwp, A:thm:stab: Dissertation.WellPosedness.System.sMin
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 42b2e53d2f710588e25de988c32456ea (pl-fp-v1:fcf19e010490b279eed58d7e622bfc124e060dec69d83048df6ca7c72ab17c40)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:01:50Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:34:23Z):
Reading for def:Dissertation.WellPosedness.System.sMin (written before seeing any Lean).

Paper notion. Assumption 2.4: G in R^{m x n} full rank; s_min(G) > 0 its smallest singular
value; c_G := s_min(G)^{-2}; then |x|^2 <= c_G |Gx|^2 when m >= n and |y|^2 <= c_G |G^T y|^2
when n >= m. The smallest singular value of an m x n matrix is sigma_{min(m,n)}(G), the
min(m,n)-th largest singular value: sqrt(lambda_min(G^T G)) when m >= n (= min_{|x|=1}|Gx|),
sqrt(lambda_min(G G^T)) when n >= m (= min_{|y|=1}|G^T y|). Equivalently
s_min(G) = max( inf_{|x|=1}|Gx| , inf_{|y|=1}|G^T y| ) in all cases. It is positive iff G has
full rank (rank = min(m,n)). Dimensions n,m >= 1.

A faithful Lean definition must:
- give the min(m,n)-th singular value for BOTH rank branches. A definition as
  inf_{|x|=1}|Gx| (or sqrt lambda_min(G^T G)) alone is correct only for m >= n and is 0 for
  m < n, which would make c_G = 0^{-1} = 0 in Lean and the n >= m bound false/vacuous; similarly
  the G^T-only version is wrong for m > n;
- use Euclidean norms on R^n, R^m (not the sup norm), since singular values are Euclidean
  notions; with sup norms the infimum is a different number;
- be nonnegative; positivity should be equivalent to full rank;
- junk: for a rank-deficient G the value 0 is the true smallest singular value, and then
  c_G = 0^{-1} is Lean junk 0 — harmless only where full rank is assumed (Ass 2.4).
Comparison (verdict recorded 2026-10-17T12:39:11Z):
Comparison for System.sMin.
Lean: sMin (G : Matrix (Fin m) (Fin n) ℝ) : ℝ := √(if n ≤ m then ⨅ i, eigenvalues (Gᴴ G) i else
⨅ i, eigenvalues (G Gᴴ) i).
- Both rank branches are covered. If n ≤ m (m ≥ n), it is √λ_min(GᵀG) (an n×n matrix, n eigenvalues),
  which is σ_n(G) = σ_{min(m,n)}(G). If m < n, it is √λ_min(GGᵀ) (m×m), which is
  σ_m(G) = σ_{min(m,n)}(G). For m = n either branch gives the same value. This is exactly the
  smallest singular value as I described it. It is not the one-branch version I warned about.
- Over ℝ, ᴴ is the transpose. The eigenvalues are those of the Hermitian (symmetric) matrices,
  which are real and ≥ 0 because the matrices are positive semidefinite. ⨅ over Fin k with k ≥ 1
  (finite, nonempty, bounded) is the minimum. The square root is the real sqrt (≥ 0).
- It is positive iff G has full rank min(m,n). Euclidean notions (eigenvalues of GᵀG) are used, so
  the norm issue does not arise.
- Junk: if n = 0 (or m = 0) the infimum over an empty index is sInf ∅ = 0 in ℝ. The paper has
  n, m ≥ 1. For a rank-deficient G the value 0 is the true smallest singular value, and
  c_G = sMin⁻² would be Lean junk 0. Assumption 2.4 assumes full rank, so this is harmless where
  full rank is assumed.
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-17T15:01:22Z): No disagreement on the substance. The author's entry (acceptance/review/definitions.md) records only the review marker and no comparison with the paper, so it does not state what I relied on: both rank branches are handled (√λ_min(GᵀG) for n ≤ m, √λ_min(GGᵀ) for m < n), giving σ_{min(m,n)}(G). The only junk is 0 at n = 0 or m = 0, outside the paper.
