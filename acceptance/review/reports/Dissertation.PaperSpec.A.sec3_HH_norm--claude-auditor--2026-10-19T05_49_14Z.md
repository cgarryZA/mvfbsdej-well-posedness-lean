### A:sec3:HH-banach: Dissertation.PaperSpec.A.sec3_HH_norm
Pins: manuscript A None; project 90f9502669c17b205fb9360fcfbae619d4e499e8; hash ed839d34f480cba140aa5342c14a73fc (pl-fp-v1:a447e8eb8d5088aaf070fa2c1ecfcfdc6701b8477584f9d9c76469ed8d58474b)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T05:49:14Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T05:36:17Z):
Reading of the clause "||.||_S satisfies the triangle inequality and is absolutely homogeneous"
(sec. 3 "Solution space", 03-main-results.tex:4-32).

Paper: S := S2(0,T;R^n) x S2(0,T;R^m) x H2_W(0,T;R^{m x d}) x H2_N(0,T;L2(nu;R^m)), with
||Theta||_S^2 := E sup_{t<=T} |X_t|^2 + E sup_{t<=T} |Y_t|^2 + E int_0^T (|Z_t|_F^2 +
||U_t||_{L2(nu)}^2) dt; |.| Euclidean, |.|_F Frobenius, ||u||^2 = int_E |u(e)|^2 nu(de)
(Euclidean on R^m). "Under this identification ||.||_S is a norm rather than a seminorm, and
(S, ||.||_S) is a Banach space." The clause is the seminorm part of "is a norm".

Faithful formal statement: on the standing basis (any T > 0, n, m, d >= 1, nu), for all
Theta, Theta' in S and every real c:
  ||Theta + Theta'||_S <= ||Theta||_S + ||Theta'||_S   and   ||c Theta||_S = |c| ||Theta||_S,
where Theta + Theta' and c Theta are componentwise (U componentwise in L2(nu), or pointwise in
e for a representative), and ||.||_S is the square root of the displayed sum (a nonnegative real,
or an extended nonnegative real; with an extended-valued norm the statement may be for all
tuples, which is broader and fine). Implicitly the sum and scalar multiple lie in S again.
Constraints on the definition used: the sup is over t in [0,T]; E is under P; the four
component norms are Euclidean / Frobenius / L2(nu) with Euclidean fibre norm (a sup norm on
R^n would be a different ||.||_S); the combination is the l2-sum (square root of the sum of the
four squared quantities). If the norm is real-valued via a junk conversion (e.g. toReal of
infinity = 0), the statement must be restricted to S, otherwise it may be false or meaningless
outside S.
Comparison (verdict recorded 2026-10-19T05:46:51Z):
Comparison: Dissertation.PaperSpec.A.sec3_HH_norm (PaperSpec/A/Sec3SpaceNorm.lean:94-115) against my
reading.

Lean: for every basis (LevyDriver D, any 𝒢₀ ≤ mΩ; no independence needed), every n, m, d, every
real T, all tuples Θ = (X,Y,Z,U), Θ' with PaperWeakTuple over enlJoint 𝒢₀ D h𝒢₀ (the class
H_weak: X, Y adapted, right-continuous paths, a.s. left limits, finite energy; Z, U predictable,
vanishing off [0,T], finite energy), and every real c:
  supSize(Θ + Θ')^{1/2} ≤ supSize(Θ)^{1/2} + supSize(Θ')^{1/2}, and
  supSize(cΘ)^{1/2} = ofReal|c| · supSize(Θ)^{1/2},
in [0, ∞], with sums and scalar multiples coordinatewise (U pointwise in e).
supSize (Stability/SupUpgrade.lean:58) = E sup_{[0,T]} Σ_i X_i² + E sup_{[0,T]} Σ_k Y_k²
  + Σ_{k,j} E ∫_[0,T] Z_kj² + Σ_k E ∫_[0,T] ∫_E U_k(e)² ν(de) ds,
i.e. ‖Θ‖_S² with the Euclidean norm on R^n, R^m, the Frobenius norm on R^{m x d} and the L2(ν; R^m)
norm with Euclidean fibre norm. The sup is over t in [0,T], E under P. Square root via rpow 1/2 in
ℝ≥0∞. This matches the paper's ||.||_S exactly (the l2 combination of the four channels).

Against my reading:
 - triangle inequality and absolute homogeneity: both present; c arbitrary real; |c| via ofReal.
 - domain: H_weak instead of S. With an extended-valued norm this is a broader statement (the
   paper's S is contained in H_weak: finite S2 norms give finite energy for T >= 0, and a paper
   element of S has a representative of the PaperWeakTuple form). The printed claim is the
   instance with finite E sup |X|², E sup |Y|² (Θ, Θ' in S), T > 0 and 𝒢₀ independent of the
   driver; any T and any 𝒢₀ are further harmless broadenings.
 - no junk: the norm is ℝ≥0∞-valued, so no toReal junk; the inequality holds as an
   inequality in [0, ∞] and gives in particular that Θ + Θ' has finite norm when Θ, Θ' do
   (closure of S under sums, implicit in the paper).
 - hypotheses can be met: the witness sec3_HH_norm_hypotheses exhibits nonzero tuples with
   ‖Θ‖² = 4 over a genuine basis (d = 1, ν = δ₀), so the statement is not vacuous.
Verdict: broader (domain H_weak with extended-valued norm; instance Θ, Θ' in S gives the printed
seminorm properties of ||.||_S).
Witness: —
Verdict: broader — The proposition states the triangle inequality and absolute homogeneity of ||Θ||_S = supSize(Θ)^{1/2}, a value in [0,∞], for all tuples of the larger class H_weak (PaperWeakTuple), any T and any 𝒢₀. supSize is exactly E sup|X|² + E sup|Y|² + E∫(|Z|_F² + ||U||²_{L2(ν)}), with Euclidean, Frobenius and L2(ν) norms. The printed claim, ||.||_S a seminorm on S, is the instance in which Θ and Θ' have finite E sup|X|² and E sup|Y|² (so lie in S, which H_weak contains for T ≥ 0), with T > 0 and 𝒢₀ independent of the driver. The extended-valued norm avoids junk values, and the inequality also gives closure of S under sums.
Disagreements with the author's review (shown 2026-10-19T05:48:51Z): none
