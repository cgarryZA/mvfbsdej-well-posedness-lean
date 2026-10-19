### A:ass:G: Dissertation.PaperSpec.A.ass_G
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba1654da9b84ef073af (pl-fp-v1:53a36f2c0365002ff30b6f6d705b85e44d5c8e691adb6475a4b4c6392d32b4c7)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:31:21Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:16:07Z):
Reading of spec ass_G, clause main (Assumption 2.4).
Setting: m,n>=1 (and d>=1, nu sigma-finite for the U-part); G in R^{m x n} of full rank (rank = min(m,n)).
||G|| the l2->l2 operator norm (spectral norm), s_min(G) the smallest of the min(m,n) singular values,
c_G := s_min(G)^{-2}.
Claims ("Write..., so that ...; and s_min(G)>0 ...; Then ...; When G^T is injective ... extends"):
 (a) |Gv| <= ||G|| |v| for v in R^n and |G^T w| <= ||G|| |w| for w in R^m (Euclidean norms);
 (b) s_min(G) > 0 (full rank);
 (c) if m >= n: |x|^2 <= c_G |Gx|^2 for all x in R^n;
 (d) if n >= m: |y|^2 <= c_G |G^T y|^2 for all y in R^m;
 (e) if G^T injective (equivalently n>=m with full rank): |Z|_F^2 <= c_G |G^T Z|_F^2 for all Z in R^{m x d},
     and ||U||^2_{L2(nu)} <= c_G ||G^T U||^2_{L2(nu)} for all U in L2(nu;R^m) (G^T applied pointwise).
Hypothesis: full rank only. Quantifiers: for all m,n,(d,nu), for all full-rank G. Constants are the defined
||G||, c_G (not free constants: a statement "exists c" would be weaker but acceptable only if c is the paper's
c_G; the paper names c_G := s_min^{-2}, used throughout as a parameter of C_stab). Edge cases: c_G must be
defined with the correct singular value (smallest nonzero, i.e. of G^T G when m>=n, of G G^T when n>=m);
a Lean c_G = (lambda_min(G^T G))^{-1} with Lean 0^{-1}=0 would be junk when m<n. ||G|| must be the
operator norm wrt Euclidean norms, not Mathlib's default sup-entry norm.
Witness: any full-rank G (e.g. G=1 when m=n).
Comparison (verdict recorded 2026-10-19T03:29:17Z):
Comparison, ass_G (Sec2.lean:53-72) vs reading.
- ∀ m n > 0, ∀ G : Matrix (Fin m) (Fin n) ℝ with G.rank = min m n (full rank). Matches.
- 0 < sMin G, with sMin = sqrt(least eigenvalue of GᵀG) if n ≤ m, of GGᵀ if m < n (FullRank.lean:109):
  the smallest of the min(m,n) singular values -- the correct one in both rank cases (no 0⁻¹ junk:
  positivity is part of the statement). Matches (b).
- ‖GX G v‖ ≤ ‖GX G‖‖v‖ and ‖(GX G)† v‖ ≤ ‖GX G‖‖v‖, with GX G = toEuclideanLin G a CLM between
  Euclidean spaces and ‖GX G‖ its operator norm (the spectral norm); the adjoint is Gᵀ (adjoint_GX).
  Matches (a).
- n ≤ m: ‖x‖² ≤ (sMin G²)⁻¹ ‖G x‖²; m ≤ n: ‖y‖² ≤ (sMin G²)⁻¹ ‖Gᵀ y‖². c_G = s_min⁻². Matches (c),(d).
- If Gᵀ injective: ∀ d, Z ∈ EuclideanSpace (Fin m × Fin d) (Frobenius): ‖Z‖² ≤ c_G ‖(GZ G)† Z‖², with
  GZ G = G ⊗ I_d acting columnwise and its adjoint Gᵀ columnwise (adjoint_GZ); ∀ E, ν (any measure),
  U ∈ L²(ν; R^m): ‖U‖² ≤ c_G ‖(GU G ν)† U‖², GU acting markwise with adjoint Gᵀ markwise (adjoint_GU).
  Matches (e); ν arbitrary is a harmless generalisation of σ-finite ν.
- Witness: G = 1 (1×1), full rank.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices: (1) G acts through the continuous linear maps GX, GZ (= G ⊗ I_d on R^{m×d}
viewed as EuclideanSpace on pairs, Frobenius norm), GU (markwise on L²(ν)), and Gᵀ is their adjoint
(proved equal to the transpose action); ‖G‖ is the operator norm of GX, i.e. the spectral norm; (2) c_G is
written inline as (sMin G ^ 2)⁻¹ with sMin the square root of the least eigenvalue of GᵀG (n ≤ m) or GGᵀ
(m < n), i.e. the smallest singular value; (3) the L²(ν) bound is stated for every measure ν, not only
σ-finite ones. None changes the meaning.
Disagreements with the author's review (shown 2026-10-19T03:29:28Z): none
