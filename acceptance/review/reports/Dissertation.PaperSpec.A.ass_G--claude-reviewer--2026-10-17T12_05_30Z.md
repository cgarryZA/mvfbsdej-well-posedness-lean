### A:ass:G: Dissertation.PaperSpec.A.ass_G
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash ed839d34f480cba1654da9b84ef073af (pl-fp-v1:53a36f2c0365002ff30b6f6d705b85e44d5c8e691adb6475a4b4c6392d32b4c7)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T12:05:30Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:04:35Z):
# Reading of Assumption 2.4 (ass:G), clause main

Setting: dimensions n, m >= 1 (and d >= 1 for the Z-bound); a sigma-finite measure nu on a
measurable space (E, cal E) (countably generated in the standing setting, not needed here);
L^2(nu; R^m) the Bochner/Lebesgue L^2 space of R^m-valued functions with norm
||u||^2 = int |u(e)|^2 nu(de).

Hypothesis: G in R^{m x n} has full rank, i.e. rank G = min(m, n).

Definitions used: ||G|| = operator norm (Euclidean to Euclidean); s_min(G) = smallest singular
value of G, i.e. the smallest of the min(m,n) singular values (sqrt of the least eigenvalue of
G^T G if m >= n, of G G^T if m <= n); c_G := s_min(G)^{-2}.

Claims (the "Then" and "so that" consequences), all for this one specific constant c_G:
 (a) |G v| <= ||G|| |v| for v in R^n and |G^T v| <= ||G|| |v| for v in R^m;
 (b) s_min(G) > 0 (asserted with the definition: follows from full rank);
 (c) if m >= n: for all x in R^n, |x|^2 <= c_G |G x|^2;
 (d) if n >= m: for all y in R^m, |y|^2 <= c_G |G^T y|^2;
 (e) if G^T is injective (equivalently, under full rank, n >= m): for all Z in R^{m x d},
     |Z|_F^2 <= c_G |G^T Z|_F^2; and for all U in L^2(nu; R^m),
     ||U||^2 <= c_G ||G^T U||^2 where (G^T U)(e) = G^T U(e) (pointwise action, well defined
     on L^2 classes).

Quantifiers: for all m, n (, d, E, nu sigma-finite), for all full-rank G, the conclusions with
c_G the specific value s_min(G)^{-2}. A faithful statement must use the singular-value constant
(or an equivalent characterisation) and not an existential constant; an existential constant
would be weaker than the printed claim. The edge cases: s_min must be the min over the
min(m,n) singular values, not over n (for m < n an n-indexed min would be 0, and 0^{-2} = 0
in Lean would make c_G = 0 and break (d)/(e)). Norm on R^{m x d} must be Frobenius; norm on
R^n Euclidean (not sup norm).

The extension in (e) to L^2(nu) needs no finiteness of nu.
Comparison (verdict recorded 2026-10-17T12:05:23Z):
# Comparison for ass_G

Lean: forall m n, 0<m, 0<n, G : Matrix (Fin m) (Fin n) R with G.rank = min m n, then
 0 < sMin G /\ op-norm bounds for GX G and its adjoint /\ (n<=m -> forward bound) /\
 (m<=n -> backward bound) /\ (Gt injective -> Z-bound for all d and U-bound for all nu).

Item by item against my reading:
- Setting n,m>=1: `0 < m`, `0 < n`. Matches.
- Full rank: `G.rank = min m n` (Matrix.rank over R). Matches.
- ||G||: `‖GX G‖`, the operator norm of `toEuclideanLin G` as a CLM between EuclideanSpaces,
  i.e. the spectral norm. Matches. `|G^T v| <= ||G|| |v|` stated with
  `ContinuousLinearMap.adjoint (GX G)`, which is `GX Gᵀ` (adjoint_GX). Matches.
- s_min: `sMin G = sqrt(min eigenvalue of Gᴴ G)` if n <= m, else `sqrt(min eigenvalue of G Gᴴ)`.
  For real G, Gᴴ = Gᵀ. These are exactly the min(m,n) squared singular values, so sMin is the
  smallest singular value; the index type of the iInf is Fin n resp. Fin m, nonempty because
  n,m>0, so no sInf-empty junk. The m=n case agrees with either branch (charpoly_mul_comm).
- (b) `0 < sMin G`. Matches.
- c_G = `(sMin G ^ 2)⁻¹`; under (b) this is s_min^{-2}, no 0⁻¹ junk is reachable.
- (c) `n ≤ m → ∀ x, ‖x‖^2 ≤ c_G ‖GX G x‖^2`. Matches (Euclidean norm on EuclideanSpace).
- (d) `m ≤ n → ∀ y, ‖y‖^2 ≤ c_G ‖Gᵀ y‖^2`. Matches.
- (e) hypothesis `Function.Injective (adjoint (GX G))` = Gᵀ injective. Matches. Z-bound: Z in
  `EuclideanSpace ℝ (Fin m × Fin d)` whose norm is the Frobenius norm; `adjoint (GZ G)` is
  `GZ Gᵀ`, i.e. Gᵀ ⊗ I_d acting column by column = Gᵀ Z (adjoint_GZ, adjoint_GZ_toLp_apply).
  Matches. U-bound: U in `Lp (EuclideanSpace ℝ (Fin m)) 2 ν`, and `adjoint (GU G ν)` is the
  mark-by-mark action e ↦ Gᵀ U(e) (adjoint_GU / coeFn_adjoint_GU); norm is the L^2(nu) norm.
  Matches.

Representation choices / broadenings (all harmless):
1. d is quantified over all naturals (d = 0 included) inside the conclusion, and nu over all
   measures on all measurable spaces E (no sigma-finiteness, no countable generation). The
   printed claim is the instance d >= 1, nu sigma-finite on a countably generated E; the broader
   form is a stronger claim that specialises directly.
2. R^{m x d} represented as `EuclideanSpace ℝ (Fin m × Fin d)` so that the norm is Frobenius;
   Gᵀ represented as the Hilbert adjoint of the CLM x ↦ Gx (equal to the transpose).
3. The universe of E is a fixed universe parameter v of the proposition; the paper has no
   universe constraint and any concrete instance lives in some universe.

Witness `ass_G_hypotheses`: 0 < 1 and the 1x1 identity has rank min 1 1, i.e. the hypotheses
are met at G = I_1 (an intended instance; e.g. Example dissipative models use G = 1). Not vacuous.

Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless:
1. d ranges over all naturals and nu over all measures on any measurable space E (no
   sigma-finiteness or countable generation required); the printed claim is the instance with
   d >= 1 and nu sigma-finite on a countably generated E, obtained by specialisation.
2. R^{m x d} is `EuclideanSpace ℝ (Fin m × Fin d)` (Euclidean norm = Frobenius norm); G^T acts as
   the Hilbert adjoint of `GX G`, `GZ G` (= G ⊗ I_d), `GU G ν` (mark-by-mark), which the file
   Operators.lean identifies with the operators of Gᵀ.
3. c_G is written `(sMin G ^ 2)⁻¹`, with `sMin` the square root of the least eigenvalue of
   GᵀG (n ≤ m) or GGᵀ (m < n), i.e. the least of the min(m,n) singular values; since 0 < sMin G
   is part of the conclusion, the 0⁻¹ = 0 convention never applies.
4. E lives in a fixed universe parameter of the proposition.
Disagreements with the author's review (shown 2026-10-17T12:05:23Z): none
