### A:ex:brownian: Dissertation.WellPosedness.System.ReducedTuple
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash d68fe71f65d1320f648e397a6f92aa48 (pl-fp-v1:1ae70923ace02c605de3bad8556855740b42e3f0b4dd26c8883de05479913f07)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:06:17Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:33:34Z):
Reading for ReducedTuple (paper Example 5.2 Brownian reduction).
Paper: "Remove the Poisson channel ... Delete the U-coordinate from the tuple, reducing H to
R^n x R^m x R^{m x d}." The reduced state space H_red = R^n x R^m x R^{m x d} with norm
|theta|^2 = |x|^2 + |y|^2 + |z|_F^2 (Euclidean and Frobenius), the Hilbert product (l^2-sum) norm,
and its Borel sigma-field; P_2(H_red) with W_2 under that norm. A ReducedTuple in Lean must be this
space (or the triple of points (x, y, z) of it). If it is a type of points, its norm must be the l^2
product norm (Euclidean on R^n, R^m and Frobenius on matrices), so that W_2 and Lipschitz
constants are those of (A1) of BYZ / the paper's Ass 2.3 restricted. Alternative: a structure
of processes (X, Y, Z) without U; then it must be the reduced solution tuple of the Brownian system.
Comparison (verdict recorded 2026-10-17T15:01:23Z):
Comparison for ReducedTuple (Examples/Brownian.lean:63): WithLp 2 (EuclideanSpace R (Fin n) x WithLp 2
(EuclideanSpace R (Fin m) x EuclideanSpace R (Fin m x Fin d))), the iterated L^2 product; the file proves
||w||^2 = |x|^2 + |y|^2 + |z|^2 (norm_reducedTuple_sq), the m x d channel being Euclidean on pairs, i.e. the
Frobenius norm. Its measurable structure is Mathlib's WithLp instance (pullback of the product
sigma-algebra) with BorelSpace (Mathlib.Analysis.Normed.Lp.MeasurableSpace), i.e. the Borel sigma-field.
Against my reading (Ex. 5.2: H reduced to R^n x R^m x R^{m x d} with the Hilbert norm
(|x|^2+|y|^2+|z|_F^2)^{1/2} and Borel sigma-field): exact match, including the l^2 (not sup) product norm,
so W_2 on its laws is the paper's. Dimensions are explicit parameters.
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-17T15:05:46Z): none (the author's excerpt shown for this unit is a marker and at most a section heading, with no
item-level reading to compare against; my comparison file records the representation choices in
detail).
