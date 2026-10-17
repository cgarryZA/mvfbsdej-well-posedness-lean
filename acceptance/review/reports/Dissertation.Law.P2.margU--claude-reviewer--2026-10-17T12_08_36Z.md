### A:remark-2.6: Dissertation.Law.P2.margU
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 537c6d484c8f0e8b128e7c03175bc3a7 (pl-fp-v1:74fb9d3710f3a218b3c79f33994db8cf4608a2dd998a813e5bd1dead39c7aab4)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T12:08:36Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:07:59Z):
# Reading: the U-marginal mu^U (def:Dissertation.Law.P2.margU)

Paper's notion (Remark 2.6, eq:margproj). For mu in P_2(H), H = R^n x R^m x R^{m x d} x
L^2(nu; R^m) with |theta|_H^2 = |x|^2+|y|^2+|z|_F^2+|u|_{L^2(nu)}^2, mu^U in P_2(L^2(nu)) is the
U-marginal: the image of mu under the coordinate projection pi_U(x,y,z,u) = u. It lies in P_2
since |u| <= |theta|_H.

A faithful Lean definition: the element of `P2 (L^2(nu;R^m)-type)` whose law is
`μ.law.map π_U`, with π_U the (measurable) projection to the fourth (jump) coordinate of the
Lean model of H. Need: the projection is the jump coordinate (not another coordinate); the
target type is the Lean model of L^2(nu; R^m) used for U (with its norm = the L^2(nu) norm);
the model of H's norm dominates the u-norm (so the projection is norm non-increasing). If H is
modelled as a nested product with the sup norm, the measure is still the right marginal (the
norm only matters for P_2 membership and W_2); check that the ambient type is the one the
propositions use for H.
Comparison (verdict recorded 2026-10-17T12:08:29Z):
# Comparison: P2.margU

Lean: `μ.margU := μ.map measurable_projUH norm_projUH_le : P2 (Lp (EuclideanSpace ℝ (Fin m)) 2 ν)`
for `μ : P2 (TupleH ν n m d)`, where `TupleH ν n m d` =
`EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m × Fin d) ×
Lp (EuclideanSpace ℝ (Fin m)) 2 ν` (Tuple.lean:134) and `projUH θ = θ.2.2.2` (the fourth
coordinate), a continuous linear map.

- Projection: onto the jump channel L^2(nu; R^m) — the paper's u-coordinate. Good.
- Target type: Mathlib's `Lp (EuclideanSpace ℝ (Fin m)) 2 ν`, i.e. L^2(nu; R^m) with the
  L^2(nu) norm (∫|u(e)|^2 ν(de))^{1/2}, Euclidean norm on R^m. Good; its σ-algebra is the
  scoped Borel instance `lpMeasurableSpace`.
- Law: the genuine pushforward `μ.law.map projUH` (`margU_law`, rfl). Good.
- P_2 membership: via `‖projUH θ‖ ≤ ‖θ‖`; TupleH carries the max of channel norms rather than
  the paper's Hilbert norm, but these are equivalent (within factor 2), so finiteness of the
  second moment, and hence the set P_2(H), are the same. The law μ^U itself does not depend on
  the norm. The norm choice matters for W_2 (other units: `w2P` on TupleH vs `w2H`), not here.
- Z channel uses EuclideanSpace on Fin m × Fin d (Frobenius); irrelevant to margU.

Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-17T12:08:29Z): No disagreement on meaning. The author's entry shown for this unit (definitions.md:254) is empty; it records no reading of margU (projection onto the fourth, L^2(nu) channel; pushforward law; P_2 membership via the max-norm bound, equivalent to the Hilbert-norm one).
