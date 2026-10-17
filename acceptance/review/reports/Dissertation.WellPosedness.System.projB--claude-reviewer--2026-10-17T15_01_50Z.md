### A:ex:brownian: Dissertation.WellPosedness.System.projB
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash f41c30f5a4e6eb53b63a9ca646ce41dd (pl-fp-v1:128a5f3be4b646d7bb11ee2a42cb10dff7bb676cf64a529c4eb94d183ec53bd3)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:01:50Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:34:23Z):
Reading for def:Dissertation.WellPosedness.System.projB (written before seeing any Lean).

Paper notion. Example 5.2 (Brownian reduction): "Delete the U-coordinate from the tuple,
reducing H to R^n x R^m x R^{m x d}." The natural object called projB is the coordinate
projection from the Brownian--Poisson tuple space H = R^n x R^m x R^{m x d} x L^2(nu;R^m) onto
the Brownian tuple space H_B = R^n x R^m x R^{m x d}: (x,y,z,u) |-> (x,y,z).

A faithful Lean definition must:
- send (x,y,z,u) to exactly (x,y,z) (no reordering, no rescaling), forgetting only u;
- have as target the Brownian tuple space H_B with the norm |x|^2+|y|^2+|z|_F^2 (Euclidean on
  R^n, R^m, Frobenius on R^{m x d}), so that the projection is 1-Lipschitz and the H_B-norm of
  projB theta is the H-norm of theta without the U-term;
- be measurable (it is continuous/linear), so that the pushforward of laws along it is a genuine
  marginal and not Lean's junk zero measure.
If instead projB goes the other way (an embedding H_B -> H, (x,y,z) |-> (x,y,z,0)), it must be
that embedding exactly; then the name is misleading but the notion of "deleting the U
coordinate" is the inverse identification. I will judge it against whichever role it plays in
the Brownian-reduction statement: the reduction must be a genuine deletion of the U coordinate
(and of the Poisson channel), not just setting h = 0 on a Brownian--Poisson basis, which the
paper says explicitly is NOT a reduction.
Comparison (verdict recorded 2026-10-17T12:39:11Z):
Comparison for System.projB.
Lean: projB (θ : TupleH ν n m d) : ReducedTuple n m d := WithLp.toLp 2 (θ.1, WithLp.toLp 2
(θ.2.1, θ.2.2.1)), with ReducedTuple n m d = WithLp 2 (ℝ^n × WithLp 2 (ℝ^m × ℝ^{m×d})) (Euclidean
channels, Frobenius on m × d).
- Sends (x,y,z,u) to (x,y,z), with no reordering or rescaling, and forgets only u. Matches.
- Target: the Brownian tuple space ℝ^n × ℝ^m × ℝ^{m×d} with its Hilbert norm,
  ‖projB θ‖² = |x|²+|y|²+|z|_F² (norm_projB_sq). Matches. It is 1-Lipschitz for the Hilbert norm of
  H (norm_projB_le_norm_toL2).
- Measurable (measurable_projB), so the pushforward of laws along it is a genuine marginal.
- Its role in the Brownian reduction: Example 5.2 is formalised as the zero intensity ν = 0 of
  the paper's own model, where L²(0;ℝ^m) is a single point and projB/liftB identify H with the
  reduced space (liftB_projB at ν = 0). This deletes the U coordinate, which is not the same as
  setting h ≡ 0 on a Brownian–Poisson basis. Whether the Example 5.2 proposition is faithful is a
  matter for that spec's review. The definition itself is the deletion map of my reading.
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-17T15:01:21Z): No disagreement on the substance. The author's entry (acceptance/review/definitions.md) records only the review marker and no comparison with the paper, so it does not state what I relied on: projB is the coordinate deletion (x,y,z,u) ↦ (x,y,z) into the Hilbert-normed ReducedTuple, and it is measurable.
