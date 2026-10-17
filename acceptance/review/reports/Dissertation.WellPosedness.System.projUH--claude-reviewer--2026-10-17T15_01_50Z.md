### A:remark-2.6: Dissertation.WellPosedness.System.projUH
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 5ed7e50cc9210991ccbb6cdcbcc90dbb (pl-fp-v1:ee12fcdd5d431e67bbb76409a7c6cba2039942cfb55037d2d57829692e70902e)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:01:50Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:34:23Z):
Reading for def:Dissertation.WellPosedness.System.projUH (written before seeing any Lean).

Paper notion. Remark 2.6 (Wasserstein bounds): "Marginal projection P_2(H) -> P_2(L^2(nu)) is
1-Lipschitz for W_2 ... write mu^U in P_2(L^2(nu)) for the U-marginal of mu. The image of this
optimal pi under (theta,theta') |-> (u,u') is a coupling of (mu^U, mu'^U)". The name projUH
indicates the U-coordinate projection of H: H -> L^2(nu;R^m), theta = (x,y,z,u) |-> u (the map
whose pushforward gives mu^U), or possibly the induced marginal map mu |-> mu^U.

A faithful Lean definition must:
- return exactly the U-component u in L^2(nu;R^m) (the fibre with its L^2(nu) norm), with no
  change of representative (it is an element of the Lp space, not a pointwise function);
- be measurable/continuous (1-Lipschitz for the H norm, since ||u|| <= |theta|_H), so that the
  pushforward of laws along it is the genuine U-marginal;
- if it is the map on laws, be the pushforward mu |-> mu o pi_U^{-1}, which sends probability
  measures with finite second moment to the same on L^2(nu).
Comparison (verdict recorded 2026-10-17T12:39:11Z):
Comparison for System.projUH.
Lean: projUH : TupleH ν n m d →L[ℝ] Lp (EuclideanSpace ℝ (Fin m)) 2 ν := snd ∘ snd ∘ snd, as a
continuous linear map, with projUH θ = θ.2.2.2 (rfl).
- Returns exactly the U-component u ∈ L²(ν;ℝ^m), the Lp element itself, with no change of
  representative. Matches.
- Continuous and linear, measurable (measurable_projUH), and 1-Lipschitz for both the max norm and
  the Hilbert norm (norm_projUH_le, norm_projUH_le_norm_toL2). The U-marginal μ^U is
  P2.margU μ = pushforward of μ.law along projUH (margU_law). Matches Remark 2.6.
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-17T15:01:22Z): No disagreement on the substance. The author's entry (acceptance/review/definitions.md) records only the review marker and no comparison with the paper, so it does not state what I relied on: projUH θ = θ.2.2.2, the U-channel as an Lp element, continuous linear and measurable.
