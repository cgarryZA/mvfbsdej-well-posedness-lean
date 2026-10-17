### A:ex:brownian: Dissertation.WellPosedness.System.projP2
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 09e433978a0199240fd17c10afb2cd5e (pl-fp-v1:9fe94b02cf06a3a4497bd70a2d95b57de28aca41f7f868ffacba3601d8d56c81)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:01:50Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:34:23Z):
Reading for def:Dissertation.WellPosedness.System.projP2 (written before seeing any Lean).

Paper notion. Example 5.2 (Brownian reduction): with the U-coordinate deleted, the law argument
lives in P_2(R^n x R^m x R^{m x d}); "the assumptions reduce to W_2-Lipschitz joint-law
dependence of (X,Y,Z)". The natural object projP2 is the induced map on laws
P_2(H) -> P_2(H_B), mu |-> mu o projB^{-1}, the (X,Y,Z)-joint marginal of mu (or, if the
reduction goes the other way, the pushforward of a Brownian law along the embedding
(x,y,z) |-> (x,y,z,0), i.e. mu_B (x) delta_0 in the U-coordinate).

A faithful Lean definition must:
- be the pushforward (Measure.map) of the measure along the coordinate projection (or the
  embedding), with that map measurable so that Lean's Measure.map does not return the junk 0
  measure;
- preserve probability measures and finite second moments (projection is 1-Lipschitz), so it
  maps P_2(H) into P_2(H_B), and be 1-Lipschitz for W_2 (as Remark 2.6 eq:margproj argues for
  the U-marginal);
- on a diagonal input, send Law(Theta) to Law(X,Y,Z) (the joint law of the first three
  components), which is what the Brownian coefficients see.
If it is packaged as a map between subtypes (P_2 or ProbabilityMeasure), the proofs of
membership are irrelevant to meaning; the underlying measure must be the marginal.
Comparison (verdict recorded 2026-10-17T12:39:11Z):
Comparison for System.projP2.
Lean: projP2 (μ : P2 (TupleH ν n m d)) : P2 (ReducedTuple n m d) := μ.mapOfLe measurable_projB
norm_projB_le, where (P2.mapOfLe_law) the underlying measure is μ.law.map projB. The instance
arguments [SigmaFinite ν] [CountablyGenerated E] are carried.
- Pushforward of the law along the measurable coordinate projection (x,y,z,u) ↦ (x,y,z): the
  (X,Y,Z) joint marginal. Matches. projB is measurable, so Measure.map is not the junk 0.
- Probability and finite second moment are preserved: the bound ‖projB θ‖ ≤ 2‖θ‖ is against the
  max norm, which is enough for P₂ membership. Matches.
- W₂ behaviour: w2P (projP2 μ) (projP2 μ') ≤ w2H μ μ', with equality at ν = 0, is proved as
  theorems. It is consistent with the 1-Lipschitz property of marginal projection.
- On a diagonal law of an L² tuple, the image is Law(X,Y,Z), by the composition of pushforwards.
- The σ-finite / countably generated instance arguments are the paper's standing assumptions on
  (E,ν). ν = 0, the case used for Example 5.2, satisfies them. This is a harmless restriction to the
  paper's setting.
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-17T15:01:21Z): No disagreement on the substance. The author's entry (acceptance/review/definitions.md) records only the review marker and no comparison with the paper, so it does not state what I relied on: projP2 is the pushforward along the measurable projB (P2.mapOfLe_law), i.e. the (X,Y,Z) marginal, restricted to the paper's σ-finite / countably generated setting (ν = 0 included).
