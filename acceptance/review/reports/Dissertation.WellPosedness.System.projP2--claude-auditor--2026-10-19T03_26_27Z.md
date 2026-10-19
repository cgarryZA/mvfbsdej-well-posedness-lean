### A:ex:brownian, A:rem:beta1-dich, A:sec5:overview: Dissertation.WellPosedness.System.projP2
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash 09e433978a0199240fd17c10afb2cd5e (pl-fp-v1:9fe94b02cf06a3a4497bd70a2d95b57de28aca41f7f868ffacba3601d8d56c81)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:26:27Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:15:07Z):
Reading of def:Dissertation.WellPosedness.System.projP2.

Paper notion. In Example 5.2 the law argument of the reduced coefficients is the joint law of
(X, Y, Z), the image of the full tuple law mu = Law(X, Y, Z, U) in P2(H) under the projection
forgetting U: mu |-> (pi_{XYZ})_# mu in P2(R^n x R^m x R^{m x d}).  This is "marginal
projection" in the sense of Remark 2.6 (02-model-assumptions.tex:222-231, where the U-marginal
mu^U is the image under (x,y,z,u) |-> u, and is shown 1-Lipschitz for W2).

What a faithful Lean definition must be. The map P2(H) -> P2(ReducedTuple) sending mu to its
pushforward Measure.map projB mu (projB the measurable coordinate projection (x,y,z,u) |->
(x,y,z)), with the proof that the image is a probability measure with finite second moment
(automatic since projB is 1-Lipschitz and fixes 0).  No junk value should be possible: projB is
continuous, so Measure.map does not degenerate to 0; if the Lean P2 type is a subtype of measures
with a finite-second-moment predicate, the definition must carry that proof rather than default to
some arbitrary measure.  The second-moment notion must be that of the Hilbert norm of the reduced
space.  For the paper's use, (projP2 mu) for mu = Law(Theta) must equal Law(X, Y, Z).
If instead the definition goes the other way (lifting a reduced law to P2(H) via u = 0), it must be
the pushforward along (x,y,z) |-> (x,y,z,0); I will check the role against the uses.
Comparison (verdict recorded 2026-10-19T03:17:28Z):
Comparison for def:Dissertation.WellPosedness.System.projP2 (Examples/Brownian.lean:150-152).

Lean: projP2 (mu : P2 (TupleH nu n m d)) : P2 (ReducedTuple n m d) :=
  mu.mapOfLe measurable_projB norm_projB_le,
where P2.mapOfLe (Law/P2Quantize.lean:56-71) has law := mu.law.map projB, the probability
property from measurability, and the finite second moment from ||projB theta|| <= 2 ||theta||
(norm_projB_le; the factor 2 because TupleH carries the max-of-channels norm). P2.mapOfLe_law: the
law is exactly Measure.map projB mu.law (rfl).

Against my reading:
- The image law is the pushforward of mu under the coordinate projection forgetting U, i.e. the
  joint (X, Y, Z)-marginal: for mu = Law(Theta), projP2 mu = Law(X, Y, Z). Matches.
- projB is measurable, so Measure.map does not degenerate (no junk zero measure).
- The P2 bundling carries a genuine proof of finite second moment in the reduced (Hilbert) norm
  (secondMoment of the pushforward <= 4 * secondMoment of mu); no default value is used.
- P2(TupleH) is defined with the second moment in the sup norm of TupleH; as that is within a
  factor 2 of the Hilbert norm, the class of laws is the paper's P2(H). Fine.
- Extra instance arguments [SigmaFinite nu] [CountablyGenerated E] (section variables) are standing
  hypotheses; harmless.
- W2 compatibility (not part of the definition, but its use): w2P (projP2 mu) (projP2 mu') <=
  w2H mu mu' with equality at nu = 0 (w2P_projP2_le, w2P_projP2), as the paper's marginal-projection
  bound needs.
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-19T03:26:15Z): none
