### A:abstract, A:ex:dealer, A:ex:fulllaw, A:rem:regimes, A:remark-2.6, A:sec5:overview: Dissertation.Law.P2.map
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash ea792c02836fa5e80da2ef5c07e4b0e0 (pl-fp-v1:2ed71eb455ce2d5aa92d40f91da7fc97ebd630a25787f1f279f53cedde4ce347)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:50:57Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T15:41:49Z):
Reading for def:Dissertation.Law.P2.map.

Paper notion: the image (pushforward) of a law under a map, e.g. the U-marginal mu^U of
mu in P2(H) (pushforward by theta |-> u), the image of a coupling under (theta, theta') |-> (u,u')
(Remark 2.6, (2.10)), and the affine image of mu^U in Ex 5.5. Pushforward of a P2 measure under a
measurable map with at most linear growth (e.g. Lipschitz, or a projection) is again in P2.

Faithful Lean: P2.map F mu = F_# mu (Measure.map F mu), packaged as an element of P2, requiring F
measurable (AEMeasurable) and with a proof (or a structural guarantee, e.g. F Lipschitz) that the
pushforward has finite second moment. Edge case: Measure.map of a non-measurable map is 0 in
Mathlib (not a probability measure); so the definition must take measurability as a hypothesis or
restrict to (Lipschitz/continuous) maps. For the U-marginal the map is the 4th-coordinate
projection of H.
Comparison (verdict recorded 2026-10-17T15:50:05Z):
Comparison for def:Dissertation.Law.P2.map (Law/P2.lean:94-105): for mu : P2 E, a measurable
P : E -> F with ||P x|| <= ||x|| for all x, and F Borel: law := mu.law.map P (pushforward), probability
by isProbabilityMeasure_map, finite second moment by monotonicity.

Matches my reading: the image law P_# mu as an element of P2, with measurability required (so the
Mathlib junk map = 0 for non-measurable maps cannot occur) and finiteness of the second moment
guaranteed by the norm bound. The domain is restricted to norm-non-increasing maps, which covers
every use: marginal projections of H onto a coordinate (e.g. margU, the U-marginal; for the max-norm
TupleH and for the Hilbert norm alike ||u|| <= ||theta||) and the Hilbert re-norming handled
separately by mapOfLe. The paper's "affine image of mu^U" in the narrative of Ex 5.5 is not a formal
object. Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Choice: the pushforward is defined only along measurable maps that do not increase the norm
(||P x|| <= ||x||), which guarantees that the image has finite second moment without a separate proof
argument; every use (coordinate/marginal projections such as the U-marginal of a law on H) is of
this kind. Within its domain it is exactly the image law P_# mu.
Disagreements with the author's review (shown 2026-10-17T15:50:12Z): No disagreement with a stated position (the author's entry shown is only the section heading). For
the record: faithful with the representation choice that the pushforward is only defined along
measurable norm-non-increasing maps, which covers every use (marginal projections).
