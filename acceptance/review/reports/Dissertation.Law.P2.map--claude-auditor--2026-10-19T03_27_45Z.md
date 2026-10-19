### A:abstract, A:ex:dealer, A:ex:fulllaw, A:rem:regimes, A:rem:wasserstein-bounds, A:sec5:overview: Dissertation.Law.P2.map
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ea792c02836fa5e80da2ef5c07e4b0e0 (pl-fp-v1:2ed71eb455ce2d5aa92d40f91da7fc97ebd630a25787f1f279f53cedde4ce347)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:27:45Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:13:54Z):
Reading of def:Dissertation.Law.P2.map.

Paper notion. Image (pushforward) of a law under a map: marginal projection
P_2(H) -> P_2(L2(nu)), mu |-> mu^U (Remark 2.6 eq:margproj; Ex. 5.4 mu^U; Ex. 5.5 "mu^U the
U-marginal of the measure argument"), the X-marginal (eq:couplingT "the X-marginal case"),
"the population's quote-curve distribution is an affine image of mu^U" (Ex. 5.5), and the image of
a coupling under (theta,theta') |-> (u,u'). For mu in P_2(S) and phi : S -> S' Borel with at most
linear growth (|phi(x)| <= C(1+|x|), e.g. Lipschitz, affine, coordinate projection), phi_# mu
(A) = mu(phi^{-1}(A)) is a Borel probability measure on S' with finite second moment, so in
P_2(S').

Faithful Lean definition: P2.map phi mu := the element of P2 S' whose underlying measure is
Measure.map phi mu, under hypotheses on phi (measurability or continuity, plus a growth/Lipschitz
condition) that guarantee the P_2 property; the hypotheses are proof obligations, not part of the
meaning. It must be the pushforward of the given measure (not of a coupling, not a different
normalization). Junk: Measure.map with non-AEMeasurable phi is 0; the definition must require
measurability (or continuity) so that this junk cannot occur. Typical admissible classes: phi
Lipschitz (LipschitzWith K phi), continuous linear maps, or norm bounded |phi x| <= C|x| + c.
Comparison (verdict recorded 2026-10-19T03:18:45Z):
def:Dissertation.Law.P2.map (Dissertation/Law/P2.lean:94-105): for μ : P2 E, P : E → F with
Measurable P and ∀ x, ‖P x‖ ≤ ‖x‖ (F Borel), law := μ.law.map P, with the probability instance
(isProbabilityMeasure_map) and secondMoment(map) ≤ secondMoment μ < ⊤.
Against the reading: the value is the pushforward P_# μ, the paper's image law; measurability is
required, so Measure.map's junk 0 cannot occur. The admissible maps are restricted to
norm-nonexpanding measurable maps (coordinate projections such as the U-marginal and the
X-marginal qualify); the paper's affine images of μ^U are not covered by this constructor, but that
is a restriction of applicability (a proof obligation), not of meaning; other images go through
mapOfLe or not at all. Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-19T03:27:23Z): Only a classification difference: the earlier review says "faithful with representation choices";
I record faithful. The only departure I see, that only measurable norm-nonexpanding maps are
admitted, limits where the constructor applies, not what it means (its value is the pushforward
P_# μ). I cannot see which representation choice the earlier review recorded (its report is not
shown), so I cannot say more.
