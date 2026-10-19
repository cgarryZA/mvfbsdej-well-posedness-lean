### A:abstract, A:ex:dealer, A:rem:regimes, A:sec5:overview: Dissertation.WellPosedness.Existence.DealerMark
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash f743d5d40f14218fb917137b1ad4a2ae (pl-fp-v1:9c8a2045f46697ce2c44ad9d071fe7260d29890d06fa7c4f9fc9853bbf5f56f8)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:28:16Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:15:20Z):
Reading of def:Dissertation.WellPosedness.Existence.DealerMark.

Paper notion (Example 5.5, "Marks and activity"): the dealer-market mark space
E = {-1,+1} x (0,1], e = (varsigma, q) with side varsigma in {-1,+1} and size q in (0,1],
carrying the product sigma-algebra (discrete on the sides, Borel on (0,1]; countably generated)
and the intensity nu(d varsigma, dq) = c_varsigma q^{-1-rho} dq (c_varsigma > 0, 0 < rho < 2),
sigma-finite with nu(E) = infinity.

Faithful Lean definition: a type (and its MeasurableSpace) representing {-1,+1} x (0,1]: e.g.
Bool x Set.Ioc 0 1, or Fin 2 x Ioc 0 1, or a structure with a side in {+-1} and a size q with
0 < q <= 1, with the product / Borel sigma-algebra. A larger carrier (e.g. side x R) is harmless
only if the intensity gives zero mass outside (0,1] and functions such as h_c = varsigma q are
read as elements of L2(nu). The side must carry the sign varsigma = +-1 (so h_c = varsigma q has
the right sign), and size must range over (0,1] (open at 0, where the density blows up; closed at
1). If DealerMark is a structure bundling more data (e.g. rho, c_varsigma), these must be as in
the paper (c_varsigma > 0, 0 < rho < 2).
Comparison (verdict recorded 2026-10-19T03:26:35Z):
def:Dissertation.WellPosedness.Existence.DealerMark (Examples/Dealer/Marks.lean:87-89):
  abbrev DealerMark : Type := Bool × Set.Ioc (0 : ℝ) 1,
side true ↦ +1, false ↦ −1 (markSide), size q ∈ (0,1] as a subtype of ℝ.
Against the reading: E = {−1,+1} × (0,1], with the product of the discrete σ-algebra on Bool
(Mathlib's ⊤ instance) and the subtype Borel σ-algebra on (0,1]: countably generated, as the
paper requires. The size range is exactly (0,1] (open at 0, closed at 1). The sign is carried by
markSide/(if e.1 then 1 else −1) where used. No extra data bundled. Bool for {±1} is a relabelling.
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-19T03:27:50Z): The author's review entry shown for DealerMark (acceptance/review/definitions.md:704) is empty, so I
have no stated reading to compare with. My finding: Bool × Set.Ioc (0:ℝ) 1 (true = +1) with the
discrete × subtype-Borel σ-algebra is the paper's E = {−1,+1} × (0,1]: faithful. The empty entry
should be filled in, or else checked to be a display artefact.
