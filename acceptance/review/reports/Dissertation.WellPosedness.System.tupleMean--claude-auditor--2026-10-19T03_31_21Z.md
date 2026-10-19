### A:ex:concrete, A:sec5:overview, A:sec:examples: Dissertation.WellPosedness.System.tupleMean
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash f12c7462da3145629603ec2e2a9cd3c9 (pl-fp-v1:653fe80f6b949f981587baff84b3ad87bd51b824b03833df94bd9a109100fb29)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:31:21Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:16:07Z):
Reading of def tupleMean.
Paper (Example 5.1(ii)): int_H theta dmu = (m_X(mu), m_Y(mu), m_Z(mu), m_U(mu)) in H, the Bochner mean of the
tuple, delta m := int theta dmu - int theta dmu' a single element of H. Faithful Lean: either the Bochner
integral of id in H, or the tuple of the four component Bochner means (equal, projections being continuous
linear and the measure in P_2). m_U(mu) in L2(nu;R^m) the Bochner mean in the L2 space (not a pointwise
integral of representatives unless shown equal). Values in H with H's components in the right order.
Comparison (verdict recorded 2026-10-19T03:29:17Z):
Comparison, def tupleMean: ∫ θ, θ ∂μ.law in TupleH ν n m d: the Bochner mean of the tuple in H; its
channels are the marginal Bochner means (tupleMean_eq), m_U the Bochner mean in L2(ν). Integrable on P2.
The norm on TupleH (max) does not affect the Bochner integral. Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-19T03:29:28Z): No disagreement on substance; I accept a point the review makes and my comparison did not: the
definition carries no countable-generation hypothesis, so for a non-separable L²(ν) the Bochner mean of the
identity could take Lean's junk value 0; in the paper's setting (ν σ-finite on a countably generated E)
L²(ν) is separable and the mean is genuine. With that caveat recorded, "faithful" (mine) and "faithful
with representation choices" (the review's) describe the same definition.
