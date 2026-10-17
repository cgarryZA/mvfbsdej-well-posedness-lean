### A:ex:concrete, A:sec:examples: Dissertation.WellPosedness.System.tupleMean
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash f12c7462da3145629603ec2e2a9cd3c9 (pl-fp-v1:653fe80f6b949f981587baff84b3ad87bd51b824b03833df94bd9a109100fb29)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:01:51Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:34:24Z):
Reading for def:Dissertation.WellPosedness.System.tupleMean (written before seeing any Lean).

Paper notion. Example 5.1(ii): the marginal means m_Psi(mu) := \int_H pi_Psi(theta) mu(dtheta),
Psi in {X,Y,Z,U}, and delta m := (delta m_X, delta m_Y, delta m_Z, delta m_U) =
\int_H theta dmu - \int_H theta dmu', "a single element of H". So tupleMean(mu) is the
barycentre \int_H theta mu(dtheta) in H, componentwise (m_X(mu), m_Y(mu), m_Z(mu), m_U(mu)),
where m_U(mu) is an element of L^2(nu;R^m) (Bochner mean of the U-marginal), used in
h(e) = -2u(e) - m_U(mu)(e). Along a diagonal input, m_Psi(Law(Theta)) = E[Psi]. (Also used for
the Li--Min Ex. 3.2 linear system in the Section 5 preamble, whose coefficients involve
expectations of the state.)

A faithful Lean definition must:
- be the Bochner integral of the identity of H against mu (or the tuple of the four componentwise
  Bochner integrals, which coincide for integrable mu), in the H-structure with the paper's norm;
- give the U-mean as an L^2(nu) element (not, e.g., a pointwise integral that might not descend
  to the class);
- junk: Lean's Bochner integral is 0 for non-integrable mu; harmless when used only at laws in
  P_2(H).
Comparison (verdict recorded 2026-10-17T12:39:11Z):
Comparison for System.tupleMean.
Lean: tupleMean (μ : P2 (TupleH ν n m d)) : TupleH ν n m d := ∫ θ, θ ∂μ.law.
- Bochner integral of the identity of H against μ: the barycentre ∫_H θ dμ of Ex 5.1(ii),
  "a single element of H". Matches. Componentwise it is (m_X, m_Y, m_Z, m_U) with m_U the Bochner
  mean in L²(ν;ℝ^m) (the integral commutes with the continuous linear projections). Matches.
- The integral does not depend on the norm chosen on the product (the max norm of TupleH is
  equivalent to the Hilbert norm; integrability and the integral coincide). Harmless.
- TupleH is complete (product of Euclidean spaces and Lp, p = 2), so the integral is not the
  "incomplete space" junk 0. On P2, ‖θ‖ is integrable. Strong measurability of the identity needs
  separability of H, which holds in the paper's standing setting (ν σ-finite on a countably
  generated E, so L²(ν) separable). The definition has no such hypothesis, so for a non-separable
  L²(ν) Lean could return junk 0; that case is outside the paper's setting.
- Along a diagonal law, the mean is E[Θ]. Matches.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices: (1) the barycentre is the Bochner integral in TupleH, whose instance norm
is the max of the channel norms instead of the paper's Hilbert norm. The norms are equivalent, so
integrability and the value of the integral are the same. (2) The domain is P2 (TupleH ν n m d).
There ‖θ‖ is integrable. Strong measurability of the identity holds whenever L²(ν) is separable
(ν σ-finite, E countably generated, as the paper assumes), so Lean's junk 0 is not reached in
the paper's setting. The definition itself does not assume separability; outside the paper's
setting it could return junk 0.
Disagreements with the author's review (shown 2026-10-17T15:01:22Z): No disagreement on the substance. The author's entry (acceptance/review/definitions.md) records only the review marker and no comparison with the paper, so it does not state what I relied on: the Bochner integral of the identity in the complete space TupleH. It is independent of the (equivalent) max norm, and Lean's junk 0 is avoided only when L²(ν) is separable (the paper's setting), which the definition does not assume.
