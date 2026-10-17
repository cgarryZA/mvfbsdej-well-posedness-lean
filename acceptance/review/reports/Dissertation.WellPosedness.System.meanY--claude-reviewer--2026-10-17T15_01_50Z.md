### A:ex:concrete, A:prop:strict: Dissertation.WellPosedness.System.meanY
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash b1bbcb6b80a91cb129a220d0bfbb8cc1 (pl-fp-v1:62fd134d51dad3508d56faa1c7bebfec36accd900659791235d8a96e8a30d715)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:01:50Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:34:23Z):
Reading for def:Dissertation.WellPosedness.System.meanY (written before seeing any Lean).

Paper notion. Prop 3.8 (eq:bmean) and Example 5.1(ii): m_Y(mu) := \int_H y mu(d theta), the
Y-marginal mean of a law mu in P_2(H), H = R^n x R^m x R^{m x d} x L^2(nu;R^m). In both uses
m = 1 (n = m = 1 in Prop 3.8; n = m = d = 1 in Ex 5.1(ii)), so m_Y(mu) is a real number, but
the general notion is a vector in R^m (Bochner mean of the Y-coordinate). Along a diagonal input
m_Y(Law(Theta)) = E[Y] (the proof of Prop 3.8 uses exactly this).

A faithful Lean definition must:
- integrate the Y-coordinate (second component, valued in R^m) of the tuple, not X, Z or U,
  against the given measure mu (Bochner integral), with no extra normalisation;
- be defined on measures/laws on the tuple space H (probability measures, or Measure with the
  probability/P_2 condition imposed where used);
- junk values: for non-integrable y (mu not in P_1), Lean's Bochner integral returns 0. This is
  harmless provided every use is at a law in P_2(H) (diagonal laws of L^2 tuples, two-point laws
  in the pointwise-failure part of Prop 3.8, which are finitely supported hence in P_2).
- satisfy m_Y(Law(Theta)) = E[Y] when Theta is an L^2 (measurable) tuple, i.e. the integral is
  taken against the law as a measure on H (pushforward), compatible with change of variables.
Comparison (verdict recorded 2026-10-17T12:39:11Z):
Comparison for System.meanY.
Lean: meanY (μ : P2 (TupleH ν 1 1 d)) : EuclideanSpace ℝ (Fin 1) := ∫ θ, θ.2.1 ∂μ.law.
- Integrates the Y-coordinate θ.2.1 (second component of (x, y, z, u)) of the tuple: matches
  m_Y(μ) = ∫_H y μ(dθ). Bochner integral against the law, no normalisation. Matches.
- Domain: P2 (TupleH ν 1 1 d), i.e. probability measures with finite second moment on
  H = ℝ¹ × ℝ¹ × ℝ^{1×d} × L²(ν;ℝ¹). The paper uses m_Y only at n = m = 1 (Prop 3.8, Ex 5.1).
  Matches the uses; the general-m notion is not needed.
- Value in EuclideanSpace ℝ (Fin 1) rather than ℝ: the paper's y ∈ ℝ^m with m = 1. Harmless.
- Junk: the Y-coordinate is continuous and bounded by the norm, so on a P2 law it is integrable
  (finite second moment implies finite first moment on a probability space); the codomain is
  finite-dimensional, so strong measurability holds. No junk value is reachable on P2.
- On a diagonal law μ = lawP2 P Θ of an L² tuple, μ.law = P.map Θ and the change of variables
  gives E[Y]. Matches.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices: (1) the value is in EuclideanSpace ℝ (Fin 1) instead of ℝ, which is the
paper's y ∈ ℝ^m at m = 1; (2) the domain is fixed to the paper's only uses, n = m = 1, with laws
in P2 (TupleH ν 1 1 d) (probability measures of finite second moment), where the Y-coordinate is
integrable, so Lean's Bochner-integral junk value 0 is never reached.
Disagreements with the author's review (shown 2026-10-17T15:01:21Z): No disagreement on the substance. The author's entry (acceptance/review/definitions.md) records only the review marker and no comparison with the paper, so it does not state what I relied on: the Y-coordinate θ.2.1 is integrated against a P2 law (no junk reachable), at the paper's n = m = 1, with the value in EuclideanSpace ℝ (Fin 1).
