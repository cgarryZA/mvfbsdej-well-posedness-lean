### A:rem:generalrank: Dissertation.PaperSpec.A.Margin212
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 2ad64300a1211b9647d3727884567824 (pl-fp-v1:61069a19a65f6fe5337c169b83b8bc3acca0b75970985f78cd2a0f99c552ab0a)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T12:22:34Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:21:29Z):
# Reading: (2.12), interior monotonicity with weighted margin c (def:Dissertation.PaperSpec.A.Margin212)

Paper (Remark 2.10, eq. (2.12) = eq:monomargin; Remark 3.7). "(2.7) holds with margin c > 0" if,
for a.e. t ∈ [0,T] and all diagonal inputs (Θ, μ), (Θ', μ') ∈ D_t (Θ, Θ' ∈ L^2(Ω, F_t; H),
μ = Law Θ, μ' = Law Θ'), with δψ = ψ(t,Θ,μ) − ψ(t,Θ',μ'):
  E[⟨δb, Gᵀ δY⟩ + ⟨δσ, Gᵀ δZ⟩_F + ⟨−δf, G δX⟩ + ∫_E ⟨δh(e), Gᵀ δU(e)⟩ ν(de)]
   ≤ −β_1 E[|Gᵀ δY|^2 + |Gᵀ δZ|_F^2 + ‖Gᵀ δU‖^2] − β_2 E|G δX|^2
     − c E[|Gᵀ δY|^2 + |Gᵀ δZ|_F^2 + ‖Gᵀ δU‖^2_{L^2(ν)} + |G δX|^2].
Weighted form: the margin term uses the G-projections (unlike (2.13), which is unweighted).
Here Gᵀ δZ is the m... (Gᵀ ∈ R^{n×m} acting on the columns of δZ ∈ R^{m×d}, giving R^{n×d}) and
Gᵀ δU ∈ L^2(ν; R^n) pointwise in e; ⟨δσ, Gᵀ δZ⟩_F the Frobenius pairing.

A faithful Lean definition (of the property, with parameters T, G, β_1, β_2, c and the
coefficients): quantifier "for a.e. t ∈ [0,T]" (Lebesgue on [0,T]), then for all F_t-measurable
square-integrable H-valued Θ, Θ' with their laws, the inequality between expectations (real
numbers). The interior pairing and the dissipation must be the same as in (2.7); the extra term
c·E[...] with the weighted quantities, all four of them (Y, Z, U projected by Gᵀ, X by G). The
constraint c > 0 may be a separate hypothesis. The probability space/filtration must be the
§2 one (or the property quantified as in the corresponding Ass. 2.5 definition). Expectations
of integrable quantities (Bochner integral junk 0 for non-integrable ones is harmless only if
both sides are integrable for L^2 inputs, which holds under the Lipschitz assumption).
Comparison (verdict recorded 2026-10-17T12:22:23Z):
# Comparison: Margin212

Lean (PaperSpec/A/Sec2Remarks.lean:179-198): for a filtration ℱ, P, T, G, β₁, β₂, c, C:
∀ᵐ t ∂(Lebesgue on [0,T]), ∀ p, p' ∈ diagonalInputs ν n m d ℱ P t,
  Integrable (ω ↦ pairing27 G C t (p.1 ω) (p'.1 ω) p.2 p'.2) P ∧
  E[pairing27 …] ≤ −β₁ E[|GᵀδY|² + |GᵀδZ|² + ‖GᵀδU‖²] − β₂ E|GδX|²
                  − c E[|GᵀδY|² + |GᵀδZ|² + ‖GᵀδU‖² + |GδX|²].

- Quantifiers: a.e. t ∈ [0,T], then all pairs of D_t. `diagonalInputs … t` = {(Θ, μ) : Θ strongly
  ℱ_t-measurable, Θ ∈ L^2(P; H), μ = lawP2 P Θ} — Definition 2.1 (every L^2(Ω, F_t; H) class has
  a strongly F_t-measurable representative; μ is the genuine law since Θ ∈ L^2). Good.
- pairing27 (WellPosedness/Spec/Assumptions.lean:165): ⟨δb, GX Gᵀ δY⟩ + ⟨δσ, GZ Gᵀ δZ⟩ +
  ⟨−δf, GX G δX⟩ + ∫_E ⟨δh(e), Gᵀ δU(e)⟩ ν(de), δψ = ψ(t,θ,μ) − ψ(t,θ',μ'). GX G = x ↦ Gx,
  GZ Gᵀ = column-wise Gᵀ on R^{m×d} (Kronecker Gᵀ ⊗ I_d) into R^{n×d}, inner on
  EuclideanSpace (Fin n × Fin d) = Frobenius pairing; the jump term pointwise through
  representatives of the L^2(ν) elements, integrated against ν. Exactly (2.7)/(2.12)'s
  left side. Good.
- Right side: β₁-block with |Gᵀ δY|², |Gᵀ δZ|_F², ‖Gᵀ δU‖²_{L^2(ν)} (GU Gᵀ ν = mark-wise Gᵀ on
  L^2(ν; R^m)), β₂-block with |G δX|², and the margin term c·E of the four WEIGHTED quantities
  (Gᵀ on Y, Z, U; G on X): the weighted form (2.12), not the unweighted (2.13). Good.
- Constants: c (no sign constraint inside; c > 0 belongs to the user). β₁, β₂ any reals. Fine.
- Extra conjunct: integrability of the pairing ("the expectation of the pairing exists").
  The paper's E[...] presupposes it; under Ass. 2.3 (the context of Remark 3.7: a baseline
  satisfying Ass. 2.2–2.5) it holds for all L^2 diagonal inputs (Lipschitz bound on the
  differences and Cauchy–Schwarz). Matches the convention of the repository's Ass. 2.5
  (`Mono27At`). Harmless.
- The filtration/probability space is a parameter; instantiated by the users.
- Norms on TupleH are not involved (only the channel norms). The squared-norm integrals are
  Bochner integrals of integrable functions for L^2 inputs (no junk).

Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices:
1. The inequality is accompanied by the requirement that the pairing be integrable (the
   expectation exists), as in the repository's Assumption 2.5. The paper's "E[...] ≤ ..."
   presupposes the expectation; in its use (Remark 3.7, baseline under Ass. 2.2–2.5) the
   Lipschitz bound of Ass. 2.3 makes the pairing integrable for every pair of L^2 diagonal
   inputs, so nothing is lost.
2. D_t is represented by strongly F_t-measurable square-integrable maps Θ : Ω → H together with
   lawP2 P Θ; every class of L^2(Ω, F_t; H) has such a representative, and the expectations do
   not depend on it.
3. The jump pairing ∫⟨δh(e), Gᵀ δU(e)⟩ ν(de) is computed through representatives of the
   L^2(ν) elements; it equals the L^2(ν) inner product ⟨δh, GU Gᵀ δU⟩ independent of them.
Disagreements with the author's review (shown 2026-10-17T12:22:23Z): No disagreement on meaning. The author's entry shown (definitions.md:304) is only a section heading; it records no reading of Margin212 (weighted margin term; the added integrability conjunct; quantification over D_t a.e. in t).
