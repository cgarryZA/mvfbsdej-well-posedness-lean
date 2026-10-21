/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Examples.Dealer.Coeffs
import Dissertation.WellPosedness.Robustness.Margin

/-!
# Example 5.5: monotonicity of the crowding correction

Let `U, U'` be integrable random elements of a separable Hilbert space `F` on a probability space
`(Ω, P)`, and `A_λ(u) = ∫ ∇V(u − v) λ(dv)` the crowding operator. Then

`𝔼⟨A_{Law U}(U) − A_{Law U'}(U'), U − U'⟩ ≥ 0`.

On `(Ω × Ω, P ⊗ P)` the second coordinate carries an independent copy `(Û, Û')` of `(U, U')`, and
`A_{Law U}(U(ω)) = ∫ ∇V(U(ω) − U(ω')) P(dω')`, so the left-hand side is the integral over `P ⊗ P`
of

`k(ω, ω') = ⟨∇V(U(ω) − U(ω')) − ∇V(U'(ω) − U'(ω')), U(ω) − U'(ω)⟩`,

integrable since `‖∇V‖ ≤ 1` and `U − U' ∈ L¹(P)`. The swap `(ω, ω') ↦ (ω', ω)` preserves `P ⊗ P`,
and `∇V` is odd, so with `a = U(ω) − U(ω')`, `b = U'(ω) − U'(ω')`,

`k(ω, ω') + k(ω', ω) = ⟨∇V(a) − ∇V(b), a − b⟩ ≥ 0`

by the monotonicity of `∇V`; averaging the integral of `k` with that of `k ∘ swap` gives the
claim. For square-integrable `U, U'` the law `Law U` is `lawP2 P U`.

For two square-integrable tuples `Θ, Θ'` of the tuple space with laws `μ, μ'`, the `U`-marginals are
`μ^U = Law U`, `μ'^U = Law U'` (`Dissertation.WellPosedness.System.margU_lawP2`), so at `G = I` the
interior pairing of the dealer system of Example 5.5 is that of Example 5.1(i) minus
`ε ⟨A_{μ^U}(U) − A_{μ'^U}(U'), U − U'⟩`, of nonnegative expectation. The crowding correction thus
only improves the interior pairing,

`𝔼 ∫_E ⟨δh(e), δU(e)⟩ ν(de) ≤ −β₁ 𝔼 ‖δU‖²_{L²(ν)}`,

and (2.7) holds with `G = I` and the constants `β₁, β₂` of Example 5.1(i), for every `ε ≥ 0`.

## Main statements

* `Dissertation.Law.crowdOp_map` — `A_{Law U}(x) = 𝔼 ∇V(x − U)`.
* `Dissertation.Law.integrable_inner_crowdOp_sub` — the pairing is integrable.
* `Dissertation.Law.integral_inner_crowdOp_sub_nonneg` — the pairing has nonnegative expectation.
* `Dissertation.Law.integral_inner_crowdOp_lawP2_sub_nonneg` — the same for square-integrable
  random elements and their laws of finite second moment.
* `interiorPairing_dealer` — the interior pairing of the dealer system at `G = I`.
* `diagonalMonotone_dealer` — Assumption 2.5, interior, with `G = I` and the constants `β₁, β₂`,
  for every `ε ≥ 0`.
* `terminalMonotone_dealer` — Assumption 2.5, terminal, with `G = I` and `α = 1`.
-/

open MeasureTheory Filter
open scoped RealInnerProductSpace

namespace Dissertation.Law

/-! ### The independent-copy argument -/

section IndependentCopy

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {U U' : Ω → F}

omit [IsProbabilityMeasure P] [CompleteSpace F] in
/-- **The crowding operator of the law of a random element** is an expectation:
`A_{Law U}(x) = 𝔼 ∇V(x − U)`. -/
theorem crowdOp_map (hU : AEMeasurable U P) (x : F) :
    crowdOp (P.map U) x = ∫ ω, crowdGrad (x - U ω) ∂P :=
  integral_map hU (stronglyMeasurable_crowdGrad_sub x).aestronglyMeasurable

omit [CompleteSpace F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] in
/-- `ω' ↦ ∇V(x − U(ω'))` is integrable. -/
theorem integrable_crowdGrad_sub_comp (hU : AEStronglyMeasurable U P) (x : F) :
    Integrable (fun ω => crowdGrad (x - U ω)) P :=
  Integrable.of_bound
    (continuous_crowdGrad.comp_aestronglyMeasurable (aestronglyMeasurable_const.sub hU)) 1
    (Eventually.of_forall fun _ => norm_crowdGrad_le_one _)

omit [CompleteSpace F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] in
/-- A bound `|⟨a − b, c⟩| ≤ 2 ‖c‖` for `‖a‖, ‖b‖ ≤ 1`. -/
private theorem abs_inner_sub_le {a b c : F} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖⟪a - b, c⟫‖ ≤ 2 * ‖c‖ := by
  rw [Real.norm_eq_abs]
  refine (abs_real_inner_le_norm _ _).trans ?_
  have := norm_sub_le a b
  nlinarith [norm_nonneg c, norm_nonneg (a - b)]

omit [CompleteSpace F] in
/-- **The crowding pairing is integrable**: for integrable `U, U'`,
`ω ↦ ⟨A_{Law U}(U(ω)) − A_{Law U'}(U'(ω)), U(ω) − U'(ω)⟩` is integrable. -/
theorem integrable_inner_crowdOp_sub (hU : Integrable U P) (hU' : Integrable U' P) :
    Integrable (fun ω => ⟪crowdOp (P.map U) (U ω) - crowdOp (P.map U') (U' ω), U ω - U' ω⟫) P := by
  haveI := Measure.isProbabilityMeasure_map (μ := P) hU.aemeasurable
  haveI := Measure.isProbabilityMeasure_map (μ := P) hU'.aemeasurable
  refine Integrable.mono' ((hU.sub hU').norm.const_mul 2)
    ((((continuous_crowdOp _).comp_aestronglyMeasurable hU.1).sub
      ((continuous_crowdOp _).comp_aestronglyMeasurable hU'.1)).inner (hU.1.sub hU'.1))
    (Eventually.of_forall fun ω => ?_)
  exact abs_inner_sub_le (norm_crowdOp_le_one _ _) (norm_crowdOp_le_one _ _)

/-- **The crowding pairing has nonnegative expectation.** For integrable random elements `U, U'`
of `F`, `𝔼⟨A_{Law U}(U) − A_{Law U'}(U'), U − U'⟩ ≥ 0`. -/
theorem integral_inner_crowdOp_sub_nonneg (hU : Integrable U P) (hU' : Integrable U' P) :
    0 ≤ ∫ ω, ⟪crowdOp (P.map U) (U ω) - crowdOp (P.map U') (U' ω), U ω - U' ω⟫ ∂P := by
  set k : Ω × Ω → ℝ := fun z =>
    ⟪crowdGrad (U z.1 - U z.2) - crowdGrad (U' z.1 - U' z.2), U z.1 - U' z.1⟫ with hk
  have h1 : AEStronglyMeasurable (fun z : Ω × Ω => U z.1) (P.prod P) := hU.1.comp_fst
  have h2 : AEStronglyMeasurable (fun z : Ω × Ω => U z.2) (P.prod P) := hU.1.comp_snd
  have h1' : AEStronglyMeasurable (fun z : Ω × Ω => U' z.1) (P.prod P) := hU'.1.comp_fst
  have h2' : AEStronglyMeasurable (fun z : Ω × Ω => U' z.2) (P.prod P) := hU'.1.comp_snd
  have hki : Integrable k (P.prod P) := by
    refine Integrable.mono' (((hU.sub hU').norm.const_mul 2).comp_fst P)
      (((continuous_crowdGrad.comp_aestronglyMeasurable (h1.sub h2)).sub
        (continuous_crowdGrad.comp_aestronglyMeasurable (h1'.sub h2'))).inner (h1.sub h1'))
      (Eventually.of_forall fun z => ?_)
    exact abs_inner_sub_le (norm_crowdGrad_le_one _) (norm_crowdGrad_le_one _)
  have hsec : ∀ ω, ⟪crowdOp (P.map U) (U ω) - crowdOp (P.map U') (U' ω), U ω - U' ω⟫
      = ∫ ω', k (ω, ω') ∂P := fun ω => by
    have hi := integrable_crowdGrad_sub_comp hU.1 (U ω)
    have hi' := integrable_crowdGrad_sub_comp hU'.1 (U' ω)
    rw [crowdOp_map hU.aemeasurable, crowdOp_map hU'.aemeasurable, ← integral_sub hi hi',
      real_inner_comm, ← integral_inner (f := fun a => crowdGrad (U ω - U a)
        - crowdGrad (U' ω - U' a)) (hi.sub hi')]
    exact integral_congr_ae (Eventually.of_forall fun ω' => real_inner_comm _ _)
  have hprod : ∫ ω, ⟪crowdOp (P.map U) (U ω) - crowdOp (P.map U') (U' ω), U ω - U' ω⟫ ∂P
      = ∫ z, k z ∂(P.prod P) := by
    simp_rw [hsec]
    exact (integral_prod k hki).symm
  have hsum : ∀ z, 0 ≤ k z + k z.swap := by
    rintro ⟨ω, ω'⟩
    have e : k (ω, ω') + k (ω, ω').swap
        = ⟪crowdGrad (U ω - U ω') - crowdGrad (U' ω - U' ω'),
            (U ω - U ω') - (U' ω - U' ω')⟫ := by
      simp only [hk, Prod.swap_prod_mk]
      rw [← neg_sub (U ω) (U ω'), ← neg_sub (U' ω) (U' ω'), crowdGrad_neg, crowdGrad_neg,
        neg_sub_neg, ← neg_sub (crowdGrad (U ω - U ω')), inner_neg_left, ← sub_eq_add_neg,
        ← inner_sub_right]
      congr 1
      abel
    rw [e]
    exact inner_crowdGrad_sub_nonneg _ _
  have hswap : ∫ z, k z.swap ∂(P.prod P) = ∫ z, k z ∂(P.prod P) := integral_prod_swap k
  have hnn : 0 ≤ ∫ z, (k z + k z.swap) ∂(P.prod P) := integral_nonneg hsum
  have hki' : Integrable (fun z => k z.swap) (P.prod P) := hki.swap
  rw [integral_add hki hki', hswap] at hnn
  rw [hprod]
  linarith

/-- **The crowding pairing has nonnegative expectation, for laws of finite second moment.** For
square-integrable random elements `U, U'` of `F`,
`𝔼⟨A_{Law U}(U) − A_{Law U'}(U'), U − U'⟩ ≥ 0`, with `Law U = lawP2 P U`. -/
theorem integral_inner_crowdOp_lawP2_sub_nonneg (hU : MemLp U 2 P) (hU' : MemLp U' 2 P) :
    0 ≤ ∫ ω, ⟪crowdOp (lawP2 P U).law (U ω) - crowdOp (lawP2 P U').law (U' ω), U ω - U' ω⟫ ∂P := by
  rw [lawP2_law hU, lawP2_law hU']
  exact integral_inner_crowdOp_sub_nonneg (hU.integrable one_le_two) (hU'.integrable one_le_two)

omit [CompleteSpace F] in
/-- The crowding pairing of square-integrable random elements and their laws of finite second
moment is integrable. -/
theorem integrable_inner_crowdOp_lawP2_sub (hU : MemLp U 2 P) (hU' : MemLp U' 2 P) :
    Integrable (fun ω =>
      ⟪crowdOp (lawP2 P U).law (U ω) - crowdOp (lawP2 P U').law (U' ω), U ω - U' ω⟫) P := by
  rw [lawP2_law hU, lawP2_law hU']
  exact integrable_inner_crowdOp_sub (hU.integrable one_le_two) (hU'.integrable one_le_two)

end IndependentCopy

end Dissertation.Law

namespace Dissertation.WellPosedness.Existence

open Dissertation.WellPosedness.System Dissertation.Law

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]
  [MeasurableSpace.CountablyGenerated E] {n d : ℕ} {β₁ β₂ ε : ℝ}
  {σc : EuclideanSpace ℝ (Fin n × Fin d)} {hc : Lp (EuclideanSpace ℝ (Fin n)) 2 ν}

omit [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
/-- **The interior pairing of the dealer system** at `G = I` is that of Example 5.1(i), the
dissipation at the system's own `β₁, β₂`, minus `ε ⟨A_{μ^U}(u) − A_{μ'^U}(u'), u − u'⟩`. -/
theorem interiorPairing_dealer (t : ℝ) (θ θ' : TupleH ν n n d) (μ μ' : P2 (TupleH ν n n d)) :
    interiorPairing (GX (1 : Matrix (Fin n) (Fin n) ℝ)) (GZ 1) (GU 1 ν)
        (diagDiff (dealerCoeffs β₁ β₂ σc hc ε) t θ θ' μ μ')
      = dissipation (GX (1 : Matrix (Fin n) (Fin n) ℝ)) (GZ 1) (GU 1 ν) β₁ β₂
          (diagDiff (dealerCoeffs β₁ β₂ σc hc ε) t θ θ' μ μ')
        - ε * ⟪crowdOp μ.margU.law θ.2.2.2 - crowdOp μ'.margU.law θ'.2.2.2,
            θ.2.2.2 - θ'.2.2.2⟫ := by
  rw [interiorPairing_diagDiff_perturb, interiorPairing_affine, dissipation_diagDiff_perturb]
  have e : -(ε • crowdOp μ.margU.law θ.2.2.2) - -(ε • crowdOp μ'.margU.law θ'.2.2.2)
      = -(ε • (crowdOp μ.margU.law θ.2.2.2 - crowdOp μ'.margU.law θ'.2.2.2)) := by
    rw [smul_sub]
    abel
  simp only [interiorPairing, diagDiff, crowdPert, GX_one, GZ_one, GU_one,
    ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_apply, sub_self, inner_zero_left,
    neg_zero, zero_add, e, inner_neg_left, real_inner_smul_left]
  ring

variable {Ω : Type*} [MeasurableSpace Ω] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {P : Measure Ω}
  [IsProbabilityMeasure P] {T : ℝ}

/-- **The crowding pairing along two square-integrable tuples has nonnegative expectation**: for
`Θ, Θ'` with laws `μ, μ'` and `U`-channels `U, U'`, `𝔼⟨A_{μ^U}(U) − A_{μ'^U}(U'), U − U'⟩ ≥ 0`. -/
theorem integral_inner_crowdOp_margU_sub_nonneg {Θ Θ' : Ω → TupleH ν n n d} (hΘ : MemLp Θ 2 P)
    (hΘ' : MemLp Θ' 2 P) :
    0 ≤ ∫ ω, ⟪crowdOp (lawP2 P Θ).margU.law (Θ ω).2.2.2
        - crowdOp (lawP2 P Θ').margU.law (Θ' ω).2.2.2, (Θ ω).2.2.2 - (Θ' ω).2.2.2⟫ ∂P := by
  rw [margU_lawP2 hΘ, margU_lawP2 hΘ']
  exact integral_inner_crowdOp_lawP2_sub_nonneg hΘ.snd.snd.snd hΘ'.snd.snd.snd

/-- The crowding pairing along two square-integrable tuples is integrable. -/
theorem integrable_inner_crowdOp_margU_sub {Θ Θ' : Ω → TupleH ν n n d} (hΘ : MemLp Θ 2 P)
    (hΘ' : MemLp Θ' 2 P) :
    Integrable (fun ω => ⟪crowdOp (lawP2 P Θ).margU.law (Θ ω).2.2.2
        - crowdOp (lawP2 P Θ').margU.law (Θ' ω).2.2.2, (Θ ω).2.2.2 - (Θ' ω).2.2.2⟫) P := by
  rw [margU_lawP2 hΘ, margU_lawP2 hΘ']
  exact integrable_inner_crowdOp_lawP2_sub hΘ.snd.snd.snd hΘ'.snd.snd.snd

/-- **Assumption 2.5, interior, along the diagonal, for the dealer system**, at every interaction
strength `ε ≥ 0`: with `G = I` and the constants `β₁, β₂` of Example 5.1(i),
`𝔼[⟨δb, δY⟩ + ⟨δσ, δZ⟩_F − ⟨δf, δX⟩ + ∫_E ⟨δh(e), δU(e)⟩ ν(de)]
  ≤ −β₁ 𝔼[|δY|² + |δZ|²_F + ‖δU‖²_{L²(ν)}] − β₂ 𝔼|δX|²`. -/
theorem diagonalMonotone_dealer (hε : 0 ≤ ε) :
    DiagonalMonotone ℱ P T (1 : Matrix (Fin n) (Fin n) ℝ) β₁ β₂ (dealerCoeffs β₁ β₂ σc hc ε) := by
  refine Eventually.of_forall fun t Θ Θ' _ _ hΘ hΘ' => ?_
  have hD := integrable_dissipation_diagDiff (GX (1 : Matrix (Fin n) (Fin n) ℝ)) (GZ 1) (GU 1 ν)
    β₁ β₂ (dealerCoeffs β₁ β₂ σc hc ε) t (lawP2 P Θ) (lawP2 P Θ') hΘ hΘ'
  have hA := integrable_inner_crowdOp_margU_sub hΘ hΘ'
  have hA0 := integral_inner_crowdOp_margU_sub_nonneg hΘ hΘ'
  simp_rw [interiorPairing_dealer]
  rw [integral_sub hD (hA.const_mul ε), integral_const_mul]
  nlinarith [mul_nonneg hε hA0]

omit [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
/-- **Assumption 2.5, terminal, along the diagonal, for the dealer system**, with `G = I` and
`α = 1`: `𝔼|δX_T|² = 𝔼⟨δg_T, δX_T⟩`. -/
theorem terminalMonotone_dealer :
    TerminalMonotone ℱ P T (1 : Matrix (Fin n) (Fin n) ℝ) 1 (dealerCoeffs β₁ β₂ σc hc ε).g :=
  terminalMonotone_affine (β₁ := β₁) (β₂ := β₂) (σc := σc) (hc := hc)

end Dissertation.WellPosedness.Existence
