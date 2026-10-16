/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Dissertation.Law.Gluing
import Dissertation.Law.P2

/-!
# The triangle inequality for the 2-Wasserstein distance

Gluing a coupling of `(μ, ν)` and a coupling of `(ν, ρ)` along the marginal `ν` they share
produces a measure on `E × E × E` whose outer projection couples `(μ, ρ)`. The norm inequality
`‖x - z‖ ≤ ‖x - y‖ + ‖y - z‖` and Minkowski's inequality at exponent two for the three-point cost
bound the root quadratic cost of that coupling by the sum of the root costs of the two given
ones, and taking the infimum over the two couplings independently turns that bound into the
triangle inequality for the root of the squared 2-Wasserstein distance in `ℝ≥0∞`, hence for the
real-valued distance and for the distance on the laws of finite second moment. The disintegration
behind the gluing requires the space to be complete, and the real-valued form needs finiteness of
the two squared distances because `w2` reads an infinite squared distance back as `0`.

## Main statements

* `Dissertation.Law.le_iInf_add_iInf`: an element of `ℝ≥0∞` below every pairwise sum lies below
  the sum of the two infima.
* `Dissertation.Law.lintegral_normSq_sub_rpow_le`: Minkowski's inequality at exponent two for the
  quadratic cost of three measurable maps.
* `Dissertation.Law.w2sq_rpow_le_of_couplings`: two couplings along a common marginal bound the
  root squared distance between the outer laws.
* `Dissertation.Law.w2sq_rpow_triangle`: the triangle inequality in `ℝ≥0∞`.
* `Dissertation.Law.w2_triangle`, `Dissertation.Law.w2P_triangle`: the triangle inequality for
  the real-valued distance.
* `Dissertation.Law.abs_w2P_sub_w2P_le`: the distance to a fixed law is `1`-Lipschitz.
* `Dissertation.Law.w2P_dirac_dirac`: the distance between two Dirac masses is the distance
  between their points.
-/

namespace Dissertation.Law

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-! ### Infima and real powers in `ℝ≥0∞` -/

section ENNRealAux

/-- An element below every pairwise sum lies below the sum of the two infima. -/
theorem le_iInf_add_iInf {ι κ : Sort*} {a : ℝ≥0∞} {B : ι → ℝ≥0∞} {C : κ → ℝ≥0∞}
    (h : ∀ i j, a ≤ B i + C j) : a ≤ (⨅ i, B i) + (⨅ j, C j) := by
  rw [← tsub_le_iff_right]
  refine le_iInf fun i => ?_
  rw [tsub_le_iff_right, ← tsub_le_iff_left]
  exact le_iInf fun j => tsub_le_iff_left.2 (h i j)

/-- A positive real power commutes with an infimum in `ℝ≥0∞`. -/
theorem iInf_rpow {ι : Sort*} (f : ι → ℝ≥0∞) {y : ℝ} (hy : 0 < y) :
    (⨅ i, f i) ^ y = ⨅ i, f i ^ y :=
  (ENNReal.orderIsoRpow y hy).map_iInf f

/-- The real part of the square root of an extended nonnegative real is the square root of its
real part. -/
theorem toReal_rpow_inv_two (x : ℝ≥0∞) : (x ^ (2⁻¹ : ℝ)).toReal = Real.sqrt x.toReal := by
  rw [Real.sqrt_eq_rpow, ← ENNReal.toReal_rpow]
  norm_num

end ENNRealAux

/-! ### Minkowski's inequality for the three-point cost -/

section Minkowski

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

/-- Minkowski's inequality at exponent two for the quadratic cost of three measurable maps. -/
theorem lintegral_normSq_sub_rpow_le {Ω : Type*} [MeasurableSpace Ω] (Γ : Measure Ω)
    {X Y Z : Ω → E} (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) :
    (∫⁻ ω, ENNReal.ofReal (‖X ω - Z ω‖ ^ 2) ∂Γ) ^ (2⁻¹ : ℝ)
      ≤ (∫⁻ ω, ENNReal.ofReal (‖X ω - Y ω‖ ^ 2) ∂Γ) ^ (2⁻¹ : ℝ)
        + (∫⁻ ω, ENNReal.ofReal (‖Y ω - Z ω‖ ^ 2) ∂Γ) ^ (2⁻¹ : ℝ) := by
  set f : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal ‖X ω - Y ω‖ with hf
  set g : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal ‖Y ω - Z ω‖ with hg
  have hfm : AEMeasurable f Γ := by fun_prop
  have hgm : AEMeasurable g Γ := by fun_prop
  have hsq : ∀ a : ℝ, 0 ≤ a → ENNReal.ofReal (a ^ 2) = ENNReal.ofReal a ^ (2 : ℝ) := by
    intro a ha
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast,
      ← ENNReal.ofReal_pow ha]
  have key : ∀ ω, ENNReal.ofReal (‖X ω - Z ω‖ ^ 2) ≤ ((f + g) ω) ^ (2 : ℝ) := by
    intro ω
    have htri : ‖X ω - Z ω‖ ≤ ‖X ω - Y ω‖ + ‖Y ω - Z ω‖ := by
      simpa using norm_sub_le_norm_sub_add_norm_sub (X ω) (Y ω) (Z ω)
    have h₁ : ENNReal.ofReal ‖X ω - Z ω‖ ≤ (f + g) ω := by
      simp only [Pi.add_apply, hf, hg]
      rw [← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal htri
    calc ENNReal.ofReal (‖X ω - Z ω‖ ^ 2)
        = ENNReal.ofReal ‖X ω - Z ω‖ ^ (2 : ℝ) := hsq _ (norm_nonneg _)
      _ ≤ ((f + g) ω) ^ (2 : ℝ) := ENNReal.rpow_le_rpow h₁ (by norm_num)
  have hmink := ENNReal.lintegral_Lp_add_le (μ := Γ) hfm hgm (p := 2) (by norm_num)
  have hle : (∫⁻ ω, ENNReal.ofReal (‖X ω - Z ω‖ ^ 2) ∂Γ) ^ (2⁻¹ : ℝ)
      ≤ (∫⁻ ω, ((f + g) ω) ^ (2 : ℝ) ∂Γ) ^ (1 / 2 : ℝ) := by
    have hm : ∫⁻ ω, ENNReal.ofReal (‖X ω - Z ω‖ ^ 2) ∂Γ ≤ ∫⁻ ω, ((f + g) ω) ^ (2 : ℝ) ∂Γ :=
      lintegral_mono key
    simpa using ENNReal.rpow_le_rpow hm (by norm_num : (0 : ℝ) ≤ 2⁻¹)
  refine hle.trans (hmink.trans (le_of_eq ?_))
  congr 1 <;>
  · rw [one_div]
    congr 1
    refine lintegral_congr fun ω => ?_
    rw [hsq _ (norm_nonneg _)]

end Minkowski

/-! ### The triangle inequality -/

section Triangle

variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

/-- Two couplings along a common marginal bound the root squared 2-Wasserstein distance between
the outer laws by the sum of their root quadratic transport costs. -/
theorem w2sq_rpow_le_of_couplings {μ ν ρ : Measure E} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ] {γ₁ γ₂ : Measure (E × E)}
    (h₁ : IsCoupling μ ν γ₁) (h₂ : IsCoupling ν ρ γ₂) :
    w2sq μ ρ ^ (2⁻¹ : ℝ)
      ≤ transportCostSq γ₁ ^ (2⁻¹ : ℝ) + transportCostSq γ₂ ^ (2⁻¹ : ℝ) := by
  obtain ⟨Γ, hA, hB⟩ := exists_glue h₁ h₂
  have hcoup := isCoupling_glue_snd (isCoupling_swap h₁) h₂ hA hB
  have hA' : (Γ.map fun p : E × E × E => (p.1, p.2.1)) = γ₁.map Prod.swap := hA
  have hB' : (Γ.map fun p : E × E × E => (p.1, p.2.2)) = γ₂ := hB
  have c₁₃ : transportCostSq (Γ.map fun p : E × E × E => (p.2.1, p.2.2))
      = ∫⁻ p, ENNReal.ofReal (‖p.2.1 - p.2.2‖ ^ 2) ∂Γ :=
    transportCostSq_map Γ (by fun_prop) (by fun_prop)
  have c₁₂ : transportCostSq γ₁ = ∫⁻ p : E × E × E, ENNReal.ofReal (‖p.2.1 - p.1‖ ^ 2) ∂Γ := by
    rw [← transportCostSq_swap γ₁, ← hA', transportCostSq_map Γ (by fun_prop) (by fun_prop)]
    exact lintegral_congr fun p => by rw [norm_sub_rev]
  have c₂₃ : transportCostSq γ₂ = ∫⁻ p : E × E × E, ENNReal.ofReal (‖p.1 - p.2.2‖ ^ 2) ∂Γ := by
    rw [← hB', transportCostSq_map Γ (by fun_prop) (by fun_prop)]
  calc w2sq μ ρ ^ (2⁻¹ : ℝ)
      ≤ transportCostSq (Γ.map fun p : E × E × E => (p.2.1, p.2.2)) ^ (2⁻¹ : ℝ) :=
        ENNReal.rpow_le_rpow (w2sq_le_transportCostSq hcoup) (by norm_num)
    _ = (∫⁻ p, ENNReal.ofReal (‖p.2.1 - p.2.2‖ ^ 2) ∂Γ) ^ (2⁻¹ : ℝ) := by rw [c₁₃]
    _ ≤ (∫⁻ p : E × E × E, ENNReal.ofReal (‖p.2.1 - p.1‖ ^ 2) ∂Γ) ^ (2⁻¹ : ℝ)
        + (∫⁻ p : E × E × E, ENNReal.ofReal (‖p.1 - p.2.2‖ ^ 2) ∂Γ) ^ (2⁻¹ : ℝ) :=
        lintegral_normSq_sub_rpow_le Γ (X := fun p => p.2.1) (Y := fun p => p.1)
          (Z := fun p => p.2.2) (by fun_prop) (by fun_prop) (by fun_prop)
    _ = transportCostSq γ₁ ^ (2⁻¹ : ℝ) + transportCostSq γ₂ ^ (2⁻¹ : ℝ) := by rw [c₁₂, c₂₃]

/-- The triangle inequality for the root squared 2-Wasserstein distance. -/
theorem w2sq_rpow_triangle (μ ν ρ : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ρ] :
    w2sq μ ρ ^ (2⁻¹ : ℝ) ≤ w2sq μ ν ^ (2⁻¹ : ℝ) + w2sq ν ρ ^ (2⁻¹ : ℝ) := by
  have hrw : ∀ a b : Measure E, w2sq a b ^ (2⁻¹ : ℝ)
      = ⨅ γ, ⨅ _ : IsCoupling a b γ, transportCostSq γ ^ (2⁻¹ : ℝ) := by
    intro a b
    rw [w2sq, iInf_rpow _ (by norm_num)]
    exact iInf_congr fun γ => iInf_rpow _ (by norm_num)
  rw [hrw μ ν, hrw ν ρ]
  refine le_iInf_add_iInf fun γ₁ γ₂ => ?_
  by_cases hc₁ : IsCoupling μ ν γ₁
  · by_cases hc₂ : IsCoupling ν ρ γ₂
    · rw [iInf_pos hc₁, iInf_pos hc₂]
      exact w2sq_rpow_le_of_couplings hc₁ hc₂
    · rw [iInf_neg hc₂]
      simp
  · rw [iInf_neg hc₁]
    simp

/-- The triangle inequality for the 2-Wasserstein distance between laws at finite squared
distance. -/
theorem w2_triangle {μ ν ρ : Measure E} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ρ] (h₁ : w2sq μ ν ≠ ⊤) (h₂ : w2sq ν ρ ≠ ⊤) :
    w2 μ ρ ≤ w2 μ ν + w2 ν ρ := by
  have hb : w2sq μ ν ^ (2⁻¹ : ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) h₁
  have hc : w2sq ν ρ ^ (2⁻¹ : ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) h₂
  have hbc : w2sq μ ν ^ (2⁻¹ : ℝ) + w2sq ν ρ ^ (2⁻¹ : ℝ) ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hb, hc⟩
  have hA := w2sq_rpow_triangle μ ν ρ
  have hAne : w2sq μ ρ ^ (2⁻¹ : ℝ) ≠ ⊤ := ne_top_of_le_ne_top hbc hA
  have hreal := (ENNReal.toReal_le_toReal hAne hbc).2 hA
  rwa [ENNReal.toReal_add hb hc, toReal_rpow_inv_two, toReal_rpow_inv_two,
    toReal_rpow_inv_two] at hreal

/-- The triangle inequality for the 2-Wasserstein distance on the laws of finite second moment. -/
theorem w2P_triangle (μ ν ρ : P2 E) : w2P μ ρ ≤ w2P μ ν + w2P ν ρ :=
  w2_triangle (w2sq_ne_top μ ν) (w2sq_ne_top ν ρ)

/-- The 2-Wasserstein distance to a fixed law of finite second moment is `1`-Lipschitz. -/
theorem abs_w2P_sub_w2P_le (μ ν μ₀ : P2 E) : |w2P μ μ₀ - w2P ν μ₀| ≤ w2P μ ν := by
  have h₁ : w2P μ μ₀ ≤ w2P μ ν + w2P ν μ₀ := w2P_triangle μ ν μ₀
  have h₂ : w2P ν μ₀ ≤ w2P ν μ + w2P μ μ₀ := w2P_triangle ν μ μ₀
  rw [w2P_comm ν μ] at h₂
  rw [abs_sub_le_iff]
  exact ⟨by linarith, by linarith⟩

end Triangle

/-! ### The distance of two Dirac masses -/

section Dirac

variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [MeasurableSingletonClass E]

omit [CompleteSpace E] in
/-- The 2-Wasserstein distance between two Dirac masses is the distance between their points. -/
theorem w2P_dirac_dirac (a b : E) : w2P (P2.dirac a) (P2.dirac b) = ‖a - b‖ := by
  have h : w2sq (Measure.dirac a) (Measure.dirac b) = ENNReal.ofReal (‖a - b‖ ^ 2) := by
    rw [w2sq_dirac, lintegral_dirac]
  rw [w2P, P2.dirac, P2.dirac, w2]
  simp only
  rw [h, ENNReal.toReal_ofReal (by positivity), Real.sqrt_sq (norm_nonneg _)]

end Dirac

end Dissertation.Law
