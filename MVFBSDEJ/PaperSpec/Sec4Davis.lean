/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Enlarged.Driver
import MVFBSDEJ.WellPosedness.Martingale.LocalIntegral

/-!
# The constant of the Burkholder–Davis–Gundy inequality at `p = 1`

Statement and equation numbers refer to the well-posedness paper at `1f67672`. The maximal
estimates of §4 use the Burkholder–Davis–Gundy inequality in quadratic-variation form with one
universal constant `c_BDG`; at `p = 1` it is Davis's inequality

`𝔼 sup_{t ≤ T} |M_t| ≤ c_BDG 𝔼 [M]_T^{1/2}`

for càdlàg local martingales `M`. The local martingales it is applied to are local stochastic
integrals on `[0, T]` for the filtration of the paper: a local Itô integral `M = ∫ H dW`, whose
quadratic variation is `[M]_T = ∫_0^T |H_s|² ds`, and a local compensated Poisson integral
`M = ∫∫ φ dÑ` of a marked predictable integrand, whose quadratic variation is
`[M]_T = ∫_{(0, T] × E} φ_s(e)² N(ds, de)`.

## Main definitions

* `MVFBSDEJ.PaperSpec.DavisValid` — `c` is a constant of Davis's inequality for these
  integrals.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MVFBSDEJ.PaperSpec

open MVFBSDEJ.WellPosedness.Enlarged MVFBSDEJ.WellPosedness.Martingale LevyStochCalc

universe u v w

/-- **A constant of Davis's inequality.** `c` is a constant of the Burkholder–Davis–Gundy
inequality at `p = 1` in quadratic-variation form, `𝔼 sup_{t ≤ T} |M_t| ≤ c 𝔼 [M]_T^{1/2}`, for
the local stochastic integrals on `[0, T]`, `T > 0`, of the filtration `enlJoint 𝒢₀ D h𝒢₀` of a
Lévy driver `D` on a countably generated mark space with an independent initial σ-algebra `𝒢₀`:
every local Itô integral `M` of an integrand `H` against the Brownian motion of `D` satisfies
`𝔼 sup_{t ≤ T} |M_t| ≤ c 𝔼 (∑_j ∫_0^T H_j(s)² ds)^{1/2}`, and every local compensated
integral `M` of a marked predictable integrand `φ` vanishing at the nonpositive times against the
Poisson random measure `N` of `D` satisfies
`𝔼 sup_{t ≤ T} |M_t| ≤ c 𝔼 (∫_{(0, T] × E} φ_s(e)² N(ds, de))^{1/2}`; the expectations are read
in `[0, ∞]`. -/
def DavisValid (c : ℝ) : Prop :=
  (∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
      [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
      (d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
      (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
      (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P) (T : ℝ), 0 < T →
      ∀ (H : ℝ → Ω → Fin d → ℝ) (M : ℝ → Ω → ℝ),
      IsLocalBrownianIntegral D.W (enlJoint 𝒢₀ D h𝒢₀)
        (isBrownianFiltration_enlJoint D h𝒢₀ hind₀) T H M →
      ∫⁻ ω, ⨆ t ∈ Set.Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞) ∂P
        ≤ ENNReal.ofReal c
          * ∫⁻ ω, (∑ j, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H s ω j‖₊ : ℝ≥0∞) ^ 2) ^ (1 / 2 : ℝ) ∂P)
  ∧ ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
      [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
      (d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
      (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
      (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P) (T : ℝ), 0 < T →
      ∀ φ : Ω → ℝ → E → ℝ, Probability.MarkedPredictable (enlJoint 𝒢₀ D h𝒢₀) ν φ →
      (∀ ω s e, s ≤ 0 → φ ω s e = 0) → ∀ M : ℝ → Ω → ℝ,
      IsLocalCompensatedIntegral D.N (enlJoint 𝒢₀ D h𝒢₀)
        (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) T φ M →
      ∫⁻ ω, ⨆ t ∈ Set.Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞) ∂P
        ≤ ENNReal.ofReal c
          * ∫⁻ ω, (∫⁻ x in Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set E),
              ‖φ ω x.1 x.2‖ₑ ^ 2 ∂(D.N.N ω)) ^ (1 / 2 : ℝ) ∂P

end MVFBSDEJ.PaperSpec
