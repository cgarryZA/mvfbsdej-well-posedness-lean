/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.System.BridgeDiffInt
import Dissertation.WellPosedness.System.PaperWeakSolutionForcedIntSolves
import Dissertation.WellPosedness.Stability.BackwardEstimate

/-!
# The Young bound of the driver pairing in the backward estimate

Step 4 of the proof of Lemma 4.3 of the well-posedness paper bounds the driver pairing
`2 𝔼⟨δY_s, λ δf_s + q^f_s⟩` of the backward difference equation (4.16) by Young's inequality,
the expected Lipschitz bound (3.2) and `ε ≤ 1`: for the difference system with interior Lipschitz
constant `K ≥ 0`, `λ ∈ [0, 1]` and `ε ∈ (0, 1]`, at almost every time `s`,

`2 𝔼⟨δY_s, λ δf_s + q^f_s⟩ ≤ ((2K + 3)/ε) 𝔼|δY_s|² + ε 𝔼(|δZ_s|²_F + ‖δU_s‖²)
  + ((2K + 3)/ε) 𝔼(|δX_s|² + |q^f_s|²)`.

Young's inequality with weight `a = (2K + 2)/ε` gives `2 𝔼⟨δY_s, φ_s⟩ ≤ a 𝔼|δY_s|² + a⁻¹ 𝔼|φ_s|²`
for `φ = λ δf + q^f`; `|φ|² ≤ 2 |δf|² + 2 |q^f|²` and (3.2) give
`a⁻¹ 𝔼|φ_s|² ≤ ε 𝔼(|δX_s|² + |δY_s|² + |δZ_s|²_F + ‖δU_s‖²) + ε 𝔼|q^f_s|²`; and `ε ≤ 1 ≤ 1/ε`
moves the terms in `δX`, `δY` and `q^f` under the weight `(2K + 3)/ε`. The left side is a Bochner
integral, read in `[0, ∞]` through its positive part.

## Main statements

* `two_mul_abs_sum_mul_le` — Young's inequality `2 |⟨y, φ⟩| ≤ a |y|² + a⁻¹ |φ|²`, `a > 0`.
* `ofReal_two_mul_integral_sum_mul_le` — its expectation, in `[0, ∞]`.
* `PairDiff.ae_backwardYoung_le` — the bound for the difference system.
* `PaperWeakSolutionForcedInt.ae_backwardYoung_le` — the bound for two solutions of the
  `λ`-forced system (4.1) in `ℍ²_weak`, with `K = 10 L²` for Assumption 2.3 with constant `L`.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace Dissertation.WellPosedness.Stability

open LevyStochCalc.BSDEJ.Solves LevyStochCalc Dissertation.WellPosedness.BrownianPoisson

universe u v w

/-! ### Young's inequality -/

section Young

variable {ι : Type*} [Fintype ι]

/-- For `a > 0`, `2 u v ≤ a u² + a⁻¹ v²`. -/
theorem two_mul_mul_le_of_pos {a : ℝ} (ha : 0 < a) (u v : ℝ) :
    2 * u * v ≤ a * u ^ 2 + a⁻¹ * v ^ 2 := by
  have h := mul_nonneg (inv_nonneg.mpr ha.le) (sq_nonneg (a * u - v))
  have e : a⁻¹ * (a * u - v) ^ 2 = a * u ^ 2 - 2 * u * v + a⁻¹ * v ^ 2 := by
    field_simp
    ring
  linarith

/-- **Young's inequality for coordinate vectors**: for `a > 0`,
`2 |∑ₖ yₖ φₖ| ≤ a ∑ₖ yₖ² + a⁻¹ ∑ₖ φₖ²`. -/
theorem two_mul_abs_sum_mul_le {a : ℝ} (ha : 0 < a) (y φ : ι → ℝ) :
    2 * |∑ k, y k * φ k| ≤ a * ∑ k, y k ^ 2 + a⁻¹ * ∑ k, φ k ^ 2 := by
  calc 2 * |∑ k, y k * φ k| ≤ 2 * ∑ k, |y k| * |φ k| := by
        gcongr
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        simp only [abs_mul]
    _ = ∑ k, 2 * |y k| * |φ k| := by rw [Finset.mul_sum]; simp only [mul_assoc]
    _ ≤ ∑ k, (a * |y k| ^ 2 + a⁻¹ * |φ k| ^ 2) :=
        Finset.sum_le_sum fun k _ => two_mul_mul_le_of_pos ha _ _
    _ = a * ∑ k, y k ^ 2 + a⁻¹ * ∑ k, φ k ^ 2 := by
        simp only [sq_abs, Finset.sum_add_distrib, Finset.mul_sum]

/-- The squared Euclidean norm of a coordinate vector, as the extended real of `∑ᵢ xᵢ²`. -/
theorem esq_eq_ofReal_sum_sq (x : ι → ℝ) : esq x = ENNReal.ofReal (∑ i, x i ^ 2) := by
  rw [ENNReal.ofReal_sum_of_nonneg fun i _ => sq_nonneg (x i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sq_nnnorm_eq_ofReal, sq]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Young's inequality in expectation**: for `a > 0` and `y` with measurable coordinates,
`2 𝔼⟨y, φ⟩ ≤ a 𝔼|y|² + a⁻¹ 𝔼|φ|²`, the left side read in `[0, ∞]` through its positive part and
the expectations on the right in `[0, ∞]`. -/
theorem ofReal_two_mul_integral_sum_mul_le {y φ : ι → Ω → ℝ} (hy : ∀ k, Measurable (y k))
    {a : ℝ} (ha : 0 < a) :
    ENNReal.ofReal (2 * ∫ ω, ∑ k, y k ω * φ k ω ∂P)
      ≤ ENNReal.ofReal a * ∫⁻ ω, esq (fun k => y k ω) ∂P
        + ENNReal.ofReal a⁻¹ * ∫⁻ ω, esq (fun k => φ k ω) ∂P := by
  by_cases hi : Integrable (fun ω => ∑ k, y k ω * φ k ω) P
  · have hesq : Measurable fun ω => esq (fun k => y k ω) :=
      Finset.measurable_sum _ fun k _ => ((hy k).nnnorm.coe_nnreal_ennreal).pow_const 2
    calc ENNReal.ofReal (2 * ∫ ω, ∑ k, y k ω * φ k ω ∂P)
        ≤ ENNReal.ofReal (2 * ∫ ω, ‖∑ k, y k ω * φ k ω‖ ∂P) := by
          refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ zero_le_two)
          exact (Real.le_norm_self _).trans (norm_integral_le_integral_norm _)
      _ = ∫⁻ ω, 2 * ‖∑ k, y k ω * φ k ω‖ₑ ∂P := by
          rw [ENNReal.ofReal_mul zero_le_two, ofReal_integral_norm_eq_lintegral_enorm hi,
            lintegral_const_mul' _ _ (by simp), ENNReal.ofReal_ofNat]
      _ ≤ ∫⁻ ω, (ENNReal.ofReal a * esq (fun k => y k ω)
            + ENNReal.ofReal a⁻¹ * esq (fun k => φ k ω)) ∂P := by
          refine lintegral_mono fun ω => ?_
          rw [esq_eq_ofReal_sum_sq, esq_eq_ofReal_sum_sq, ← ENNReal.ofReal_mul ha.le,
            ← ENNReal.ofReal_mul (inv_nonneg.mpr ha.le),
            ← ENNReal.ofReal_add (by positivity) (by positivity), Real.enorm_eq_ofReal_abs,
            ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul zero_le_two]
          exact ENNReal.ofReal_le_ofReal (two_mul_abs_sum_mul_le ha _ _)
      _ = _ := by
          rw [lintegral_add_left (hesq.const_mul _), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  · rw [integral_undef hi, mul_zero, ENNReal.ofReal_zero]
    exact zero_le

/-- The arithmetic of the Young bound: if `F ≤ 2 F_f + 2 Q` and `F_f ≤ K (A + B + J)` with
`K ≥ 0`, then for `ε ∈ (0, 1]`, with `a = (2K + 2)/ε`,
`a B + a⁻¹ F ≤ ((2K + 3)/ε) B + ε J + ((2K + 3)/ε) (A + Q)`. -/
theorem young_weight_le {A B J Q Ff F : ℝ≥0∞} {K ε : ℝ} (hK : 0 ≤ K) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hF : F ≤ 2 * Ff + 2 * Q) (hFf : Ff ≤ ENNReal.ofReal K * (A + B + J)) :
    ENNReal.ofReal ((2 * K + 2) / ε) * B + ENNReal.ofReal ((2 * K + 2) / ε)⁻¹ * F
      ≤ ENNReal.ofReal ((2 * K + 3) / ε) * B + ENNReal.ofReal ε * J
        + ENNReal.ofReal ((2 * K + 3) / ε) * (A + Q) := by
  have hK2 : 0 < 2 * K + 2 := by linarith
  have hc : 0 ≤ ((2 * K + 2) / ε)⁻¹ := by positivity
  have h1 : ENNReal.ofReal ((2 * K + 2) / ε)⁻¹ * F
      ≤ ENNReal.ofReal ε * (A + B + J) + ENNReal.ofReal ε * Q := by
    calc ENNReal.ofReal ((2 * K + 2) / ε)⁻¹ * F
        ≤ ENNReal.ofReal ((2 * K + 2) / ε)⁻¹
          * (2 * (ENNReal.ofReal K * (A + B + J)) + 2 * Q) := by
          gcongr
          exact hF.trans (by gcongr)
      _ = ENNReal.ofReal (((2 * K + 2) / ε)⁻¹ * 2 * K) * (A + B + J)
          + ENNReal.ofReal (((2 * K + 2) / ε)⁻¹ * 2) * Q := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hc, ENNReal.ofReal_ofNat]
          ring
      _ ≤ _ := by
          gcongr
          · rw [inv_div, div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ hK2]
            nlinarith
          · rw [inv_div, div_mul_eq_mul_div, div_le_iff₀ hK2]
            nlinarith
  have hεε : ε ≤ 1 / ε := by
    rw [le_div_iff₀ hε]
    nlinarith
  calc ENNReal.ofReal ((2 * K + 2) / ε) * B + ENNReal.ofReal ((2 * K + 2) / ε)⁻¹ * F
      ≤ ENNReal.ofReal ((2 * K + 2) / ε) * B
        + (ENNReal.ofReal ε * (A + B + J) + ENNReal.ofReal ε * Q) := by gcongr
    _ = (ENNReal.ofReal ((2 * K + 2) / ε) + ENNReal.ofReal ε) * B + ENNReal.ofReal ε * J
        + ENNReal.ofReal ε * (A + Q) := by ring
    _ = ENNReal.ofReal ((2 * K + 2) / ε + ε) * B + ENNReal.ofReal ε * J
        + ENNReal.ofReal ε * (A + Q) := by
        rw [ENNReal.ofReal_add (by positivity) hε.le]
    _ ≤ _ := by
        gcongr
        · calc (2 * K + 2) / ε + ε ≤ (2 * K + 2) / ε + 1 / ε := by gcongr
            _ = (2 * K + 3) / ε := by ring
        · calc ε ≤ 1 / ε := hεε
            _ ≤ (2 * K + 3) / ε := by gcongr; linarith

end Young

/-! ### The difference system -/

namespace PairDiff

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d n m : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {T lam K KT α β₁ β₂ ε : ℝ}
  {G : Matrix (Fin m) (Fin n) ℝ} {ξ₀ : Fin n → Ω → ℝ}
  {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ}
  {Z : Fin m → ℝ → Ω → Fin d → ℝ} {U : Fin m → ℝ → Ω → E → ℝ}
  {b : Fin n → Ω → ℝ → ℝ} {σ : Fin n → ℝ → Ω → Fin d → ℝ} {h : Fin n → ℝ → Ω → E → ℝ}
  {f : Fin m → Ω → ℝ → ℝ} {g : Fin m → Ω → ℝ}
  {qb : Fin n → Ω → ℝ → ℝ} {qσ : Fin n → ℝ → Ω → Fin d → ℝ} {qh : Fin n → ℝ → Ω → E → ℝ}
  {qf : Fin m → Ω → ℝ → ℝ} {qg : Fin m → Ω → ℝ}

/-- **The Young bound of the driver pairing for the difference system.** For the difference
system at `λ ∈ [0, 1]` with interior Lipschitz constant `K ≥ 0` and `ε ∈ (0, 1]`, at almost
every `s ∈ [0, T]`,

`2 𝔼⟨δY_s, λ δf_s + q^f_s⟩ ≤ ((2K + 3)/ε) 𝔼|δY_s|² + ε 𝔼(|δZ_s|²_F + ‖δU_s‖²)
  + ((2K + 3)/ε) 𝔼(|δX_s|² + |q^f_s|²)`. -/
theorem ae_backwardYoung_le
    (hD : PairDiff D ℱ hℱW hℱN T lam K KT α β₁ β₂ G ξ₀ X Y Z U b σ h f g qb qσ qh qf qg)
    (hK : 0 ≤ K) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      ENNReal.ofReal (2 * ∫ ω, ∑ k, Y k s ω * (lam * f k ω s + qf k ω s) ∂P)
        ≤ ENNReal.ofReal ((2 * K + 3) / ε) * ∫⁻ ω, esq (fun k => Y k s ω) ∂P
          + ENNReal.ofReal ε * ∫⁻ ω, (∑ k, esq (Z k s ω)
              + ∑ k, ∫⁻ e, (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ∂P
          + ENNReal.ofReal ((2 * K + 3) / ε)
            * ∫⁻ ω, (esq (fun i => X i s ω) + esq (fun k => qf k ω s)) ∂P := by
  have hl : lam ^ 2 ≤ 1 := by nlinarith
  filter_upwards [hD.lip] with s hs
  have hsq : ∀ {ι : Type} [Fintype ι] {x : ι → Ω → ℝ}, (∀ k, Measurable (x k)) →
      Measurable fun ω => esq (fun k => x k ω) := fun hx =>
    Finset.measurable_sum _ fun k _ => ((hx k).nnnorm.coe_nnreal_ennreal).pow_const 2
  have hY : ∀ k, Measurable (Y k s) := fun k => ((hD.bwd k).Y_adapted s).mono (ℱ.le s) le_rfl
  have hX : ∀ i, Measurable (X i s) := fun i => ((hD.fwd i).X_adapted s).mono (ℱ.le s) le_rfl
  have hq : ∀ k, Measurable fun ω => qf k ω s := fun k =>
    (hD.qf_meas k).comp (measurable_id.prodMk measurable_const)
  have ha : 0 < (2 * K + 2) / ε := by positivity
  -- Young's inequality with weight `(2K + 2)/ε`
  have hyoung := ofReal_two_mul_integral_sum_mul_le (P := P) (y := fun k ω => Y k s ω)
    (φ := fun k ω => lam * f k ω s + qf k ω s) hY ha
  -- the driver integrand against the coefficient difference and the forcing
  have hF : ∫⁻ ω, esq (fun k => lam * f k ω s + qf k ω s) ∂P
      ≤ 2 * ∫⁻ ω, esq (fun k => f k ω s) ∂P + 2 * ∫⁻ ω, esq (fun k => qf k ω s) ∂P := by
    calc ∫⁻ ω, esq (fun k => lam * f k ω s + qf k ω s) ∂P
        ≤ ∫⁻ ω, (2 * esq (fun k => f k ω s) + 2 * esq (fun k => qf k ω s)) ∂P :=
          lintegral_mono fun ω => esq_mul_add_le hl _ _
      _ = _ := by
          rw [lintegral_add_right _ ((hsq hq).const_mul _), lintegral_const_mul' _ _ (by simp),
            lintegral_const_mul' _ _ (by simp)]
  -- the expected Lipschitz bound at `s`, for the driver alone
  have hFf : ∫⁻ ω, esq (fun k => f k ω s) ∂P
      ≤ ENNReal.ofReal K * (∫⁻ ω, esq (fun i => X i s ω) ∂P
        + ∫⁻ ω, esq (fun k => Y k s ω) ∂P
        + ∫⁻ ω, (∑ k, esq (Z k s ω) + ∑ k, ∫⁻ e, (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ∂P) := by
    refine le_trans (lintegral_mono fun ω => le_add_self) (hs.trans (le_of_eq ?_))
    congr 1
    simp only [add_assoc]
    rw [lintegral_add_left (hsq hX), lintegral_add_left (hsq hY)]
  refine hyoung.trans (le_trans (young_weight_le hK hε hε1 hF hFf) (le_of_eq ?_))
  rw [lintegral_add_left (hsq hX)]

end PairDiff

end Dissertation.WellPosedness.Stability

namespace Dissertation.WellPosedness.System

open LevyStochCalc.BSDEJ.Solves Dissertation.WellPosedness.BrownianPoisson
  Dissertation.WellPosedness.Stability

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}
  {P : Measure Ω} [IsProbabilityMeasure P] {T lam ε : ℝ} {C : Coeffs ν n m d}
  {ξ₁ ξ₂ : Fin n → Ω → ℝ}
  {qb₁ qb₂ : Fin n → Ω → ℝ → ℝ} {qσ₁ qσ₂ : Fin n → ℝ → Ω → Fin d → ℝ}
  {qh₁ qh₂ : Fin n → ℝ → Ω → E → ℝ} {qf₁ qf₂ : Fin m → Ω → ℝ → ℝ} {qg₁ qg₂ : Fin m → Ω → ℝ}
  {X₁ X₂ : Fin n → ℝ → Ω → ℝ} {Y₁ Y₂ : Fin m → ℝ → Ω → ℝ}
  {Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ} {U₁ U₂ : Fin m → ℝ → Ω → E → ℝ}
  {γ₁ γ₂ : Fin n → ℝ → Ω → E → ℝ} {L α β₁ β₂ : ℝ} {G : Matrix (Fin m) (Fin n) ℝ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}

/-- **The Young bound of the driver pairing for two solutions in `ℍ²_weak`.** For two solutions
of the `λ`-forced system (4.1) in the sense of `PaperWeakSolutionForcedInt`, `λ ∈ [0, 1]`, with
the same coefficients satisfying Assumption 2.3 along the diagonal with constant `L` and
Assumption 2.5 along the diagonal, and `ε ∈ (0, 1]`, at almost every `s ∈ [0, T]`, with
`C = 2 (10 L²) + 3`,

`2 𝔼⟨δY_s, λ δf_s + δq^f_s⟩ ≤ (C/ε) 𝔼|δY_s|² + ε 𝔼(|δZ_s|²_F + ‖δU_s‖²)
  + (C/ε) 𝔼(|δX_s|² + |δq^f_s|²)`,

`δf_s = f(s, Θ¹_s, μ¹_s) − f(s, Θ²_s, μ²_s)`. -/
theorem PaperWeakSolutionForcedInt.ae_backwardYoung_le {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
    {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}
    (h₁ : PaperWeakSolutionForcedInt D ℱ hℱW hℱN T lam C ξ₁ qb₁ qσ₁ qh₁ qf₁ qg₁ X₁ Y₁ Z₁ U₁ γ₁)
    (h₂ : PaperWeakSolutionForcedInt D ℱ hℱW hℱN T lam C ξ₂ qb₂ qσ₂ qh₂ qf₂ qg₂ X₂ Y₂ Z₂ U₂ γ₂)
    (hT : 0 ≤ T) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hL : DiagonalLipschitz ℱ P T L C) (hLT : TerminalLipschitz ℱ P T L C.g)
    (hM : DiagonalMonotone ℱ P T G β₁ β₂ C) (hMT : TerminalMonotone ℱ P T G α C.g) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      ENNReal.ofReal (2 * ∫ ω, ∑ k, (Y₁ k s ω - Y₂ k s ω)
          * (lam * (driverProc P T C X₁ Y₁ Z₁ U₁ k ω s - driverProc P T C X₂ Y₂ Z₂ U₂ k ω s)
            + (qf₁ k ω s - qf₂ k ω s)) ∂P)
        ≤ ENNReal.ofReal ((2 * (10 * L ^ 2) + 3) / ε)
            * ∫⁻ ω, esq (fun k => Y₁ k s ω - Y₂ k s ω) ∂P
          + ENNReal.ofReal ε * ∫⁻ ω, (∑ k, esq (fun j => Z₁ k s ω j - Z₂ k s ω j)
              + ∑ k, ∫⁻ e, (‖U₁ k s ω e - U₂ k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ∂P
          + ENNReal.ofReal ((2 * (10 * L ^ 2) + 3) / ε)
            * ∫⁻ ω, (esq (fun i => X₁ i s ω - X₂ i s ω)
              + esq (fun k => qf₁ k ω s - qf₂ k ω s)) ∂P := by
  obtain ⟨X₁', Y₁', hX₁, hY₁, hs₁⟩ := h₁.exists_solvesForcedInt hT
  obtain ⟨X₂', Y₂', hX₂, hY₂, hs₂⟩ := h₂.exists_solvesForcedInt hT
  have hD := hs₁.pairDiff_of_assumptions hs₂ hT hL hLT hM hMT
  have hK : (0 : ℝ) ≤ 10 * L ^ 2 := by positivity
  rw [← driverProc_eq_of_eqOn (P := P) (C := C) (Z := Z₁) (U := U₁) hX₁ hY₁,
    ← driverProc_eq_of_eqOn (P := P) (C := C) (Z := Z₂) (U := U₂) hX₂ hY₂]
  filter_upwards [hD.ae_backwardYoung_le hK hlam0 hlam1 hε hε1, ae_restrict_mem measurableSet_Icc]
    with s hs hsT
  have eX : ∀ i, X₁' i s = X₁ i s ∧ X₂' i s = X₂ i s := fun i => ⟨hX₁ i s hsT, hX₂ i s hsT⟩
  have eY : ∀ k, Y₁' k s = Y₁ k s ∧ Y₂' k s = Y₂ k s := fun k => ⟨hY₁ k s hsT, hY₂ k s hsT⟩
  simp only [fun i => (eX i).1, fun i => (eX i).2, fun k => (eY k).1, fun k => (eY k).2] at hs
  exact hs

end Dissertation.WellPosedness.System
