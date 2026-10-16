/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.System.ChannelCoords
import Dissertation.WellPosedness.System.SolvesMemLp

/-!
# The expected Lipschitz bounds along two solutions

Let `Θ¹, Θ²` solve the `λ`-forced system (4.1) with the same coefficients `(b, σ, h, f, g)`,
satisfying Assumption 2.3 along the diagonal with constant `L`, and write `δψ` for the
coefficient differences along the pair and `|δΘ_s|² = |δX_s|² + |δY_s|² + |δZ_s|²_F + ‖δU_s‖²`.
At almost every time `s ∈ [0, T]` the tuples `Θ¹_s, Θ²_s` are square integrable and strongly
`ℱ_s`-measurable, so `(Θ¹_s, μ¹_s)` and `(Θ²_s, μ²_s)` are diagonal inputs and, almost surely,
with the jump channels in the norm of `L²(ν)`,

`|δb_s| + |δσ_s|_F + ‖δh_s‖ + |δf_s| ≤ L (|δX_s| + |δY_s| + |δZ_s|_F + ‖δU_s‖ + W₂(μ¹_s, μ²_s))`.

Squaring, with `(x + w)² ≤ 2x² + 2w²`, `(|δX_s| + |δY_s| + |δZ_s|_F + ‖δU_s‖)² ≤ 4 |δΘ_s|²`
and the coupling bound (2.8) `W₂(μ¹_s, μ²_s)² ≤ 𝔼 |δΘ_s|²`, gives the expected bound (3.2):

`𝔼[|δb_s|² + |δσ_s|²_F + ‖δh_s‖² + |δf_s|²] ≤ 10 L² 𝔼 |δΘ_s|²`.

In the same way the terminal bound (2.6) and the coupling bound (2.9) give
`𝔼 |δg_T|² ≤ 4 L² 𝔼 |δX_T|²`. Both sides are written through the coordinates, and the jump
coefficient enters through its representatives, whose difference represents `δh_s` in `L²(ν)` at
almost every time, almost surely. This is `PairLipschitz` with `K = 10 L²` and `K_T = 4 L²`.

The two bounds hold along any two tuples of coordinate processes that are square integrable at
almost every time, with square-integrable values at the horizon (`DiagonalLipschitz.lip_pair`,
`TerminalLipschitz.lipT_pair`). For two solutions of `SolvesForced` the filtration is one on which
Lemma 4.1 applies: its null sets lie in its time-`0` field, its right-continuation is constant
before `0`, and it admits a cross witness. Lemma 4.1 puts the coordinates of `X` and `Y` in
`S²(0, T)`, which makes the tuples square integrable at almost every time.

## Main statements

* `enorm_sq_add_le_of_le_mul_add`, `enorm_sq_le_of_le_mul_add` — squaring a Lipschitz bound.
* `DiagonalLipschitz.lip_pair`, `TerminalLipschitz.lipT_pair` — (3.2) and (2.6) with (2.9) along
  two tuples.
* `SolvesForced.lip_pair` — (3.2) along two solutions.
* `SolvesForced.lipT_pair` — (2.6) with (2.9) along two solutions.
* `SolvesForced.pairLipschitz` — the expected Lipschitz bounds at the pair.
-/

open MeasureTheory Filter WithLp Dissertation.Law
open scoped NNReal ENNReal

namespace Dissertation.WellPosedness.System

open Dissertation.WellPosedness.BrownianPoisson Dissertation.WellPosedness.Stability

universe u v w

/-! ### Squaring a Lipschitz bound -/

section Square

variable {F₁ F₂ F₃ F₄ : Type*} [NormedAddCommGroup F₁] [NormedAddCommGroup F₂]
  [NormedAddCommGroup F₃] [NormedAddCommGroup F₄]

/-- **Squaring a Lipschitz bound in four channels**: if `|v₁| + |v₂| + |v₃| + |v₄| ≤ L (x + w)`,
then `|v₁|² + |v₂|² + |v₃|² + |v₄|² ≤ 2L² (x² + w²)`. -/
theorem enorm_sq_add_le_of_le_mul_add (v₁ : F₁) (v₂ : F₂) (v₃ : F₃) (v₄ : F₄) {L x w : ℝ}
    (h : ‖v₁‖ + ‖v₂‖ + ‖v₃‖ + ‖v₄‖ ≤ L * (x + w)) :
    ‖v₁‖ₑ ^ 2 + ‖v₂‖ₑ ^ 2 + ‖v₃‖ₑ ^ 2 + ‖v₄‖ₑ ^ 2
      ≤ ENNReal.ofReal (2 * L ^ 2) * (ENNReal.ofReal (x ^ 2) + ENNReal.ofReal (w ^ 2)) := by
  have h₁ := norm_nonneg v₁
  have h₂ := norm_nonneg v₂
  have h₃ := norm_nonneg v₃
  have h₄ := norm_nonneg v₄
  have hsq : (‖v₁‖ + ‖v₂‖ + ‖v₃‖ + ‖v₄‖) ^ 2 ≤ (L * (x + w)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h 2
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
    ← ENNReal.ofReal_pow h₁, ← ENNReal.ofReal_pow h₂, ← ENNReal.ofReal_pow h₃,
    ← ENNReal.ofReal_pow h₄, ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  nlinarith [mul_nonneg h₁ h₂, mul_nonneg h₁ h₃, mul_nonneg h₁ h₄, mul_nonneg h₂ h₃,
    mul_nonneg h₂ h₄, mul_nonneg h₃ h₄, mul_nonneg (sq_nonneg L) (sq_nonneg (x - w))]

/-- **Squaring a Lipschitz bound**: if `|v| ≤ L (x + w)`, then `|v|² ≤ 2L² (x² + w²)`. -/
theorem enorm_sq_le_of_le_mul_add (v : F₁) {L x w : ℝ} (h : ‖v‖ ≤ L * (x + w)) :
    ‖v‖ₑ ^ 2 ≤ ENNReal.ofReal (2 * L ^ 2) * (ENNReal.ofReal (x ^ 2) + ENNReal.ofReal (w ^ 2)) := by
  have h₁ := norm_nonneg v
  have hsq : ‖v‖ ^ 2 ≤ (L * (x + w)) ^ 2 := pow_le_pow_left₀ h₁ h 2
  rw [← ofReal_norm, ← ENNReal.ofReal_pow h₁,
    ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  nlinarith [mul_nonneg (sq_nonneg L) (sq_nonneg (x - w))]

end Square

/-! ### The bounds along two solutions -/

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}
  {P : Measure Ω} [IsProbabilityMeasure P] {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {T lam : ℝ} {C : Coeffs ν n m d}
  {ξ₁ ξ₂ : Fin n → Ω → ℝ}
  {qb₁ qb₂ : Fin n → Ω → ℝ → ℝ} {qσ₁ qσ₂ : Fin n → ℝ → Ω → Fin d → ℝ}
  {qh₁ qh₂ : Fin n → ℝ → Ω → E → ℝ} {qf₁ qf₂ : Fin m → Ω → ℝ → ℝ} {qg₁ qg₂ : Fin m → Ω → ℝ}
  {X₁ X₂ : Fin n → ℝ → Ω → ℝ} {Y₁ Y₂ : Fin m → ℝ → Ω → ℝ}
  {Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ} {U₁ U₂ : Fin m → ℝ → Ω → E → ℝ}
  {γ₁ γ₂ : Fin n → ℝ → Ω → E → ℝ} {L : ℝ}

/-- **(3.2) along two tuples.** For coefficients satisfying Assumption 2.3 along the diagonal
with constant `L`, and two tuples of coordinate processes that are strongly `ℱ_s`-measurable at
every time, square integrable at almost every time of `[0, T]`, whose jump channels are almost
surely square integrable at almost every time and along which `γ¹, γ²` represent the jump
coefficient, at almost every time `s ∈ [0, T]`,
`𝔼[|δb_s|² + |δσ_s|²_F + ‖δh_s‖²_{L²(ν)} + |δf_s|²] ≤ 10 L² 𝔼 |δΘ_s|²`, in coordinates. -/
theorem DiagonalLipschitz.lip_pair (hL : DiagonalLipschitz ℱ P T L C)
    (hsm₁ : ∀ s, StronglyMeasurable[ℱ s] (tupleAt ν X₁ Y₁ Z₁ U₁ s))
    (hsm₂ : ∀ s, StronglyMeasurable[ℱ s] (tupleAt ν X₂ Y₂ Z₂ U₂ s))
    (hm₁ : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), MemLp (tupleAt ν X₁ Y₁ Z₁ U₁ s) 2 P)
    (hm₂ : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), MemLp (tupleAt ν X₂ Y₂ Z₂ U₂ s) 2 P)
    (hU₁ : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P, ∀ k,
      MemLp (fun e => U₁ k s ω e) 2 ν)
    (hU₂ : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P, ∀ k,
      MemLp (fun e => U₂ k s ω e) 2 ν)
    (hr₁ : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P,
      (fun e => (toLp 2 fun i => γ₁ i s ω e : EuclideanSpace ℝ (Fin n)))
        =ᵐ[ν] C.h s (tupleAt ν X₁ Y₁ Z₁ U₁ s ω) (lawP2 P (tupleAt ν X₁ Y₁ Z₁ U₁ s)))
    (hr₂ : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P,
      (fun e => (toLp 2 fun i => γ₂ i s ω e : EuclideanSpace ℝ (Fin n)))
        =ᵐ[ν] C.h s (tupleAt ν X₂ Y₂ Z₂ U₂ s ω) (lawP2 P (tupleAt ν X₂ Y₂ Z₂ U₂ s))) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      ∫⁻ ω, (esq (fun i => driftProc P T C X₁ Y₁ Z₁ U₁ i ω s
            - driftProc P T C X₂ Y₂ Z₂ U₂ i ω s)
          + ∑ i, esq (fun j => diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j
            - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j)
          + ∑ i, ∫⁻ e, (‖jumpProc T γ₁ i s ω e - jumpProc T γ₂ i s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν
          + esq (fun k => driverProc P T C X₁ Y₁ Z₁ U₁ k ω s
            - driverProc P T C X₂ Y₂ Z₂ U₂ k ω s)) ∂P
        ≤ ENNReal.ofReal (10 * L ^ 2) * ∫⁻ ω, (esq (fun i => X₁ i s ω - X₂ i s ω)
          + esq (fun k => Y₁ k s ω - Y₂ k s ω) + ∑ k, esq (fun j => Z₁ k s ω j - Z₂ k s ω j)
          + ∑ k, ∫⁻ e, (‖U₁ k s ω e - U₂ k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ∂P := by
  filter_upwards [hL, ae_restrict_mem measurableSet_Icc, hr₁, hr₂, hm₁, hm₂, hU₁, hU₂]
    with s hLs hs hr₁ hr₂ hm₁ hm₂ hU₁ hU₂
  have hb := hLs _ _ (hsm₁ s) (hsm₂ s) hm₁ hm₂
  set W := w2P (lawP2 P (tupleAt ν X₁ Y₁ Z₁ U₁ s)) (lawP2 P (tupleAt ν X₂ Y₂ Z₂ U₂ s))
  have hW := ofReal_w2P_lawP2_tupleAt_sq_le hm₁ hm₂ hU₁ hU₂
  calc _ ≤ ∫⁻ ω, ENNReal.ofReal (2 * L ^ 2) * (ENNReal.ofReal (tupleNorm
          (tupleAt ν X₁ Y₁ Z₁ U₁ s ω - tupleAt ν X₂ Y₂ Z₂ U₂ s ω) ^ 2) + ENNReal.ofReal (W ^ 2))
        ∂P := by
        refine lintegral_mono_ae ?_
        filter_upwards [hb, hr₁, hr₂] with ω hω hω₁ hω₂
        refine le_trans ?_ (enorm_sq_add_le_of_le_mul_add _ _ _ _ hω)
        rw [b_sub_eq_toLp hs, σ_sub_eq_toLp hs, f_sub_eq_toLp hs, esq_eq_enorm_sq,
          esq_eq_enorm_sq, sum_esq_eq_enorm_sq]
        gcongr
        exact sum_lintegral_le_enorm_sq (coeFn_h_sub hs hω₁ hω₂).symm
    _ = ENNReal.ofReal (2 * L ^ 2) * (∫⁻ ω, ENNReal.ofReal (tupleNorm
          (tupleAt ν X₁ Y₁ Z₁ U₁ s ω - tupleAt ν X₂ Y₂ Z₂ U₂ s ω) ^ 2) ∂P
          + ENNReal.ofReal (W ^ 2)) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
    _ ≤ ENNReal.ofReal (2 * L ^ 2) * (4 * ∫⁻ ω, (esq (fun i => X₁ i s ω - X₂ i s ω)
          + esq (fun k => Y₁ k s ω - Y₂ k s ω) + ∑ k, esq (fun j => Z₁ k s ω j - Z₂ k s ω j)
          + ∑ k, ∫⁻ e, (‖U₁ k s ω e - U₂ k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ∂P
          + ∫⁻ ω, (esq (fun i => X₁ i s ω - X₂ i s ω)
          + esq (fun k => Y₁ k s ω - Y₂ k s ω) + ∑ k, esq (fun j => Z₁ k s ω j - Z₂ k s ω j)
          + ∑ k, ∫⁻ e, (‖U₁ k s ω e - U₂ k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ∂P) := by
        gcongr
        · rw [← lintegral_const_mul' _ _ (by norm_num)]
          refine lintegral_mono_ae ?_
          filter_upwards [hU₁, hU₂] with ω h1 h2
          exact ofReal_tupleNorm_tupleAt_sub_sq_le h1 h2
        · exact hW
    _ = _ := by
        have h10 : ENNReal.ofReal (10 * L ^ 2) = ENNReal.ofReal (2 * L ^ 2) * 5 := by
          rw [← ENNReal.ofReal_ofNat 5, ← ENNReal.ofReal_mul (by positivity)]
          ring_nf
        rw [h10]
        ring

/-- **(2.6) with (2.9) along two tuples.** For a terminal function satisfying (2.6) along the
diagonal with constant `L`, and two processes whose values at the horizon are `ℱ_T`-measurable
and square integrable, `𝔼 |δg_T|² ≤ 4 L² 𝔼 |δX_T|²`, in coordinates. -/
theorem TerminalLipschitz.lipT_pair (hLT : TerminalLipschitz ℱ P T L C.g)
    (hX₁ : ∀ i, Measurable[ℱ T] (X₁ i T)) (hX₂ : ∀ i, Measurable[ℱ T] (X₂ i T))
    (hq₁ : ∀ i, MemLp (X₁ i T) 2 P) (hq₂ : ∀ i, MemLp (X₂ i T) 2 P) :
    ∫⁻ ω, esq (fun k => terminalVal P T C X₁ k ω - terminalVal P T C X₂ k ω) ∂P
      ≤ ENNReal.ofReal (4 * L ^ 2) * ∫⁻ ω, esq (fun i => X₁ i T ω - X₂ i T ω) ∂P := by
  set x₁ : Ω → EuclideanSpace ℝ (Fin n) := fun ω => toLp 2 fun i => X₁ i T ω
  set x₂ : Ω → EuclideanSpace ℝ (Fin n) := fun ω => toLp 2 fun i => X₂ i T ω
  have hL₁ : MemLp x₁ 2 P := memLp_toLp_of_forall (u := fun ω i => X₁ i T ω) hq₁
  have hL₂ : MemLp x₂ 2 P := memLp_toLp_of_forall (u := fun ω i => X₂ i T ω) hq₂
  have hb := hLT x₁ x₂ (measurable_toLp_of_forall (mΩ := ℱ T) hX₁).stronglyMeasurable
    (measurable_toLp_of_forall (mΩ := ℱ T) hX₂).stronglyMeasurable hL₁ hL₂
  have hW := ofReal_w2P_lawP2_sq_le hL₁ hL₂
  set W := w2P (lawP2 P x₁) (lawP2 P x₂)
  have hx : ∀ ω, ENNReal.ofReal (‖x₁ ω - x₂ ω‖ ^ 2) = esq (fun i => X₁ i T ω - X₂ i T ω) :=
    fun ω => by
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, esq_eq_enorm_sq, ← toLp_sub]
      rfl
  have hg : ∀ ω, C.g (x₁ ω) (lawP2 P x₁) - C.g (x₂ ω) (lawP2 P x₂)
      = toLp 2 fun k => terminalVal P T C X₁ k ω - terminalVal P T C X₂ k ω := fun ω =>
    g_sub_eq_toLp
  calc ∫⁻ ω, esq (fun k => terminalVal P T C X₁ k ω - terminalVal P T C X₂ k ω) ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal (2 * L ^ 2)
          * (ENNReal.ofReal (‖x₁ ω - x₂ ω‖ ^ 2) + ENNReal.ofReal (W ^ 2)) ∂P := by
        refine lintegral_mono_ae ?_
        filter_upwards [hb] with ω hω
        rw [esq_eq_enorm_sq, ← hg]
        exact enorm_sq_le_of_le_mul_add _ hω
    _ = ENNReal.ofReal (2 * L ^ 2)
          * (∫⁻ ω, ENNReal.ofReal (‖x₁ ω - x₂ ω‖ ^ 2) ∂P + ENNReal.ofReal (W ^ 2)) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
    _ ≤ ENNReal.ofReal (2 * L ^ 2) * (∫⁻ ω, ENNReal.ofReal (‖x₁ ω - x₂ ω‖ ^ 2) ∂P
          + ∫⁻ ω, ENNReal.ofReal (‖x₁ ω - x₂ ω‖ ^ 2) ∂P) := by
        gcongr
    _ = ENNReal.ofReal (4 * L ^ 2) * ∫⁻ ω, esq (fun i => X₁ i T ω - X₂ i T ω) ∂P := by
        have h4 : ENNReal.ofReal (4 * L ^ 2) = ENNReal.ofReal (2 * L ^ 2) * 2 := by
          rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by positivity)]
          ring_nf
        simp only [hx]
        rw [h4]
        ring

/-- **(3.2) along two solutions.** For two solutions of the `λ`-forced system with the same
coefficients, satisfying Assumption 2.3 along the diagonal with constant `L`, at almost every time
`s ∈ [0, T]`,
`𝔼[|δb_s|² + |δσ_s|²_F + ‖δh_s‖²_{L²(ν)} + |δf_s|²] ≤ 10 L² 𝔼 |δΘ_s|²`, in coordinates. -/
theorem SolvesForced.lip_pair
    (h₁ : SolvesForced D ℱ hℱW hℱN T lam C ξ₁ qb₁ qσ₁ qh₁ qf₁ qg₁ X₁ Y₁ Z₁ U₁ γ₁)
    (h₂ : SolvesForced D ℱ hℱW hℱN T lam C ξ₂ qb₂ qσ₂ qh₂ qf₂ qg₂ X₂ Y₂ Z₂ U₂ γ₂)
    (𝒲 : D.CrossWitness ℱ) (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T)
    (hL : DiagonalLipschitz ℱ P T L C) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      ∫⁻ ω, (esq (fun i => driftProc P T C X₁ Y₁ Z₁ U₁ i ω s
            - driftProc P T C X₂ Y₂ Z₂ U₂ i ω s)
          + ∑ i, esq (fun j => diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j
            - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j)
          + ∑ i, ∫⁻ e, (‖jumpProc T γ₁ i s ω e - jumpProc T γ₂ i s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν
          + esq (fun k => driverProc P T C X₁ Y₁ Z₁ U₁ k ω s
            - driverProc P T C X₂ Y₂ Z₂ U₂ k ω s)) ∂P
        ≤ ENNReal.ofReal (10 * L ^ 2) * ∫⁻ ω, (esq (fun i => X₁ i s ω - X₂ i s ω)
          + esq (fun k => Y₁ k s ω - Y₂ k s ω) + ∑ k, esq (fun j => Z₁ k s ω j - Z₂ k s ω j)
          + ∑ k, ∫⁻ e, (‖U₁ k s ω e - U₂ k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ∂P :=
  hL.lip_pair h₁.stronglyMeasurable_tupleAt h₂.stronglyMeasurable_tupleAt
    (h₁.ae_memLp_tupleAt 𝒲 hℱ0 hnull hT) (h₂.ae_memLp_tupleAt 𝒲 hℱ0 hnull hT)
    h₁.ae_ae_memLp_jump h₂.ae_ae_memLp_jump h₁.jump_rep h₂.jump_rep

/-- **(2.6) with (2.9) along two solutions.** For two solutions of the `λ`-forced system with the
same terminal function, satisfying (2.6) along the diagonal with constant `L`,
`𝔼 |δg_T|² ≤ 4 L² 𝔼 |δX_T|²`, in coordinates. -/
theorem SolvesForced.lipT_pair
    (h₁ : SolvesForced D ℱ hℱW hℱN T lam C ξ₁ qb₁ qσ₁ qh₁ qf₁ qg₁ X₁ Y₁ Z₁ U₁ γ₁)
    (h₂ : SolvesForced D ℱ hℱW hℱN T lam C ξ₂ qb₂ qσ₂ qh₂ qf₂ qg₂ X₂ Y₂ Z₂ U₂ γ₂)
    (hT : 0 ≤ T) (hLT : TerminalLipschitz ℱ P T L C.g) :
    ∫⁻ ω, esq (fun k => terminalVal P T C X₁ k ω - terminalVal P T C X₂ k ω) ∂P
      ≤ ENNReal.ofReal (4 * L ^ 2) * ∫⁻ ω, esq (fun i => X₁ i T ω - X₂ i T ω) ∂P :=
  hLT.lipT_pair (fun i => (h₁.fwd i).X_adapted T) (fun i => (h₂.fwd i).X_adapted T)
    (fun i => (h₁.fwd i).memLp_terminal hT) (fun i => (h₂.fwd i).memLp_terminal hT)

/-- **The expected Lipschitz bounds at the pair.** Two solutions of the `λ`-forced system with
the same coefficients, satisfying Assumption 2.3 along the diagonal with constant `L`, satisfy
`PairLipschitz` with `K = 10 L²` and `K_T = 4 L²`, over a filtration whose null sets lie in its
time-`0` field, whose right-continuation is constant before `0` and which admits a cross
witness. -/
theorem SolvesForced.pairLipschitz
    (h₁ : SolvesForced D ℱ hℱW hℱN T lam C ξ₁ qb₁ qσ₁ qh₁ qf₁ qg₁ X₁ Y₁ Z₁ U₁ γ₁)
    (h₂ : SolvesForced D ℱ hℱW hℱN T lam C ξ₂ qb₂ qσ₂ qh₂ qf₂ qg₂ X₂ Y₂ Z₂ U₂ γ₂)
    (𝒲 : D.CrossWitness ℱ) (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T)
    (hL : DiagonalLipschitz ℱ P T L C) (hLT : TerminalLipschitz ℱ P T L C.g) :
    PairLipschitz P ν T (10 * L ^ 2) (4 * L ^ 2) (fun i t ω => X₁ i t ω - X₂ i t ω)
      (fun k t ω => Y₁ k t ω - Y₂ k t ω) (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j)
      (fun k t ω e => U₁ k t ω e - U₂ k t ω e)
      (fun i ω s => driftProc P T C X₁ Y₁ Z₁ U₁ i ω s - driftProc P T C X₂ Y₂ Z₂ U₂ i ω s)
      (fun i s ω j => diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j
        - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j)
      (fun i s ω e => jumpProc T γ₁ i s ω e - jumpProc T γ₂ i s ω e)
      (fun k ω s => driverProc P T C X₁ Y₁ Z₁ U₁ k ω s - driverProc P T C X₂ Y₂ Z₂ U₂ k ω s)
      (fun k ω => terminalVal P T C X₁ k ω - terminalVal P T C X₂ k ω) where
  lip := h₁.lip_pair h₂ 𝒲 hℱ0 hnull hT hL
  lipT := h₁.lipT_pair h₂ hT.le hLT

end Dissertation.WellPosedness.System
