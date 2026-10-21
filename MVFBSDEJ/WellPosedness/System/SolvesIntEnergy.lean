/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.System.SolvesIntPair

/-!
# Finite energy of the coefficient differences along two solutions in `ℍ²`

Along a single solution of (1.1) in `ℍ²` the drift and the driver need not be square integrable
in time: without Assumption 2.2 their origin values `b(·, 0, δ₀)`, `f(·, 0, δ₀)` need only be
integrable on `[0, T]`. Along two solutions
`Θ¹, Θ²` the differences are, as in the proof of Theorem 3.3 of the well-posedness paper:
integrating the expected Lipschitz bound (3.2) at the pair over `[0, T]` gives

`𝔼 ∫_0^T (|δb_t|² + |δσ_t|²_F + ‖δh_t‖²_{L²(ν)} + |δf_t|²) dt
  ≤ K 𝔼 ∫_0^T (|δX_t|² + |δY_t|² + |δZ_t|²_F + ‖δU_t‖²_{L²(ν)}) dt < ∞`,

the right-hand side finite because both solutions lie in `ℍ²`. For the `λ`-forced system the
drift and the driver of the difference equations are `λ δb + δq^b` and `λ δf + δq^f`, of finite
energy since the forcings are square integrable, and the terminal difference `λ δg_T + δq^g_T` is
square integrable by the terminal bound (2.6) with (2.9), since `X¹_T, X²_T` are.

## Main statements

* `PairLipschitz.energy_le` — (3.2) integrated over `[0, T]`.
* `SolvesForcedInt.diffEnergy_lt_top` — the difference of two solutions has finite energy.
* `SolvesForcedInt.coeffEnergy_sub_le` — the energy of the coefficient differences is at most `K`
  times that of the difference of the solutions, for `λ ≠ 0`.
* `SolvesForcedInt.energy_driftProc_sub_ne_top`, `SolvesForcedInt.energy_driverProc_sub_ne_top` —
  the drift and driver differences have finite energy, for `λ ≠ 0`.
* `SolvesForcedInt.energy_drift_sub_ne_top`, `SolvesForcedInt.energy_driver_sub_ne_top` — the
  drifts of the difference equations have finite energy.
* `SolvesForcedInt.memLp_terminal_sub` — the terminal difference is square integrable.
-/

open MeasureTheory Filter MVFBSDEJ.Law
open scoped NNReal ENNReal

namespace MVFBSDEJ.WellPosedness.System

open LevyStochCalc MVFBSDEJ.WellPosedness.BrownianPoisson MVFBSDEJ.WellPosedness.Stability

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  {n m d : ℕ}

/-! ### (3.2) integrated in time -/

section Integrated

variable {P : Measure Ω} [SFinite P] [SFinite ν] {T K KT : ℝ} {X : Fin n → ℝ → Ω → ℝ}
  {Y : Fin m → ℝ → Ω → ℝ} {Z : Fin m → ℝ → Ω → Fin d → ℝ} {U : Fin m → ℝ → Ω → E → ℝ}
  {b : Fin n → Ω → ℝ → ℝ} {σ : Fin n → ℝ → Ω → Fin d → ℝ} {h : Fin n → ℝ → Ω → E → ℝ}
  {f : Fin m → Ω → ℝ → ℝ} {g : Fin m → Ω → ℝ}

/-- **(3.2) integrated over `[0, T]`.** If the expected Lipschitz bounds at the pair hold with
interior constant `K`, and the difference and the coefficient differences are jointly measurable,
then
`𝔼 ∫_0^T (|δb|² + |δσ|²_F + ‖δh‖²_{L²(ν)} + |δf|²) ≤ K 𝔼 ∫_0^T (|δX|² + |δY|² + |δZ|²_F + ‖δU‖²)`,
in coordinates. -/
theorem PairLipschitz.energy_le (hL : PairLipschitz P ν T K KT X Y Z U b σ h f g)
    (hX : ∀ i, Measurable (Function.uncurry fun ω s => X i s ω))
    (hY : ∀ k, Measurable (Function.uncurry fun ω s => Y k s ω))
    (hZ : ∀ k j, Measurable (Function.uncurry fun ω s => Z k s ω j))
    (hU : ∀ k, Measurable fun p : Ω × ℝ × E => U k p.2.1 p.1 p.2.2)
    (hb : ∀ i, Measurable (Function.uncurry (b i)))
    (hσ : ∀ i j, Measurable (Function.uncurry fun ω s => σ i s ω j))
    (hh : ∀ i, Measurable fun p : Ω × ℝ × E => h i p.2.1 p.1 p.2.2)
    (hf : ∀ k, Measurable (Function.uncurry (f k))) :
    ∑ i, Brownian.Ito.energy P T (b i)
        + ∑ i, ∑ j, Brownian.Ito.energy P T (fun ω s => σ i s ω j)
        + ∑ i, Poisson.Compensated.markedEnergy P ν T (fun ω s e => h i s ω e)
        + ∑ k, Brownian.Ito.energy P T (f k)
      ≤ ENNReal.ofReal K * (∑ i, Brownian.Ito.energy P T (fun ω s => X i s ω)
          + (∑ k, Brownian.Ito.energy P T (fun ω s => Y k s ω)
            + ∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z k s ω j)
            + ∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U k s ω e))) := by
  have hsq : ∀ {u : Ω → ℝ}, Measurable u → Measurable fun ω => (‖u ω‖₊ : ℝ≥0∞) ^ 2 :=
    fun hu => hu.nnnorm.coe_nnreal_ennreal.pow_const 2
  -- the bound between sample energies at almost every time
  have hpt : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      sampleEnergy P b s + ∑ i, sampleEnergy P (fun j ω s => σ i s ω j) s
          + markedSampleEnergy P ν (fun i ω s e => h i s ω e) s + sampleEnergy P f s
        ≤ ENNReal.ofReal K * (sampleEnergy P (fun i ω s => X i s ω) s
          + (sampleEnergy P (fun k ω s => Y k s ω) s
            + ∑ k, sampleEnergy P (fun j ω s => Z k s ω j) s
            + markedSampleEnergy P ν (fun k ω s e => U k s ω e) s)) := by
    filter_upwards [hL.lip] with s hs
    have hXs : ∀ i, Measurable (X i s) := fun i =>
      (hX i).comp (measurable_id.prodMk measurable_const)
    have hYs : ∀ k, Measurable (Y k s) := fun k =>
      (hY k).comp (measurable_id.prodMk measurable_const)
    have hZs : ∀ k j, Measurable fun ω => Z k s ω j := fun k j =>
      (hZ k j).comp (measurable_id.prodMk measurable_const)
    have hUs : ∀ k, Measurable fun ω => ∫⁻ e, (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν := fun k =>
      (measurable_uncurry_lintegral_sq_mark (ν := ν) (φ := fun ω s e => U k s ω e)
        (hU k)).comp (measurable_id.prodMk measurable_const)
    refine le_trans ?_ (hs.trans (le_of_eq ?_))
    · simp only [sampleEnergy, markedSampleEnergy, esq]
      exact le_trans (add_le_add (add_le_add (add_le_add (sum_lintegral_le _ _)
        ((Finset.sum_le_sum fun i _ => sum_lintegral_le _ _).trans (sum_lintegral_le _ _)))
        (sum_lintegral_le _ _)) (sum_lintegral_le _ _)) (lintegral_add_four_le _ _ _ _)
    · simp only [sampleEnergy, markedSampleEnergy, esq]
      rw [lintegral_add_four (Finset.measurable_sum _ fun i _ => hsq (hXs i))
          (Finset.measurable_sum _ fun k _ => hsq (hYs k))
          (Finset.measurable_sum _ fun k _ => Finset.measurable_sum _ fun j _ => hsq (hZs k j)),
        lintegral_finsetSum' _ fun i _ => (hsq (hXs i)).aemeasurable,
        lintegral_finsetSum' _ fun k _ => (hsq (hYs k)).aemeasurable,
        lintegral_finsetSum' _ fun k _ =>
          (Finset.measurable_sum _ fun j _ => hsq (hZs k j)).aemeasurable,
        lintegral_finsetSum' _ fun k _ => (hUs k).aemeasurable]
      simp only [lintegral_finsetSum' _ fun j _ => (hsq (hZs _ j)).aemeasurable, add_assoc]
  -- integration in time
  have hAm := measurable_sampleEnergy_add (P := P) (ν := ν) (x := b)
    (z := fun i j ω s => σ i s ω j) (u := fun i ω s e => h i s ω e) hb hσ hh
  have hRm : Measurable fun s => sampleEnergy P (fun i ω s => X i s ω) s
      + (sampleEnergy P (fun k ω s => Y k s ω) s + ∑ k, sampleEnergy P (fun j ω s => Z k s ω j) s
        + markedSampleEnergy P ν (fun k ω s e => U k s ω e) s) :=
    (measurable_sampleEnergy (P := P) (x := fun i ω s => X i s ω) hX).add
      (measurable_sampleEnergy_add (P := P) (ν := ν) (x := fun k ω s => Y k s ω)
        (z := fun k j ω s => Z k s ω j) (u := fun k ω s e => U k s ω e) hY hZ hU)
  calc _ = ∫⁻ s in Set.Icc (0 : ℝ) T, (sampleEnergy P b s
          + ∑ i, sampleEnergy P (fun j ω s => σ i s ω j) s
          + markedSampleEnergy P ν (fun i ω s e => h i s ω e) s + sampleEnergy P f s) := by
        rw [lintegral_add_left hAm, lintegral_sampleEnergy_add (P := P) (ν := ν) (x := b)
          (z := fun i j ω s => σ i s ω j) (u := fun i ω s e => h i s ω e) hb hσ hh T,
          lintegral_sampleEnergy hf T]
    _ ≤ ∫⁻ s in Set.Icc (0 : ℝ) T, ENNReal.ofReal K * (sampleEnergy P (fun i ω s => X i s ω) s
          + (sampleEnergy P (fun k ω s => Y k s ω) s
            + ∑ k, sampleEnergy P (fun j ω s => Z k s ω j) s
            + markedSampleEnergy P ν (fun k ω s e => U k s ω e) s)) := lintegral_mono_ae hpt
    _ = _ := by
        rw [lintegral_const_mul _ hRm, lintegral_add_left
            (measurable_sampleEnergy (P := P) (x := fun i ω s => X i s ω) hX),
          lintegral_sampleEnergy hX T, lintegral_sampleEnergy_add (P := P) (ν := ν)
            (x := fun k ω s => Y k s ω) (z := fun k j ω s => Z k s ω j)
            (u := fun k ω s e => U k s ω e) hY hZ hU T]

end Integrated

/-! ### Two solutions in `ℍ²` -/

variable [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
  {P : Measure Ω} [IsProbabilityMeasure P] {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {T lam : ℝ}
  {C₁ C₂ : Coeffs ν n m d} {ξ₁ ξ₂ : Fin n → Ω → ℝ}
  {qb₁ qb₂ : Fin n → Ω → ℝ → ℝ} {qσ₁ qσ₂ : Fin n → ℝ → Ω → Fin d → ℝ}
  {qh₁ qh₂ : Fin n → ℝ → Ω → E → ℝ} {qf₁ qf₂ : Fin m → Ω → ℝ → ℝ} {qg₁ qg₂ : Fin m → Ω → ℝ}
  {X₁ X₂ : Fin n → ℝ → Ω → ℝ} {Y₁ Y₂ : Fin m → ℝ → Ω → ℝ}
  {Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ} {U₁ U₂ : Fin m → ℝ → Ω → E → ℝ}
  {γ₁ γ₂ : Fin n → ℝ → Ω → E → ℝ} {K KT : ℝ}

namespace SolvesForcedInt

variable (h₁ : SolvesForcedInt D ℱ hℱW hℱN T lam C₁ ξ₁ qb₁ qσ₁ qh₁ qf₁ qg₁ X₁ Y₁ Z₁ U₁ γ₁)
  (h₂ : SolvesForcedInt D ℱ hℱW hℱN T lam C₂ ξ₂ qb₂ qσ₂ qh₂ qf₂ qg₂ X₂ Y₂ Z₂ U₂ γ₂)
include h₁ h₂

/-- **The difference of two solutions in `ℍ²` has finite energy on `[0, T]`**:
`𝔼 ∫_0^T (|δX|² + |δY|² + |δZ|²_F + ‖δU‖²_{L²(ν)}) < ∞`, in coordinates. -/
theorem diffEnergy_lt_top :
    ∑ i, Brownian.Ito.energy P T (fun ω s => X₁ i s ω - X₂ i s ω)
        + (∑ k, Brownian.Ito.energy P T (fun ω s => Y₁ k s ω - Y₂ k s ω)
          + ∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z₁ k s ω j - Z₂ k s ω j)
          + ∑ k, Poisson.Compensated.markedEnergy P ν T
            (fun ω s e => U₁ k s ω e - U₂ k s ω e)) < ⊤ := by
  have hX : ∀ i, Brownian.Ito.energy P T (fun ω s => X₁ i s ω - X₂ i s ω) ≠ ⊤ := fun i =>
    BSDEJ.Solves.energy_sub_ne_top (h₁.measurable_X i) (h₂.measurable_X i) (h₁.X_sq i)
      (h₂.X_sq i)
  have hY : ∀ k, Brownian.Ito.energy P T (fun ω s => Y₁ k s ω - Y₂ k s ω) ≠ ⊤ := fun k =>
    BSDEJ.Solves.energy_sub_ne_top (h₁.measurable_Y k) (h₂.measurable_Y k) (h₁.Y_sq k)
      (h₂.Y_sq k)
  have hZ : ∀ k j, Brownian.Ito.energy P T (fun ω s => Z₁ k s ω j - Z₂ k s ω j) ≠ ⊤ :=
    fun k j => BSDEJ.Solves.energy_sub_ne_top ((h₁.bwd k).Z_meas j) ((h₂.bwd k).Z_meas j)
      ((h₁.bwd k).Z_sq j) ((h₂.bwd k).Z_sq j)
  have hU : ∀ k, Poisson.Compensated.markedEnergy P ν T
      (fun ω s e => U₁ k s ω e - U₂ k s ω e) ≠ ⊤ := fun k => by
    simpa only [neg_one_mul, ← sub_eq_add_neg] using
      Poisson.Compensated.markedEnergy_add_ne_top (h₁.bwd k).U_meas
        ((h₂.bwd k).U_meas.const_mul (-1)) (h₁.bwd k).U_sq
        (Poisson.Compensated.markedEnergy_const_mul_ne_top (h₂.bwd k).U_meas (h₂.bwd k).U_sq (-1))
  refine ENNReal.add_lt_top.mpr ⟨ENNReal.sum_lt_top.mpr fun i _ => lt_top_iff_ne_top.mpr (hX i),
    ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨?_, ?_⟩, ?_⟩⟩
  · exact ENNReal.sum_lt_top.mpr fun k _ => lt_top_iff_ne_top.mpr (hY k)
  · exact ENNReal.sum_lt_top.mpr fun k _ => ENNReal.sum_lt_top.mpr fun j _ =>
      lt_top_iff_ne_top.mpr (hZ k j)
  · exact ENNReal.sum_lt_top.mpr fun k _ => lt_top_iff_ne_top.mpr (hU k)

/-- **The coefficient differences along two solutions in `ℍ²`, integrated in time.** For
`λ ≠ 0` and the expected Lipschitz bounds at the pair with interior constant `K`,
`𝔼 ∫_0^T (|δb|² + |δσ|²_F + ‖δγ‖²_{L²(ν)} + |δf|²) ≤ K 𝔼 ∫_0^T (|δX|² + |δY|² + |δZ|²_F + ‖δU‖²)`,
in coordinates. -/
theorem coeffEnergy_sub_le (hlam : lam ≠ 0)
    (hL : PairLipschitz P ν T K KT (fun i t ω => X₁ i t ω - X₂ i t ω)
      (fun k t ω => Y₁ k t ω - Y₂ k t ω) (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j)
      (fun k t ω e => U₁ k t ω e - U₂ k t ω e)
      (fun i ω s => driftProc P T C₁ X₁ Y₁ Z₁ U₁ i ω s - driftProc P T C₂ X₂ Y₂ Z₂ U₂ i ω s)
      (fun i s ω j => diffusionProc P T C₁ X₁ Y₁ Z₁ U₁ i s ω j
        - diffusionProc P T C₂ X₂ Y₂ Z₂ U₂ i s ω j)
      (fun i s ω e => jumpProc T γ₁ i s ω e - jumpProc T γ₂ i s ω e)
      (fun k ω s => driverProc P T C₁ X₁ Y₁ Z₁ U₁ k ω s - driverProc P T C₂ X₂ Y₂ Z₂ U₂ k ω s)
      (fun k ω => terminalVal P T C₁ X₁ k ω - terminalVal P T C₂ X₂ k ω)) :
    ∑ i, Brownian.Ito.energy P T
          (fun ω s => driftProc P T C₁ X₁ Y₁ Z₁ U₁ i ω s - driftProc P T C₂ X₂ Y₂ Z₂ U₂ i ω s)
        + ∑ i, ∑ j, Brownian.Ito.energy P T (fun ω s => diffusionProc P T C₁ X₁ Y₁ Z₁ U₁ i s ω j
          - diffusionProc P T C₂ X₂ Y₂ Z₂ U₂ i s ω j)
        + ∑ i, Poisson.Compensated.markedEnergy P ν T
          (fun ω s e => jumpProc T γ₁ i s ω e - jumpProc T γ₂ i s ω e)
        + ∑ k, Brownian.Ito.energy P T
          (fun ω s => driverProc P T C₁ X₁ Y₁ Z₁ U₁ k ω s - driverProc P T C₂ X₂ Y₂ Z₂ U₂ k ω s)
      ≤ ENNReal.ofReal K * (∑ i, Brownian.Ito.energy P T (fun ω s => X₁ i s ω - X₂ i s ω)
          + (∑ k, Brownian.Ito.energy P T (fun ω s => Y₁ k s ω - Y₂ k s ω)
            + ∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z₁ k s ω j - Z₂ k s ω j)
            + ∑ k, Poisson.Compensated.markedEnergy P ν T
              (fun ω s e => U₁ k s ω e - U₂ k s ω e))) :=
  hL.energy_le (fun i => (h₁.measurable_X i).sub (h₂.measurable_X i))
    (fun k => (h₁.measurable_Y k).sub (h₂.measurable_Y k))
    (fun k j => ((h₁.bwd k).Z_meas j).sub ((h₂.bwd k).Z_meas j))
    (fun k => (h₁.bwd k).U_meas.sub (h₂.bwd k).U_meas)
    (fun i => (h₁.measurable_driftProc hlam i).sub (h₂.measurable_driftProc hlam i))
    (fun i j => (h₁.measurable_diffusionProc hlam i j).sub (h₂.measurable_diffusionProc hlam i j))
    (fun i => (h₁.measurable_jumpProc hlam i).sub (h₂.measurable_jumpProc hlam i))
    (fun k => (h₁.measurable_driverProc hlam k).sub (h₂.measurable_driverProc hlam k))

/-- The drift difference along two solutions in `ℍ²` has finite energy on `[0, T]`, for `λ ≠ 0`
and the expected Lipschitz bounds at the pair. -/
theorem energy_driftProc_sub_ne_top (hlam : lam ≠ 0)
    (hL : PairLipschitz P ν T K KT (fun i t ω => X₁ i t ω - X₂ i t ω)
      (fun k t ω => Y₁ k t ω - Y₂ k t ω) (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j)
      (fun k t ω e => U₁ k t ω e - U₂ k t ω e)
      (fun i ω s => driftProc P T C₁ X₁ Y₁ Z₁ U₁ i ω s - driftProc P T C₂ X₂ Y₂ Z₂ U₂ i ω s)
      (fun i s ω j => diffusionProc P T C₁ X₁ Y₁ Z₁ U₁ i s ω j
        - diffusionProc P T C₂ X₂ Y₂ Z₂ U₂ i s ω j)
      (fun i s ω e => jumpProc T γ₁ i s ω e - jumpProc T γ₂ i s ω e)
      (fun k ω s => driverProc P T C₁ X₁ Y₁ Z₁ U₁ k ω s - driverProc P T C₂ X₂ Y₂ Z₂ U₂ k ω s)
      (fun k ω => terminalVal P T C₁ X₁ k ω - terminalVal P T C₂ X₂ k ω)) (i : Fin n) :
    Brownian.Ito.energy P T
      (fun ω s => driftProc P T C₁ X₁ Y₁ Z₁ U₁ i ω s - driftProc P T C₂ X₂ Y₂ Z₂ U₂ i ω s) ≠ ⊤ := by
  have hsum := (h₁.coeffEnergy_sub_le h₂ hlam hL).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (h₁.diffEnergy_lt_top h₂))
  simp only [ENNReal.add_lt_top, ENNReal.sum_lt_top, Finset.mem_univ, true_implies] at hsum
  exact (hsum.1.1.1 i).ne

/-- The driver difference along two solutions in `ℍ²` has finite energy on `[0, T]`, for
`λ ≠ 0` and the expected Lipschitz bounds at the pair. -/
theorem energy_driverProc_sub_ne_top (hlam : lam ≠ 0)
    (hL : PairLipschitz P ν T K KT (fun i t ω => X₁ i t ω - X₂ i t ω)
      (fun k t ω => Y₁ k t ω - Y₂ k t ω) (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j)
      (fun k t ω e => U₁ k t ω e - U₂ k t ω e)
      (fun i ω s => driftProc P T C₁ X₁ Y₁ Z₁ U₁ i ω s - driftProc P T C₂ X₂ Y₂ Z₂ U₂ i ω s)
      (fun i s ω j => diffusionProc P T C₁ X₁ Y₁ Z₁ U₁ i s ω j
        - diffusionProc P T C₂ X₂ Y₂ Z₂ U₂ i s ω j)
      (fun i s ω e => jumpProc T γ₁ i s ω e - jumpProc T γ₂ i s ω e)
      (fun k ω s => driverProc P T C₁ X₁ Y₁ Z₁ U₁ k ω s - driverProc P T C₂ X₂ Y₂ Z₂ U₂ k ω s)
      (fun k ω => terminalVal P T C₁ X₁ k ω - terminalVal P T C₂ X₂ k ω)) (k : Fin m) :
    Brownian.Ito.energy P T
      (fun ω s => driverProc P T C₁ X₁ Y₁ Z₁ U₁ k ω s - driverProc P T C₂ X₂ Y₂ Z₂ U₂ k ω s)
      ≠ ⊤ := by
  have hsum := (h₁.coeffEnergy_sub_le h₂ hlam hL).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (h₁.diffEnergy_lt_top h₂))
  simp only [ENNReal.add_lt_top, ENNReal.sum_lt_top, Finset.mem_univ, true_implies] at hsum
  exact (hsum.2 k).ne

/-- **The drift of the forward difference equation has finite energy**: for the expected
Lipschitz bounds at the pair, `(λ b¹ + q^{b,1}) − (λ b² + q^{b,2})` has finite energy on
`[0, T]`, coordinatewise. -/
theorem energy_drift_sub_ne_top
    (hL : PairLipschitz P ν T K KT (fun i t ω => X₁ i t ω - X₂ i t ω)
      (fun k t ω => Y₁ k t ω - Y₂ k t ω) (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j)
      (fun k t ω e => U₁ k t ω e - U₂ k t ω e)
      (fun i ω s => driftProc P T C₁ X₁ Y₁ Z₁ U₁ i ω s - driftProc P T C₂ X₂ Y₂ Z₂ U₂ i ω s)
      (fun i s ω j => diffusionProc P T C₁ X₁ Y₁ Z₁ U₁ i s ω j
        - diffusionProc P T C₂ X₂ Y₂ Z₂ U₂ i s ω j)
      (fun i s ω e => jumpProc T γ₁ i s ω e - jumpProc T γ₂ i s ω e)
      (fun k ω s => driverProc P T C₁ X₁ Y₁ Z₁ U₁ k ω s - driverProc P T C₂ X₂ Y₂ Z₂ U₂ k ω s)
      (fun k ω => terminalVal P T C₁ X₁ k ω - terminalVal P T C₂ X₂ k ω)) (i : Fin n) :
    Brownian.Ito.energy P T (fun ω s => (lam * driftProc P T C₁ X₁ Y₁ Z₁ U₁ i ω s + qb₁ i ω s)
      - (lam * driftProc P T C₂ X₂ Y₂ Z₂ U₂ i ω s + qb₂ i ω s)) ≠ ⊤ := by
  have hq := BSDEJ.Solves.energy_sub_ne_top (h₁.forcing.qb_meas i) (h₂.forcing.qb_meas i)
    (h₁.forcing.qb_sq i) (h₂.forcing.qb_sq i)
  rcases eq_or_ne lam 0 with rfl | hlam
  · simpa only [zero_mul, zero_add] using hq
  have hm : Measurable (Function.uncurry fun ω s =>
      driftProc P T C₁ X₁ Y₁ Z₁ U₁ i ω s - driftProc P T C₂ X₂ Y₂ Z₂ U₂ i ω s) :=
    (h₁.measurable_driftProc hlam i).sub (h₂.measurable_driftProc hlam i)
  have e : (fun ω s => (lam * driftProc P T C₁ X₁ Y₁ Z₁ U₁ i ω s + qb₁ i ω s)
      - (lam * driftProc P T C₂ X₂ Y₂ Z₂ U₂ i ω s + qb₂ i ω s))
      = fun ω s => lam * (driftProc P T C₁ X₁ Y₁ Z₁ U₁ i ω s
        - driftProc P T C₂ X₂ Y₂ Z₂ U₂ i ω s) + (qb₁ i ω s - qb₂ i ω s) := by
    funext ω s
    ring
  rw [e]
  exact Brownian.Ito.energy_add_ne_top (hm.const_mul lam)
    ((h₁.forcing.qb_meas i).sub (h₂.forcing.qb_meas i))
    (Brownian.Ito.energy_const_mul_ne_top hm (h₁.energy_driftProc_sub_ne_top h₂ hlam hL i) lam)
    hq

/-- **The drift of the backward difference equation has finite energy**: for the expected
Lipschitz bounds at the pair, `(λ f¹ + q^{f,1}) − (λ f² + q^{f,2})` has finite energy on
`[0, T]`, coordinatewise. -/
theorem energy_driver_sub_ne_top
    (hL : PairLipschitz P ν T K KT (fun i t ω => X₁ i t ω - X₂ i t ω)
      (fun k t ω => Y₁ k t ω - Y₂ k t ω) (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j)
      (fun k t ω e => U₁ k t ω e - U₂ k t ω e)
      (fun i ω s => driftProc P T C₁ X₁ Y₁ Z₁ U₁ i ω s - driftProc P T C₂ X₂ Y₂ Z₂ U₂ i ω s)
      (fun i s ω j => diffusionProc P T C₁ X₁ Y₁ Z₁ U₁ i s ω j
        - diffusionProc P T C₂ X₂ Y₂ Z₂ U₂ i s ω j)
      (fun i s ω e => jumpProc T γ₁ i s ω e - jumpProc T γ₂ i s ω e)
      (fun k ω s => driverProc P T C₁ X₁ Y₁ Z₁ U₁ k ω s - driverProc P T C₂ X₂ Y₂ Z₂ U₂ k ω s)
      (fun k ω => terminalVal P T C₁ X₁ k ω - terminalVal P T C₂ X₂ k ω)) (k : Fin m) :
    Brownian.Ito.energy P T (fun ω s => (lam * driverProc P T C₁ X₁ Y₁ Z₁ U₁ k ω s + qf₁ k ω s)
      - (lam * driverProc P T C₂ X₂ Y₂ Z₂ U₂ k ω s + qf₂ k ω s)) ≠ ⊤ := by
  have hq := BSDEJ.Solves.energy_sub_ne_top (h₁.forcing.qf_meas k) (h₂.forcing.qf_meas k)
    (h₁.forcing.qf_sq k) (h₂.forcing.qf_sq k)
  rcases eq_or_ne lam 0 with rfl | hlam
  · simpa only [zero_mul, zero_add] using hq
  have hm : Measurable (Function.uncurry fun ω s =>
      driverProc P T C₁ X₁ Y₁ Z₁ U₁ k ω s - driverProc P T C₂ X₂ Y₂ Z₂ U₂ k ω s) :=
    (h₁.measurable_driverProc hlam k).sub (h₂.measurable_driverProc hlam k)
  have e : (fun ω s => (lam * driverProc P T C₁ X₁ Y₁ Z₁ U₁ k ω s + qf₁ k ω s)
      - (lam * driverProc P T C₂ X₂ Y₂ Z₂ U₂ k ω s + qf₂ k ω s))
      = fun ω s => lam * (driverProc P T C₁ X₁ Y₁ Z₁ U₁ k ω s
        - driverProc P T C₂ X₂ Y₂ Z₂ U₂ k ω s) + (qf₁ k ω s - qf₂ k ω s) := by
    funext ω s
    ring
  rw [e]
  exact Brownian.Ito.energy_add_ne_top (hm.const_mul lam)
    ((h₁.forcing.qf_meas k).sub (h₂.forcing.qf_meas k))
    (Brownian.Ito.energy_const_mul_ne_top hm (h₁.energy_driverProc_sub_ne_top h₂ hlam hL k) lam)
    hq

/-- **The terminal value of the backward difference equation is square integrable**: for
`T ≥ 0` and the expected Lipschitz bounds at the pair,
`(λ g¹(X¹_T, Law X¹_T) + q^{g,1}) − (λ g²(X²_T, Law X²_T) + q^{g,2})` is square integrable,
coordinatewise, since `𝔼 |δg_T|² ≤ K_T 𝔼 |δX_T|² < ∞`. -/
theorem memLp_terminal_sub (hT : 0 ≤ T)
    (hL : PairLipschitz P ν T K KT (fun i t ω => X₁ i t ω - X₂ i t ω)
      (fun k t ω => Y₁ k t ω - Y₂ k t ω) (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j)
      (fun k t ω e => U₁ k t ω e - U₂ k t ω e)
      (fun i ω s => driftProc P T C₁ X₁ Y₁ Z₁ U₁ i ω s - driftProc P T C₂ X₂ Y₂ Z₂ U₂ i ω s)
      (fun i s ω j => diffusionProc P T C₁ X₁ Y₁ Z₁ U₁ i s ω j
        - diffusionProc P T C₂ X₂ Y₂ Z₂ U₂ i s ω j)
      (fun i s ω e => jumpProc T γ₁ i s ω e - jumpProc T γ₂ i s ω e)
      (fun k ω s => driverProc P T C₁ X₁ Y₁ Z₁ U₁ k ω s - driverProc P T C₂ X₂ Y₂ Z₂ U₂ k ω s)
      (fun k ω => terminalVal P T C₁ X₁ k ω - terminalVal P T C₂ X₂ k ω)) (k : Fin m) :
    MemLp (fun ω => (lam * terminalVal P T C₁ X₁ k ω + qg₁ k ω)
      - (lam * terminalVal P T C₂ X₂ k ω + qg₂ k ω)) 2 P := by
  have hq : MemLp (fun ω => qg₁ k ω - qg₂ k ω) 2 P :=
    (h₁.forcing.qg_sq k).sub (h₂.forcing.qg_sq k)
  rcases eq_or_ne lam 0 with rfl | hlam
  · simpa only [zero_mul, zero_add] using hq
  have hXT : ∫⁻ ω, esq (fun i => X₁ i T ω - X₂ i T ω) ∂P < ⊤ :=
    lintegral_esq_lt_top (x := fun i ω => X₁ i T ω - X₂ i T ω) fun i =>
      (h₁.XT_sq i).sub (h₂.XT_sq i)
  have hg : MemLp (fun ω => terminalVal P T C₁ X₁ k ω - terminalVal P T C₂ X₂ k ω) 2 P := by
    refine Brownian.Ito.memLp_two_of_lintegral_sq_lt_top
      ((h₁.aestronglyMeasurable_terminalVal hlam hT k).sub
        (h₂.aestronglyMeasurable_terminalVal hlam hT k)) ?_
    refine lt_of_le_of_lt (lintegral_mono fun ω => ?_)
      (hL.lipT.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hXT))
    exact Finset.single_le_sum
      (f := fun k => (‖terminalVal P T C₁ X₁ k ω - terminalVal P T C₂ X₂ k ω‖₊ : ℝ≥0∞) ^ 2)
      (fun _ _ => zero_le) (Finset.mem_univ k)
  have e : (fun ω => (lam * terminalVal P T C₁ X₁ k ω + qg₁ k ω)
      - (lam * terminalVal P T C₂ X₂ k ω + qg₂ k ω))
      = fun ω => lam * (terminalVal P T C₁ X₁ k ω - terminalVal P T C₂ X₂ k ω)
        + (qg₁ k ω - qg₂ k ω) := by
    funext ω
    ring
  rw [e]
  exact (hg.const_mul lam).add hq

end SolvesForcedInt

end MVFBSDEJ.WellPosedness.System
