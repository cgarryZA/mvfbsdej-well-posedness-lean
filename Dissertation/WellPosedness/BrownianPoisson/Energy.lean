/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.BrownianPoisson.ItoLevy

/-!
# The time-zero energy bound of an Itô–Lévy process with drift `−φ`

For an Itô–Lévy process `X` with initial value `X₀`, drift `−φ`, diffusion vector `σ` and jump
integrand `γ`, the exponentially weighted second-moment identity at weight `e^s` reads

`e^T 𝔼[X_T²] = 𝔼[X₀²] + ∫_0^T e^s (𝔼[X_s²] − 2 𝔼[X_s φ_s] + ∑_j 𝔼[σ_j(s)²]
  + 𝔼 ∫_E γ(s, e)² ν(de)) ds`,

which for a solution of the linear backward equation is the expectation of the Itô identity (4.5)
of the well-posedness paper at `t = 0`. Young's inequality `𝔼[X_s²] − 2 𝔼[X_s φ_s] ≥ −𝔼[φ_s²]`
and `1 ≤ e^s ≤ e^T` on `[0, T]` turn it into

`𝔼[X₀²] + ∑_j 𝔼 ∫_0^T σ_j² ds + 𝔼 ∫_0^T ∫_E γ² dν ds ≤ e^T (𝔼[X_T²] + 𝔼 ∫_0^T φ² ds)`.

## Main statements

* `lintegral_sq_initial_add_energy_le` — the bound above, over a filtration carrying the driver
  with a cross witness.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Dissertation.WellPosedness.BrownianPoisson

open LevyStochCalc LevyStochCalc.Ito.SecondMoment

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}
  {T : ℝ} {X : ℝ → Ω → ℝ} {X₀ : Ω → ℝ} {φ : Ω → ℝ → ℝ} {σ : ℝ → Ω → Fin d → ℝ}
  {γ : Ω → ℝ → E → ℝ}

omit [IsProbabilityMeasure P] in
/-- Young's inequality under the expectation: `−𝔼[f²] ≤ 𝔼[x²] + 2 𝔼[x (−f)]`. -/
theorem neg_integral_mul_self_le {x f : Ω → ℝ} (hx : MemLp x 2 P) (hf : MemLp f 2 P) :
    -∫ ω, f ω * f ω ∂P ≤ ∫ ω, x ω * x ω ∂P + 2 * ∫ ω, x ω * -f ω ∂P := by
  have hsq := integral_mul_self_add (g := fun ω => -f ω) hx hf.neg
  have h0 : 0 ≤ ∫ ω, (x ω + -f ω) * (x ω + -f ω) ∂P :=
    integral_nonneg fun ω => mul_self_nonneg _
  have hff : ∫ ω, -f ω * -f ω ∂P = ∫ ω, f ω * f ω ∂P := by simp only [neg_mul_neg]
  linarith

/-- **The time-zero energy bound.** For an Itô–Lévy process with initial value `X₀` measurable at
time `0` and square integrable, drift `−φ` with `φ` progressive, of finite energy on `[0, T]` and
vanishing off it, diffusion vector `σ` and jump integrand `γ`,

`𝔼[X₀²] + ∑_j 𝔼 ∫_0^T σ_j² ds + 𝔼 ∫_0^T ∫_E γ² dν ds ≤ e^T (𝔼[X_T²] + 𝔼 ∫_0^T φ² ds)`. -/
theorem lintegral_sq_initial_add_energy_le
    (h : Ito.Setting.IsItoLevyProcess D.W D.N ℱ hℱW hℱN X X₀ (fun s ω => -φ ω s) σ γ)
    (𝒲 : D.CrossWitness ℱ) (hX₀ : StronglyMeasurable[ℱ 0] X₀) (hX₀2 : MemLp X₀ 2 P)
    (hφm : Measurable (Function.uncurry φ)) (hφp : Probability.ProgressivelyMeasurable ℱ φ)
    (hφv : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → φ ω s = 0)
    (hφq : Brownian.Ito.energy P T φ ≠ ⊤) (hT : 0 < T) :
    ∫⁻ ω, (‖X₀ ω‖₊ : ℝ≥0∞) ^ 2 ∂P
        + (∑ j : Fin d, Brownian.Ito.energy P T (fun ω s => σ s ω j))
        + Poisson.Compensated.markedEnergy P ν T γ
      ≤ ENNReal.ofReal (Real.exp T)
        * (∫⁻ ω, (‖X T ω‖₊ : ℝ≥0∞) ^ 2 ∂P + Brownian.Ito.energy P T φ) := by
  classical
  -- the drift `−φ` in the form the second-moment identities take
  have hbm : Measurable (Function.uncurry fun ω s => -φ ω s) := hφm.neg
  have hbp : Probability.ProgressivelyMeasurable ℱ fun ω s => -φ ω s :=
    continuous_neg.comp_progressivelyMeasurable neg_zero hφp
  have hbq : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖-φ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := fun T' _ =>
    BSDEJ.Solves.neg_drift_sq_int_global hφv hφq T'
  have hφm2 : Measurable (Function.uncurry fun ω s => (‖φ ω s‖₊ : ℝ≥0∞) ^ 2) :=
    hφm.nnnorm.coe_nnreal_ennreal.pow_const 2
  -- the four rates of the identity, integrable on the window
  have hA : IntegrableOn (fun s => ∫ ω, X s ω * X s ω ∂P) (Set.Icc (0 : ℝ) T) :=
    integrableOn_integral_mul_self h 𝒲 hX₀ hX₀2 hbm hbp hbq hT
  have hB : IntegrableOn (fun s => ∫ ω, X s ω * -φ ω s ∂P) (Set.Icc (0 : ℝ) T) :=
    integrableOn_integral_mul_drift h hX₀2 hbm hbp hbq hT
  have hC : IntegrableOn (fun s => ∑ j : Fin d, (∫⁻ ω, (‖σ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
      (Set.Icc (0 : ℝ) T) :=
    integrable_finsetSum _ fun j _ =>
      integrableOn_toReal_lintegral (measurable_uncurry_sq_diffusion h j) (h.σ_sq j T hT)
  have hG : IntegrableOn (fun s => (∫⁻ ω, ∫⁻ e, (‖γ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal)
      (Set.Icc (0 : ℝ) T) :=
    integrableOn_toReal_lintegral (measurable_uncurry_lintegral_sq_jump h) (h.γ_sq T hT)
  have hF : IntegrableOn (fun s => (∫⁻ ω, (‖φ ω s‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
      (Set.Icc (0 : ℝ) T) :=
    integrableOn_toReal_lintegral hφm2 hφq.lt_top
  have hupper : IntegrableOn (fun s => Real.exp (1 * s)
      * (1 * ∫ ω, X s ω * X s ω ∂P + 2 * ∫ ω, X s ω * -φ ω s ∂P
        + (∑ j : Fin d, (∫⁻ ω, (‖σ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
        + (∫⁻ ω, ∫⁻ e, (‖γ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal)) (Set.Icc (0 : ℝ) T) :=
    integrableOn_exp_mul 1 ((((hA.const_mul 1).add (hB.const_mul 2)).add hC).add hG)
  have hlower : IntegrableOn (fun s =>
      (∑ j : Fin d, (∫⁻ ω, (‖σ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
        + (∫⁻ ω, ∫⁻ e, (‖γ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal
        - Real.exp T * (∫⁻ ω, (‖φ ω s‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal) (Set.Icc (0 : ℝ) T) :=
    (hC.add hG).sub (hF.const_mul _)
  -- the rates dominate the energy rates, less `e^T` times the drift rate, almost everywhere
  have hmono : ∫ s in Set.Icc (0 : ℝ) T,
      ((∑ j : Fin d, (∫⁻ ω, (‖σ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
        + (∫⁻ ω, ∫⁻ e, (‖γ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal
        - Real.exp T * (∫⁻ ω, (‖φ ω s‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
      ≤ ∫ s in Set.Icc (0 : ℝ) T, Real.exp (1 * s)
        * (1 * ∫ ω, X s ω * X s ω ∂P + 2 * ∫ ω, X s ω * -φ ω s ∂P
          + (∑ j : Fin d, (∫⁻ ω, (‖σ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
          + (∫⁻ ω, ∫⁻ e, (‖γ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal) := by
    refine integral_mono_ae hlower hupper ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_memLp_two_eval (P := P) hφm hφq.lt_top] with s hs hφs
    have hXs : MemLp (X s) 2 P := memLp_two_of_isItoLevyProcess h hX₀2 hbm hbq hs.1
    have hyoung := neg_integral_mul_self_le hXs hφs
    rw [integral_mul_self_eq_toReal hφs] at hyoung
    have hC0 : 0 ≤ ∑ j : Fin d, (∫⁻ ω, (‖σ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal :=
      Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
    have hG0 : 0 ≤ (∫⁻ ω, ∫⁻ e, (‖γ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal := ENNReal.toReal_nonneg
    have hF0 : 0 ≤ (∫⁻ ω, (‖φ ω s‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal := ENNReal.toReal_nonneg
    have he1 : 1 ≤ Real.exp (1 * s) := Real.one_le_exp (by linarith [hs.1])
    have heT : Real.exp (1 * s) ≤ Real.exp T := Real.exp_le_exp.mpr (by linarith [hs.2])
    generalize (∑ j : Fin d, (∫⁻ ω, (‖σ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal) = c at hC0 ⊢
    generalize (∫⁻ ω, ∫⁻ e, (‖γ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal = g at hG0 ⊢
    generalize (∫⁻ ω, (‖φ ω s‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal = f at hF0 hyoung ⊢
    generalize ∫ ω, X s ω * X s ω ∂P = a at hyoung ⊢
    generalize ∫ ω, X s ω * -φ ω s ∂P = b at hyoung ⊢
    generalize Real.exp (1 * s) = es at he1 heT ⊢
    have k1 : 0 ≤ (es - 1) * (c + g) := mul_nonneg (by linarith) (by linarith)
    have k2 : 0 ≤ (Real.exp T - es) * f := mul_nonneg (by linarith) hF0
    have k3 : 0 ≤ es * (1 * a + 2 * b + f) := mul_nonneg (by linarith) (by linarith)
    nlinarith
  -- the three time integrals are the energies
  have hCint : ∫ s in Set.Icc (0 : ℝ) T,
      ∑ j : Fin d, (∫⁻ ω, (‖σ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal
        = ∑ j : Fin d, (Brownian.Ito.energy P T (fun ω s => σ s ω j)).toReal := by
    rw [integral_finsetSum _ fun j _ =>
      integrableOn_toReal_lintegral (measurable_uncurry_sq_diffusion h j) (h.σ_sq j T hT)]
    exact Finset.sum_congr rfl fun j _ =>
      (toReal_lintegral_lintegral_eq (measurable_uncurry_sq_diffusion h j) (h.σ_sq j T hT)).symm
  have hGint : ∫ s in Set.Icc (0 : ℝ) T, (∫⁻ ω, ∫⁻ e, (‖γ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal
      = (Poisson.Compensated.markedEnergy P ν T γ).toReal :=
    (toReal_lintegral_lintegral_eq (measurable_uncurry_lintegral_sq_jump h) (h.γ_sq T hT)).symm
  have hFint : ∫ s in Set.Icc (0 : ℝ) T, (∫⁻ ω, (‖φ ω s‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal
      = (Brownian.Ito.energy P T φ).toReal :=
    (toReal_lintegral_lintegral_eq hφm2 hφq.lt_top).symm
  have hsplit : ∫ s in Set.Icc (0 : ℝ) T,
      ((∑ j : Fin d, (∫⁻ ω, (‖σ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
        + (∫⁻ ω, ∫⁻ e, (‖γ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal
        - Real.exp T * (∫⁻ ω, (‖φ ω s‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
      = (∑ j : Fin d, (Brownian.Ito.energy P T (fun ω s => σ s ω j)).toReal)
        + (Poisson.Compensated.markedEnergy P ν T γ).toReal
        - Real.exp T * (Brownian.Ito.energy P T φ).toReal := by
    have hCG : IntegrableOn (fun s =>
        (∑ j : Fin d, (∫⁻ ω, (‖σ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
          + (∫⁻ ω, ∫⁻ e, (‖γ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal) (Set.Icc (0 : ℝ) T) :=
      hC.add hG
    rw [integral_sub hCG (hF.const_mul _), integral_add hC hG, integral_const_mul,
      hCint, hGint, hFint]
  -- the weighted identity at weight `e^s`
  have key := integral_exp_mul_self_eq_of_isItoLevyProcess h 𝒲 hX₀ hX₀2 hbm hbp hbq 1 hT
  have hXT : MemLp (X T) 2 P := memLp_two_of_isItoLevyProcess h hX₀2 hbm hbq hT.le
  rw [integral_mul_self_eq_toReal hXT, integral_mul_self_eq_toReal hX₀2, one_mul] at key
  have hreal : (∫⁻ ω, (‖X₀ ω‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal
      + (∑ j : Fin d, (Brownian.Ito.energy P T (fun ω s => σ s ω j)).toReal)
      + (Poisson.Compensated.markedEnergy P ν T γ).toReal
      ≤ Real.exp T * ((∫⁻ ω, (‖X T ω‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal
        + (Brownian.Ito.energy P T φ).toReal) := by
    rw [hsplit] at hmono
    nlinarith [hmono, key]
  -- back to `ℝ≥0∞`
  have hX₀f : ∫⁻ ω, (‖X₀ ω‖₊ : ℝ≥0∞) ^ 2 ∂P ≠ ⊤ := (lintegral_sq_lt_top_of_memLp_two hX₀2).ne
  have hXTf : ∫⁻ ω, (‖X T ω‖₊ : ℝ≥0∞) ^ 2 ∂P ≠ ⊤ := (lintegral_sq_lt_top_of_memLp_two hXT).ne
  have hσf : ∀ j ∈ Finset.univ, Brownian.Ito.energy P T (fun ω s => σ s ω j) ≠ ⊤ :=
    fun j _ => (h.σ_sq j T hT).ne
  have hγf : Poisson.Compensated.markedEnergy P ν T γ ≠ ⊤ := (h.γ_sq T hT).ne
  have hLf : ∫⁻ ω, (‖X₀ ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      + (∑ j : Fin d, Brownian.Ito.energy P T (fun ω s => σ s ω j))
      + Poisson.Compensated.markedEnergy P ν T γ ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hX₀f, ENNReal.sum_ne_top.mpr hσf⟩, hγf⟩
  have hRf : ENNReal.ofReal (Real.exp T)
      * (∫⁻ ω, (‖X T ω‖₊ : ℝ≥0∞) ^ 2 ∂P + Brownian.Ito.energy P T φ) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.mpr ⟨hXTf, hφq⟩)
  rw [← ENNReal.toReal_le_toReal hLf hRf, ENNReal.toReal_mul, ENNReal.toReal_ofReal
    (Real.exp_pos T).le, ENNReal.toReal_add hXTf hφq,
    ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hX₀f, ENNReal.sum_ne_top.mpr hσf⟩) hγf,
    ENNReal.toReal_add hX₀f (ENNReal.sum_ne_top.mpr hσf), ENNReal.toReal_sum hσf]
  exact hreal

end Dissertation.WellPosedness.BrownianPoisson
