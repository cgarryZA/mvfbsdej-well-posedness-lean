/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.Acceptance.A.WitnessForced
import Dissertation.Acceptance.A.Solution
import Dissertation.WellPosedness.Existence.CoeffShift
import Dissertation.WellPosedness.System.FrozenDifference
import Dissertation.WellPosedness.System.WeakPairDiff
import Dissertation.WellPosedness.System.WeakPairEnergy

/-!
# Instances of the hypotheses of Lemma 4.3 at explicit solutions

Statement and equation numbers refer to the well-posedness paper at `1f67672`. Over a probability
space carrying a Lévy driver with `d = 1` and `ν = δ₀` on `ℝ`, with `𝒢₀ = ⊥`, `n = m = 1` and
`T = 1`, take the system of Example 5.1(i) with `β₁ = β₂ = 1` and `σ_c = h_c = 0`,
`b = −y`, `σ = −z`, `h = −u`, `f = x`, `g = x`. Let `M^W`, `M^N` be everywhere-càdlàg versions of
`∫_0^t 1_{(0, 1]} dW` and `∫_0^t ∫ 1_{(0, 1]} Ñ(ds, de)`. For reals `x₀, a, c, y₀, a', c'` the tuple

`X = x₀ + a M^W + c M^N`, `Y = y₀ + a' M^W + c' M^N`, `Z = a' 1_{(0, 1]}`, `U = c' 1_{(0, 1]}`

solves the system at `λ = 0` with the forcing `(0, a 1_{(0, 1]}, c 1_{(0, 1]}, 0, Y_1)`, and hence
the system (4.1) at `λ = 1` with the forcing `q = (0, a 1_{(0, 1]}, c 1_{(0, 1]}, 0, Y_1) − Ψ(Θ)`,
`Ψ(Θ)` the coefficient processes along the tuple. Its forced diffusion and jump integrands are
`a 1_{(0, 1]}` and `c 1_{(0, 1]}`. Paired with the solution at the parameters `0` (the zero tuple),
three choices of parameters make the integrands of the four bounds of (4.18) and of the fifth
term of (4.17) nonzero.

## Main statements

* `Dissertation.Acceptance.A.affineWindow_pair` — the solution at given parameters and the one
  at the parameters `0`, with their differences.
* `Dissertation.Acceptance.A.lem_pert_backward_window_hypotheses` — `δX ≡ 1`, `δZ = δU =
  1_{(0, 1]}`: the integrands of the first and third bounds of (4.18) are `1_{(0, 1]}`.
* `Dissertation.Acceptance.A.lem_pert_forward_window_hypotheses` — `δY ≡ 1` and the forced
  diffusion and jump integrands `1_{(0, 1]}`: the integrands of the second and fourth bounds are
  `1_{(0, 1]}`.
* `Dissertation.Acceptance.A.lem_pert_jump_window_hypotheses` — the forced jump integrand and
  `δU` equal to `1_{(0, 1]}`: the fifth integrand is `1_{(0, 1]}`.
-/

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped ENNReal Topology

namespace Dissertation.Acceptance.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence
  Dissertation.WellPosedness.Enlarged Dissertation.WellPosedness.Spec Dissertation.PaperSpec.A
  Dissertation.WellPosedness.Stability Dissertation.WellPosedness.BrownianPoisson LevyStochCalc

universe w

/-- The system of Example 5.1(i) with `n = d = 1`, `ν = δ₀` on `ℝ`, `β₁ = β₂ = 1`, `σ_c = 0` and
`h_c = 0`. -/
local notation "sysW" =>
  affineCoeffs (ν := Measure.dirac (0 : ℝ)) (n := 1) (d := 1) 1 1 0 0

/-! ### The window integrands -/

section Window

variable {Ω : Type*} [MeasurableSpace Ω] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

/-- A multiple of the window `(0, 1]` is predictable. -/
theorem predictable_const_mul_unitWindow (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (r : ℝ) :
    Probability.Predictable ℱ fun (_ : Ω) s => r * unitWindow s :=
  (predictable_unitWindow ℱ).const_mul r

/-- A multiple of the window `(0, 1]` is marked predictable at `ν = δ₀`. -/
theorem markedPredictable_const_mul_unitWindow (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (r : ℝ) :
    Probability.MarkedPredictable ℱ (Measure.dirac (0 : ℝ))
      fun (_ : Ω) s (_ : ℝ) => r * unitWindow s :=
  (markedPredictable_unitWindow ℱ (Measure.dirac (0 : ℝ))).const_mul r

/-- A multiple of the window `(0, 1]` is jointly measurable. -/
theorem measurable_const_mul_unitWindow (r : ℝ) :
    Measurable (Function.uncurry fun (_ : Ω) s => r * unitWindow s) :=
  (measurable_unitWindow.comp measurable_snd).const_mul r

/-- A multiple of the window `(0, 1]` is jointly measurable in the sample point, the time and the
mark. -/
theorem measurable_marked_const_mul_unitWindow (r : ℝ) :
    Measurable fun p : Ω × ℝ × ℝ => r * unitWindow p.2.1 :=
  (measurable_unitWindow.comp measurable_snd.fst).const_mul r

variable (P : Measure Ω) [IsProbabilityMeasure P]

/-- The window `(0, 1]` has energy `1` on `[0, 1]`. -/
theorem energy_unitWindow : Brownian.Ito.energy P 1 (fun (_ : Ω) s => unitWindow s) = 1 := by
  simp [Brownian.Ito.energy, setLIntegral_unitWindow_sq]

/-- The window `(0, 1]` has marked energy `1` on `[0, 1]` at `ν = δ₀`. -/
theorem markedEnergy_unitWindow :
    Poisson.Compensated.markedEnergy P (Measure.dirac (0 : ℝ)) 1
      (fun (_ : Ω) s (_ : ℝ) => unitWindow s) = 1 := by
  simp [Poisson.Compensated.markedEnergy, setLIntegral_unitWindow_sq]

/-- A multiple of the window `(0, 1]` has finite energy on `[0, 1]`. -/
theorem energy_const_mul_unitWindow_ne_top (r : ℝ) :
    Brownian.Ito.energy P 1 (fun (_ : Ω) s => r * unitWindow s) ≠ ⊤ :=
  Brownian.Ito.energy_const_mul_ne_top (H := fun (_ : Ω) s => unitWindow s)
    (measurable_unitWindow.comp measurable_snd)
    (by rw [energy_unitWindow]; exact ENNReal.one_ne_top) r

/-- A multiple of the window `(0, 1]` has finite marked energy on `[0, 1]` at `ν = δ₀`. -/
theorem markedEnergy_const_mul_unitWindow_ne_top (r : ℝ) :
    Poisson.Compensated.markedEnergy P (Measure.dirac (0 : ℝ)) 1
      (fun (_ : Ω) s (_ : ℝ) => r * unitWindow s) ≠ ⊤ :=
  Poisson.Compensated.markedEnergy_const_mul_ne_top (φ := fun (_ : Ω) s (_ : ℝ) => unitWindow s)
    (measurable_unitWindow.comp measurable_snd.fst)
    (by rw [markedEnergy_unitWindow]; exact ENNReal.one_ne_top) r

end Window

/-! ### The linear equations of the explicit tuple -/

section Linear

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {D : LevyStochCalc.Driver.LevyDriver P 1 (Measure.dirac (0 : ℝ))}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin 1, Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : Poisson.IsPoissonFiltration D.N ℱ} {MW MN : ℝ → Ω → ℝ}

/-- The window `(0, 1]`, as a diffusion vector, is jointly measurable. -/
theorem window_meas : ∀ j : Fin 1, Measurable (Function.uncurry fun (ω : Ω) s =>
    (fun s (_ : Ω) (_ : Fin 1) => unitWindow s) s ω j) :=
  fun _ => measurable_unitWindow.comp measurable_snd

/-- The window `(0, 1]`, as a diffusion vector, is progressively measurable. -/
theorem window_prog (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) :
    ∀ j : Fin 1, Probability.ProgressivelyMeasurable ℱ fun (ω : Ω) s =>
      (fun s (_ : Ω) (_ : Fin 1) => unitWindow s) s ω j :=
  progressivelyMeasurable_of_predictable_of_vanish (T := 1)
    (Z := fun s (_ : Ω) (_ : Fin 1) => unitWindow s) (fun _ => predictable_unitWindow ℱ)
    fun _ _ hs => funext fun _ => unitWindow_of_notMem hs

/-- The window `(0, 1]`, as a diffusion vector, is square integrable on every horizon. -/
theorem window_sq (P : Measure Ω) [IsProbabilityMeasure P] :
    ∀ (j : Fin 1) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖(fun s (_ : Ω) (_ : Fin 1) => unitWindow s) s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
  BSDEJ.Solves.sq_int_global_of_vanishing (T := 1)
    (fun _ _ hs => funext fun _ => unitWindow_of_notMem hs)
    fun _ => by rw [energy_unitWindow]; exact ENNReal.one_ne_top

/-- The window `(0, 1]`, as a marked integrand, is jointly measurable. -/
theorem windowN_meas : Measurable fun p : Ω × ℝ × ℝ =>
    (fun (_ : Ω) s (_ : ℝ) => unitWindow s) p.1 p.2.1 p.2.2 :=
  measurable_unitWindow.comp measurable_snd.fst

/-- The window `(0, 1]`, as a marked integrand, is marked progressively measurable. -/
theorem windowN_prog (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) :
    Probability.MarkedProgressivelyMeasurable ℱ fun (_ : Ω) s (_ : ℝ) => unitWindow s :=
  (markedPredictable_unitWindow ℱ (Measure.dirac (0 : ℝ))).markedProgressivelyMeasurable

/-- The window `(0, 1]`, as a marked integrand, is square integrable on every horizon. -/
theorem windowN_sq (P : Measure Ω) [IsProbabilityMeasure P] :
    ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖(fun (_ : Ω) s (_ : ℝ) => unitWindow s) ω s e‖₊ : ℝ≥0∞) ^ 2
        ∂(Measure.dirac (0 : ℝ)) ∂volume ∂P < ⊤ :=
  BSDEJ.Solves.marked_sq_int_global_of_vanishing (T := 1)
    (fun _ _ _ hs => unitWindow_of_notMem hs)
    (by rw [markedEnergy_unitWindow]; exact ENNReal.one_ne_top)

/-- **The forward equation of the explicit tuple.** For versions `M^W`, `M^N` of the Itô and
compensated integrals of the window `(0, 1]`, adapted with right-continuous paths, the process
`x₀ + a M^W + c M^N` solves the linear forward equation on `[0, 1]` from `x₀` with drift `0`,
diffusion `a 1_{(0, 1]}` and jump integrand `c 1_{(0, 1]}`. -/
theorem linearFSDEJ_window (hWa : ∀ t, Measurable[ℱ t] (MW t))
    (hNa : ∀ t, Measurable[ℱ t] (MN t))
    (hWr : ∀ ω t, Tendsto (fun s => MW s ω) (𝓝[>] t) (𝓝 (MW t ω)))
    (hNr : ∀ ω t, Tendsto (fun s => MN s ω) (𝓝[>] t) (𝓝 (MN t ω)))
    (hWe : ∀ t, MW t =ᵐ[P] Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ
      hℱW (fun s (_ : Ω) (_ : Fin 1) => unitWindow s) window_meas (window_prog ℱ) (window_sq P)
      t)
    (hNe : ∀ t, MN t =ᵐ[P] Poisson.Compensated.stochasticIntegral D.N ℱ hℱN
      (fun (_ : Ω) s (_ : ℝ) => unitWindow s) windowN_meas (windowN_prog ℱ) (windowN_sq P) t)
    (x₀ a c : ℝ) :
    LinearFSDEJ D ℱ hℱW hℱN 1 (fun _ => x₀) (fun _ _ => 0)
      (fun t ω => x₀ + a * MW t ω + c * MN t ω) (fun s _ _ => a * unitWindow s)
      (fun s _ _ => c * unitWindow s) where
  σ_meas _ := measurable_const_mul_unitWindow a
  σ_prog := progressivelyMeasurable_of_predictable_of_vanish (T := 1)
    (Z := fun s (_ : Ω) (_ : Fin 1) => a * unitWindow s)
    (fun _ => predictable_const_mul_unitWindow ℱ a)
    fun _ _ hs => funext fun _ => by simp [unitWindow_of_notMem hs]
  σ_vanish _ _ hs := funext fun _ => by simp [unitWindow_of_notMem hs]
  σ_sq _ := energy_const_mul_unitWindow_ne_top P a
  γ_meas := measurable_marked_const_mul_unitWindow c
  γ_prog := (markedPredictable_const_mul_unitWindow ℱ c).markedProgressivelyMeasurable
  γ_vanish _ _ _ hs := by simp [unitWindow_of_notMem hs]
  γ_sq := markedEnergy_const_mul_unitWindow_ne_top P c
  b_meas := measurable_const
  b_prog := Brownian.Ito.progressivelyMeasurable_zero ℱ
  b_vanish _ _ _ := rfl
  b_sq := by simp [Brownian.Ito.energy]
  ξ₀_sq := memLp_const x₀
  X_adapted t := (measurable_const.add ((hWa t).const_mul a)).add ((hNa t).const_mul c)
  X_rightCont ω t := (tendsto_const_nhds.add ((hWr ω t).const_mul a)).add ((hNr ω t).const_mul c)
  eqn t _ := by
    filter_upwards [hWe t, hNe t,
      multidimStochasticIntegral_const_mul_ae D.W hℱW (Z := fun s (_ : Ω) (_ : Fin 1) =>
        unitWindow s) a window_meas (window_prog ℱ) (window_sq P)
        (fun _ => measurable_const_mul_unitWindow a)
        (progressivelyMeasurable_of_predictable_of_vanish (T := 1)
          (Z := fun s (_ : Ω) (_ : Fin 1) => a * unitWindow s)
          (fun _ => predictable_const_mul_unitWindow ℱ a)
          fun _ _ hs => funext fun _ => by simp [unitWindow_of_notMem hs])
        (BSDEJ.Solves.sq_int_global_of_vanishing (T := 1)
          (fun _ _ hs => funext fun _ => by simp [unitWindow_of_notMem hs])
          fun _ => energy_const_mul_unitWindow_ne_top P a) t,
      compensatedIntegral_const_mul_ae D.N hℱN (φ := fun (_ : Ω) s (_ : ℝ) => unitWindow s) c
        windowN_meas (windowN_prog ℱ) (windowN_sq P) (measurable_marked_const_mul_unitWindow c)
        (markedPredictable_const_mul_unitWindow ℱ c).markedProgressivelyMeasurable
        (BSDEJ.Solves.marked_sq_int_global_of_vanishing (T := 1)
          (fun _ _ _ hs => by simp [unitWindow_of_notMem hs])
          (markedEnergy_const_mul_unitWindow_ne_top P c)) t] with ω h1 h2 h3 h4
    rw [h3, h4, ← h1, ← h2]
    simp

/-- **The backward equation of the explicit tuple.** For versions `M^W`, `M^N` as in
`linearFSDEJ_window`, the process `y₀ + a' M^W + c' M^N` solves, with `Z = a' 1_{(0, 1]}` and
`U = c' 1_{(0, 1]}`, the linear backward equation on `[0, 1]` with terminal value
`y₀ + a' M^W_1 + c' M^N_1` and drift `0`. -/
theorem linearBSDEJ_window (hWa : ∀ t, Measurable[ℱ t] (MW t))
    (hNa : ∀ t, Measurable[ℱ t] (MN t))
    (hWr : ∀ ω t, Tendsto (fun s => MW s ω) (𝓝[>] t) (𝓝 (MW t ω)))
    (hNr : ∀ ω t, Tendsto (fun s => MN s ω) (𝓝[>] t) (𝓝 (MN t ω)))
    (hWe : ∀ t, MW t =ᵐ[P] Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ
      hℱW (fun s (_ : Ω) (_ : Fin 1) => unitWindow s) window_meas (window_prog ℱ) (window_sq P)
      t)
    (hNe : ∀ t, MN t =ᵐ[P] Poisson.Compensated.stochasticIntegral D.N ℱ hℱN
      (fun (_ : Ω) s (_ : ℝ) => unitWindow s) windowN_meas (windowN_prog ℱ) (windowN_sq P) t)
    (y₀ a' c' : ℝ) :
    LinearBSDEJ D ℱ hℱW hℱN 1 (fun ω => y₀ + a' * MW 1 ω + c' * MN 1 ω) (fun _ _ => 0)
      (fun t ω => y₀ + a' * MW t ω + c' * MN t ω) (fun s _ _ => a' * unitWindow s)
      (fun s _ _ => c' * unitWindow s) where
  Z_meas _ := measurable_const_mul_unitWindow a'
  Z_prog := progressivelyMeasurable_of_predictable_of_vanish (T := 1)
    (Z := fun s (_ : Ω) (_ : Fin 1) => a' * unitWindow s)
    (fun _ => predictable_const_mul_unitWindow ℱ a')
    fun _ _ hs => funext fun _ => by simp [unitWindow_of_notMem hs]
  Z_vanish _ _ hs := funext fun _ => by simp [unitWindow_of_notMem hs]
  Z_sq _ := energy_const_mul_unitWindow_ne_top P a'
  U_meas := measurable_marked_const_mul_unitWindow c'
  U_prog := (markedPredictable_const_mul_unitWindow ℱ c').markedProgressivelyMeasurable
  U_vanish _ _ _ hs := by simp [unitWindow_of_notMem hs]
  U_sq := markedEnergy_const_mul_unitWindow_ne_top P c'
  φ_meas := measurable_const
  φ_prog := Brownian.Ito.progressivelyMeasurable_zero ℱ
  φ_vanish _ _ _ := rfl
  φ_sq := by simp [Brownian.Ito.energy]
  ξ_sq := by
    have hW1 : MemLp (MW 1) 2 P := by
      refine MemLp.ae_eq (hWe 1).symm ?_
      unfold Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral
      refine memLp_finsetSum (ι := Fin 1) (μ := P) (p := 2) Finset.univ fun j _ => ?_
      exact (Lp.memLp _).ae_eq
        (Brownian.Ito.stochasticIntegralBrownian_ae_eq _ _ _ _ _ _ _ 1).symm
    have hN1 : MemLp (MN 1) 2 P :=
      MemLp.ae_eq (hNe 1).symm (Poisson.Compensated.stochasticIntegral_memLp D.N ℱ hℱN _ _ _ _ 1)
    exact ((memLp_const y₀).add (hW1.const_mul a')).add (hN1.const_mul c')
  Y_adapted t := (measurable_const.add ((hWa t).const_mul a')).add ((hNa t).const_mul c')
  Y_rightCont ω t :=
    (tendsto_const_nhds.add ((hWr ω t).const_mul a')).add ((hNr ω t).const_mul c')
  eqn t _ := by
    have hZ := fun t => multidimStochasticIntegral_const_mul_ae D.W hℱW
      (Z := fun s (_ : Ω) (_ : Fin 1) => unitWindow s) a' window_meas (window_prog ℱ)
      (window_sq P) (fun _ => measurable_const_mul_unitWindow a')
      (progressivelyMeasurable_of_predictable_of_vanish (T := 1)
        (Z := fun s (_ : Ω) (_ : Fin 1) => a' * unitWindow s)
        (fun _ => predictable_const_mul_unitWindow ℱ a')
        fun _ _ hs => funext fun _ => by simp [unitWindow_of_notMem hs])
      (BSDEJ.Solves.sq_int_global_of_vanishing (T := 1)
        (fun _ _ hs => funext fun _ => by simp [unitWindow_of_notMem hs])
        fun _ => energy_const_mul_unitWindow_ne_top P a') t
    have hU := fun t => compensatedIntegral_const_mul_ae D.N hℱN
      (φ := fun (_ : Ω) s (_ : ℝ) => unitWindow s) c' windowN_meas (windowN_prog ℱ)
      (windowN_sq P) (measurable_marked_const_mul_unitWindow c')
      (markedPredictable_const_mul_unitWindow ℱ c').markedProgressivelyMeasurable
      (BSDEJ.Solves.marked_sq_int_global_of_vanishing (T := 1)
        (fun _ _ _ hs => by simp [unitWindow_of_notMem hs])
        (markedEnergy_const_mul_unitWindow_ne_top P c')) t
    filter_upwards [hWe t, hNe t, hWe 1, hNe 1, hZ t, hZ 1, hU t, hU 1]
      with ω h1 h2 h3 h4 h5 h6 h7 h8
    rw [h5, h6, h7, h8, ← h1, ← h2, ← h3, ← h4]
    simp only [integral_zero]
    ring

end Linear

end Dissertation.Acceptance.A
