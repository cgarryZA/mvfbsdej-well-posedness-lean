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
term of (4.17) nonzero, and one makes the differences of the solutions, of the terminal values
and of all five forcings nonzero.

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
* `Dissertation.Acceptance.A.lem_pert_data_forcing_hypotheses` — `δX ≡ 1`, `δY = M^W + M^N`,
  `δZ = δU = 1_{(0, 1]}`, `δg_T ≡ 1`, and nonzero differences of the five forcings.
-/

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped ENNReal Topology

namespace Dissertation.Acceptance.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence
  Dissertation.WellPosedness.Enlarged Dissertation.WellPosedness.Spec Dissertation.PaperSpec.A
  Dissertation.WellPosedness.Stability Dissertation.WellPosedness.BrownianPoisson Dissertation.Law
  LevyStochCalc

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

/-! ### The explicit solutions -/

section Solution

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (D : LevyStochCalc.Driver.LevyDriver.{0, 0, w} P 1 (Measure.dirac (0 : ℝ)))
  (hind₀ : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P)

/-- **The explicit solution of (4.1).** Let `M^W`, `M^N` be versions of the Itô and compensated
integrals of the window `(0, 1]`, adapted, with every path right-continuous with left limits.
For reals `x₀, a, c, y₀, a', c'`, the tuple `X = x₀ + a M^W + c M^N`, `Y = y₀ + a' M^W + c' M^N`,
`Z = a' 1_{(0, 1]}`, `U = c' 1_{(0, 1]}`, with the representative `γ = −U` of the jump
coefficient, solves the system of Example 5.1(i) at `λ = 1` from the initial datum `x₀`, for a
forcing of the class of the paper, and its forced diffusion and jump integrands are
`a 1_{(0, 1]}` and `c 1_{(0, 1]}`. -/
theorem affineWindow_solution {MW MN : ℝ → Ω → ℝ}
    (hWa : ∀ t, Measurable[enlJoint ⊥ D bot_le t] (MW t))
    (hNa : ∀ t, Measurable[enlJoint ⊥ D bot_le t] (MN t))
    (hWc : ∀ ω t, Tendsto (fun s => MW s ω) (𝓝[>] t) (𝓝 (MW t ω))
      ∧ ∃ L : ℝ, Tendsto (fun s => MW s ω) (𝓝[<] t) (𝓝 L))
    (hNc : ∀ ω t, Tendsto (fun s => MN s ω) (𝓝[>] t) (𝓝 (MN t ω))
      ∧ ∃ L : ℝ, Tendsto (fun s => MN s ω) (𝓝[<] t) (𝓝 L))
    (hWe : ∀ t, MW t =ᵐ[P] Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W
      (enlJoint ⊥ D bot_le) (isBrownianFiltration_enlJoint D bot_le hind₀)
      (fun s (_ : Ω) (_ : Fin 1) => unitWindow s) window_meas (window_prog _) (window_sq P) t)
    (hNe : ∀ t, MN t =ᵐ[P] Poisson.Compensated.stochasticIntegral D.N (enlJoint ⊥ D bot_le)
      (isPoissonFiltration_enlJoint D bot_le hind₀) (fun (_ : Ω) s (_ : ℝ) => unitWindow s)
      windowN_meas (windowN_prog _) (windowN_sq P) t)
    (x₀ a c y₀ a' c' : ℝ) :
    ∃ (qb : Fin 1 → Ω → ℝ → ℝ) (qσ : Fin 1 → ℝ → Ω → Fin 1 → ℝ) (qh : Fin 1 → ℝ → Ω → ℝ → ℝ)
      (qf : Fin 1 → Ω → ℝ → ℝ) (qg : Fin 1 → Ω → ℝ) (X Y : Fin 1 → ℝ → Ω → ℝ)
      (Z : Fin 1 → ℝ → Ω → Fin 1 → ℝ) (U : Fin 1 → ℝ → Ω → ℝ → ℝ)
      (γ : Fin 1 → ℝ → Ω → ℝ → ℝ),
      PredForcing (enlJoint ⊥ D bot_le) P (Measure.dirac (0 : ℝ)) 1 qb qσ qh qf qg
      ∧ PaperSolutionForced D (enlJoint ⊥ D bot_le) (isBrownianFiltration_enlJoint D bot_le hind₀)
          (isPoissonFiltration_enlJoint D bot_le hind₀) 1 1 sysW
          (fun i ω => ((fun _ : Ω => (WithLp.toLp 2 fun _ => x₀ : EuclideanSpace ℝ (Fin 1)))
            ω).ofLp i) qb qσ qh qf qg X Y Z U γ
      ∧ (∀ i ω, ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∃ l : ℝ, Tendsto (fun s => X i s ω) (𝓝[<] t) (𝓝 l))
      ∧ (∀ k ω, ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∃ l : ℝ, Tendsto (fun s => Y k s ω) (𝓝[<] t) (𝓝 l))
      ∧ (∀ i t ω, X i t ω = x₀ + a * MW t ω + c * MN t ω)
      ∧ (∀ k t ω, Y k t ω = y₀ + a' * MW t ω + c' * MN t ω)
      ∧ (∀ k s ω j, Z k s ω j = a' * unitWindow s)
      ∧ (∀ k s ω e, U k s ω e = c' * unitWindow s)
      ∧ (∀ i s ω j, 1 * diffusionProc P 1 sysW X Y Z U i s ω j + qσ i s ω j = a * unitWindow s)
      ∧ (∀ i s ω e, 1 * jumpProc 1 γ i s ω e + qh i s ω e = c * unitWindow s)
      ∧ (∀ i ω s, qb i ω s = -(1 * driftProc P 1 sysW X Y Z U i ω s))
      ∧ (∀ i s ω e, qh i s ω e = (c + c') * unitWindow s)
      ∧ (∀ k ω s, qf k ω s = -(1 * driverProc P 1 sysW X Y Z U k ω s))
      ∧ ∀ k ω, qg k ω = y₀ + a' * MW 1 ω + c' * MN 1 ω - 1 * terminalVal P 1 sysW X k ω := by
  set ℱ := enlJoint ⊥ D bot_le with hℱdef
  have hW := isBrownianFiltration_enlJoint D bot_le hind₀
  have hN := isPoissonFiltration_enlJoint D bot_le hind₀
  have hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s :=
    fun _ hs h0 => measurableSet_enlJoint_of_null D bot_le hs h0
  obtain ⟨hJ, -, -, -, -⟩ :=
    affine_assumptions (ν := Measure.dirac (0 : ℝ)) (d := 1) (ℱ := ℱ) (P := P) (T := 1)
      (σc := 0) (hc := 0) one_pos one_pos (0 : EuclideanSpace ℝ (Fin 1))
  have hfwd := linearFSDEJ_window (hℱW := hW) (hℱN := hN) hWa hNa (fun ω t => (hWc ω t).1)
    (fun ω t => (hNc ω t).1) hWe hNe x₀ a c
  have hbwd := linearBSDEJ_window (hℱW := hW) (hℱN := hN) hWa hNa (fun ω t => (hWc ω t).1)
    (fun ω t => (hNc ω t).1) hWe hNe y₀ a' c'
  set X : Fin 1 → ℝ → Ω → ℝ := fun _ t ω => x₀ + a * MW t ω + c * MN t ω with hX
  set Y : Fin 1 → ℝ → Ω → ℝ := fun _ t ω => y₀ + a' * MW t ω + c' * MN t ω with hY
  set Z : Fin 1 → ℝ → Ω → Fin 1 → ℝ := fun _ s _ _ => a' * unitWindow s with hZ
  set U : Fin 1 → ℝ → Ω → ℝ → ℝ := fun _ s _ _ => c' * unitWindow s with hU
  set γ : Fin 1 → ℝ → Ω → ℝ → ℝ := fun _ s _ _ => -(c' * unitWindow s) with hγ
  -- the forcing of the `λ = 0` system
  have hq₀ : Forcing ℱ P (Measure.dirac (0 : ℝ)) 1 (fun (_ : Fin 1) (_ : Ω) (_ : ℝ) => (0 : ℝ))
      (fun (_ : Fin 1) s (_ : Ω) (_ : Fin 1) => a * unitWindow s)
      (fun (_ : Fin 1) s (_ : Ω) (_ : ℝ) => c * unitWindow s)
      (fun (_ : Fin 1) (_ : Ω) (_ : ℝ) => (0 : ℝ))
      (fun (_ : Fin 1) ω => y₀ + a' * MW 1 ω + c' * MN 1 ω) :=
    { qb_meas := fun _ => measurable_const
      qb_prog := fun _ => Brownian.Ito.progressivelyMeasurable_zero ℱ
      qb_vanish := fun _ _ _ _ => rfl
      qb_sq := fun _ => by simp [Brownian.Ito.energy]
      qσ_meas := fun _ => hfwd.σ_meas
      qσ_prog := fun _ => hfwd.σ_prog
      qσ_vanish := fun _ => hfwd.σ_vanish
      qσ_sq := fun _ => hfwd.σ_sq
      qh_meas := fun _ => hfwd.γ_meas
      qh_prog := fun _ => hfwd.γ_prog
      qh_vanish := fun _ => hfwd.γ_vanish
      qh_sq := fun _ => hfwd.γ_sq
      qf_meas := fun _ => measurable_const
      qf_prog := fun _ => Brownian.Ito.progressivelyMeasurable_zero ℱ
      qf_vanish := fun _ _ _ _ => rfl
      qf_sq := fun _ => by simp [Brownian.Ito.energy]
      qg_meas := fun _ => (hbwd.Y_adapted 1).stronglyMeasurable
      qg_sq := fun _ => hbwd.ξ_sq }
  -- `γ = −U` represents `h = −u` along the tuple
  have hrep : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), ∀ᵐ ω ∂P,
      (fun e => (WithLp.toLp 2 fun i => γ i s ω e : EuclideanSpace ℝ (Fin 1)))
        =ᵐ[Measure.dirac (0 : ℝ)] (sysW).h s (tupleAt (Measure.dirac (0 : ℝ)) X Y Z U s ω)
          (lawP2 P (tupleAt (Measure.dirac (0 : ℝ)) X Y Z U s)) := by
    refine ae_of_all _ fun s => ae_of_all _ fun ω => ?_
    have hmem : MemLp (fun e : ℝ => (WithLp.toLp 2 ((fun e k => U k s ω e) e) :
        EuclideanSpace ℝ (Fin 1))) 2 (Measure.dirac (0 : ℝ)) :=
      memLp_const (WithLp.toLp 2 fun _ : Fin 1 => c' * unitWindow s)
    simp only [affineCoeffs, tupleAt, one_smul]
    rw [uLift_of_memLp hmem]
    filter_upwards [Lp.coeFn_sub (0 : Lp (EuclideanSpace ℝ (Fin 1)) 2 (Measure.dirac (0 : ℝ)))
      (hmem.toLp _), Lp.coeFn_zero (EuclideanSpace ℝ (Fin 1)) 2 (Measure.dirac (0 : ℝ)),
      hmem.coeFn_toLp] with e h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3, Pi.zero_apply, zero_sub]
    ext i
    simp [hγ, hU]
  have h0 : SolvesForced D ℱ hW hN 1 0 sysW
      (fun i ω => ((fun _ : Ω => (WithLp.toLp 2 fun _ => x₀ : EuclideanSpace ℝ (Fin 1)))
        ω).ofLp i)
      (fun (_ : Fin 1) (_ : Ω) (_ : ℝ) => (0 : ℝ))
      (fun (_ : Fin 1) s (_ : Ω) (_ : Fin 1) => a * unitWindow s)
      (fun (_ : Fin 1) s (_ : Ω) (_ : ℝ) => c * unitWindow s)
      (fun (_ : Fin 1) (_ : Ω) (_ : ℝ) => (0 : ℝ))
      (fun (_ : Fin 1) ω => y₀ + a' * MW 1 ω + c' * MN 1 ω) X Y Z U γ :=
    { forcing := hq₀
      jump_rep := hrep
      fwd := fun _ => by
        simp only [zero_mul, zero_add]
        exact hfwd
      bwd := fun _ => by
        simp only [zero_mul, zero_add]
        exact hbwd }
  -- the coefficient processes along the tuple, with the jump component `γ`
  have hjp : ∀ i s ω e, jumpProc 1 γ i s ω e = -c' * unitWindow s := by
    intro i s ω e
    by_cases hs : s ∈ Set.Icc (0 : ℝ) 1
    · simp [jumpProc, hs, hγ]
    · simp [jumpProc, hs, unitWindow_of_notMem hs]
  have hjpf : jumpProc 1 γ = fun (_ : Fin 1) s (_ : Ω) (_ : ℝ) => -c' * unitWindow s :=
    funext fun i => funext fun s => funext fun ω => funext fun e => hjp i s ω e
  obtain ⟨γ', -, hΨ'⟩ := h0.exists_forcing_coeff (crossWitnessEnl D bot_le hind₀)
    (hF0_enlJoint D bot_le) hnull one_pos (hJ.coeffRegular ℱ P) (coeffOrigin_affine 1)
    (diagonalLipschitz_affine (L := 1) zero_le_one zero_le_one (by norm_num))
    (terminalLipschitz_affine le_rfl) (fun _ => measurable_id)
  have hΨ : Forcing ℱ P (Measure.dirac (0 : ℝ)) 1 (driftProc P 1 sysW X Y Z U)
      (diffusionProc P 1 sysW X Y Z U) (jumpProc 1 γ) (driverProc P 1 sysW X Y Z U)
      (terminalVal P 1 sysW X) := by
    rw [hjpf]
    exact { hΨ' with
      qh_meas := fun _ => measurable_marked_const_mul_unitWindow (-c')
      qh_prog := fun _ =>
        (markedPredictable_const_mul_unitWindow ℱ (-c')).markedProgressivelyMeasurable
      qh_vanish := fun _ _ s _ hs => by simp [unitWindow_of_notMem hs]
      qh_sq := fun _ => markedEnergy_const_mul_unitWindow_ne_top P (-c') }
  have h1 := h0.of_zero_sub_coeff hΨ 1
  have hpred : PredForcing ℱ P (Measure.dirac (0 : ℝ)) 1
      (fun i ω s => (fun (_ : Fin 1) (_ : Ω) (_ : ℝ) => (0 : ℝ)) i ω s
        - 1 * driftProc P 1 sysW X Y Z U i ω s)
      (fun i s ω j => (fun (_ : Fin 1) s (_ : Ω) (_ : Fin 1) => a * unitWindow s) i s ω j
        - 1 * diffusionProc P 1 sysW X Y Z U i s ω j)
      (fun i s ω e => (fun (_ : Fin 1) s (_ : Ω) (_ : ℝ) => c * unitWindow s) i s ω e
        - 1 * jumpProc 1 γ i s ω e)
      (fun k ω s => (fun (_ : Fin 1) (_ : Ω) (_ : ℝ) => (0 : ℝ)) k ω s
        - 1 * driverProc P 1 sysW X Y Z U k ω s)
      (fun k ω => (fun (_ : Fin 1) ω => y₀ + a' * MW 1 ω + c' * MN 1 ω) k ω
        - 1 * terminalVal P 1 sysW X k ω) := by
    refine { toForcing := h1.forcing, qh_pred := fun i => ?_ }
    have e : (fun ω s e => (fun (_ : Fin 1) s (_ : Ω) (_ : ℝ) => c * unitWindow s) i s ω e
        - 1 * jumpProc 1 γ i s ω e) = fun (_ : Ω) s (_ : ℝ) => (c + c') * unitWindow s := by
      funext ω s e
      rw [hjp]
      ring
    rw [e]
    exact markedPredictable_const_mul_unitWindow ℱ (c + c')
  have hpaper := h1.paperSolutionForced (fun _ _ => predictable_const_mul_unitWindow ℱ a')
    (fun _ => markedPredictable_const_mul_unitWindow ℱ c') (crossWitnessEnl D bot_le hind₀)
    (hF0_enlJoint D bot_le) hnull one_pos
  refine ⟨_, _, _, _, _, X, Y, Z, U, γ, hpred, hpaper, fun _ ω t _ => ?_, fun _ ω t _ => ?_,
    fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl,
    fun _ _ _ _ => by ring, fun _ _ _ _ => by ring, fun _ _ _ => zero_sub _,
    fun i s ω e => ?_, fun _ _ _ => zero_sub _, fun _ _ => rfl⟩
  · obtain ⟨L₁, h₁⟩ := (hWc ω t).2
    obtain ⟨L₂, h₂⟩ := (hNc ω t).2
    exact ⟨x₀ + a * L₁ + c * L₂, (tendsto_const_nhds.add (h₁.const_mul a)).add (h₂.const_mul c)⟩
  · obtain ⟨L₁, h₁⟩ := (hWc ω t).2
    obtain ⟨L₂, h₂⟩ := (hNc ω t).2
    exact ⟨y₀ + a' * L₁ + c' * L₂,
      (tendsto_const_nhds.add (h₁.const_mul a')).add (h₂.const_mul c')⟩
  · change c * unitWindow s - 1 * jumpProc 1 γ i s ω e = (c + c') * unitWindow s
    rw [hjp]
    ring

end Solution

/-! ### Pairs of explicit solutions -/

section Coefficients

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The drift process of `sysW` along a tuple is `−Y`, cut to `[0, 1]`. -/
theorem driftProc_sysW (X Y : Fin 1 → ℝ → Ω → ℝ) (Z : Fin 1 → ℝ → Ω → Fin 1 → ℝ)
    (U : Fin 1 → ℝ → Ω → ℝ → ℝ) (i : Fin 1) (ω : Ω) (s : ℝ) :
    driftProc P 1 sysW X Y Z U i ω s = (Set.Icc (0 : ℝ) 1).indicator (fun s => -Y i s ω) s := by
  by_cases hs : s ∈ Set.Icc (0 : ℝ) 1
  · simp [driftProc, Set.indicator_of_mem hs, affineCoeffs, tupleAt]
  · simp [driftProc, Set.indicator_of_notMem hs]

/-- The diffusion process of `sysW` along a tuple is `−Z`, cut to `[0, 1]`. -/
theorem diffusionProc_sysW (X Y : Fin 1 → ℝ → Ω → ℝ) (Z : Fin 1 → ℝ → Ω → Fin 1 → ℝ)
    (U : Fin 1 → ℝ → Ω → ℝ → ℝ) (i : Fin 1) (s : ℝ) (ω : Ω) (j : Fin 1) :
    diffusionProc P 1 sysW X Y Z U i s ω j
      = (Set.Icc (0 : ℝ) 1).indicator (fun s => -Z i s ω j) s := by
  by_cases hs : s ∈ Set.Icc (0 : ℝ) 1
  · simp [diffusionProc, Set.indicator_of_mem hs, affineCoeffs, tupleAt]
  · simp [diffusionProc, Set.indicator_of_notMem hs]

/-- The driver process of `sysW` along a tuple is `X`, cut to `[0, 1]`. -/
theorem driverProc_sysW (X Y : Fin 1 → ℝ → Ω → ℝ) (Z : Fin 1 → ℝ → Ω → Fin 1 → ℝ)
    (U : Fin 1 → ℝ → Ω → ℝ → ℝ) (k : Fin 1) (ω : Ω) (s : ℝ) :
    driverProc P 1 sysW X Y Z U k ω s = (Set.Icc (0 : ℝ) 1).indicator (fun s => X k s ω) s := by
  by_cases hs : s ∈ Set.Icc (0 : ℝ) 1
  · simp [driverProc, Set.indicator_of_mem hs, affineCoeffs, tupleAt]
  · simp [driverProc, Set.indicator_of_notMem hs]

/-- The terminal value of `sysW` is `X_1`. -/
theorem terminalVal_sysW (X : Fin 1 → ℝ → Ω → ℝ) (k : Fin 1) (ω : Ω) :
    terminalVal P 1 sysW X k ω = X k 1 ω := by
  simp [terminalVal, affineCoeffs]

end Coefficients

/-- **A pair of explicit solutions of (4.1).** Over a probability space carrying a Lévy driver
with `d = 1` and `ν = δ₀` on `ℝ`, with `𝒢₀ = ⊥`, `n = m = 1` and `T = 1`, the system of Example
5.1(i) with `β₁ = β₂ = 1`, `σ_c = h_c = 0` satisfies (2.3), Assumption 2.3 with `L = 1` and
Assumption 2.5 with `G = 1`, `α = β₁ = β₂ = 1`; for reals `x₀, a, c, y₀, a', c'`, the explicit
solutions at `λ = 1` of `affineWindow_solution` at these parameters and at the parameters `0`
are two solutions of (4.1) in `𝕊` for forcings of the class of the paper, from the initial data
`x₀` and `0`, whose difference lies in `𝕊` and is
`δX = x₀ + a M^W + c M^N`, `δY = y₀ + a' M^W + c' M^N`, `δZ = a' 1_{(0, 1]}`,
`δU = c' 1_{(0, 1]}`, for versions `M^W`, `M^N` of `∫ 1_{(0, 1]} dW`, `∫∫ 1_{(0, 1]} dÑ`; the
difference of the forced diffusion integrands is `a 1_{(0, 1]}`, and that of the forced jump
integrands, with the jump coefficient at the predictable tuples, is `c 1_{(0, 1]}` almost
everywhere on `Ω × [0, 1] × ℝ`. -/
theorem affineWindow_pair (x₀ a c y₀ a' c' : ℝ) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyStochCalc.Driver.LevyDriver.{0, 0, w} P 1 (Measure.dirac (0 : ℝ)))
      (hind₀ : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P) (MW MN : ℝ → Ω → ℝ)
      (qb₁ qb₂ : Fin 1 → Ω → ℝ → ℝ) (qσ₁ qσ₂ : Fin 1 → ℝ → Ω → Fin 1 → ℝ)
      (qh₁ qh₂ : Fin 1 → ℝ → Ω → ℝ → ℝ) (qf₁ qf₂ : Fin 1 → Ω → ℝ → ℝ) (qg₁ qg₂ : Fin 1 → Ω → ℝ)
      (X₁ X₂ Y₁ Y₂ : Fin 1 → ℝ → Ω → ℝ) (Z₁ Z₂ : Fin 1 → ℝ → Ω → Fin 1 → ℝ)
      (U₁ U₂ : Fin 1 → ℝ → Ω → ℝ → ℝ),
      JointBorel 1 sysW ∧ Assumption23 (enlJoint ⊥ D bot_le) P 1 1 sysW
      ∧ (1 : Matrix (Fin 1) (Fin 1) ℝ).rank = min 1 1
      ∧ Assumption25 (enlJoint ⊥ D bot_le) P 1 (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 1 1 sysW
      ∧ PredForcing (enlJoint ⊥ D bot_le) P (Measure.dirac (0 : ℝ)) 1 qb₁ qσ₁ qh₁ qf₁ qg₁
      ∧ PredForcing (enlJoint ⊥ D bot_le) P (Measure.dirac (0 : ℝ)) 1 qb₂ qσ₂ qh₂ qf₂ qg₂
      ∧ ForcedSolution D bot_le hind₀ 1 1 sysW
          (fun _ => (WithLp.toLp 2 fun _ => x₀ : EuclideanSpace ℝ (Fin 1)))
          qb₁ qσ₁ qh₁ qf₁ qg₁ X₁ Y₁ Z₁ U₁
      ∧ ForcedSolution D bot_le hind₀ 1 1 sysW
          (fun _ => (WithLp.toLp 2 fun _ => 0 : EuclideanSpace ℝ (Fin 1)))
          qb₂ qσ₂ qh₂ qf₂ qg₂ X₂ Y₂ Z₂ U₂
      ∧ supSize P (Measure.dirac (0 : ℝ)) 1 (fun i t ω => X₁ i t ω - X₂ i t ω)
          (fun k t ω => Y₁ k t ω - Y₂ k t ω) (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j)
          (fun k t ω e => U₁ k t ω e - U₂ k t ω e) < ⊤
      ∧ (∀ i t ω, X₁ i t ω - X₂ i t ω = x₀ + a * MW t ω + c * MN t ω)
      ∧ (∀ k t ω, Y₁ k t ω - Y₂ k t ω = y₀ + a' * MW t ω + c' * MN t ω)
      ∧ (∀ k s ω j, Z₁ k s ω j - Z₂ k s ω j = a' * unitWindow s)
      ∧ (∀ k s ω e, U₁ k s ω e - U₂ k s ω e = c' * unitWindow s)
      ∧ (∀ i s ω j, 1 * (diffusionProc P 1 sysW X₁ Y₁ Z₁ U₁ i s ω j
          - diffusionProc P 1 sysW X₂ Y₂ Z₂ U₂ i s ω j) + (qσ₁ i s ω j - qσ₂ i s ω j)
            = a * unitWindow s)
      ∧ (∀ᵐ q ∂(Poisson.Compensated.markedEnergyMeasure P (Measure.dirac (0 : ℝ)) 1), ∀ i,
          1 * (jumpProc 1 (coeffJump P 1 sysW (leftLimProc X₁) (leftLimProc Y₁) Z₁ U₁) i
              q.2.1 q.1 q.2.2
            - jumpProc 1 (coeffJump P 1 sysW (leftLimProc X₂) (leftLimProc Y₂) Z₂ U₂) i
              q.2.1 q.1 q.2.2) + (qh₁ i q.2.1 q.1 q.2.2 - qh₂ i q.2.1 q.1 q.2.2)
            = c * unitWindow q.2.1)
      ∧ (∀ t, MW t =ᵐ[P] Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W
          (enlJoint ⊥ D bot_le) (isBrownianFiltration_enlJoint D bot_le hind₀)
          (fun s (_ : Ω) (_ : Fin 1) => unitWindow s) window_meas (window_prog _) (window_sq P) t)
      ∧ (∀ t, MN t =ᵐ[P] Poisson.Compensated.stochasticIntegral D.N (enlJoint ⊥ D bot_le)
          (isPoissonFiltration_enlJoint D bot_le hind₀) (fun (_ : Ω) s (_ : ℝ) => unitWindow s)
          windowN_meas (windowN_prog _) (windowN_sq P) t)
      ∧ (∀ i ω s, qb₁ i ω s - qb₂ i ω s
          = (Set.Icc (0 : ℝ) 1).indicator (fun s => y₀ + a' * MW s ω + c' * MN s ω) s)
      ∧ (∀ i s ω j, qσ₁ i s ω j - qσ₂ i s ω j = (a + a') * unitWindow s)
      ∧ (∀ i s ω e, qh₁ i s ω e - qh₂ i s ω e = (c + c') * unitWindow s)
      ∧ (∀ k ω s, qf₁ k ω s - qf₂ k ω s
          = -(Set.Icc (0 : ℝ) 1).indicator (fun s => x₀ + a * MW s ω + c * MN s ω) s)
      ∧ ∀ k ω, qg₁ k ω - qg₂ k ω
          = (y₀ + a' * MW 1 ω + c' * MN 1 ω) - (x₀ + a * MW 1 ω + c * MN 1 ω) := by
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ := LevyStochCalc.Driver.LevyDriver.exists 1 ℝ (Measure.dirac (0 : ℝ))
  have hind₀ : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P := indep_bot_left _
  set ℱ := enlJoint ⊥ D bot_le with hℱdef
  have hW := isBrownianFiltration_enlJoint D bot_le hind₀
  have hN := isPoissonFiltration_enlJoint D bot_le hind₀
  have hrc : ℱ.rightCont = ℱ := MeasureTheory.Filtration.IsRightContinuous.eq
  have hF0 := hF0_enlJoint D (bot_le : (⊥ : MeasurableSpace Ω) ≤ _)
  have hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s :=
    fun _ hs h0 => measurableSet_enlJoint_of_null D bot_le hs h0
  obtain ⟨MW, hWa, -, hWe, hWc, -⟩ :=
    BSDEJ.Solves.exists_cadlag_vectorIntegral_supBound D.W ℱ hW
      (fun s (_ : Ω) (_ : Fin 1) => unitWindow s) window_meas (window_prog ℱ) (window_sq P) hF0
      hnull 1 zero_le_one
  obtain ⟨MN, hNa, -, hNe, hNc, -⟩ :=
    BSDEJ.Solves.exists_cadlag_compensatedIntegral_supBound D.N ℱ hN
      (fun (_ : Ω) s (_ : ℝ) => unitWindow s) windowN_meas (windowN_prog ℱ) (windowN_sq P) hF0
      hnull 1 zero_le_one
  rw [hrc] at hWa hNa
  obtain ⟨hJ, h22, h23, hG, h25⟩ :=
    affine_assumptions (ν := Measure.dirac (0 : ℝ)) (d := 1) (ℱ := ℱ) (P := P) (T := 1)
      (σc := 0) (hc := 0) one_pos one_pos (0 : EuclideanSpace ℝ (Fin 1))
  have e : max (max (1 : ℝ) 1) 1 = 1 := by norm_num
  rw [e] at h23
  obtain ⟨qb₁, qσ₁, qh₁, qf₁, qg₁, X₁, Y₁, Z₁, U₁, γ₁, hq₁, hp₁, hXl₁, hYl₁, hX₁, hY₁, hZ₁, hU₁,
    hσ₁, hh₁, hb₁, hqh₁, hf₁, hg₁⟩ :=
    affineWindow_solution D hind₀ hWa hNa hWc hNc hWe hNe x₀ a c y₀ a' c'
  obtain ⟨qb₂, qσ₂, qh₂, qf₂, qg₂, X₂, Y₂, Z₂, U₂, γ₂, hq₂, hp₂, hXl₂, hYl₂, hX₂, hY₂, hZ₂, hU₂,
    hσ₂, hh₂, hb₂, hqh₂, hf₂, hg₂⟩ :=
    affineWindow_solution D hind₀ hWa hNa hWc hNc hWe hNe 0 0 0 0 0 0
  have hs₁ := forcedSolution_of_paperSolutionForced (hind₀ := hind₀)
    (ξ₀ := fun _ => (WithLp.toLp 2 fun _ => x₀ : EuclideanSpace ℝ (Fin 1))) zero_le_one hp₁
    hXl₁ hYl₁
  have hs₂ := forcedSolution_of_paperSolutionForced (hind₀ := hind₀)
    (ξ₀ := fun _ => (WithLp.toLp 2 fun _ => 0 : EuclideanSpace ℝ (Fin 1))) zero_le_one hp₂
    hXl₂ hYl₂
  have hj := (paperWeakSolutionForcedInt_of_paperSolutionForced (hind₀ := hind₀) zero_le_one
    hp₁).ae_forcedJump_sub_leftLim_eq
    (paperWeakSolutionForcedInt_of_paperSolutionForced (hind₀ := hind₀) zero_le_one hp₂)
    zero_le_one (jointBorel_iff.mp hJ).1.toCoeffBorel hXl₁ hYl₁ hXl₂ hYl₂
  refine ⟨Ω, inferInstance, P, inferInstance, D, hind₀, MW, MN, qb₁, qb₂, qσ₁, qσ₂, qh₁, qh₂,
    qf₁, qf₂, qg₁, qg₂, X₁, X₂, Y₁, Y₂, Z₁, Z₂, U₁, U₂, hJ, h23, hG, h25, hq₁, hq₂, hs₁, hs₂,
    ForcedSolution.supSize_sub_lt_top one_pos hJ h22.origin h23 hJ h22.origin h23 hs₁ hs₂,
    fun i t ω => ?_, fun k t ω => ?_, fun k s ω j => ?_, fun k s ω e => ?_, fun i s ω j => ?_,
    ?_, hWe, hNe, fun i ω s => ?_, fun i s ω j => ?_, fun i s ω e => ?_, fun k ω s => ?_,
    fun k ω => ?_⟩
  · rw [hX₁, hX₂]
    ring
  · rw [hY₁, hY₂]
    ring
  · rw [hZ₁, hZ₂]
    ring
  · rw [hU₁, hU₂]
    ring
  · linear_combination hσ₁ i s ω j - hσ₂ i s ω j
  · filter_upwards [hj] with q hq i
    rw [hq i]
    linear_combination hh₁ i q.2.1 q.1 q.2.2 - hh₂ i q.2.1 q.1 q.2.2
  · rw [hb₁, hb₂, driftProc_sysW, driftProc_sysW]
    by_cases hs : s ∈ Set.Icc (0 : ℝ) 1
    · simp only [Set.indicator_of_mem hs, hY₁, hY₂]
      ring
    · simp only [Set.indicator_of_notMem hs]
      ring
  · have h1 := hσ₁ i s ω j
    have h2 := hσ₂ i s ω j
    rw [diffusionProc_sysW] at h1 h2
    by_cases hs : s ∈ Set.Icc (0 : ℝ) 1
    · simp only [Set.indicator_of_mem hs, hZ₁, hZ₂] at h1 h2
      linear_combination h1 - h2
    · simp only [Set.indicator_of_notMem hs, unitWindow_of_notMem hs] at h1 h2 ⊢
      linear_combination h1 - h2
  · rw [hqh₁, hqh₂]
    ring
  · rw [hf₁, hf₂, driverProc_sysW, driverProc_sysW]
    by_cases hs : s ∈ Set.Icc (0 : ℝ) 1
    · simp only [Set.indicator_of_mem hs, hX₁, hX₂]
      ring
    · simp only [Set.indicator_of_notMem hs]
      ring
  · rw [hg₁, hg₂, terminalVal_sysW, terminalVal_sysW, hX₁, hX₂]
    ring

/-! ### Four instances of Lemma 4.3 -/

/-- The left limit of a process that is constant in time is that constant. -/
theorem leftLimProc_of_const {Ω : Type*} {X : Fin 1 → ℝ → Ω → ℝ} {r : ℝ}
    (h : ∀ i t ω, X i t ω = r) (i : Fin 1) (s : ℝ) (ω : Ω) : leftLimProc X i s ω = r := by
  have e : (fun t => X i t ω) = fun _ => r := funext fun t => h i t ω
  simp only [leftLimProc, e]
  exact leftLim_eq_of_tendsto tendsto_const_nhds

/-- `1_{(0, 1]}(s)` is the indicator of `s ∈ (0, 1]`. -/
theorem ite_Ioc_eq_unitWindow (s : ℝ) :
    (if s ∈ Set.Ioc (0 : ℝ) 1 then (1 : ℝ) else 0) = unitWindow s := by
  by_cases hs : s ∈ Set.Ioc (0 : ℝ) 1 <;> simp [hs, unitWindow]

/-- `1_{(0, 1]}² = 1_{(0, 1]}`. -/
theorem unitWindow_mul_self (s : ℝ) : unitWindow s * unitWindow s = unitWindow s := by
  by_cases hs : s ∈ Set.Ioc (0 : ℝ) 1 <;> simp [hs, unitWindow]

/-- **The hypotheses of Lemma 4.3 hold with the integrands of the first and third bounds of
(4.18) nonzero.** At the instance of `affineWindow_pair` with `x₀ = 1`, `a = c = y₀ = 0`,
`a' = c' = 1`: two solutions of (4.1) at `λ̲ = λ = 1` for forcings of the class of the paper, from
the initial data `1` and `0`, whose difference is `δX ≡ 1`, `δY = M^W + M^N`,
`δZ = δU = 1_{(0, 1]}`. The integrands `⟨G δX_{s−}, δZ_s ·⟩` and `⟨G δX_{s−}, δU_s(e)⟩`, `G = 1`,
are `1_{(0, 1]}`, of energy `1`. -/
theorem lem_pert_backward_window_hypotheses :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyStochCalc.Driver.LevyDriver.{0, 0, w} P 1 (Measure.dirac (0 : ℝ)))
      (hind₀ : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P)
      (ξ₁ ξ₂ : Ω → EuclideanSpace ℝ (Fin 1))
      (qb₁ qb₂ : Fin 1 → Ω → ℝ → ℝ) (qσ₁ qσ₂ : Fin 1 → ℝ → Ω → Fin 1 → ℝ)
      (qh₁ qh₂ : Fin 1 → ℝ → Ω → ℝ → ℝ) (qf₁ qf₂ : Fin 1 → Ω → ℝ → ℝ) (qg₁ qg₂ : Fin 1 → Ω → ℝ)
      (X₁ X₂ Y₁ Y₂ : Fin 1 → ℝ → Ω → ℝ) (Z₁ Z₂ : Fin 1 → ℝ → Ω → Fin 1 → ℝ)
      (U₁ U₂ : Fin 1 → ℝ → Ω → ℝ → ℝ),
      JointBorel 1 sysW ∧ Assumption23 (enlJoint ⊥ D bot_le) P 1 1 sysW
      ∧ (1 : Matrix (Fin 1) (Fin 1) ℝ).rank = min 1 1
      ∧ Assumption25 (enlJoint ⊥ D bot_le) P 1 (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 1 1 sysW
      ∧ Measurable[enlJoint ⊥ D bot_le 0] ξ₁ ∧ Measurable[enlJoint ⊥ D bot_le 0] ξ₂
      ∧ PredForcing (enlJoint ⊥ D bot_le) P (Measure.dirac (0 : ℝ)) 1 qb₁ qσ₁ qh₁ qf₁ qg₁
      ∧ PredForcing (enlJoint ⊥ D bot_le) P (Measure.dirac (0 : ℝ)) 1 qb₂ qσ₂ qh₂ qf₂ qg₂
      ∧ WeakForcedSolution D bot_le hind₀ 1 1 sysW ξ₁ qb₁ qσ₁ qh₁ qf₁ qg₁ X₁ Y₁ Z₁ U₁
      ∧ WeakForcedSolution D bot_le hind₀ 1 1 sysW ξ₂ qb₂ qσ₂ qh₂ qf₂ qg₂ X₂ Y₂ Z₂ U₂
      ∧ supSize P (Measure.dirac (0 : ℝ)) 1 (fun i t ω => X₁ i t ω - X₂ i t ω)
          (fun k t ω => Y₁ k t ω - Y₂ k t ω) (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j)
          (fun k t ω e => U₁ k t ω e - U₂ k t ω e) < ⊤
      ∧ Brownian.Ito.energy P 1 (fun ω s => ∑ k, ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ fun i =>
          if s ∈ Set.Ioc (0 : ℝ) 1 then leftLimProc (fun a t ω => X₁ a t ω - X₂ a t ω) i s ω
          else 0) k * (Z₁ k s ω 0 - Z₂ k s ω 0)) = 1
      ∧ Poisson.Compensated.markedEnergy P (Measure.dirac (0 : ℝ)) 1 (fun ω s e => ∑ k,
          ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ fun i => if s ∈ Set.Ioc (0 : ℝ) 1 then
            leftLimProc (fun a t ω => X₁ a t ω - X₂ a t ω) i s ω else 0) k
          * (U₁ k s ω e - U₂ k s ω e)) = 1 := by
  obtain ⟨Ω, _, P, _, D, hind₀, MW, MN, qb₁, qb₂, qσ₁, qσ₂, qh₁, qh₂, qf₁, qf₂, qg₁, qg₂, X₁, X₂,
    Y₁, Y₂, Z₁, Z₂, U₁, U₂, hJ, h23, hG, h25, hq₁, hq₂, hs₁, hs₂, hsup, hX, hY, hZ, hU, hσ, hh,
    -⟩ :=
    affineWindow_pair.{w} 1 0 0 0 1 1
  refine ⟨Ω, inferInstance, P, inferInstance, D, hind₀, _, _, qb₁, qb₂, qσ₁, qσ₂, qh₁, qh₂, qf₁,
    qf₂, qg₁, qg₂, X₁, X₂, Y₁, Y₂, Z₁, Z₂, U₁, U₂, hJ, h23, hG, h25, measurable_const,
    measurable_const, hq₁, hq₂, hs₁.1, hs₂.1, hsup, ?_⟩
  have hl := leftLimProc_of_const (X := fun a t ω => X₁ a t ω - X₂ a t ω) (r := 1)
    fun i t ω => by rw [hX i t ω]; ring
  refine ⟨?_, ?_⟩
  · have e : (fun ω s => ∑ k, ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ fun i =>
        if s ∈ Set.Ioc (0 : ℝ) 1 then leftLimProc (fun a t ω => X₁ a t ω - X₂ a t ω) i s ω
        else 0) k * (Z₁ k s ω 0 - Z₂ k s ω 0)) = fun (_ : Ω) s => unitWindow s := by
      funext ω s
      simp only [Matrix.one_mulVec, Fin.sum_univ_one, hl, hZ, ite_Ioc_eq_unitWindow]
      rw [one_mul, unitWindow_mul_self]
    rw [e, energy_unitWindow]
  · have e : (fun ω s e => ∑ k, ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ fun i =>
        if s ∈ Set.Ioc (0 : ℝ) 1 then leftLimProc (fun a t ω => X₁ a t ω - X₂ a t ω) i s ω
        else 0) k * (U₁ k s ω e - U₂ k s ω e)) = fun (_ : Ω) s (_ : ℝ) => unitWindow s := by
      funext ω s e
      simp only [Matrix.one_mulVec, Fin.sum_univ_one, hl, hU, ite_Ioc_eq_unitWindow]
      rw [one_mul, unitWindow_mul_self]
    rw [e, markedEnergy_unitWindow]

/-- **The hypotheses of Lemma 4.3 hold with the integrands of the second and fourth bounds of
(4.18) nonzero.** At the instance of `affineWindow_pair` with `a = c = y₀ = 1`,
`x₀ = a' = c' = 0`: two solutions of (4.1) at `λ̲ = λ = 1` for forcings of the class of the paper,
from the initial datum `0`, whose difference is `δX = M^W + M^N`, `δY ≡ 1`, `δZ = 0`, `δU = 0`,
with forced diffusion difference `λ δσ + q^σ = 1_{(0, 1]}` and forced jump difference
`λ δh + q^h = 1_{(0, 1]}` almost everywhere. The integrand `⟨G (λ δσ_s + q^σ_s) ·, δY_{s−}⟩`,
`G = 1`, is `1_{(0, 1]}`, of energy `1`; and for every integrand `H` equal almost everywhere to
`λ δh + q^h`, the integrand `⟨G H_s(e), δY_{s−}⟩` has marked energy `1`. -/
theorem lem_pert_forward_window_hypotheses :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyStochCalc.Driver.LevyDriver.{0, 0, w} P 1 (Measure.dirac (0 : ℝ)))
      (hind₀ : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P)
      (ξ₁ ξ₂ : Ω → EuclideanSpace ℝ (Fin 1))
      (qb₁ qb₂ : Fin 1 → Ω → ℝ → ℝ) (qσ₁ qσ₂ : Fin 1 → ℝ → Ω → Fin 1 → ℝ)
      (qh₁ qh₂ : Fin 1 → ℝ → Ω → ℝ → ℝ) (qf₁ qf₂ : Fin 1 → Ω → ℝ → ℝ) (qg₁ qg₂ : Fin 1 → Ω → ℝ)
      (X₁ X₂ Y₁ Y₂ : Fin 1 → ℝ → Ω → ℝ) (Z₁ Z₂ : Fin 1 → ℝ → Ω → Fin 1 → ℝ)
      (U₁ U₂ : Fin 1 → ℝ → Ω → ℝ → ℝ),
      JointBorel 1 sysW ∧ Assumption23 (enlJoint ⊥ D bot_le) P 1 1 sysW
      ∧ (1 : Matrix (Fin 1) (Fin 1) ℝ).rank = min 1 1
      ∧ Assumption25 (enlJoint ⊥ D bot_le) P 1 (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 1 1 sysW
      ∧ Measurable[enlJoint ⊥ D bot_le 0] ξ₁ ∧ Measurable[enlJoint ⊥ D bot_le 0] ξ₂
      ∧ PredForcing (enlJoint ⊥ D bot_le) P (Measure.dirac (0 : ℝ)) 1 qb₁ qσ₁ qh₁ qf₁ qg₁
      ∧ PredForcing (enlJoint ⊥ D bot_le) P (Measure.dirac (0 : ℝ)) 1 qb₂ qσ₂ qh₂ qf₂ qg₂
      ∧ WeakForcedSolution D bot_le hind₀ 1 1 sysW ξ₁ qb₁ qσ₁ qh₁ qf₁ qg₁ X₁ Y₁ Z₁ U₁
      ∧ WeakForcedSolution D bot_le hind₀ 1 1 sysW ξ₂ qb₂ qσ₂ qh₂ qf₂ qg₂ X₂ Y₂ Z₂ U₂
      ∧ supSize P (Measure.dirac (0 : ℝ)) 1 (fun i t ω => X₁ i t ω - X₂ i t ω)
          (fun k t ω => Y₁ k t ω - Y₂ k t ω) (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j)
          (fun k t ω e => U₁ k t ω e - U₂ k t ω e) < ⊤
      ∧ Brownian.Ito.energy P 1 (fun ω s => ∑ k, ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ fun i =>
          1 * (diffusionProc P 1 sysW X₁ Y₁ Z₁ U₁ i s ω 0
            - diffusionProc P 1 sysW X₂ Y₂ Z₂ U₂ i s ω 0) + (qσ₁ i s ω 0 - qσ₂ i s ω 0)) k
          * (if s ∈ Set.Ioc (0 : ℝ) 1 then
              leftLimProc (fun a t ω => Y₁ a t ω - Y₂ a t ω) k s ω else 0)) = 1
      ∧ ∀ H : Fin 1 → Ω → ℝ → ℝ → ℝ,
        (∀ i, ∀ᵐ p ∂(Poisson.Compensated.markedEnergyMeasure P (Measure.dirac (0 : ℝ)) 1),
          H i p.1 p.2.1 p.2.2
            = 1 * (jumpProc 1 (coeffJump P 1 sysW (leftLimProc X₁) (leftLimProc Y₁) Z₁ U₁) i
                p.2.1 p.1 p.2.2
              - jumpProc 1 (coeffJump P 1 sysW (leftLimProc X₂) (leftLimProc Y₂) Z₂ U₂) i
                p.2.1 p.1 p.2.2) + (qh₁ i p.2.1 p.1 p.2.2 - qh₂ i p.2.1 p.1 p.2.2)) →
        Poisson.Compensated.markedEnergy P (Measure.dirac (0 : ℝ)) 1 (fun ω s e => ∑ k,
          ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ fun i => H i ω s e) k
          * (if s ∈ Set.Ioc (0 : ℝ) 1 then
              leftLimProc (fun a t ω => Y₁ a t ω - Y₂ a t ω) k s ω else 0)) = 1 := by
  obtain ⟨Ω, _, P, _, D, hind₀, MW, MN, qb₁, qb₂, qσ₁, qσ₂, qh₁, qh₂, qf₁, qf₂, qg₁, qg₂, X₁, X₂,
    Y₁, Y₂, Z₁, Z₂, U₁, U₂, hJ, h23, hG, h25, hq₁, hq₂, hs₁, hs₂, hsup, hX, hY, hZ, hU, hσ, hh,
    -⟩ :=
    affineWindow_pair.{w} 0 1 1 1 0 0
  refine ⟨Ω, inferInstance, P, inferInstance, D, hind₀, _, _, qb₁, qb₂, qσ₁, qσ₂, qh₁, qh₂, qf₁,
    qf₂, qg₁, qg₂, X₁, X₂, Y₁, Y₂, Z₁, Z₂, U₁, U₂, hJ, h23, hG, h25, measurable_const,
    measurable_const, hq₁, hq₂, hs₁.1, hs₂.1, hsup, ?_⟩
  have hl := leftLimProc_of_const (X := fun a t ω => Y₁ a t ω - Y₂ a t ω) (r := 1)
    fun k t ω => by rw [hY k t ω]; ring
  refine ⟨?_, fun H hH => ?_⟩
  · have e : (fun ω s => ∑ k, ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ fun i =>
        1 * (diffusionProc P 1 sysW X₁ Y₁ Z₁ U₁ i s ω 0
          - diffusionProc P 1 sysW X₂ Y₂ Z₂ U₂ i s ω 0) + (qσ₁ i s ω 0 - qσ₂ i s ω 0)) k
        * (if s ∈ Set.Ioc (0 : ℝ) 1 then
            leftLimProc (fun a t ω => Y₁ a t ω - Y₂ a t ω) k s ω else 0))
        = fun (_ : Ω) s => unitWindow s := by
      funext ω s
      simp only [Matrix.one_mulVec, Fin.sum_univ_one, hl, hσ, ite_Ioc_eq_unitWindow]
      rw [one_mul, unitWindow_mul_self]
    rw [e, energy_unitWindow]
  · rw [markedEnergy_congr_ae (φ₂ := fun (_ : Ω) s (_ : ℝ) => unitWindow s),
      markedEnergy_unitWindow]
    filter_upwards [hH 0, hh] with q h1 h2
    simp only [Matrix.one_mulVec, Fin.sum_univ_one, hl, ite_Ioc_eq_unitWindow]
    rw [h1, h2 0, one_mul, unitWindow_mul_self]

/-- **The hypotheses of Lemma 4.3 hold with the fifth integrand of (4.17) nonzero.** At the
instance of `affineWindow_pair` with `c = c' = 1`, `x₀ = a = y₀ = a' = 0`: two solutions of
(4.1) at `λ̲ = λ = 1` for forcings of the class of the paper, from the initial datum `0`, whose
difference is `δX = δY = M^N`, `δZ = 0`, `δU = 1_{(0, 1]}`, with forced jump difference
`λ δh + q^h = 1_{(0, 1]}` almost everywhere. For every integrand `H` equal almost everywhere to
`λ δh + q^h`, the fifth integrand `⟨H_s(e), Gᵀ δU_s(e)⟩`, `G = 1`, has marked energy `1`. -/
theorem lem_pert_jump_window_hypotheses :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyStochCalc.Driver.LevyDriver.{0, 0, w} P 1 (Measure.dirac (0 : ℝ)))
      (hind₀ : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P)
      (ξ₁ ξ₂ : Ω → EuclideanSpace ℝ (Fin 1))
      (qb₁ qb₂ : Fin 1 → Ω → ℝ → ℝ) (qσ₁ qσ₂ : Fin 1 → ℝ → Ω → Fin 1 → ℝ)
      (qh₁ qh₂ : Fin 1 → ℝ → Ω → ℝ → ℝ) (qf₁ qf₂ : Fin 1 → Ω → ℝ → ℝ) (qg₁ qg₂ : Fin 1 → Ω → ℝ)
      (X₁ X₂ Y₁ Y₂ : Fin 1 → ℝ → Ω → ℝ) (Z₁ Z₂ : Fin 1 → ℝ → Ω → Fin 1 → ℝ)
      (U₁ U₂ : Fin 1 → ℝ → Ω → ℝ → ℝ),
      JointBorel 1 sysW ∧ Assumption23 (enlJoint ⊥ D bot_le) P 1 1 sysW
      ∧ (1 : Matrix (Fin 1) (Fin 1) ℝ).rank = min 1 1
      ∧ Assumption25 (enlJoint ⊥ D bot_le) P 1 (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 1 1 sysW
      ∧ Measurable[enlJoint ⊥ D bot_le 0] ξ₁ ∧ Measurable[enlJoint ⊥ D bot_le 0] ξ₂
      ∧ PredForcing (enlJoint ⊥ D bot_le) P (Measure.dirac (0 : ℝ)) 1 qb₁ qσ₁ qh₁ qf₁ qg₁
      ∧ PredForcing (enlJoint ⊥ D bot_le) P (Measure.dirac (0 : ℝ)) 1 qb₂ qσ₂ qh₂ qf₂ qg₂
      ∧ WeakForcedSolution D bot_le hind₀ 1 1 sysW ξ₁ qb₁ qσ₁ qh₁ qf₁ qg₁ X₁ Y₁ Z₁ U₁
      ∧ WeakForcedSolution D bot_le hind₀ 1 1 sysW ξ₂ qb₂ qσ₂ qh₂ qf₂ qg₂ X₂ Y₂ Z₂ U₂
      ∧ supSize P (Measure.dirac (0 : ℝ)) 1 (fun i t ω => X₁ i t ω - X₂ i t ω)
          (fun k t ω => Y₁ k t ω - Y₂ k t ω) (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j)
          (fun k t ω e => U₁ k t ω e - U₂ k t ω e) < ⊤
      ∧ ∀ H : Fin 1 → Ω → ℝ → ℝ → ℝ,
        (∀ i, ∀ᵐ p ∂(Poisson.Compensated.markedEnergyMeasure P (Measure.dirac (0 : ℝ)) 1),
          H i p.1 p.2.1 p.2.2
            = 1 * (jumpProc 1 (coeffJump P 1 sysW (leftLimProc X₁) (leftLimProc Y₁) Z₁ U₁) i
                p.2.1 p.1 p.2.2
              - jumpProc 1 (coeffJump P 1 sysW (leftLimProc X₂) (leftLimProc Y₂) Z₂ U₂) i
                p.2.1 p.1 p.2.2) + (qh₁ i p.2.1 p.1 p.2.2 - qh₂ i p.2.1 p.1 p.2.2)) →
        Poisson.Compensated.markedEnergy P (Measure.dirac (0 : ℝ)) 1 (fun ω s e =>
          (fun i => H i ω s e) ⬝ᵥ ((1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ *ᵥ
            fun k => U₁ k s ω e - U₂ k s ω e)) = 1 := by
  obtain ⟨Ω, _, P, _, D, hind₀, MW, MN, qb₁, qb₂, qσ₁, qσ₂, qh₁, qh₂, qf₁, qf₂, qg₁, qg₂, X₁, X₂,
    Y₁, Y₂, Z₁, Z₂, U₁, U₂, hJ, h23, hG, h25, hq₁, hq₂, hs₁, hs₂, hsup, hX, hY, hZ, hU, hσ, hh,
    -⟩ :=
    affineWindow_pair.{w} 0 0 1 0 0 1
  refine ⟨Ω, inferInstance, P, inferInstance, D, hind₀, _, _, qb₁, qb₂, qσ₁, qσ₂, qh₁, qh₂, qf₁,
    qf₂, qg₁, qg₂, X₁, X₂, Y₁, Y₂, Z₁, Z₂, U₁, U₂, hJ, h23, hG, h25, measurable_const,
    measurable_const, hq₁, hq₂, hs₁.1, hs₂.1, hsup, ?_⟩
  intro H hH
  rw [markedEnergy_congr_ae (φ₂ := fun (_ : Ω) s (_ : ℝ) => unitWindow s),
    markedEnergy_unitWindow]
  filter_upwards [hH 0, hh] with q h1 h2
  simp only [Matrix.transpose_one, Matrix.one_mulVec, dotProduct, Fin.sum_univ_one, hU]
  rw [h1, h2 0, one_mul, unitWindow_mul_self]

/-- **The hypotheses of Lemma 4.3 hold at two solutions with different initial data and different
forcings.** At the instance of `affineWindow_pair` with `x₀ = 1`, `a = c = y₀ = 0`, `a' = c' = 1`:
the system of Example 5.1(i) with `β₁ = β₂ = 1`, `σ_c = h_c = 0` satisfies (2.3), Assumption 2.3
with `L = 1` and Assumption 2.5 with `G = 1`, `α = β₁ = β₂ = 1`; `λ̲ = λ = 1`; two solutions of
(4.1) in `ℍ²` from the `ℱ₀`-measurable initial data `1` and `0`, for forcings of the class of
the paper, with difference in `𝕊`. For versions `M^W`, `M^N` of `∫_0^t 1_{(0, 1]} dW` and
`∫_0^t ∫ 1_{(0, 1]} Ñ(ds, de)`, the differences are `δX ≡ 1`, `δY = M^W + M^N`,
`δZ = δU = 1_{(0, 1]}` and `δg_T ≡ 1`, and the differences of the forcings are
`δq^b_s = 1_{[0, 1]}(s) (M^W_s + M^N_s)`, `δq^σ = δq^h = 1_{(0, 1]}`, `δq^f = −1_{[0, 1]}` and
`δq^g_T = M^W_1 + M^N_1 − 1`. -/
theorem lem_pert_data_forcing_hypotheses :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyStochCalc.Driver.LevyDriver.{0, 0, w} P 1 (Measure.dirac (0 : ℝ)))
      (hind₀ : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P) (MW MN : ℝ → Ω → ℝ)
      (ξ₁ ξ₂ : Ω → EuclideanSpace ℝ (Fin 1))
      (qb₁ qb₂ : Fin 1 → Ω → ℝ → ℝ) (qσ₁ qσ₂ : Fin 1 → ℝ → Ω → Fin 1 → ℝ)
      (qh₁ qh₂ : Fin 1 → ℝ → Ω → ℝ → ℝ) (qf₁ qf₂ : Fin 1 → Ω → ℝ → ℝ) (qg₁ qg₂ : Fin 1 → Ω → ℝ)
      (X₁ X₂ Y₁ Y₂ : Fin 1 → ℝ → Ω → ℝ) (Z₁ Z₂ : Fin 1 → ℝ → Ω → Fin 1 → ℝ)
      (U₁ U₂ : Fin 1 → ℝ → Ω → ℝ → ℝ),
      JointBorel 1 sysW ∧ Assumption23 (enlJoint ⊥ D bot_le) P 1 1 sysW
      ∧ (1 : Matrix (Fin 1) (Fin 1) ℝ).rank = min 1 1
      ∧ Assumption25 (enlJoint ⊥ D bot_le) P 1 (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 1 1 sysW
      ∧ Measurable[enlJoint ⊥ D bot_le 0] ξ₁ ∧ Measurable[enlJoint ⊥ D bot_le 0] ξ₂
      ∧ PredForcing (enlJoint ⊥ D bot_le) P (Measure.dirac (0 : ℝ)) 1 qb₁ qσ₁ qh₁ qf₁ qg₁
      ∧ PredForcing (enlJoint ⊥ D bot_le) P (Measure.dirac (0 : ℝ)) 1 qb₂ qσ₂ qh₂ qf₂ qg₂
      ∧ WeakForcedSolution D bot_le hind₀ 1 1 sysW ξ₁ qb₁ qσ₁ qh₁ qf₁ qg₁ X₁ Y₁ Z₁ U₁
      ∧ WeakForcedSolution D bot_le hind₀ 1 1 sysW ξ₂ qb₂ qσ₂ qh₂ qf₂ qg₂ X₂ Y₂ Z₂ U₂
      ∧ supSize P (Measure.dirac (0 : ℝ)) 1 (fun i t ω => X₁ i t ω - X₂ i t ω)
          (fun k t ω => Y₁ k t ω - Y₂ k t ω) (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j)
          (fun k t ω e => U₁ k t ω e - U₂ k t ω e) < ⊤
      ∧ (∀ t, MW t =ᵐ[P] Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W
          (enlJoint ⊥ D bot_le) (isBrownianFiltration_enlJoint D bot_le hind₀)
          (fun s (_ : Ω) (_ : Fin 1) => unitWindow s) window_meas (window_prog _) (window_sq P) t)
      ∧ (∀ t, MN t =ᵐ[P] Poisson.Compensated.stochasticIntegral D.N (enlJoint ⊥ D bot_le)
          (isPoissonFiltration_enlJoint D bot_le hind₀) (fun (_ : Ω) s (_ : ℝ) => unitWindow s)
          windowN_meas (windowN_prog _) (windowN_sq P) t)
      ∧ (∀ i ω, ξ₁ ω i - ξ₂ ω i = 1)
      ∧ (∀ i t ω, X₁ i t ω - X₂ i t ω = 1)
      ∧ (∀ k t ω, Y₁ k t ω - Y₂ k t ω = MW t ω + MN t ω)
      ∧ (∀ k s ω j, Z₁ k s ω j - Z₂ k s ω j = unitWindow s)
      ∧ (∀ k s ω e, U₁ k s ω e - U₂ k s ω e = unitWindow s)
      ∧ (∀ k ω, terminalVal P 1 sysW X₁ k ω - terminalVal P 1 sysW X₂ k ω = 1)
      ∧ (∀ i ω s, qb₁ i ω s - qb₂ i ω s
          = (Set.Icc (0 : ℝ) 1).indicator (fun s => MW s ω + MN s ω) s)
      ∧ (∀ i s ω j, qσ₁ i s ω j - qσ₂ i s ω j = unitWindow s)
      ∧ (∀ i s ω e, qh₁ i s ω e - qh₂ i s ω e = unitWindow s)
      ∧ (∀ k ω s, qf₁ k ω s - qf₂ k ω s = -(Set.Icc (0 : ℝ) 1).indicator 1 s)
      ∧ ∀ k ω, qg₁ k ω - qg₂ k ω = MW 1 ω + MN 1 ω - 1 := by
  obtain ⟨Ω, _, P, _, D, hind₀, MW, MN, qb₁, qb₂, qσ₁, qσ₂, qh₁, qh₂, qf₁, qf₂, qg₁, qg₂, X₁, X₂,
    Y₁, Y₂, Z₁, Z₂, U₁, U₂, hJ, h23, hG, h25, hq₁, hq₂, hs₁, hs₂, hsup, hX, hY, hZ, hU, -, -,
    hWe, hNe, hb, hσ, hh, hf, hg⟩ := affineWindow_pair.{w} 1 0 0 0 1 1
  refine ⟨Ω, inferInstance, P, inferInstance, D, hind₀, MW, MN, _, _, qb₁, qb₂, qσ₁, qσ₂, qh₁,
    qh₂, qf₁, qf₂, qg₁, qg₂, X₁, X₂, Y₁, Y₂, Z₁, Z₂, U₁, U₂, hJ, h23, hG, h25, measurable_const,
    measurable_const, hq₁, hq₂, hs₁.1, hs₂.1, hsup, hWe, hNe, fun i ω => by simp,
    fun i t ω => ?_, fun k t ω => ?_, fun k s ω j => ?_, fun k s ω e => ?_, fun k ω => ?_,
    fun i ω s => ?_, fun i s ω j => ?_, fun i s ω e => ?_, fun k ω s => ?_, fun k ω => ?_⟩
  · rw [hX]
    ring
  · rw [hY]
    ring
  · rw [hZ]
    ring
  · rw [hU]
    ring
  · rw [terminalVal_sysW, terminalVal_sysW, hX]
    ring
  · rw [hb]
    by_cases hs : s ∈ Set.Icc (0 : ℝ) 1
    · simp only [Set.indicator_of_mem hs]
      ring
    · simp only [Set.indicator_of_notMem hs]
  · rw [hσ]
    ring
  · rw [hh]
    ring
  · rw [hf]
    by_cases hs : s ∈ Set.Icc (0 : ℝ) 1
    · simp only [Set.indicator_of_mem hs, Pi.one_apply]
      ring
    · simp only [Set.indicator_of_notMem hs]
  · rw [hg]
    ring

end Dissertation.Acceptance.A
