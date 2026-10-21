/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.Acceptance.A.WitnessContraction
import Dissertation.Acceptance.A.WitnessForced

/-!
# Two trials of Lemma 4.2 whose coefficient differences are nonzero in every channel

Statement and equation numbers refer to the well-posedness paper at `1f67672`. The instance is
that of `Dissertation.Acceptance.A.frozen_hypotheses`: a Lévy driver with `d = 1` and `ν = δ₀` on
`ℝ`, `𝒢₀ = ⊥`, `n = m = 1`, `T = 1`, the system of Example 5.1(i) with `β₁ = β₂ = 1`,
`σ_c = h_c = 0` (`b = −y`, `σ = −z`, `h = −u`) and initial datum `0`, `λ = 1` and the zero
forcing, with the two trials of `𝕊` the zero tuple and `(X, Y, Z, U) = (1, 1, 1_{(0, 1]},
1_{(0, 1]})`. The coefficient differences are `δb = 1_{[0, 1]}`, `δσ = δh = 1_{(0, 1]}`.

## Main statements

* `Dissertation.Acceptance.A.hTuple_const_window` — a tuple with constant `X`, `Y` and
  `Z = U = 1_{(0, 1]}` lies in `𝕊`.
* `Dissertation.Acceptance.A.coeffJump_affine` — the canonical representative of `h = −u` at a
  tuple, at the mark `0`.
* `Dissertation.Acceptance.A.frozen_pair_window_hypotheses` — the hypotheses of the forward
  difference before (4.10), with `δb`, `δσ` and `δh` of energy `1`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace Dissertation.Acceptance.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence
  Dissertation.WellPosedness.Enlarged Dissertation.WellPosedness.Spec Dissertation.PaperSpec.A
  Dissertation.WellPosedness.Stability Dissertation.Law LevyStochCalc

universe w

/-- The system of Example 5.1(i) with `n = d = 1`, `ν = δ₀` on `ℝ`, `β₁ = β₂ = 1`, `σ_c = 0` and
`h_c = 0`. -/
local notation "sysF" =>
  affineCoeffs (ν := Measure.dirac (0 : ℝ)) (n := 1) (d := 1) 1 1 0 0

/-- A tuple with constant `X ≡ a`, `Y ≡ b` and `Z = U = 1_{(0, 1]}` lies in `𝕊` on `[0, 1]` at
`ν = δ₀`, over every filtration. -/
theorem hTuple_const_window {Ω : Type*} [MeasurableSpace Ω] (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (P : Measure Ω) [IsProbabilityMeasure P] (a b : ℝ) :
    HTuple ℱ P (Measure.dirac (0 : ℝ)) 1 (fun (_ : Fin 1) _ _ => a) (fun (_ : Fin 1) _ _ => b)
      (fun (_ : Fin 1) s _ (_ : Fin 1) => unitWindow s)
      (fun (_ : Fin 1) s _ (_ : ℝ) => unitWindow s) := by
  obtain ⟨hc, -, -, hsa, hsb⟩ := hTuple_const (n := 1) (m := 1) (d := 1)
    (ν := Measure.dirac (0 : ℝ)) ℱ P 1 a b
  have hE : Brownian.Ito.energy P 1 (fun (_ : Ω) s => unitWindow s) = 1 := by
    simp [Brownian.Ito.energy, setLIntegral_unitWindow_sq]
  have hEm : Poisson.Compensated.markedEnergy P (Measure.dirac (0 : ℝ)) 1
      (fun (_ : Ω) s (_ : ℝ) => unitWindow s) = 1 := by
    simp [Poisson.Compensated.markedEnergy, setLIntegral_unitWindow_sq]
  refine ⟨{ hc with
      Z_pred := fun _ _ => predictable_unitWindow ℱ
      Z_vanish := fun _ _ _ hs => funext fun _ => unitWindow_of_notMem hs
      Z_sq := fun _ _ => by rw [hE]; exact ENNReal.one_ne_top
      U_pred := fun _ => markedPredictable_unitWindow ℱ (Measure.dirac (0 : ℝ))
      U_vanish := fun _ _ _ _ hs => unitWindow_of_notMem hs
      U_sq := fun _ => by rw [hEm]; exact ENNReal.one_ne_top },
    fun _ _ _ _ => ⟨a, tendsto_const_nhds⟩, fun _ _ _ _ => ⟨b, tendsto_const_nhds⟩, hsa, hsb⟩

/-- **The canonical representative of `h = −u` at a tuple.** For the system of Example 5.1(i)
with `β₁ = 1`, `h_c = 0` at `ν = δ₀`, at every time `s ∈ [0, T]` and sample point `ω`, the
canonical representative `coeffJump` of `h(s, Θ_s, ·, μ_s)` takes the value `−U_s(ω, 0)` at the
mark `0`. -/
theorem coeffJump_affine {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {T : ℝ} {X Y : Fin 1 → ℝ → Ω → ℝ} {Z : Fin 1 → ℝ → Ω → Fin 1 → ℝ}
    {U : Fin 1 → ℝ → Ω → ℝ → ℝ} {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) T) (ω : Ω) :
    coeffJump P T sysF X Y Z U 0 s ω 0 = -U 0 s ω 0 := by
  have h1 := coeffJump_ae_eq (P := P) (C := sysF) (X := X) (Y := Y) (Z := Z) (U := U) hs ω
  set cj := coeffJump P T sysF X Y Z U with hcj
  have hmem : MemLp (fun e : ℝ => (WithLp.toLp 2 ((fun e k => U k s ω e) e) :
      EuclideanSpace ℝ (Fin 1))) 2 (Measure.dirac (0 : ℝ)) :=
    (memLp_const (WithLp.toLp 2 fun k => U k s ω 0 : EuclideanSpace ℝ (Fin 1))).ae_eq
      (ae_eq_dirac (fun e : ℝ => (WithLp.toLp 2 ((fun e k => U k s ω e) e) :
        EuclideanSpace ℝ (Fin 1)))).symm
  simp only [affineCoeffs, tupleAt, one_smul] at h1
  rw [uLift_of_memLp hmem] at h1
  have h2 : (⇑((0 : Lp (EuclideanSpace ℝ (Fin 1)) 2 (Measure.dirac (0 : ℝ))) - hmem.toLp _))
      =ᵐ[Measure.dirac (0 : ℝ)] fun e => -(WithLp.toLp 2 fun k => U k s ω e :
        EuclideanSpace ℝ (Fin 1)) := by
    filter_upwards [Lp.coeFn_sub (0 : Lp (EuclideanSpace ℝ (Fin 1)) 2 (Measure.dirac (0 : ℝ)))
      (hmem.toLp _), Lp.coeFn_zero (EuclideanSpace ℝ (Fin 1)) 2 (Measure.dirac (0 : ℝ)),
      hmem.coeFn_toLp] with e e1 e2 e3
    rw [e1, Pi.sub_apply, e2, e3, Pi.zero_apply, zero_sub]
  have h3 := h1.trans h2
  rw [EventuallyEq, ae_dirac_eq, Filter.eventually_pure] at h3
  have h4 := congrArg (fun v : EuclideanSpace ℝ (Fin 1) => v 0) h3
  simp only [PiLp.neg_apply] at h4
  exact h4

/-- The drift process of Example 5.1(i) with `β₁ = 1` along a tuple is `−Y`, cut to `[0, T]`. -/
theorem driftProc_affine {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {T : ℝ} {X Y : Fin 1 → ℝ → Ω → ℝ} {Z : Fin 1 → ℝ → Ω → Fin 1 → ℝ}
    {U : Fin 1 → ℝ → Ω → ℝ → ℝ} (ω : Ω) (s : ℝ) :
    driftProc P T sysF X Y Z U 0 ω s = (Set.Icc (0 : ℝ) T).indicator (fun s => -Y 0 s ω) s := by
  by_cases hs : s ∈ Set.Icc (0 : ℝ) T
  · simp [driftProc, Set.indicator_of_mem hs, affineCoeffs, tupleAt]
  · simp [driftProc, Set.indicator_of_notMem hs]

/-- **The hypotheses of the forward difference before (4.10) hold with `δb`, `δσ` and `δh`
nonzero.** At the instance of `frozen_hypotheses` — the system of Example 5.1(i) with initial
datum `0`, (2.3) and Assumptions 2.2–2.3 with `L = 1`, `λ = 1` and the zero forcing — the zero
tuple and the tuple `(X, Y, Z, U) = (1, 1, 1_{(0, 1]}, 1_{(0, 1]})` are two trials of `𝕊`, each
has a frozen step, and the coefficient differences `δb = 1_{[0, 1]}`, `δσ = 1_{(0, 1]}` and
`δh = 1_{(0, 1]}` (through `coeffJump`) each have energy `1` on `[0, 1]`. -/
theorem frozen_pair_window_hypotheses :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyStochCalc.Driver.LevyDriver.{0, 0, w} P 1 (Measure.dirac (0 : ℝ)))
      (hind₀ : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P),
      JointBorel 1 sysF
      ∧ Assumption22 (enlJoint ⊥ D bot_le) P 1 sysF (fun _ => 0)
      ∧ Assumption23 (enlJoint ⊥ D bot_le) P 1 1 sysF
      ∧ PredForcing (enlJoint ⊥ D bot_le) P (Measure.dirac (0 : ℝ)) 1
          (0 : Fin 1 → Ω → ℝ → ℝ) (0 : Fin 1 → ℝ → Ω → Fin 1 → ℝ) (0 : Fin 1 → ℝ → Ω → ℝ → ℝ)
          (0 : Fin 1 → Ω → ℝ → ℝ) (0 : Fin 1 → Ω → ℝ)
      ∧ HTuple (enlJoint ⊥ D bot_le) P (Measure.dirac (0 : ℝ)) 1
          (fun (_ : Fin 1) _ _ => (0 : ℝ)) (fun (_ : Fin 1) _ _ => (0 : ℝ))
          (fun (_ : Fin 1) _ _ (_ : Fin 1) => (0 : ℝ)) (fun (_ : Fin 1) _ _ (_ : ℝ) => (0 : ℝ))
      ∧ HTuple (enlJoint ⊥ D bot_le) P (Measure.dirac (0 : ℝ)) 1
          (fun (_ : Fin 1) _ _ => (1 : ℝ)) (fun (_ : Fin 1) _ _ => (1 : ℝ))
          (fun (_ : Fin 1) s _ (_ : Fin 1) => unitWindow s)
          (fun (_ : Fin 1) s _ (_ : ℝ) => unitWindow s)
      ∧ (∃ (X₁' X₂' : Fin 1 → ℝ → Ω → ℝ) (Y₁' Y₂' : Fin 1 → ℝ → Ω → ℝ)
          (Z₁' Z₂' : Fin 1 → ℝ → Ω → Fin 1 → ℝ) (U₁' U₂' : Fin 1 → ℝ → Ω → ℝ → ℝ),
        FrozenStep D bot_le hind₀ 1 1 sysF (fun _ => 0) 0 0 0 0 0
            (fun (_ : Fin 1) _ _ => (0 : ℝ)) (fun (_ : Fin 1) _ _ => (0 : ℝ))
            (fun (_ : Fin 1) _ _ (_ : Fin 1) => (0 : ℝ)) (fun (_ : Fin 1) _ _ (_ : ℝ) => (0 : ℝ))
            X₁' Y₁' Z₁' U₁'
          ∧ FrozenStep D bot_le hind₀ 1 1 sysF (fun _ => 0) 0 0 0 0 0
            (fun (_ : Fin 1) _ _ => (1 : ℝ)) (fun (_ : Fin 1) _ _ => (1 : ℝ))
            (fun (_ : Fin 1) s _ (_ : Fin 1) => unitWindow s)
            (fun (_ : Fin 1) s _ (_ : ℝ) => unitWindow s) X₂' Y₂' Z₂' U₂')
      ∧ Brownian.Ito.energy P 1 (fun ω s =>
          driftProc P 1 sysF (fun (_ : Fin 1) _ _ => (0 : ℝ)) (fun (_ : Fin 1) _ _ => (0 : ℝ))
              (fun (_ : Fin 1) _ _ (_ : Fin 1) => (0 : ℝ))
              (fun (_ : Fin 1) _ _ (_ : ℝ) => (0 : ℝ)) 0 ω s
            - driftProc P 1 sysF (fun (_ : Fin 1) _ _ => (1 : ℝ)) (fun (_ : Fin 1) _ _ => (1 : ℝ))
              (fun (_ : Fin 1) s _ (_ : Fin 1) => unitWindow s)
              (fun (_ : Fin 1) s _ (_ : ℝ) => unitWindow s) 0 ω s) = 1
      ∧ Brownian.Ito.energy P 1 (fun ω s =>
          diffusionProc P 1 sysF (fun (_ : Fin 1) _ _ => (0 : ℝ))
              (fun (_ : Fin 1) _ _ => (0 : ℝ)) (fun (_ : Fin 1) _ _ (_ : Fin 1) => (0 : ℝ))
              (fun (_ : Fin 1) _ _ (_ : ℝ) => (0 : ℝ)) 0 s ω 0
            - diffusionProc P 1 sysF (fun (_ : Fin 1) _ _ => (1 : ℝ))
              (fun (_ : Fin 1) _ _ => (1 : ℝ)) (fun (_ : Fin 1) s _ (_ : Fin 1) => unitWindow s)
              (fun (_ : Fin 1) s _ (_ : ℝ) => unitWindow s) 0 s ω 0) = 1
      ∧ Poisson.Compensated.markedEnergy P (Measure.dirac (0 : ℝ)) 1 (fun ω s e =>
          coeffJump P 1 sysF (fun (_ : Fin 1) _ _ => (0 : ℝ)) (fun (_ : Fin 1) _ _ => (0 : ℝ))
              (fun (_ : Fin 1) _ _ (_ : Fin 1) => (0 : ℝ))
              (fun (_ : Fin 1) _ _ (_ : ℝ) => (0 : ℝ)) 0 s ω e
            - coeffJump P 1 sysF (fun (_ : Fin 1) _ _ => (1 : ℝ)) (fun (_ : Fin 1) _ _ => (1 : ℝ))
              (fun (_ : Fin 1) s _ (_ : Fin 1) => unitWindow s)
              (fun (_ : Fin 1) s _ (_ : ℝ) => unitWindow s) 0 s ω e) = 1 := by
  obtain ⟨Ω, _, P, _, D, hind₀, hJ, h22, h23, hq, hH₀, -⟩ := frozen_hypotheses.{w}
  have hH₁ := hTuple_const_window (enlJoint ⊥ D bot_le) P 1 1
  obtain ⟨-, ⟨X₁', Y₁', Z₁', U₁', h₁⟩, -⟩ := eq_frozenbwd.{0, 0, w} ⊥ (Measure.dirac (0 : ℝ)) 1 1 1
    P D bot_le hind₀ one_pos one_pos one_pos 1 one_pos 1 sysF (fun _ => 0) hJ h22 h23 1
    zero_le_one le_rfl 0 0 0 0 0 hq _ _ _ _ hH₀
  obtain ⟨-, ⟨X₂', Y₂', Z₂', U₂', h₂⟩, -⟩ := eq_frozenbwd.{0, 0, w} ⊥ (Measure.dirac (0 : ℝ)) 1 1 1
    P D bot_le hind₀ one_pos one_pos one_pos 1 one_pos 1 sysF (fun _ => 0) hJ h22 h23 1
    zero_le_one le_rfl 0 0 0 0 0 hq _ _ _ _ hH₁
  refine ⟨Ω, inferInstance, P, inferInstance, D, hind₀, hJ, h22, h23, hq, hH₀, hH₁,
    ⟨X₁', X₂', Y₁', Y₂', Z₁', Z₂', U₁', U₂', h₁, h₂⟩, ?_, ?_, ?_⟩
  · simp only [Brownian.Ito.energy, driftProc_affine]
    have e : ∫⁻ s in Set.Icc (0 : ℝ) 1, (‖(Set.Icc (0 : ℝ) 1).indicator (fun _ => -(0 : ℝ)) s
        - (Set.Icc (0 : ℝ) 1).indicator (fun _ => -(1 : ℝ)) s‖₊ : ℝ≥0∞) ^ 2 = 1 := by
      rw [setLIntegral_congr_fun measurableSet_Icc (g := fun _ => (1 : ℝ≥0∞)) fun s hs => by
        simp [Set.indicator_of_mem hs]]
      simp
    simp only [e, lintegral_const, measure_univ, mul_one]
  · have e : (fun (ω : Ω) s =>
          diffusionProc P 1 sysF (fun (_ : Fin 1) _ _ => (0 : ℝ))
              (fun (_ : Fin 1) _ _ => (0 : ℝ)) (fun (_ : Fin 1) _ _ (_ : Fin 1) => (0 : ℝ))
              (fun (_ : Fin 1) _ _ (_ : ℝ) => (0 : ℝ)) 0 s ω 0
            - diffusionProc P 1 sysF (fun (_ : Fin 1) _ _ => (1 : ℝ))
              (fun (_ : Fin 1) _ _ => (1 : ℝ)) (fun (_ : Fin 1) s _ (_ : Fin 1) => unitWindow s)
              (fun (_ : Fin 1) s _ (_ : ℝ) => unitWindow s) 0 s ω 0)
        = fun _ s => unitWindow s := by
      funext ω s
      rw [diffusionProc_affine, diffusionProc_affine]
      by_cases hs : s ∈ Set.Icc (0 : ℝ) 1
      · simp [Set.indicator_of_mem hs]
      · simp [Set.indicator_of_notMem hs, unitWindow_of_notMem hs]
    rw [e]
    simp [Brownian.Ito.energy, setLIntegral_unitWindow_sq]
  · simp only [Poisson.Compensated.markedEnergy, lintegral_dirac]
    have e : ∀ ω : Ω, ∫⁻ s in Set.Icc (0 : ℝ) 1, (‖coeffJump P 1 sysF
          (fun (_ : Fin 1) _ _ => (0 : ℝ)) (fun (_ : Fin 1) _ _ => (0 : ℝ))
          (fun (_ : Fin 1) _ _ (_ : Fin 1) => (0 : ℝ)) (fun (_ : Fin 1) _ _ (_ : ℝ) => (0 : ℝ))
          0 s ω 0
        - coeffJump P 1 sysF (fun (_ : Fin 1) _ _ => (1 : ℝ)) (fun (_ : Fin 1) _ _ => (1 : ℝ))
          (fun (_ : Fin 1) s _ (_ : Fin 1) => unitWindow s)
          (fun (_ : Fin 1) s _ (_ : ℝ) => unitWindow s) 0 s ω 0‖₊ : ℝ≥0∞) ^ 2
        = ∫⁻ s in Set.Icc (0 : ℝ) 1, (‖unitWindow s‖₊ : ℝ≥0∞) ^ 2 := fun ω =>
      setLIntegral_congr_fun measurableSet_Icc fun s hs => by
        rw [coeffJump_affine hs, coeffJump_affine hs]
        simp
    simp only [e, setLIntegral_unitWindow_sq, lintegral_const, measure_univ, mul_one]

end Dissertation.Acceptance.A
