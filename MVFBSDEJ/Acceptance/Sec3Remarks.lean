/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.PaperSpec.Sec3Remarks
import MVFBSDEJ.PaperSpec.Sec2Measurability
import MVFBSDEJ.Acceptance.Sec3
import MVFBSDEJ.WellPosedness.Spec.Examples
import MVFBSDEJ.WellPosedness.System.JumpPredictable

/-!
# The measurability (2.5) and Remark 3.2 of the well-posedness paper: proofs

The measurability (2.5) is a consequence of the joint Borel measurability (2.3), through
`MVFBSDEJ.WellPosedness.Spec.JointBorel.coeffRegular` and
`MVFBSDEJ.WellPosedness.Spec.JointBorel.predictable_jump`; the marked predictable representative
of the jump coefficient is the jointly measurable representative `MVFBSDEJ.Law.lpRep` of the
elements of `L²(ν; ℝⁿ)` along the predictable tuple, cut to the positive times. For Remark 3.2,
along a tuple of `ℍ²` satisfying (1.1), (2.5) and Assumptions 2.2–2.3 bound the energy of the
drift and driver processes by (4.2), so the tuple satisfies (1.1) with square-integrable
coefficient processes; the `S²` bounds of `𝕊` then follow from the forward form of both
equations.

## Main statements

* `MVFBSDEJ.Acceptance.exists_markedPredictable_jump` — a marked predictable
  representative of the jump coefficient along a predictable tuple.
* `MVFBSDEJ.Acceptance.eq_coefmeas`, `eq_coefmeas_jump` — (2.5).
* `MVFBSDEJ.Acceptance.rem_cwp_class` — Remark 3.2, and `rem_cwp_class_hypotheses` — its
  hypotheses hold at Example 5.1(i).
-/

open MeasureTheory ProbabilityTheory

namespace MVFBSDEJ.Acceptance

open MVFBSDEJ.WellPosedness.System MVFBSDEJ.WellPosedness.Enlarged
  MVFBSDEJ.WellPosedness.Spec MVFBSDEJ.WellPosedness.Existence MVFBSDEJ.PaperSpec

universe u v w

/-- (2.5), the first line: along a progressive tuple the drift, diffusion and driver evaluations
are progressively measurable, and the jump coefficient has a marked progressive representative. -/
theorem eq_coefmeas : PaperSpec.eq_coefmeas.{u, v} := by
  intro Ω mΩ ℱ P _ E _ ν _ _ n m d T C hJ
  exact hJ.coeffRegular ℱ P

/-- **A marked predictable representative of the jump coefficient along a predictable tuple.**
For coefficients with (2.3), a predictable tuple `Θ` and a Borel law flow `ρ`, there are marked
predictable `γ_i` such that `e ↦ (γ_i(ω, s, e))_i` represents `h(s, Θ_s(ω), ·, ρ_s)` at every
`ω` and every `s ∈ (0, T]`. -/
theorem exists_markedPredictable_jump {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {ℱ : Filtration ℝ mΩ} {E : Type*} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]
    [MeasurableSpace.CountablyGenerated E] {n m d : ℕ} {T : ℝ} {C : Coeffs ν n m d}
    (hJ : JointBorel T C) {Θ : Ω → ℝ → TupleH ν n m d} {ρ : ℝ → TupleP2WH ν n m d}
    (hΘ : LevyStochCalc.Probability.Predictable ℱ Θ) (hρ : Measurable ρ) :
    ∃ γ : Fin n → Ω → ℝ → E → ℝ,
      (∀ i, LevyStochCalc.Probability.MarkedPredictable ℱ ν (γ i))
      ∧ ∀ ω, ∀ s ∈ Set.Ioc (0 : ℝ) T,
        (fun e => (WithLp.toLp 2 fun i => γ i ω s e : EuclideanSpace ℝ (Fin n)))
          =ᵐ[ν] C.h s (Θ ω s) (ρ s).toP2 := by
  classical
  have hh := (jointBorel_iff.mp hJ).1.h_meas
  rw [← BorelSpace.measurable_eq (α := Lp (EuclideanSpace ℝ (Fin n)) 2 ν),
    ← BorelSpace.measurable_eq (α := Set.Icc (0 : ℝ) T × TupleH ν n m d × TupleP2WH ν n m d)]
    at hh
  set S : Set (ℝ × TupleH ν n m d × TupleP2WH ν n m d) := {q | q.1 ∈ Set.Icc (0 : ℝ) T}
  have hS : MeasurableSet S := measurable_fst measurableSet_Icc
  have hφ : Measurable fun q : S => ((⟨q.1.1, q.2⟩ : Set.Icc (0 : ℝ) T), q.1.2.1, q.1.2.2) :=
    (Measurable.subtype_mk (measurable_fst.comp measurable_subtype_coe)).prodMk
      ((measurable_snd.fst.comp measurable_subtype_coe).prodMk
        (measurable_snd.snd.comp measurable_subtype_coe))
  have hG : Measurable fun q : S => C.h q.1.1 q.1.2.1 q.1.2.2.toP2 := hh.comp hφ
  have hcut : Measurable fun q : ℝ × TupleH ν n m d × TupleP2WH ν n m d =>
      (Set.Icc (0 : ℝ) T).indicator (fun t => C.h t q.2.1 q.2.2.toP2) q.1 := by
    have heq : (fun q : ℝ × TupleH ν n m d × TupleP2WH ν n m d =>
          (Set.Icc (0 : ℝ) T).indicator (fun t => C.h t q.2.1 q.2.2.toP2) q.1)
        = fun q => if hq : q ∈ S then (fun r : S => C.h r.1.1 r.1.2.1 r.1.2.2.toP2) ⟨q, hq⟩
          else (fun _ : (Sᶜ : Set _) => (0 : Lp (EuclideanSpace ℝ (Fin n)) 2 ν)) ⟨q, hq⟩ := by
      funext q
      by_cases hq : q ∈ S
      · rw [dif_pos hq, Set.indicator_of_mem (show q.1 ∈ Set.Icc (0 : ℝ) T from hq)]
      · rw [dif_neg hq, Set.indicator_of_notMem (show q.1 ∉ Set.Icc (0 : ℝ) T from hq)]
    rw [heq]
    exact hG.dite measurable_const hS
  have hcutρ : Measurable fun q : ℝ × TupleH ν n m d =>
      (Set.Icc (0 : ℝ) T).indicator (fun t => C.h t q.2 (ρ t).toP2) q.1 :=
    hcut.comp (measurable_fst.prodMk (measurable_snd.prodMk (hρ.comp measurable_fst)))
  set F : Fin n → ℝ → TupleH ν n m d → E → ℝ := fun i s θ e =>
    MVFBSDEJ.Law.lpRep ν (EuclideanSpace ℝ (Fin n))
      ((Set.Icc (0 : ℝ) T).indicator (fun t => C.h t θ (ρ t).toP2) s, e) i with hFdef
  have hF : ∀ i, Measurable fun q : ℝ × TupleH ν n m d × E => F i q.1 q.2.1 q.2.2 := by
    intro i
    have hproj : Measurable fun v : EuclideanSpace ℝ (Fin n) => v i :=
      (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).continuous.measurable
    exact hproj.comp (MVFBSDEJ.Law.stronglyMeasurable_lpRep.measurable.comp
      ((hcutρ.comp (measurable_fst.prodMk measurable_snd.fst)).prodMk measurable_snd.snd))
  have hΛ : Measurable[LevyStochCalc.Probability.predictableSigma ℱ]
      fun p : ℝ × Ω => Θ p.2 p.1 := hΘ.measurable
  refine ⟨fun i ω s e => if 0 < s then F i s (Θ ω s) e else 0,
    fun i => markedPredictable_ite_comp (Λ := fun s ω => Θ ω s) hΛ (hF i), fun ω s hs => ?_⟩
  have hsI : s ∈ Set.Icc (0 : ℝ) T := Set.Ioc_subset_Icc_self hs
  filter_upwards [MVFBSDEJ.Law.lpRep_ae_eq (C.h s (Θ ω s) (ρ s).toP2)] with e he
  rw [← he]
  simp only [if_pos hs.1, hFdef, Set.indicator_of_mem hsI]

/-- (2.5), the second line: the jump coefficient along a predictable tuple and a Borel law flow is
predictable, and has a marked predictable representative at the times of `(0, T]`. -/
theorem eq_coefmeas_jump : PaperSpec.eq_coefmeas_jump.{u, v} := by
  intro Ω mΩ ℱ E _ ν _ _ n m d T C Θ ρ hJ hΘ hρ
  exact ⟨hJ.predictable_jump hΘ hρ, exists_markedPredictable_jump hJ hΘ hρ⟩

/-- Remark 3.2: under (2.3) and Assumptions 2.2–2.3, a tuple of `ℍ²` satisfying (1.1) solves
(1.1) in `𝕊`. -/
theorem rem_cwp_class : PaperSpec.rem_cwp_class.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ hind₀ T hT L C ξ₀ hJ h22 h23 X Y Z U hW
  obtain ⟨γ, hw⟩ := hW.1
  obtain ⟨γ', hadm⟩ := hw.toPaperWeakTuple.exists_paperAdmissible hT.le
    (eq_coefmeas _ P ν n m d T C hJ) (originValues_iff_coeffOrigin.mp h22.origin)
    h23.interior.diagonalLipschitz_two_mul
  have hpw : PaperWeakSolution D (enlJoint 𝒢₀ D h𝒢₀) (isBrownianFiltration_enlJoint D h𝒢₀ hind₀)
      (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) T C (fun i ω => ξ₀ ω i) X Y Z U γ :=
    { toPaperWeakTuple := hw.toPaperWeakTuple
      toPaperAdmissible := { hw.toPaperAdmissibleInt with b_sq := hadm.b_sq, f_sq := hadm.f_sq }
      fwd := hw.fwd
      bwd := hw.bwd }
  have hs := hpw.toPaperSolution (crossWitnessEnl D h𝒢₀ hind₀) (hF0_enlJoint D h𝒢₀)
    (fun _ hs h0 => measurableSet_enlJoint_of_null D h𝒢₀ hs h0) hT
  exact ⟨hW, hs.X_sup, hs.Y_sup⟩

/-- The system of Example 5.1(i) with `n = d = 1`, `ν = δ₀` on `ℝ`, `β₁ = β₂ = β`, `σ_c = 0` and
`h_c = 0`. -/
local notation "sys " β:max =>
  affineCoeffs (ν := Measure.dirac (0 : ℝ)) (n := 1) (d := 1) β β 0 0

/-- **The hypotheses of Remark 3.2 hold at Example 5.1(i).** Over a probability space carrying a
Lévy driver with `d = 1` and `ν = δ₀` on `ℝ`, with `𝒢₀ = ⊥`, `n = m = 1` and `T = 1`, the system
of Example 5.1(i) with `β₁ = β₂ = 1`, `σ_c = 0`, `h_c = 0` and initial datum `0` satisfies (2.3),
Assumption 2.2 and Assumption 2.3 with `L = 1`, and a tuple of `ℍ²` satisfies (1.1) (the
solution of Theorem 3.5). -/
theorem rem_cwp_class_hypotheses :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyStochCalc.Driver.LevyDriver P 1 (Measure.dirac (0 : ℝ)))
      (hind₀ : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P),
      JointBorel 1 (sys 1)
      ∧ Assumption22 (enlJoint ⊥ D bot_le) P 1 (sys 1) (fun _ => 0)
      ∧ Assumption23 (enlJoint ⊥ D bot_le) P 1 1 (sys 1)
      ∧ ∃ (X : Fin 1 → ℝ → Ω → ℝ) (Y : Fin 1 → ℝ → Ω → ℝ) (Z : Fin 1 → ℝ → Ω → Fin 1 → ℝ)
          (U : Fin 1 → ℝ → Ω → ℝ → ℝ),
          WeakSolution D bot_le hind₀ 1 (sys 1) (fun _ => 0) X Y Z U := by
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ := LevyStochCalc.Driver.LevyDriver.exists 1 ℝ (Measure.dirac (0 : ℝ))
  have hind₀ : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P := indep_bot_left _
  obtain ⟨hJ, h22, h23, hG, h25⟩ :=
    affine_assumptions (ν := Measure.dirac (0 : ℝ)) (ℱ := enlJoint ⊥ D bot_le) (P := P) (T := 1)
      (σc := 0) (hc := 0) one_pos one_pos (0 : EuclideanSpace ℝ (Fin 1))
  have e₁ : max (max (1 : ℝ) 1) 1 = 1 := by norm_num
  rw [e₁] at h23
  obtain ⟨X, Y, Z, U, hW, -, -⟩ := (thm_cwp ⊥ _ 1 1 1 P D bot_le hind₀ one_pos one_pos
    one_pos 1 one_pos 1 1 1 1 1 _ _ hJ h22 h23 hG h25).1
  exact ⟨Ω, inferInstance, P, inferInstance, D, hind₀, hJ, h22, h23, X, Y, Z, U, hW⟩

end MVFBSDEJ.Acceptance
