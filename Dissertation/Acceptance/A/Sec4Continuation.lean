/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.PaperSpec.A.Sec4Continuation
import Dissertation.Acceptance.A.Sec4
import Dissertation.WellPosedness.Existence.Unique

/-!
# Sections 4.4 and 4.5 of the well-posedness paper: proofs

Statement and equation numbers refer to the well-posedness paper at `1f67672`.

## Main statements

* `Dissertation.Acceptance.A.ForcedSolution.supSize_sub_lt_top` — the difference of two solutions
  of (4.1) in `ℍ` lies in `ℍ`.
* `Dissertation.Acceptance.A.ForcedSolution.eq_of_supSize_sub_eq_zero` — zero size of the
  difference is uniqueness.
* `Dissertation.Acceptance.A.sec4_uniq_homotopy` — uniqueness along the homotopy, with `λ*` the
  constant of Lemma 4.2.
* `Dissertation.Acceptance.A.sec45_proof_thm35` — the continuation sequence, with `λ*` and `ζ₀`
  the constants of Lemmas 4.2 and 4.4.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace Dissertation.Acceptance.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence
  Dissertation.WellPosedness.Enlarged Dissertation.WellPosedness.Stability
  Dissertation.WellPosedness.Spec LevyStochCalc

universe u v w

section Forced

variable {Ω : Type u} {𝒢₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {E : Type v}
  [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
  {n m d : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {h𝒢₀ : 𝒢₀ ≤ mΩ}
  {hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P} {T L lam₁ lam₂ : ℝ} {C₁ C₂ : Coeffs ν n m d}
  {ξ₁ ξ₂ : Ω → EuclideanSpace ℝ (Fin n)}
  {qb₁ qb₂ : Fin n → Ω → ℝ → ℝ} {qσ₁ qσ₂ : Fin n → ℝ → Ω → Fin d → ℝ}
  {qh₁ qh₂ : Fin n → ℝ → Ω → E → ℝ} {qf₁ qf₂ : Fin m → Ω → ℝ → ℝ} {qg₁ qg₂ : Fin m → Ω → ℝ}
  {X₁ X₂ : Fin n → ℝ → Ω → ℝ} {Y₁ Y₂ : Fin m → ℝ → Ω → ℝ}
  {Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ} {U₁ U₂ : Fin m → ℝ → Ω → E → ℝ}

/-- A solution of (4.1) in `ℍ` for coefficients with (2.3), the origin bounds of Assumption 2.2
and Assumption 2.3 agrees on `[0, T]` with a solution of `SolvesForced`. -/
theorem ForcedSolution.exists_solvesForced {L₁ : ℝ} (hT : 0 ≤ T) (hJ : JointBorel T C₁)
    (horig : OriginValues T C₁) (h23 : Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L₁ C₁)
    (h : PaperSpec.A.ForcedSolution D h𝒢₀ hind₀ T lam₁ C₁ ξ₁ qb₁ qσ₁ qh₁ qf₁ qg₁ X₁ Y₁ Z₁ U₁) :
    ∃ (X' : Fin n → ℝ → Ω → ℝ) (Y' : Fin m → ℝ → Ω → ℝ) (γ : Fin n → ℝ → Ω → E → ℝ),
      (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T, X' i t = X₁ i t)
      ∧ (∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T, Y' k t = Y₁ k t)
      ∧ SolvesForced D (enlJoint 𝒢₀ D h𝒢₀) (isBrownianFiltration_enlJoint D h𝒢₀ hind₀)
          (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) T lam₁ C₁ (fun i ω => ξ₁ ω i) qb₁ qσ₁ qh₁
          qf₁ qg₁ X' Y' Z₁ U₁ γ := by
  obtain ⟨⟨γ, hs⟩, -, -⟩ := ForcedSolution.paperSolutionForced hT hJ horig h23 h
  obtain ⟨X', Y', hX, hY, hS⟩ := hs.exists_solvesForced hT
  exact ⟨X', Y', γ, hX, hY, hS⟩

/-- **The difference of two solutions of (4.1) in `ℍ` lies in `ℍ`**, for coefficients with (2.3),
the origin bounds of Assumption 2.2 and Assumption 2.3, at any parameters, initial data and
forcings. -/
theorem ForcedSolution.supSize_sub_lt_top {L₁ L₂ : ℝ} (hT : 0 < T) (hJ₁ : JointBorel T C₁)
    (horig₁ : OriginValues T C₁) (h23₁ : Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L₁ C₁)
    (hJ₂ : JointBorel T C₂) (horig₂ : OriginValues T C₂)
    (h23₂ : Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L₂ C₂)
    (h₁ : PaperSpec.A.ForcedSolution D h𝒢₀ hind₀ T lam₁ C₁ ξ₁ qb₁ qσ₁ qh₁ qf₁ qg₁ X₁ Y₁ Z₁ U₁)
    (h₂ : PaperSpec.A.ForcedSolution D h𝒢₀ hind₀ T lam₂ C₂ ξ₂ qb₂ qσ₂ qh₂ qf₂ qg₂ X₂ Y₂ Z₂ U₂) :
    supSize P ν T (fun i t ω => X₁ i t ω - X₂ i t ω) (fun k t ω => Y₁ k t ω - Y₂ k t ω)
      (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j) (fun k t ω e => U₁ k t ω e - U₂ k t ω e) < ⊤ := by
  obtain ⟨X₁', Y₁', γ₁, hX₁, hY₁, hS₁⟩ :=
    ForcedSolution.exists_solvesForced hT.le hJ₁ horig₁ h23₁ h₁
  obtain ⟨X₂', Y₂', γ₂, hX₂, hY₂, hS₂⟩ :=
    ForcedSolution.exists_solvesForced hT.le hJ₂ horig₂ h23₂ h₂
  have he := supSize_eq_of_eqOn (P := P) (ν := ν) (T := T)
    (X := fun i t ω => X₁ i t ω - X₂ i t ω) (X' := fun i t ω => X₁' i t ω - X₂' i t ω)
    (Y := fun k t ω => Y₁ k t ω - Y₂ k t ω) (Y' := fun k t ω => Y₁' k t ω - Y₂' k t ω)
    (fun i t ht => by simp only [hX₁ i t ht, hX₂ i t ht])
    (fun k t ht => by simp only [hY₁ k t ht, hY₂ k t ht])
    (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j) (fun k t ω e => U₁ k t ω e - U₂ k t ω e)
  rw [← he]
  exact hS₁.supSize_sub_lt_top hS₂ (crossWitnessEnl D h𝒢₀ hind₀) (hF0_enlJoint D h𝒢₀)
    (fun _ hs h0 => measurableSet_enlJoint_of_null D h𝒢₀ hs h0) hT

/-- **Zero size of the difference of two solutions of (4.1) in `ℍ` is uniqueness**, for
coefficients with (2.3), the origin bounds of Assumption 2.2 and Assumption 2.3. -/
theorem ForcedSolution.eq_of_supSize_sub_eq_zero {L₁ L₂ : ℝ} (hT : 0 ≤ T)
    (hJ₁ : JointBorel T C₁) (horig₁ : OriginValues T C₁)
    (h23₁ : Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L₁ C₁)
    (hJ₂ : JointBorel T C₂) (horig₂ : OriginValues T C₂)
    (h23₂ : Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L₂ C₂)
    (h₁ : PaperSpec.A.ForcedSolution D h𝒢₀ hind₀ T lam₁ C₁ ξ₁ qb₁ qσ₁ qh₁ qf₁ qg₁ X₁ Y₁ Z₁ U₁)
    (h₂ : PaperSpec.A.ForcedSolution D h𝒢₀ hind₀ T lam₂ C₂ ξ₂ qb₂ qσ₂ qh₂ qf₂ qg₂ X₂ Y₂ Z₂ U₂)
    (h0 : supSize P ν T (fun i t ω => X₁ i t ω - X₂ i t ω) (fun k t ω => Y₁ k t ω - Y₂ k t ω)
      (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j) (fun k t ω e => U₁ k t ω e - U₂ k t ω e) = 0) :
    (∀ i, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, X₁ i t ω = X₂ i t ω)
      ∧ (∀ k, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, Y₁ k t ω = Y₂ k t ω)
      ∧ (∀ k j, Brownian.Ito.energy P T (fun ω s => Z₁ k s ω j - Z₂ k s ω j) = 0)
      ∧ ∀ k, Poisson.Compensated.markedEnergy P ν T
          (fun ω s e => U₁ k s ω e - U₂ k s ω e) = 0 := by
  obtain ⟨X₁', Y₁', γ₁, hX₁, hY₁, hS₁⟩ := ForcedSolution.exists_solvesForced hT hJ₁ horig₁ h23₁ h₁
  obtain ⟨X₂', Y₂', γ₂, hX₂, hY₂, hS₂⟩ := ForcedSolution.exists_solvesForced hT hJ₂ horig₂ h23₂ h₂
  have he := supSize_eq_of_eqOn (P := P) (ν := ν) (T := T)
    (X := fun i t ω => X₁ i t ω - X₂ i t ω) (X' := fun i t ω => X₁' i t ω - X₂' i t ω)
    (Y := fun k t ω => Y₁ k t ω - Y₂ k t ω) (Y' := fun k t ω => Y₁' k t ω - Y₂' k t ω)
    (fun i t ht => by simp only [hX₁ i t ht, hX₂ i t ht])
    (fun k t ht => by simp only [hY₁ k t ht, hY₂ k t ht])
    (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j) (fun k t ω e => U₁ k t ω e - U₂ k t ω e)
  obtain ⟨hX, hY, hZ, hU⟩ := hS₁.eq_of_supSize_sub_eq_zero hS₂ hT (he.trans h0)
  refine ⟨fun i => ?_, fun k => ?_, hZ, hU⟩
  · filter_upwards [hX i] with ω hω t ht
    rw [← congrFun (hX₁ i t ht) ω, ← congrFun (hX₂ i t ht) ω]
    exact hω t ht
  · filter_upwards [hY k] with ω hω t ht
    rw [← congrFun (hY₁ k t ht) ω, ← congrFun (hY₂ k t ht) ω]
    exact hω t ht

end Forced

/-- §4.4, uniqueness along the homotopy, with `λ*` the constant of Lemma 4.2: Lemma 4.3 at
`λ̲ = λ*` with identical data on `[λ*, 1]`, Lemma 4.2 on `[0, λ*]`. -/
theorem sec4_uniq_homotopy : PaperSpec.A.sec4_uniq_homotopy.{u, v, w} := by
  obtain ⟨lamStar, hsmall⟩ := lem_small.{u, v, w}
  obtain ⟨CB, hpert⟩ := lem_pert.{u, v, w}
  refine ⟨lamStar, ?_⟩
  intro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ hind₀ hn hm hd T hT L α β₁ β₂ G C ξ₀ hJ h22 h23 hG h25
  obtain ⟨hpos, hle, hwp⟩ := hsmall 𝒢₀ ν n m d P D h𝒢₀ hind₀ hn hm hd T hT L C ξ₀ hJ h22 h23
  refine ⟨hpos, hle, fun lam hlam qb qσ qh qf qg hq X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ hS₁ hS₂ => ?_⟩
  rcases hlam with ⟨hl1, hl2⟩ | ⟨hl1, hl2⟩
  · have hξ : Measurable[enlJoint 𝒢₀ D h𝒢₀ 0] ξ₀ := h22.initial_meas.measurable
    have hsup := ForcedSolution.supSize_sub_lt_top hT hJ h22.origin h23 hJ h22.origin h23 hS₁ hS₂
    have h := hpert 𝒢₀ ν n m d P D h𝒢₀ hind₀ hn hm hd T hT L α β₁ β₂ G C hJ h23 hG h25
      (lamStar T L) lam hpos hle hl1 hl2 ξ₀ ξ₀ hξ hξ qb qb qσ qσ qh qh qf qf qg qg hq hq
      X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ hS₁.1 hS₂.1 hsup
    have hd0 : dataSize P ν T (fun i ω => ξ₀ ω i - ξ₀ ω i) (fun i ω s => qb i ω s - qb i ω s)
        (fun i s ω j => qσ i s ω j - qσ i s ω j) (fun i s ω e => qh i s ω e - qh i s ω e)
        (fun k ω s => qf k ω s - qf k ω s) (fun k ω => qg k ω - qg k ω) = 0 := by
      simp [dataSize, esq, Brownian.Ito.energy, Poisson.Compensated.markedEnergy]
    rw [hd0, mul_zero, nonpos_iff_eq_zero] at h
    exact ForcedSolution.eq_of_supSize_sub_eq_zero hT.le hJ h22.origin h23 hJ h22.origin h23 hS₁
      hS₂ h
  · exact (hwp lam hl1 hl2 qb qσ qh qf qg hq).2 X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ hS₁ hS₂

/-- The steps `λ_k = min{a + k z, 1}` from `a ≤ 1` with `z > 0`: `λ_0 = a`, consecutive steps
differ by at most `z`, `λ_k` is nondecreasing in `[a, 1]`, and `λ_k = 1` for `k ≥ ⌈(1 − a)/z⌉`. -/
theorem lambdaSeq_facts {a z : ℝ} (ha1 : a ≤ 1) (hz : 0 < z) :
    min (a + ((0 : ℕ) : ℝ) * z) 1 = a
    ∧ (∀ k : ℕ, min (a + ((k + 1 : ℕ) : ℝ) * z) 1 - min (a + (k : ℝ) * z) 1 ≤ z)
    ∧ (∀ k : ℕ, ⌈(1 - a) / z⌉₊ ≤ k → min (a + (k : ℝ) * z) 1 = 1)
    ∧ (∀ k : ℕ, a ≤ min (a + (k : ℝ) * z) 1)
    ∧ ∀ k : ℕ, min (a + (k : ℝ) * z) 1 ≤ min (a + ((k + 1 : ℕ) : ℝ) * z) 1 := by
  refine ⟨by simp [ha1], fun k => ?_, fun k hk => ?_, fun k => ?_, fun k => ?_⟩
  · push_cast
    rcases le_total 1 (a + k * z) with h | h
    · rw [min_eq_right h, min_eq_right (by nlinarith)]
      linarith
    · rw [min_eq_left h]
      have := min_le_left (a + ((k : ℝ) + 1) * z) 1
      linarith
  · have h1 : (1 - a) / z ≤ k := (Nat.le_ceil _).trans (by exact_mod_cast hk)
    rw [div_le_iff₀ hz] at h1
    exact min_eq_right (by linarith)
  · exact le_min (by nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]) ha1
  · push_cast
    exact min_le_min_right _ (by nlinarith)

/-- §4.5, the proof of Theorem 3.5, with `λ*` and `ζ₀` the constants of Lemmas 4.2 and 4.4. -/
theorem sec45_proof_thm35 : PaperSpec.A.sec45_proof_thm35.{u, v, w} := by
  obtain ⟨lamStar, hsmall⟩ := lem_small.{u, v, w}
  obtain ⟨zeta0, hcont⟩ := lem_cont.{u, v, w}
  refine ⟨lamStar, zeta0, ?_⟩
  intro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ hind₀ hn hm hd T hT L α β₁ β₂ G C ξ₀ hJ h22 h23 hG h25
  obtain ⟨hpos, hle, hwp⟩ := hsmall 𝒢₀ ν n m d P D h𝒢₀ hind₀ hn hm hd T hT L C ξ₀ hJ h22 h23
  obtain ⟨hz, hstep⟩ := hcont 𝒢₀ ν n m d P D h𝒢₀ hind₀ hn hm hd T hT L α β₁ β₂ G C ξ₀ hJ h22 h23
    hG h25 (lamStar T L) hpos hle
  obtain ⟨h0, hdiff, hone, hlow, hmono⟩ := lambdaSeq_facts hle hz
  have hwpk : ∀ k : ℕ, PaperSpec.A.WP D h𝒢₀ hind₀ T
      (min (lamStar T L + (k : ℝ) * zeta0 T L ‖GX G‖ (sMin G ^ 2)⁻¹ α β₁ β₂ (lamStar T L)) 1)
      C ξ₀ := by
    intro k
    induction k with
    | zero =>
      have e := h0
      push_cast at e ⊢
      rw [e]
      exact hwp _ hpos.le le_rfl
    | succ k ih =>
      have hstep' := hstep _ (hlow k) (min_le_right _ _) ih _ (sub_nonneg.mpr (hmono k))
        (hdiff k) (by rw [add_sub_cancel]; exact min_le_right _ _)
      rwa [add_sub_cancel] at hstep'
  refine ⟨hpos, hle, hz, hstep, hwp, h0, hdiff, hone, hwpk, ?_⟩
  have h1 := hone _ le_rfl
  rw [← h1]
  exact hwpk _

end Dissertation.Acceptance.A
