/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Existence.Congr
import Dissertation.WellPosedness.Existence.WPZero
import Dissertation.WellPosedness.System.LawFlow

/-!
# Predictable versions of the martingale integrands of a solution

The solution space `𝕊` of the paper takes the integrands `Z` and `U` predictable, while the
solution predicate `SolvesForced` takes them progressively measurable and marked progressively
measurable. Every such integrand of finite energy agrees almost everywhere with a predictable one
(`LevyStochCalc.Probability.exists_predictable_ae_eq`,
`LevyStochCalc.Probability.exists_markedPredictable_ae_eq`); cut to `(0, T]`, the version still
vanishes off `[0, T]` and is progressively measurable. This file shows that replacing `(Z, U)` by
such versions `(Z', U')` gives again a solution, with the same `X`, `Y` and jump representative
`γ`.

* The stochastic integrals of `Z` and `Z'`, and of `U` and `U'`, agree almost surely at every
  time up to `T`, and so do the drift integrals of two drifts agreeing almost everywhere: the
  energy of their differences vanishes.
* The tuples `Θ = (X, Y, Z, U)` and `Θ' = (X, Y, Z', U')` agree `dP ⊗ ds`-almost everywhere, and
  their laws at almost every time (`ae_tupleAt_eq_of_ae_eq`), so the coefficient processes along
  them agree `dP ⊗ ds`-almost everywhere and `γ` represents the jump coefficient along `Θ'`.
* The coefficient processes along `Θ'` must still be jointly and progressively measurable, and the
  solution predicate constrains the coefficients only along `Θ`. This is (2.5) along `Θ'`, which the
  theorem takes from `Dissertation.WellPosedness.Existence.CoeffRegular`, (2.5) along every
  progressive tuple; that follows from the joint measurability (2.3) of the coefficients
  (`Dissertation.WellPosedness.Existence.CoeffBorel.coeffRegular`,
  `Dissertation.WellPosedness.Existence.CoeffBorelW2.toCoeffBorel`).

## Main statements

* `progressivelyMeasurable_indicator_Ioc` — a predictable process cut to `(0, T]` is
  progressively measurable.
* `energy_sub_eq_zero_of_ae_eq`, `markedEnergy_sub_eq_zero_of_ae_eq` — integrands agreeing almost
  everywhere differ by zero energy.
* `LinearBSDEJ.congr_integrands` — the linear backward equation is unchanged by a change of its
  drift and integrands of zero energy.
* `SolvesForced.exists_predictable` — a solution has predictable versions of `(Z, U)` with which
  it is again a solution.
-/

open MeasureTheory Filter Dissertation.Law
open scoped NNReal ENNReal

namespace Dissertation.WellPosedness.System

open Dissertation.WellPosedness.BrownianPoisson Dissertation.WellPosedness.Stability
  Dissertation.WellPosedness.Existence LevyStochCalc.BSDEJ.Solves LevyStochCalc

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]

/-! ### Predictable processes cut to the horizon -/

section Predictable

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

/-- For `t ≥ 0`, the inclusion of the time-truncated product into `ℝ × Ω` is measurable from the
`ℱ t`-product σ-algebra to the predictable σ-algebra. -/
private theorem measurable_inclusion_predictableSigma_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    @Measurable (Set.Iic t × Ω) (ℝ × Ω)
      (Subtype.instMeasurableSpace.prod (ℱ t)) (Probability.predictableSigma ℱ)
      (fun x => ((x.1 : ℝ), x.2)) := by
  letI : MeasurableSpace (Set.Iic t × Ω) := Subtype.instMeasurableSpace.prod (ℱ t)
  refine measurable_generateFrom ?_
  rintro - (⟨A, hA, rfl⟩ | ⟨r, A, hA, rfl⟩)
  · have hpre : (fun x : Set.Iic t × Ω => ((x.1 : ℝ), x.2)) ⁻¹' (Set.Iic (0 : ℝ) ×ˢ A)
        = (Subtype.val ⁻¹' Set.Iic (0 : ℝ)) ×ˢ A := by
      ext ⟨u, ω⟩; simp
    rw [hpre]
    exact (measurable_subtype_coe measurableSet_Iic).prod (ℱ.mono ht _ hA)
  · rcases le_or_gt r t with h | h
    · have hpre : (fun x : Set.Iic t × Ω => ((x.1 : ℝ), x.2)) ⁻¹' (Set.Ioi r ×ˢ A)
          = (Subtype.val ⁻¹' Set.Ioi r) ×ˢ A := by
        ext ⟨u, ω⟩; simp
      rw [hpre]
      exact (measurable_subtype_coe measurableSet_Ioi).prod (ℱ.mono h _ hA)
    · have hpre : (fun x : Set.Iic t × Ω => ((x.1 : ℝ), x.2)) ⁻¹' (Set.Ioi r ×ˢ A) = ∅ := by
        ext ⟨u, ω⟩
        have := u.2
        simp only [Set.mem_Iic] at this
        simp only [Set.mem_preimage, Set.mem_prod, Set.mem_Ioi, Set.mem_empty_iff_false,
          iff_false, not_and]
        intro hu
        exact absurd (hu.trans_le this) (not_lt.mpr h.le)
      rw [hpre]
      exact MeasurableSet.empty

/-- **A predictable process cut to `(0, T]` is progressively measurable**, for any filtration
indexed by `ℝ`. -/
theorem progressivelyMeasurable_indicator_Ioc {K : Ω → ℝ → ℝ}
    (hK : Probability.Predictable ℱ K) {T : ℝ} (hT : 0 ≤ T) :
    Probability.ProgressivelyMeasurable ℱ
      fun ω s => (Set.Ioc (0 : ℝ) T).indicator (fun _ => K ω s) s := by
  have hK' := Brownian.Ito.predictable_indicator_Ioc hK hT
  refine Probability.ProgressivelyMeasurable.of_isStronglyProgressive fun t => ?_
  rcases lt_or_ge t 0 with ht | ht
  · convert (stronglyMeasurable_const (b := (0 : ℝ))) using 1
    funext q
    exact Set.indicator_of_notMem
      (fun hq => absurd (hq.1.trans_le (q.1.2.trans ht.le)) (lt_irrefl 0)) _
  · letI : MeasurableSpace (ℝ × Ω) := Probability.predictableSigma ℱ
    letI : MeasurableSpace (Set.Iic t × Ω) := Subtype.instMeasurableSpace.prod (ℱ t)
    exact StronglyMeasurable.comp_measurable hK'
      (measurable_inclusion_predictableSigma_of_nonneg ht)

end Predictable

/-! ### Zero energy from almost-everywhere equality -/

section Energy

variable {P : Measure Ω} {ν : Measure E} {T : ℝ}

/-- Two jointly measurable integrands agreeing almost everywhere for the product of `P` with
Lebesgue measure on `[0, T]` differ by zero energy on `[0, T]`. -/
theorem energy_sub_eq_zero_of_ae_eq {H₁ H₂ : Ω → ℝ → ℝ}
    (hm₁ : Measurable (Function.uncurry H₁)) (hm₂ : Measurable (Function.uncurry H₂))
    (h : ∀ᵐ p ∂(Brownian.Ito.energyMeasure P T), H₁ p.1 p.2 = H₂ p.1 p.2) :
    Brownian.Ito.energy P T (fun ω s => H₁ ω s - H₂ ω s) = 0 := by
  rw [Brownian.Ito.energy_eq_eLpNorm_sq (H := fun ω s => H₁ ω s - H₂ ω s) (hm₁.sub hm₂)]
  have h0 : (fun p : Ω × ℝ => H₁ p.1 p.2 - H₂ p.1 p.2)
      =ᵐ[Brownian.Ito.energyMeasure P T] 0 :=
    h.mono fun p hp => by simp only [hp, sub_self, Pi.zero_apply]
  rw [eLpNorm_congr_ae h0, eLpNorm_zero]
  simp

/-- Two jointly measurable marked integrands agreeing almost everywhere for the product of `P`,
Lebesgue measure on `[0, T]` and `ν` differ by zero marked energy on `[0, T]`. -/
theorem markedEnergy_sub_eq_zero_of_ae_eq [SigmaFinite ν] {φ₁ φ₂ : Ω → ℝ → E → ℝ}
    (hm₁ : Measurable fun p : Ω × ℝ × E => φ₁ p.1 p.2.1 p.2.2)
    (hm₂ : Measurable fun p : Ω × ℝ × E => φ₂ p.1 p.2.1 p.2.2)
    (h : ∀ᵐ p ∂(Poisson.Compensated.markedEnergyMeasure P ν T),
      φ₁ p.1 p.2.1 p.2.2 = φ₂ p.1 p.2.1 p.2.2) :
    Poisson.Compensated.markedEnergy P ν T (fun ω s e => φ₁ ω s e - φ₂ ω s e) = 0 := by
  rw [Poisson.Compensated.markedEnergy_eq_eLpNorm_sq (φ := fun ω s e => φ₁ ω s e - φ₂ ω s e)
    (hm₁.sub hm₂)]
  have h0 : (fun p : Ω × ℝ × E => φ₁ p.1 p.2.1 p.2.2 - φ₂ p.1 p.2.1 p.2.2)
      =ᵐ[Poisson.Compensated.markedEnergyMeasure P ν T] 0 :=
    h.mono fun p hp => by simp only [hp, sub_self, Pi.zero_apply]
  rw [eLpNorm_congr_ae h0, eLpNorm_zero]
  simp

end Energy

/-! ### The linear backward equation under a change of integrands -/

variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {T : ℝ}

section Backward

variable {ξ : Ω → ℝ} {φ φ' : Ω → ℝ → ℝ} {Y : ℝ → Ω → ℝ} {Z Z' : ℝ → Ω → (Fin d → ℝ)}
  {U U' : ℝ → Ω → E → ℝ}

/-- **The linear backward equation is unchanged by a change of integrands of zero energy**: if
`(Y, Z, U)` solves it with terminal value `ξ` and drift `φ`, then `(Y, Z', U')` solves it with
terminal value `ξ` and drift `φ'`, for jointly measurable, progressive `φ'`, `Z'`, `U'` vanishing
off `[0, T]` such that `φ − φ'`, each coordinate of `Z − Z'` and `U − U'` have zero energy on
`[0, T]`. -/
theorem _root_.Dissertation.WellPosedness.BrownianPoisson.LinearBSDEJ.congr_integrands
    (h : LinearBSDEJ D ℱ hℱW hℱN T ξ φ Y Z U)
    (hφm : Measurable (Function.uncurry φ')) (hφp : Probability.ProgressivelyMeasurable ℱ φ')
    (hφv : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → φ' ω s = 0)
    (hZm : ∀ j : Fin d, Measurable (Function.uncurry fun ω s => Z' s ω j))
    (hZp : ∀ j : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s => Z' s ω j)
    (hZv : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → Z' s ω = 0)
    (hUm : Measurable fun p : Ω × ℝ × E => U' p.2.1 p.1 p.2.2)
    (hUp : Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => U' s ω e)
    (hUv : ∀ ω s e, s ∉ Set.Icc (0 : ℝ) T → U' s ω e = 0)
    (hφ : Brownian.Ito.energy P T (fun ω s => φ ω s - φ' ω s) = 0)
    (hZ : ∀ j : Fin d, Brownian.Ito.energy P T (fun ω s => Z s ω j - Z' s ω j) = 0)
    (hU : Poisson.Compensated.markedEnergy P ν T (fun ω s e => U s ω e - U' s ω e) = 0) :
    LinearBSDEJ D ℱ hℱW hℱN T ξ φ' Y Z' U' := by
  have hφq : Brownian.Ito.energy P T φ' ≠ ⊤ := by
    rw [energy_eq_of_energy_sub_eq_zero h.φ_meas hφm hφ]
    exact h.φ_sq
  have hZq : ∀ j : Fin d, Brownian.Ito.energy P T (fun ω s => Z' s ω j) ≠ ⊤ := fun j => by
    rw [energy_eq_of_energy_sub_eq_zero (H₁ := fun ω s => Z s ω j) (h.Z_meas j) (hZm j) (hZ j)]
    exact h.Z_sq j
  have hUq : Poisson.Compensated.markedEnergy P ν T (fun ω s e => U' s ω e) ≠ ⊤ := by
    rw [markedEnergy_eq_of_markedEnergy_sub_eq_zero (φ₁ := fun ω s e => U s ω e) h.U_meas hUm
      hU]
    exact h.U_sq
  refine
    { Z_meas := hZm
      Z_prog := hZp
      Z_vanish := hZv
      Z_sq := hZq
      U_meas := hUm
      U_prog := hUp
      U_vanish := hUv
      U_sq := hUq
      φ_meas := hφm
      φ_prog := hφp
      φ_vanish := hφv
      φ_sq := hφq
      ξ_sq := h.ξ_sq
      Y_adapted := h.Y_adapted
      Y_rightCont := h.Y_rightCont
      eqn := fun t ht => ?_ }
  have hBr : ∀ {r : ℝ}, r ≤ T →
      Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hℱW Z h.Z_meas h.Z_prog
          (sq_int_global_of_vanishing h.Z_vanish h.Z_sq) r
        =ᵐ[P] Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hℱW Z' hZm hZp
          (sq_int_global_of_vanishing hZv hZq) r := fun hr =>
    multidimStochasticIntegral_congr_of_energy D.W hℱW h.Z_meas h.Z_prog
      (sq_int_global_of_vanishing h.Z_vanish h.Z_sq) hZm hZp
      (sq_int_global_of_vanishing hZv hZq) hZ hr
  have hPo : ∀ {r : ℝ}, r ≤ T →
      Poisson.Compensated.stochasticIntegral D.N ℱ hℱN (fun ω' s e => U s ω' e) h.U_meas
          h.U_prog (marked_sq_int_global_of_vanishing h.U_vanish h.U_sq) r
        =ᵐ[P] Poisson.Compensated.stochasticIntegral D.N ℱ hℱN (fun ω' s e => U' s ω' e) hUm
          hUp (marked_sq_int_global_of_vanishing hUv hUq) r := fun hr =>
    compensatedIntegral_congr_of_markedEnergy D.N hℱN (φ₁ := fun ω s e => U s ω e)
      (φ₂ := fun ω s e => U' s ω e) h.U_meas h.U_prog
      (marked_sq_int_global_of_vanishing h.U_vanish h.U_sq) hUm hUp
      (marked_sq_int_global_of_vanishing hUv hUq) hU hr
  filter_upwards [h.eqn t ht,
    ae_setIntegral_congr_of_energy h.φ_meas hφm hφ (Set.Icc_subset_Icc ht.1 le_rfl),
    hBr (le_refl T), hBr ht.2, hPo (le_refl T), hPo ht.2] with ω e1 e2 e3 e4 e5 e6
  rw [e1, e2, e3, e4, e5, e6]

end Backward

/-! ### Predictable versions of a solution -/

variable [MeasurableSpace.CountablyGenerated E] {n m : ℕ} {lam : ℝ} {C : Coeffs ν n m d}
  {ξ₀ : Fin n → Ω → ℝ} {qb : Fin n → Ω → ℝ → ℝ} {qσ : Fin n → ℝ → Ω → Fin d → ℝ}
  {qh : Fin n → ℝ → Ω → E → ℝ} {qf : Fin m → Ω → ℝ → ℝ} {qg : Fin m → Ω → ℝ}
  {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ} {Z : Fin m → ℝ → Ω → Fin d → ℝ}
  {U : Fin m → ℝ → Ω → E → ℝ} {γ : Fin n → ℝ → Ω → E → ℝ}

/-- **A solution has predictable martingale integrands, up to versions.** Let `(X, Y, Z, U)` solve
the `λ`-forced system (4.1) with jump representative `γ`, for coefficients with (2.5) along every
progressive tuple, and `T > 0`. Then there are `Z'` predictable and `U'` marked predictable,
coordinatewise, with `Z = Z'` `dP ⊗ ds`-almost everywhere on `Ω × [0, T]` and `U = U'`
`dP ⊗ ds ⊗ ν`-almost everywhere on `Ω × [0, T] × E`, such that `(X, Y, Z', U')` solves the same
system with the same forcing and the same `γ`. The stochastic integrals of `Z'` and `U'` are then
those of `Z` and `U`, almost surely at every time up to `T`. -/
theorem SolvesForced.exists_predictable
    (h : SolvesForced D ℱ hℱW hℱN T lam C ξ₀ qb qσ qh qf qg X Y Z U γ)
    (hC : CoeffRegular ℱ P T C) (hT : 0 < T) :
    ∃ (Z' : Fin m → ℝ → Ω → Fin d → ℝ) (U' : Fin m → ℝ → Ω → E → ℝ),
      (∀ k j, Probability.Predictable ℱ fun ω s => Z' k s ω j)
      ∧ (∀ k, Probability.MarkedPredictable ℱ ν fun ω s e => U' k s ω e)
      ∧ (∀ k j, ∀ᵐ p ∂(Brownian.Ito.energyMeasure P T), Z k p.2 p.1 j = Z' k p.2 p.1 j)
      ∧ (∀ k, ∀ᵐ q ∂(Poisson.Compensated.markedEnergyMeasure P ν T),
          U k q.2.1 q.1 q.2.2 = U' k q.2.1 q.1 q.2.2)
      ∧ SolvesForced D ℱ hℱW hℱN T lam C ξ₀ qb qσ qh qf qg X Y Z' U' γ := by
  choose K hKpred hKae using fun (k : Fin m) (j : Fin d) =>
    Probability.exists_predictable_ae_eq ℱ ((h.bwd k).Z_meas j) ((h.bwd k).Z_prog j) hT
      ((h.bwd k).Z_sq j)
  choose ψ hψpred hψae using fun k : Fin m =>
    Probability.exists_markedPredictable_ae_eq D.N (h.bwd k).U_meas (h.bwd k).U_prog hT
      (h.bwd k).U_sq
  set Z' : Fin m → ℝ → Ω → Fin d → ℝ :=
    fun k s ω j => (Set.Ioc (0 : ℝ) T).indicator (fun _ => K k j ω s) s with hZ'def
  set U' : Fin m → ℝ → Ω → E → ℝ :=
    fun k s ω e => (Set.Ioc (0 : ℝ) T).indicator (fun _ => ψ k ω s e) s with hU'def
  -- the versions
  have hZpred : ∀ k j, Probability.Predictable ℱ fun ω s => Z' k s ω j := fun k j =>
    Brownian.Ito.predictable_indicator_Ioc (hKpred k j) hT.le
  have hUpred : ∀ k, Probability.MarkedPredictable ℱ ν fun ω s e => U' k s ω e := fun k =>
    Poisson.Compensated.markedPredictable_indicator_Ioc (hψpred k) T
  have hZae : ∀ k j, ∀ᵐ p ∂(Brownian.Ito.energyMeasure P T), Z k p.2 p.1 j = Z' k p.2 p.1 j :=
    fun k j => by
      filter_upwards [hKae k j, Brownian.Ito.ae_mem_Ioc_energyMeasure (P := P) hT.le]
        with p hp hIoc
      exact hp.trans (Set.indicator_of_mem hIoc fun _ => K k j p.1 p.2).symm
  have hUae : ∀ k, ∀ᵐ q ∂(Poisson.Compensated.markedEnergyMeasure P ν T),
      U k q.2.1 q.1 q.2.2 = U' k q.2.1 q.1 q.2.2 := fun k => by
    filter_upwards [hψae k,
      Poisson.Compensated.ae_mem_Ioc_markedEnergyMeasure (P := P) (ν := ν) hT.le] with q hq hIoc
    exact hq.trans (Set.indicator_of_mem hIoc fun _ => ψ k q.1 q.2.1 q.2.2).symm
  -- their regularity
  have hZm : ∀ k j, Measurable (Function.uncurry fun ω s => Z' k s ω j) := fun k j =>
    Brownian.Ito.measurable_uncurry_of_predictable (hZpred k j)
  have hZp : ∀ k j, Probability.ProgressivelyMeasurable ℱ fun ω s => Z' k s ω j := fun k j =>
    progressivelyMeasurable_indicator_Ioc (hKpred k j) hT.le
  have hZv : ∀ k ω s, s ∉ Set.Icc (0 : ℝ) T → Z' k s ω = 0 := fun k ω s hs => by
    funext j
    exact Set.indicator_of_notMem (fun hs' => hs ⟨hs'.1.le, hs'.2⟩) _
  have hZ0 : ∀ k j, Brownian.Ito.energy P T (fun ω s => Z k s ω j - Z' k s ω j) = 0 :=
    fun k j => energy_sub_eq_zero_of_ae_eq ((h.bwd k).Z_meas j) (hZm k j) (hZae k j)
  have hZq : ∀ k j, Brownian.Ito.energy P T (fun ω s => Z' k s ω j) ≠ ⊤ := fun k j => by
    rw [energy_eq_of_energy_sub_eq_zero (H₁ := fun ω s => Z k s ω j) ((h.bwd k).Z_meas j)
      (hZm k j) (hZ0 k j)]
    exact (h.bwd k).Z_sq j
  have hUm : ∀ k, Measurable fun p : Ω × ℝ × E => U' k p.2.1 p.1 p.2.2 := fun k =>
    (hUpred k).mono (Probability.markedPredictableSigma_le ℱ ν) le_rfl
  have hUp : ∀ k, Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => U' k s ω e :=
    fun k => (hUpred k).markedProgressivelyMeasurable
  have hUv : ∀ k ω s e, s ∉ Set.Icc (0 : ℝ) T → U' k s ω e = 0 := fun k ω s e hs =>
    Set.indicator_of_notMem (fun hs' => hs ⟨hs'.1.le, hs'.2⟩) _
  have hU0 : ∀ k, Poisson.Compensated.markedEnergy P ν T
      (fun ω s e => U k s ω e - U' k s ω e) = 0 := fun k =>
    markedEnergy_sub_eq_zero_of_ae_eq (φ₁ := fun ω s e => U k s ω e)
      (φ₂ := fun ω s e => U' k s ω e) (h.bwd k).U_meas (hUm k) (hUae k)
  have hUq : ∀ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U' k s ω e) ≠ ⊤ :=
    fun k => by
      rw [markedEnergy_eq_of_markedEnergy_sub_eq_zero (φ₁ := fun ω s e => U k s ω e)
        (h.bwd k).U_meas (hUm k) (hU0 k)]
      exact (h.bwd k).U_sq
  -- (2.5) along the new tuple
  have hΘ : ProgTuple ℱ P ν T X Y Z' U' :=
    { X_adapted := fun i => (h.fwd i).X_adapted
      X_rightCont := fun i => (h.fwd i).X_rightCont
      Y_adapted := fun k => (h.bwd k).Y_adapted
      Y_rightCont := fun k => (h.bwd k).Y_rightCont
      Z_meas := hZm
      Z_prog := hZp
      Z_sq := hZq
      U_meas := hUm
      U_prog := hUp
      U_sq := hUq }
  obtain ⟨γ', hX⟩ := hC X Y Z' U' hΘ
  -- the tuples, their laws and the coefficient processes agree almost everywhere
  have hΘae : ∀ᵐ p ∂(Brownian.Ito.energyMeasure P T),
      tupleAt ν X Y Z U p.2 p.1 = tupleAt ν X Y Z' U' p.2 p.1 :=
    ae_tupleAt_eq_of_ae_eq hZae hUae
  have hΘs := ae_ae_tupleAt_eq_of_ae_eq (X := X) (Y := Y) hZae hUae
  have hμae : ∀ᵐ p ∂(Brownian.Ito.energyMeasure P T),
      lawP2 P (tupleAt ν X Y Z U p.2) = lawP2 P (tupleAt ν X Y Z' U' p.2) := by
    rw [Brownian.Ito.energyMeasure]
    exact ae_prod_of_ae_snd (hΘs.mono fun _ hs => lawP2_congr hs)
  have hb : ∀ i, ∀ᵐ p ∂(Brownian.Ito.energyMeasure P T),
      lam * driftProc P T C X Y Z U i p.1 p.2 + qb i p.1 p.2
        = lam * driftProc P T C X Y Z' U' i p.1 p.2 + qb i p.1 p.2 := fun i => by
    filter_upwards [hΘae, hμae] with p h1 h2
    simp only [driftProc, Set.indicator_apply, h1, h2]
  have hσ : ∀ i j, ∀ᵐ p ∂(Brownian.Ito.energyMeasure P T),
      lam * diffusionProc P T C X Y Z U i p.2 p.1 j + qσ i p.2 p.1 j
        = lam * diffusionProc P T C X Y Z' U' i p.2 p.1 j + qσ i p.2 p.1 j := fun i j => by
    filter_upwards [hΘae, hμae] with p h1 h2
    simp only [diffusionProc, Set.indicator_apply, h1, h2]
  have hf : ∀ k, ∀ᵐ p ∂(Brownian.Ito.energyMeasure P T),
      lam * driverProc P T C X Y Z U k p.1 p.2 + qf k p.1 p.2
        = lam * driverProc P T C X Y Z' U' k p.1 p.2 + qf k p.1 p.2 := fun k => by
    filter_upwards [hΘae, hμae] with p h1 h2
    simp only [driverProc, Set.indicator_apply, h1, h2]
  -- regularity of the new coefficient processes
  have hbm : ∀ i, Measurable (Function.uncurry fun ω s =>
      lam * driftProc P T C X Y Z' U' i ω s + qb i ω s) := fun i =>
    (measurable_const.mul (hX.b_meas i)).add (h.forcing.qb_meas i)
  have hbp : ∀ i, Probability.ProgressivelyMeasurable ℱ fun ω s =>
      lam * driftProc P T C X Y Z' U' i ω s + qb i ω s := fun i =>
    ((hX.b_prog i).comp_continuous (continuous_const.mul continuous_id) (mul_zero lam)).add
      (h.forcing.qb_prog i)
  have hσm : ∀ i j, Measurable (Function.uncurry fun ω s =>
      lam * diffusionProc P T C X Y Z' U' i s ω j + qσ i s ω j) := fun i j =>
    (measurable_const.mul (hX.σ_meas i j)).add (h.forcing.qσ_meas i j)
  have hσp : ∀ i j, Probability.ProgressivelyMeasurable ℱ fun ω s =>
      lam * diffusionProc P T C X Y Z' U' i s ω j + qσ i s ω j := fun i j =>
    ((hX.σ_prog i j).comp_continuous (continuous_const.mul continuous_id) (mul_zero lam)).add
      (h.forcing.qσ_prog i j)
  have hfm : ∀ k, Measurable (Function.uncurry fun ω s =>
      lam * driverProc P T C X Y Z' U' k ω s + qf k ω s) := fun k =>
    (measurable_const.mul (hX.f_meas k)).add (h.forcing.qf_meas k)
  have hfp : ∀ k, Probability.ProgressivelyMeasurable ℱ fun ω s =>
      lam * driverProc P T C X Y Z' U' k ω s + qf k ω s := fun k =>
    ((hX.f_prog k).comp_continuous (continuous_const.mul continuous_id) (mul_zero lam)).add
      (h.forcing.qf_prog k)
  refine ⟨Z', U', hZpred, hUpred, hZae, hUae, ?_⟩
  refine
    { forcing := h.forcing
      jump_rep := ?_
      fwd := fun i => (h.fwd i).congr (hbm i) (hbp i) ?_ (hσm i) (hσp i) ?_ (h.fwd i).γ_meas
        (h.fwd i).γ_prog (h.fwd i).γ_vanish
        (energy_sub_eq_zero_of_ae_eq (h.fwd i).b_meas (hbm i) (hb i))
        (fun j => energy_sub_eq_zero_of_ae_eq ((h.fwd i).σ_meas j) (hσm i j) (hσ i j)) ?_
      bwd := fun k => (h.bwd k).congr_integrands (hfm k) (hfp k) ?_ (hZm k) (hZp k) (hZv k)
        (hUm k) (hUp k) (hUv k)
        (energy_sub_eq_zero_of_ae_eq (h.bwd k).φ_meas (hfm k) (hf k)) (hZ0 k) (hU0 k) }
  · filter_upwards [h.jump_rep, hΘs] with s hs heq
    filter_upwards [hs, heq] with ω hω hωeq
    rw [← hωeq, ← lawP2_congr heq]
    exact hω
  · intro ω s hs
    simp [driftProc, Set.indicator_of_notMem hs, h.forcing.qb_vanish i ω s hs]
  · intro ω s hs
    funext j
    simp [diffusionProc, Set.indicator_of_notMem hs, h.forcing.qσ_vanish i ω s hs]
  · simp [Poisson.Compensated.markedEnergy]
  · intro ω s hs
    simp [driverProc, Set.indicator_of_notMem hs, h.forcing.qf_vanish k ω s hs]

end Dissertation.WellPosedness.System
