/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-!
# A jointly measurable representative of the elements of `L²`

Each element `u` of `L²(ν; V)` is a class of functions; this file chooses a representative of
every class at once, jointly measurably in the class and the point. For a separable `L²(ν; V)`
with its Borel σ-algebra there is a strongly measurable `Φ : L²(ν; V) × E → V` with
`Φ(u, ·) = u` `ν`-almost everywhere for every `u`, and `Φ(0, ·) = 0`.

The construction fixes a dense sequence `(d_k)` of `L²(ν; V)` together with representatives of
its terms. For `u ∈ L²(ν; V)` let `κ_j(u)` be the least `k` with `‖u − d_k‖ < 2^{-j}`; it is
measurable in `u`, and `g_j(u, e) = d_{κ_j(u)}(e)` is jointly measurable. Since
`∫ ∑_j |g_j(u, e) − u(e)|² ν(de) ≤ ∑_j 4^{-j} < ∞`, the sequence `g_j(u, ·)` converges to `u`
at `ν`-almost every point, and `Φ` is its limit where it converges, set to `0` at `u = 0`.

## Main definitions

* `MVFBSDEJ.Law.lpRep`: a jointly measurable representative of the elements of `L²(ν; V)`.

## Main statements

* `MVFBSDEJ.Law.Lp.exists_stronglyMeasurable_rep`: the existence of such a representative.
* `MVFBSDEJ.Law.stronglyMeasurable_lpRep`, `MVFBSDEJ.Law.lpRep_ae_eq`,
  `MVFBSDEJ.Law.lpRep_zero`: `lpRep` is strongly measurable, represents every element and
  vanishes at `0`.
-/

namespace MVFBSDEJ.Law

open MeasureTheory Filter Topology
open scoped ENNReal

variable {E : Type*} {mE : MeasurableSpace E} {ν : Measure E}
  {V : Type*} [NormedAddCommGroup V] [CompleteSpace V] [MeasurableSpace V] [BorelSpace V]
  [SecondCountableTopology V]

omit [CompleteSpace V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] in
/-- The square of the `L²` seminorm is the lower integral of the squared norm. -/
private theorem eLpNorm_two_sq_eq_lintegral (f : E → V) :
    eLpNorm f 2 ν ^ 2 = ∫⁻ e, ‖f e‖ₑ ^ 2 ∂ν := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := ν) (p := 2) two_ne_zero
  simpa only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_two] using h

/-- **A jointly measurable representative of the elements of `L²`.** For a separable `L²(ν; V)`
with its Borel σ-algebra there is a strongly measurable `Φ : L²(ν; V) × E → V` with
`Φ(u, ·) = u` `ν`-almost everywhere for every `u` and `Φ(0, e) = 0` for every `e`. -/
theorem Lp.exists_stronglyMeasurable_rep [TopologicalSpace.SeparableSpace (Lp V 2 ν)]
    [MeasurableSpace (Lp V 2 ν)] [BorelSpace (Lp V 2 ν)] :
    ∃ Φ : Lp V 2 ν × E → V, StronglyMeasurable Φ ∧ (∀ u, (fun e => Φ (u, e)) =ᵐ[ν] u)
      ∧ ∀ e, Φ (0, e) = 0 := by
  classical
  obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq (Lp V 2 ν)
  have hex : ∀ (j : ℕ) (u : Lp V 2 ν), ∃ k, dist u (d k) < (2⁻¹ : ℝ) ^ j :=
    fun j u => hd.exists_dist_lt u (by positivity)
  set κ : ℕ → Lp V 2 ν → ℕ := fun j u => Nat.find (hex j u) with hκ_def
  have hκ : ∀ j, Measurable (κ j) := fun j =>
    measurable_find (hex j) fun k =>
      measurableSet_lt (continuous_id.dist continuous_const).measurable measurable_const
  set g : ℕ → Lp V 2 ν × E → V := fun j p => (d (κ j p.1) : E → V) p.2 with hg_def
  have hdm : Measurable fun q : E × ℕ => (d q.2 : E → V) q.1 :=
    measurable_from_prod_countable_left fun k => (Lp.stronglyMeasurable (d k)).measurable
  have hg : ∀ j, StronglyMeasurable (g j) := fun j =>
    (hdm.comp (measurable_snd.prodMk ((hκ j).comp measurable_fst))).stronglyMeasurable
  set Ψ : Lp V 2 ν × E → V := fun p => limUnder atTop fun j => g j p with hΨ_def
  have hΨ : StronglyMeasurable Ψ := StronglyMeasurable.limUnder hg
  have hrep : ∀ u, (fun e => Ψ (u, e)) =ᵐ[ν] u := by
    intro u
    have hsq : ∀ j, ∫⁻ e, ‖(d (κ j u) : E → V) e - u e‖ₑ ^ 2 ∂ν ≤ (4⁻¹ : ℝ≥0∞) ^ j := by
      intro j
      have hk : dist u (d (κ j u)) < (2⁻¹ : ℝ) ^ j := Nat.find_spec (hex j u)
      have hfin : eLpNorm ((d (κ j u) : E → V) - (u : E → V)) 2 ν ≠ ⊤ :=
        ((Lp.memLp _).sub (Lp.memLp _)).eLpNorm_ne_top
      have hle : eLpNorm ((d (κ j u) : E → V) - (u : E → V)) 2 ν
          ≤ ENNReal.ofReal ((2⁻¹ : ℝ) ^ j) := by
        rw [dist_comm, Lp.dist_def] at hk
        rw [← ENNReal.ofReal_toReal hfin]
        exact ENNReal.ofReal_le_ofReal hk.le
      have h2 := eLpNorm_two_sq_eq_lintegral (ν := ν) ((d (κ j u) : E → V) - (u : E → V))
      simp only [Pi.sub_apply] at h2
      rw [← h2]
      calc eLpNorm ((d (κ j u) : E → V) - (u : E → V)) 2 ν ^ 2
          ≤ ENNReal.ofReal ((2⁻¹ : ℝ) ^ j) ^ 2 := by gcongr
        _ = (4⁻¹ : ℝ≥0∞) ^ j := by
          rw [← ENNReal.ofReal_pow (by positivity), ← pow_mul, mul_comm, pow_mul]
          norm_num
          congr 1
          rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
          norm_num
    have hmeas : ∀ j, Measurable fun e => ‖(d (κ j u) : E → V) e - u e‖ₑ ^ 2 := fun j =>
      (((Lp.stronglyMeasurable _).measurable.sub
        (Lp.stronglyMeasurable u).measurable).enorm).pow_const 2
    have hsum : ∫⁻ e, ∑' j, ‖(d (κ j u) : E → V) e - u e‖ₑ ^ 2 ∂ν ≠ ⊤ := by
      rw [lintegral_tsum fun j => (hmeas j).aemeasurable]
      refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hsq)
      rw [ENNReal.tsum_geometric]
      exact ENNReal.inv_ne_top.mpr (tsub_pos_of_lt (by norm_num : (4⁻¹ : ℝ≥0∞) < 1)).ne'
    filter_upwards [ae_lt_top (Measurable.tsum hmeas) hsum] with e he
    have h0 := ENNReal.tendsto_atTop_zero_of_tsum_ne_top he.ne
    have h1 : Tendsto (fun j => ‖(d (κ j u) : E → V) e - u e‖ₑ) atTop (𝓝 0) := by
      have := (ENNReal.continuous_rpow_const (y := (2⁻¹ : ℝ))).tendsto 0 |>.comp h0
      simp only [Function.comp_def, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)]
        at this
      refine this.congr fun j => ?_
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      norm_num
    have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    simp only [Function.comp_def, toReal_enorm, ENNReal.toReal_zero] at h2
    exact (tendsto_iff_norm_sub_tendsto_zero.mpr h2).limUnder_eq
  set S : Set (Lp V 2 ν × E) := Prod.fst ⁻¹' ({0}ᶜ : Set (Lp V 2 ν)) with hS_def
  refine ⟨S.indicator Ψ, hΨ.indicator (measurable_fst (measurableSet_singleton 0).compl),
    fun u => ?_, fun e => ?_⟩
  · by_cases hu : u = 0
    · subst hu
      filter_upwards [Lp.coeFn_zero V 2 ν] with e he
      rw [he, Set.indicator_of_notMem (by simp [hS_def])]
      rfl
    · filter_upwards [hrep u] with e he
      rw [Set.indicator_of_mem (show (u, e) ∈ S by simp [hS_def, hu]), he]
  · exact Set.indicator_of_notMem (by simp [hS_def]) _

variable (ν V) in
/-- A jointly measurable representative of the elements of a separable `L²(ν; V)`: a strongly
measurable `Φ : L²(ν; V) × E → V` with `Φ(u, ·) = u` `ν`-almost everywhere for every `u` and
`Φ(0, ·) = 0`, measurable for the Borel σ-algebra of `L²(ν; V)`. -/
noncomputable def lpRep [TopologicalSpace.SeparableSpace (Lp V 2 ν)] : Lp V 2 ν × E → V :=
  letI : MeasurableSpace (Lp V 2 ν) := borel _
  haveI : BorelSpace (Lp V 2 ν) := ⟨rfl⟩
  Classical.choose (Lp.exists_stronglyMeasurable_rep (ν := ν) (V := V))

variable [TopologicalSpace.SeparableSpace (Lp V 2 ν)]

/-- The representative `lpRep` is strongly measurable for the Borel σ-algebra of `L²(ν; V)`. -/
theorem stronglyMeasurable_lpRep [MeasurableSpace (Lp V 2 ν)] [hB : BorelSpace (Lp V 2 ν)] :
    StronglyMeasurable (lpRep ν V) := by
  obtain ⟨h⟩ := hB
  subst h
  letI : MeasurableSpace (Lp V 2 ν) := borel _
  haveI : BorelSpace (Lp V 2 ν) := ⟨rfl⟩
  exact (Classical.choose_spec (Lp.exists_stronglyMeasurable_rep (ν := ν) (V := V)
    (mE := mE))).1

/-- The representative `lpRep` represents every element of `L²(ν; V)`. -/
theorem lpRep_ae_eq (u : Lp V 2 ν) : (fun e => lpRep ν V (u, e)) =ᵐ[ν] u :=
  letI : MeasurableSpace (Lp V 2 ν) := borel _
  haveI : BorelSpace (Lp V 2 ν) := ⟨rfl⟩
  (Classical.choose_spec (Lp.exists_stronglyMeasurable_rep (ν := ν) (V := V))).2.1 u

/-- The representative `lpRep` vanishes at `0`. -/
theorem lpRep_zero (e : E) : lpRep ν V (0, e) = 0 :=
  letI : MeasurableSpace (Lp V 2 ν) := borel _
  haveI : BorelSpace (Lp V 2 ν) := ⟨rfl⟩
  (Classical.choose_spec (Lp.exists_stronglyMeasurable_rep (ν := ν) (V := V))).2.2 e

end MVFBSDEJ.Law
