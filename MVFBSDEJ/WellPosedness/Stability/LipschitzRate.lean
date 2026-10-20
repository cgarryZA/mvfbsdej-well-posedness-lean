/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Stability.SampleEnergy

/-!
# The expected Lipschitz bound at almost every time

The expected Lipschitz bound (3.2) of the well-posedness paper, as recorded by the difference
system `PairDiff`, compares at almost every time `s` the expectation of the pointwise sum
`|δb_s|² + |δσ_s|²_F + ‖δh_s‖²_{L²(ν)} + |δf_s|²` with that of
`|δX_s|² + |δY_s|² + |δZ_s|²_F + ‖δU_s‖²_{L²(ν)}`. Since the lower integral is superadditive and,
for measurable integrands, additive, the bound passes to the sample energies of the coordinates:
the left side dominates the sum of the sample energies of the coefficient differences, and the
right side is the sum of the sample energies of the difference.

## Main statements

* `sum_lintegral_le` — the lower integral is superadditive over finite sums.
* `PairDiff.ae_lip` — (3.2) between sample energies at almost every time.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace MVFBSDEJ.WellPosedness.Stability

open LevyStochCalc.BSDEJ.Solves LevyStochCalc MVFBSDEJ.WellPosedness.BrownianPoisson

universe u v w

/-- The lower integral is superadditive over finite sums. -/
theorem sum_lintegral_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {ι : Type*}
    (s : Finset ι) (f : ι → α → ℝ≥0∞) : ∑ i ∈ s, ∫⁻ a, f i a ∂μ ≤ ∫⁻ a, ∑ i ∈ s, f i a ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (add_le_add le_rfl ih).trans (le_lintegral_add _ _)

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}

/-- Four lower integrals add up to at most the lower integral of the sum. -/
theorem lintegral_add_four_le (A B C D : Ω → ℝ≥0∞) :
    ∫⁻ ω, A ω ∂P + ∫⁻ ω, B ω ∂P + ∫⁻ ω, C ω ∂P + ∫⁻ ω, D ω ∂P
      ≤ ∫⁻ ω, (A ω + B ω + C ω + D ω) ∂P :=
  (add_le_add ((add_le_add (le_lintegral_add A B) le_rfl).trans (le_lintegral_add _ C))
    le_rfl).trans (le_lintegral_add _ D)

/-- The lower integral of a sum of four functions, three of them measurable. -/
theorem lintegral_add_four {A B C : Ω → ℝ≥0∞} (hA : Measurable A) (hB : Measurable B)
    (hC : Measurable C) (D : Ω → ℝ≥0∞) :
    ∫⁻ ω, (A ω + B ω + C ω + D ω) ∂P
      = ∫⁻ ω, A ω ∂P + ∫⁻ ω, B ω ∂P + ∫⁻ ω, C ω ∂P + ∫⁻ ω, D ω ∂P := by
  rw [lintegral_add_left (f := fun ω => A ω + B ω + C ω) ((hA.add hB).add hC),
    lintegral_add_left (f := fun ω => A ω + B ω) (hA.add hB), lintegral_add_left hA]

section PairDiff

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} {d n m : ℕ} [IsProbabilityMeasure P]
  [SigmaFinite ν]
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {T lam K KT α β₁ β₂ : ℝ}
  {G : Matrix (Fin m) (Fin n) ℝ} {ξ₀ : Fin n → Ω → ℝ}
  {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ}
  {Z : Fin m → ℝ → Ω → Fin d → ℝ} {U : Fin m → ℝ → Ω → E → ℝ}
  {b : Fin n → Ω → ℝ → ℝ} {σ : Fin n → ℝ → Ω → Fin d → ℝ} {h : Fin n → ℝ → Ω → E → ℝ}
  {f : Fin m → Ω → ℝ → ℝ} {g : Fin m → Ω → ℝ}
  {qb : Fin n → Ω → ℝ → ℝ} {qσ : Fin n → ℝ → Ω → Fin d → ℝ} {qh : Fin n → ℝ → Ω → E → ℝ}
  {qf : Fin m → Ω → ℝ → ℝ} {qg : Fin m → Ω → ℝ}

/-- **The expected Lipschitz bound (3.2) between sample energies.** At almost every time of the
horizon, the sample energy of the coefficient differences is at most `K` times that of the
difference, written as the part of `δX` plus the part of `(δY, δZ, δU)`. -/
theorem PairDiff.ae_lip
    (hD : PairDiff D ℱ hℱW hℱN T lam K KT α β₁ β₂ G ξ₀ X Y Z U b σ h f g qb qσ qh qf qg) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      sampleEnergy P b s + ∑ i, sampleEnergy P (fun j ω s => σ i s ω j) s
          + markedSampleEnergy P ν (fun i ω s e => h i s ω e) s + sampleEnergy P f s
        ≤ ENNReal.ofReal K * (sampleEnergy P (fun i ω s => X i s ω) s
          + (sampleEnergy P (fun k ω s => Y k s ω) s
            + ∑ k, sampleEnergy P (fun j ω s => Z k s ω j) s
            + markedSampleEnergy P ν (fun k ω s e => U k s ω e) s)) := by
  filter_upwards [hD.lip] with s hs
  have hsq : ∀ {u : Ω → ℝ}, Measurable u → Measurable fun ω => (‖u ω‖₊ : ℝ≥0∞) ^ 2 :=
    fun hu => hu.nnnorm.coe_nnreal_ennreal.pow_const 2
  have hX : ∀ i, Measurable (X i s) := fun i =>
    ((hD.fwd i).X_adapted s).mono (ℱ.le s) le_rfl
  have hY : ∀ k, Measurable (Y k s) := fun k =>
    ((hD.bwd k).Y_adapted s).mono (ℱ.le s) le_rfl
  have hZ : ∀ k j, Measurable fun ω => Z k s ω j := fun k j =>
    ((hD.bwd k).Z_meas j).comp (measurable_id.prodMk measurable_const)
  have hU : ∀ k, Measurable fun ω => ∫⁻ e, (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν := fun k =>
    (measurable_uncurry_lintegral_sq_mark (ν := ν) (φ := fun ω s e => U k s ω e)
      (hD.bwd k).U_meas).comp (measurable_id.prodMk measurable_const)
  refine le_trans ?_ (hs.trans (le_of_eq ?_))
  · simp only [sampleEnergy, markedSampleEnergy, esq]
    exact le_trans (add_le_add (add_le_add (add_le_add (sum_lintegral_le _ _)
      ((Finset.sum_le_sum fun i _ => sum_lintegral_le _ _).trans (sum_lintegral_le _ _)))
      (sum_lintegral_le _ _)) (sum_lintegral_le _ _)) (lintegral_add_four_le _ _ _ _)
  · simp only [sampleEnergy, markedSampleEnergy, esq]
    rw [lintegral_add_four (Finset.measurable_sum _ fun i _ => hsq (hX i))
        (Finset.measurable_sum _ fun k _ => hsq (hY k))
        (Finset.measurable_sum _ fun k _ => Finset.measurable_sum _ fun j _ => hsq (hZ k j)),
      lintegral_finsetSum' _ fun i _ => (hsq (hX i)).aemeasurable,
      lintegral_finsetSum' _ fun k _ => (hsq (hY k)).aemeasurable,
      lintegral_finsetSum' _ fun k _ =>
        (Finset.measurable_sum _ fun j _ => hsq (hZ k j)).aemeasurable,
      lintegral_finsetSum' _ fun k _ => (hU k).aemeasurable]
    simp only [lintegral_finsetSum' _ fun j _ => (hsq (hZ _ j)).aemeasurable, add_assoc]

end PairDiff

end MVFBSDEJ.WellPosedness.Stability
