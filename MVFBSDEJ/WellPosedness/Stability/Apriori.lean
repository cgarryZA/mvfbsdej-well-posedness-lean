/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Stability.SupUpgrade
import MVFBSDEJ.WellPosedness.Stability.RankBlocks
import MVFBSDEJ.WellPosedness.Stability.Closure
import MVFBSDEJ.WellPosedness.Stability.ForwardEstimate
import MVFBSDEJ.WellPosedness.Stability.BackwardEstimate

/-!
# The a-priori estimate (4.14) of Lemma 4.3

Lemma 4.3 of the well-posedness paper bounds the difference `(δX, δY, δZ, δU)` of two solutions
of the `λ`-scaled forced system (4.1), `λ ∈ [λ̲, 1]`, by the differences of their data:

`𝔼 sup_{t ≤ T} |δX_t|² + 𝔼 sup_{t ≤ T} |δY_t|² + 𝔼 ∫_0^T (|δZ_t|²_F + ‖δU_t‖²_{L²(ν)}) dt
  ≤ C_B (𝔼|δξ₀|² + 𝔼|δq^g_T|² + 𝔼 ∫_0^T (|δq^b|² + |δq^σ|²_F + ‖δq^h‖² + |δq^f|²) dt)`. (4.14)

Over the difference system `PairDiff`, the forward and backward estimates, the coercivity bound
(4.22) and the rank case of Assumption 2.4 close through Step 5 on the time-integrated size:
`N' ≤ C_cl P`, with `C_cl = closureConst k_F k_B ‖G‖ c_G α β₁ β₂ λ̲`,
`k_F = 2 (K + 1) e^{(2 + 2K) T}` and `k_B = 4 (K + K_T + 1) e^{(4K + 2) T}`. The supremum upgrade
`N ≤ c_S (N' + P)`, `c_S = 6 (T + 4) (K + 1)`, then gives (4.14) with

`C_B = c_S (C_cl + 1)`,

which depends only on `T, K, K_T, ‖G‖, c_G, α, β₁, β₂` and `λ̲`. The Burkholder–Davis–Gundy
constant does not enter: the running suprema are controlled by Doob's `L²` maximal inequality.
With zero data the differences vanish: `δX` and `δY` are indistinguishable from `0` on `[0, T]`,
and `δZ`, `δU` have zero energy.

The estimate holds over any filtration carrying the driver whose null sets lie in its time-`0`
field, whose right-continuation is constant before `0`, and which admits a cross witness, the
setting of Lemma 4.1. The coupling matrix enters through a bound `|G x|² ≤ g² |x|²`; every matrix
admits one, with `g²` the squared Frobenius norm.

## Main definitions

* `aprioriConst` — the constant `C_B = c_S (C_cl + 1)` of (4.14).

## Main statements

* `PairDiff.toReal_diffSize_le` — Step 5: `N' ≤ C_cl P`.
* `PairDiff.apriori` — the estimate (4.14).
* `PairDiff.eq_zero` — zero data forces the differences to vanish.
* `exists_mulVec_dotProduct_le` — `|G x|² ≤ ‖G‖²_F |x|²`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped NNReal ENNReal

namespace MVFBSDEJ.WellPosedness.Stability

open LevyStochCalc.BSDEJ.Solves LevyStochCalc MVFBSDEJ.WellPosedness.BrownianPoisson

universe u v w

/-! ### The constant -/

/-- The constant `C_B = c_S (C_cl + 1)` of (4.14), with `c_S = 6 (T + 4) (K + 1)` the constant of
the supremum upgrade and `C_cl` the closure constant at the forward and backward constants
`k_F = 2 (K + 1) e^{(2 + 2K) T}` and `k_B = 4 (K + K_T + 1) e^{(4K + 2) T}`. -/
noncomputable def aprioriConst (T K KT gG cG α β₁ β₂ lamLow : ℝ) : ℝ :=
  supConst T K
    * (closureConst (forwardConst T K) (backwardConst T K KT) gG cG α β₁ β₂ lamLow + 1)

/-- The closure constant is nonnegative for nonnegative `k_F, k_B, c_G, α, β₁, β₂` and
`λ̲ > 0`. -/
theorem closureConst_nonneg {kF kB gG cG α β₁ β₂ lamLow : ℝ} (hkF : 0 ≤ kF) (hkB : 0 ≤ kB)
    (hcG : 0 ≤ cG) (hα : 0 ≤ α) (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂) (hlow : 0 < lamLow) :
    0 ≤ closureConst kF kB gG cG α β₁ β₂ lamLow := by
  unfold closureConst
  exact add_nonneg
    (absorbConst_nonneg (by positivity) (div_nonneg hcG (mul_nonneg hlow.le hβ₁)) gG)
    (absorbConst_nonneg (by positivity) (div_nonneg hcG (mul_nonneg hlow.le (le_min hα hβ₂)))
      gG)

section Constant

variable {T K KT gG cG α β₁ β₂ lamLow : ℝ}

/-- The constant of (4.14) is positive. -/
theorem aprioriConst_pos (hT : 0 ≤ T) (hK : 0 ≤ K) (hKT : 0 ≤ KT) (hcG : 0 ≤ cG) (hα : 0 ≤ α)
    (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂) (hlow : 0 < lamLow) :
    0 < aprioriConst T K KT gG cG α β₁ β₂ lamLow := by
  have hC := closureConst_nonneg (gG := gG) (forwardConst_nonneg hK T)
    (backwardConst_nonneg hK hKT T) hcG hα hβ₁ hβ₂ hlow
  unfold aprioriConst supConst
  positivity

end Constant

/-! ### A bound for the coupling matrix -/

/-- Every coupling matrix satisfies `|G x|² ≤ g² |x|²` for some `g`, for instance the Frobenius
norm of `G`. -/
theorem exists_mulVec_dotProduct_le {n m : ℕ} (G : Matrix (Fin m) (Fin n) ℝ) :
    ∃ g : ℝ, ∀ x : Fin n → ℝ, (G *ᵥ x) ⬝ᵥ (G *ᵥ x) ≤ g ^ 2 * (x ⬝ᵥ x) := by
  have hF : 0 ≤ ∑ k, ∑ i, G k i ^ 2 := by positivity
  refine ⟨Real.sqrt (∑ k, ∑ i, G k i ^ 2), fun x => ?_⟩
  rw [Real.sq_sqrt hF, Finset.sum_mul]
  unfold dotProduct mulVec dotProduct
  refine Finset.sum_le_sum fun k _ => ?_
  have hx : ∑ i, x i * x i = ∑ i, x i ^ 2 := by simp only [sq]
  rw [hx, ← sq]
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-! ### Vanishing of the running supremum -/

section Vanish

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}

/-- If the running supremum over `[0, T]` of a sum of squares of right-continuous processes has
zero expectation, each process vanishes on `[0, T]` almost surely. -/
theorem ae_forall_eq_zero_of_lintegral_biSup_esq {ι : Type*} [Fintype ι] {x : ι → ℝ → Ω → ℝ}
    {T : ℝ} (hT : 0 ≤ T) (hm : ∀ i t, Measurable (x i t))
    (hrc : ∀ i ω t, Tendsto (fun s => x i s ω) (𝓝[>] t) (𝓝 (x i t ω)))
    (h0 : ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => x i t ω)) ∂P = 0) (i : ι) :
    ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, x i t ω = 0 := by
  have hmeas := measurable_biSup_sq_of_rightContinuous hT (hm i) (hrc i)
  have hi : ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖x i t ω‖₊ : ℝ≥0∞) ^ 2) ∂P = 0 := by
    refine le_antisymm (h0 ▸ lintegral_mono fun ω => iSup₂_mono fun t _ => ?_) zero_le
    exact Finset.single_le_sum (f := fun j => (‖x j t ω‖₊ : ℝ≥0∞) ^ 2)
      (fun _ _ => zero_le) (Finset.mem_univ i)
  filter_upwards [(lintegral_eq_zero_iff hmeas).mp hi] with ω hω t ht
  have hle := le_iSup₂ (f := fun t (_ : t ∈ Set.Icc (0 : ℝ) T) => (‖x i t ω‖₊ : ℝ≥0∞) ^ 2) t ht
  rw [hω, Pi.zero_apply] at hle
  simpa using hle

end Vanish

namespace PairDiff

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d n m : ℕ}
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

/-- **Step 5 of Lemma 4.3.** For the difference system at `λ ∈ [λ̲, 1]`, `λ̲ > 0`, with
Lipschitz constants `K, K_T ≥ 0`, finite data size `P`, a coupling matrix with
`|G x|² ≤ g² |x|²`, nonnegative `c_G, α, β₁, β₂` and a rank case of Assumption 2.4, over a
filtration whose null sets lie in its time-`0` field, whose right-continuation is constant before
`0`, and which admits a cross witness,

`N' ≤ closureConst k_F k_B g c_G α β₁ β₂ λ̲ · P`. -/
theorem toReal_diffSize_le
    (hD : PairDiff D ℱ hℱW hℱN T lam K KT α β₁ β₂ G ξ₀ X Y Z U b σ h f g qb qσ qh qf qg)
    (𝒲 : D.CrossWitness ℱ) (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T)
    {lamLow : ℝ} (hlow : 0 < lamLow) (hlam : lamLow ≤ lam) (hlam1 : lam ≤ 1) (hK : 0 ≤ K)
    (hKT : 0 ≤ KT) {gG cG : ℝ} (hcG : 0 ≤ cG) (hα : 0 ≤ α) (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂)
    (hGn : ∀ x : Fin n → ℝ, (G *ᵥ x) ⬝ᵥ (G *ᵥ x) ≤ gG ^ 2 * (x ⬝ᵥ x))
    (hrank : RankCase G cG α β₁ β₂) (hP : dataSize P ν T ξ₀ qb qσ qh qf qg ≠ ⊤) :
    (diffSize P ν T X Y Z U).toReal
      ≤ closureConst (forwardConst T K) (backwardConst T K KT) gG cG α β₁ β₂ lamLow
        * (dataSize P ν T ξ₀ qb qσ qh qf qg).toReal := by
  have hlam0 : 0 ≤ lam := hlow.le.trans hlam
  rw [toReal_diffSize (hD.diffSize_lt_top 𝒲 hℱ0 hnull hT).ne]
  exact closure_le ENNReal.toReal_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg blockXT_nonneg blockX_nonneg blockY_nonneg
    (forwardConst_nonneg hK T) (backwardConst_nonneg hK hKT T) hcG hα hβ₁ hβ₂ hlow hlam
    (hD.forward_le 𝒲 hT hlam0 hlam1 hK hP) (hD.backward_le 𝒲 hT hlam0 hlam1 hK hKT hP)
    (hD.coercivity 𝒲 hT hlam0 hP hGn) (hD.rankCase_blocks 𝒲 hT hrank)

/-- **Lemma 4.3, the a-priori estimate (4.14).** For the difference system at `λ ∈ [λ̲, 1]`,
`λ̲ > 0`, with Lipschitz constants `K, K_T ≥ 0`, a coupling matrix with `|G x|² ≤ g² |x|²`,
nonnegative `c_G, α, β₁, β₂` and a rank case of Assumption 2.4, over a filtration whose null sets
lie in its time-`0` field, whose right-continuation is constant before `0`, and which admits a
cross witness,

`𝔼 sup_{t ≤ T} |δX_t|² + 𝔼 sup_{t ≤ T} |δY_t|² + 𝔼 ∫_0^T (|δZ|²_F + ‖δU‖²)
  ≤ C_B (𝔼|δξ₀|² + 𝔼|q^g|² + 𝔼 ∫_0^T (|q^b|² + |q^σ|²_F + ‖q^h‖² + |q^f|²))`,

`C_B = aprioriConst T K K_T g c_G α β₁ β₂ λ̲`. -/
theorem apriori
    (hD : PairDiff D ℱ hℱW hℱN T lam K KT α β₁ β₂ G ξ₀ X Y Z U b σ h f g qb qσ qh qf qg)
    (𝒲 : D.CrossWitness ℱ) (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T)
    {lamLow : ℝ} (hlow : 0 < lamLow) (hlam : lamLow ≤ lam) (hlam1 : lam ≤ 1) (hK : 0 ≤ K)
    (hKT : 0 ≤ KT) {gG cG : ℝ} (hcG : 0 ≤ cG) (hα : 0 ≤ α) (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂)
    (hGn : ∀ x : Fin n → ℝ, (G *ᵥ x) ⬝ᵥ (G *ᵥ x) ≤ gG ^ 2 * (x ⬝ᵥ x))
    (hrank : RankCase G cG α β₁ β₂) :
    supSize P ν T X Y Z U
      ≤ ENNReal.ofReal (aprioriConst T K KT gG cG α β₁ β₂ lamLow)
        * dataSize P ν T ξ₀ qb qσ qh qf qg := by
  have hlam0 : 0 ≤ lam := hlow.le.trans hlam
  by_cases hP : dataSize P ν T ξ₀ qb qσ qh qf qg = ⊤
  · rw [hP, ENNReal.mul_top (ENNReal.ofReal_pos.mpr
      (aprioriConst_pos hT.le hK hKT hcG hα hβ₁ hβ₂ hlow)).ne']
    exact le_top
  set Ccl := closureConst (forwardConst T K) (backwardConst T K KT) gG cG α β₁ β₂ lamLow
    with hCcl
  have hC : 0 ≤ Ccl := closureConst_nonneg (forwardConst_nonneg hK T)
    (backwardConst_nonneg hK hKT T) hcG hα hβ₁ hβ₂ hlow
  have hN := hD.diffSize_lt_top 𝒲 hℱ0 hnull hT
  have hN' : diffSize P ν T X Y Z U ≤ ENNReal.ofReal Ccl * dataSize P ν T ξ₀ qb qσ qh qf qg := by
    rw [← ENNReal.ofReal_toReal hN.ne, ← ENNReal.ofReal_toReal hP, ← ENNReal.ofReal_mul hC]
    exact ENNReal.ofReal_le_ofReal (hD.toReal_diffSize_le 𝒲 hℱ0 hnull hT hlow hlam hlam1 hK hKT
      hcG hα hβ₁ hβ₂ hGn hrank hP)
  calc supSize P ν T X Y Z U
      ≤ ENNReal.ofReal (supConst T K)
        * (diffSize P ν T X Y Z U + dataSize P ν T ξ₀ qb qσ qh qf qg) :=
        hD.supSize_le 𝒲 hℱ0 hnull hT hlam0 hlam1 hK
    _ ≤ ENNReal.ofReal (supConst T K)
        * (ENNReal.ofReal Ccl * dataSize P ν T ξ₀ qb qσ qh qf qg
          + dataSize P ν T ξ₀ qb qσ qh qf qg) := by gcongr
    _ = ENNReal.ofReal (aprioriConst T K KT gG cG α β₁ β₂ lamLow)
        * dataSize P ν T ξ₀ qb qσ qh qf qg := by
        rw [aprioriConst, ← hCcl, ENNReal.ofReal_mul (supConst_nonneg hT.le hK),
          ENNReal.ofReal_add hC zero_le_one, ENNReal.ofReal_one]
        ring

/-- **Zero data forces the differences to vanish.** For the difference system at `λ ∈ (0, 1]`
with Lipschitz constants `K, K_T ≥ 0`, nonnegative `c_G, α, β₁, β₂` and a rank case of
Assumption 2.4, over a filtration whose null sets lie in its time-`0` field, whose
right-continuation is constant before `0`, and which admits a cross witness, zero data size
`P = 0` gives `δX = 0` and `δY = 0` on `[0, T]` almost surely, and `δZ`, `δU` of zero energy. -/
theorem eq_zero
    (hD : PairDiff D ℱ hℱW hℱN T lam K KT α β₁ β₂ G ξ₀ X Y Z U b σ h f g qb qσ qh qf qg)
    (𝒲 : D.CrossWitness ℱ) (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T)
    (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) (hK : 0 ≤ K) (hKT : 0 ≤ KT) {cG : ℝ} (hcG : 0 ≤ cG)
    (hα : 0 ≤ α) (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂) (hrank : RankCase G cG α β₁ β₂)
    (h0 : dataSize P ν T ξ₀ qb qσ qh qf qg = 0) :
    (∀ i, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, X i t ω = 0)
      ∧ (∀ k, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, Y k t ω = 0)
      ∧ (∀ k j, Brownian.Ito.energy P T (fun ω s => Z k s ω j) = 0)
      ∧ (∀ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U k s ω e) = 0) := by
  obtain ⟨gG, hGn⟩ := exists_mulVec_dotProduct_le G
  have hN := hD.apriori 𝒲 hℱ0 hnull hT hlam0 le_rfl hlam1 hK hKT hcG hα hβ₁ hβ₂ hGn hrank
  rw [h0, mul_zero, nonpos_iff_eq_zero] at hN
  unfold supSize at hN
  simp only [add_eq_zero, Finset.sum_eq_zero_iff, Finset.mem_univ, true_implies] at hN
  obtain ⟨⟨⟨hX, hY⟩, hZ⟩, hU⟩ := hN
  exact ⟨ae_forall_eq_zero_of_lintegral_biSup_esq hT.le
      (fun i t => ((hD.fwd i).X_adapted t).mono (ℱ.le t) le_rfl) (fun i => (hD.fwd i).X_rightCont)
      hX,
    ae_forall_eq_zero_of_lintegral_biSup_esq hT.le
      (fun k t => ((hD.bwd k).Y_adapted t).mono (ℱ.le t) le_rfl) (fun k => (hD.bwd k).Y_rightCont)
      hY, hZ, hU⟩

end PairDiff

end MVFBSDEJ.WellPosedness.Stability
