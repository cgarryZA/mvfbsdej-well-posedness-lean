/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Stability.Coercivity
import Dissertation.WellPosedness.Stability.Coercive

/-!
# The coercive blocks in the rank cases

The closure step of Lemma 4.3 of the well-posedness paper reads the coercive blocks of (4.22)
through Assumption 2.4. In Case A (`β₁ > 0`, `|y|² ≤ c_G |Gᵀ y|²`) the backward block bounds
`J = 𝔼 ∫_0^T (|δY|² + |δZ|²_F + ‖δU‖²)`: the bound extends to the columns of `δZ` and to the
marks of `δU`, and integrates over the window. In Case B (`α, β₂ > 0`, `|x|² ≤ c_G |G x|²`) the
terminal and forward blocks bound `A = 𝔼|δX_T|²` and `I_X = 𝔼 ∫_0^T |δX|²`. This file states
the rank case in exactly this form, records that the three blocks are nonnegative, and splits the
size of the difference as `N' = A + Y₀ + I_X + J` with `Y₀ = 𝔼|δY_0|²`.

## Main statements

* `PairDiff.rankCase_blocks` — the rank case in terms of the blocks.
* `blockXT_nonneg`, `blockX_nonneg`, `blockY_nonneg` — the blocks are nonnegative.
* `toReal_diffSize` — `N' = A + Y₀ + I_X + J` for a finite size.
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped NNReal ENNReal

namespace Dissertation.WellPosedness.Stability

open LevyStochCalc.BSDEJ.Solves LevyStochCalc Dissertation.WellPosedness.BrownianPoisson

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} {ν : Measure E} {d n m : ℕ} {T : ℝ} {G : Matrix (Fin m) (Fin n) ℝ}
  {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ}
  {Z : Fin m → ℝ → Ω → Fin d → ℝ} {U : Fin m → ℝ → Ω → E → ℝ}

/-! ### Nonnegativity of the blocks and the size of the difference -/

omit [MeasurableSpace E] in
/-- The terminal block is nonnegative. -/
theorem blockXT_nonneg : 0 ≤ blockXT P G X T :=
  integral_nonneg fun _ => dotProduct_self_star_nonneg _

omit [MeasurableSpace E] in
/-- The forward block is nonnegative. -/
theorem blockX_nonneg : 0 ≤ blockX P G X T :=
  integral_nonneg fun _ => integral_nonneg fun _ => dotProduct_self_star_nonneg _

/-- The backward block is nonnegative. -/
theorem blockY_nonneg : 0 ≤ blockY P ν G Y Z U T :=
  integral_nonneg fun _ => integral_nonneg fun _ => add_nonneg (add_nonneg
    (dotProduct_self_star_nonneg _) (Finset.sum_nonneg fun _ _ => dotProduct_self_star_nonneg _))
    (integral_nonneg fun _ => dotProduct_self_star_nonneg _)

/-- **The size of a difference, split.** For a finite size,
`N' = A + Y₀ + I_X + J` with `A = 𝔼|δX_T|²`, `Y₀ = 𝔼|δY_0|²`, `I_X = 𝔼 ∫_0^T |δX|²` and
`J = 𝔼 ∫_0^T (|δY|² + |δZ|²_F + ‖δU‖²)`. -/
theorem toReal_diffSize (hN : diffSize P ν T X Y Z U ≠ ⊤) :
    (diffSize P ν T X Y Z U).toReal
      = (∫⁻ ω, esq (fun i => X i T ω) ∂P).toReal + (∫⁻ ω, esq (fun k => Y k 0 ω) ∂P).toReal
        + (∑ i, Brownian.Ito.energy P T (fun ω s => X i s ω)).toReal
        + (∑ k, Brownian.Ito.energy P T (fun ω s => Y k s ω)
          + ∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z k s ω j)
          + ∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U k s ω e)).toReal := by
  have e : diffSize P ν T X Y Z U = ∫⁻ ω, esq (fun i => X i T ω) ∂P
      + ∫⁻ ω, esq (fun k => Y k 0 ω) ∂P + ∑ i, Brownian.Ito.energy P T (fun ω s => X i s ω)
      + (∑ k, Brownian.Ito.energy P T (fun ω s => Y k s ω)
        + ∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z k s ω j)
        + ∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U k s ω e)) := by
    unfold diffSize
    ring
  rw [e] at hN ⊢
  obtain ⟨h123, h4⟩ := ENNReal.add_ne_top.mp hN
  obtain ⟨h12, h3⟩ := ENNReal.add_ne_top.mp h123
  obtain ⟨h1, h2⟩ := ENNReal.add_ne_top.mp h12
  rw [ENNReal.toReal_add h123 h4, ENNReal.toReal_add h12 h3, ENNReal.toReal_add h1 h2]

/-! ### The rank cases -/

namespace PairDiff

variable [IsProbabilityMeasure P] [SigmaFinite ν]
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {lam K KT α β₁ β₂ : ℝ}
  {ξ₀ : Fin n → Ω → ℝ}
  {b : Fin n → Ω → ℝ → ℝ} {σ : Fin n → ℝ → Ω → Fin d → ℝ} {h : Fin n → ℝ → Ω → E → ℝ}
  {f : Fin m → Ω → ℝ → ℝ} {g : Fin m → Ω → ℝ}
  {qb : Fin n → Ω → ℝ → ℝ} {qσ : Fin n → ℝ → Ω → Fin d → ℝ} {qh : Fin n → ℝ → Ω → E → ℝ}
  {qf : Fin m → Ω → ℝ → ℝ} {qg : Fin m → Ω → ℝ}

/-- **The rank case in terms of the coercive blocks.** Over a filtration with a cross witness,
Case A of Assumption 2.4 gives `β₁ > 0` and `J ≤ c_G · 𝔼 ∫_0^T (|GᵀδY|² + |GᵀδZ|²_F +
‖GᵀδU‖²)`, and Case B gives `α, β₂ > 0`, `A ≤ c_G 𝔼|GδX_T|²` and
`I_X ≤ c_G 𝔼 ∫_0^T |GδX|²`. -/
theorem rankCase_blocks
    (hD : PairDiff D ℱ hℱW hℱN T lam K KT α β₁ β₂ G ξ₀ X Y Z U b σ h f g qb qσ qh qf qg)
    (𝒲 : D.CrossWitness ℱ) (hT : 0 < T) {cG : ℝ} (hrank : RankCase G cG α β₁ β₂) :
    (0 < β₁ ∧ (∑ k, Brownian.Ito.energy P T (fun ω s => Y k s ω)
        + ∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z k s ω j)
        + ∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U k s ω e)).toReal
        ≤ cG * blockY P ν G Y Z U T)
      ∨ (0 < α ∧ 0 < β₂ ∧ (∫⁻ ω, esq (fun i => X i T ω) ∂P).toReal ≤ cG * blockXT P G X T
        ∧ (∑ i, Brownian.Ito.energy P T (fun ω s => X i s ω)).toReal ≤ cG * blockX P G X T) := by
  set μ₂ := P.prod (volume.restrict (Set.Icc (0 : ℝ) T)) with hμ₂
  have mX := hD.memLp_window_X 𝒲 hT
  have mY := hD.memLp_window_Y 𝒲 hT
  have mZ := hD.memLp_window_Z (T := T)
  have mU := hD.memLp_markedWindow_U (T := T)
  rcases hrank with ⟨hβ₁, hb⟩ | ⟨hα, hβ₂, hf⟩
  · refine Or.inl ⟨hβ₁, ?_⟩
    have hB2 : Integrable (fun p : Ω × ℝ => (fun k => Y k p.2 p.1) ⬝ᵥ (fun k => Y k p.2 p.1)
        + ∑ k, Z k p.2 p.1 ⬝ᵥ Z k p.2 p.1
        + ∫ e, (fun k => U k p.2 p.1 e) ⬝ᵥ (fun k => U k p.2 p.1 e) ∂ν) μ₂ :=
      ((integrable_dotProduct_of_memLp mY mY).add (integrable_finsetSum Finset.univ fun k _ =>
        integrable_dotProduct_of_memLp (mZ k) (mZ k))).add
        (integrable_dotProduct_of_memLp mU mU).integral_prod_left
    have hBYi := hD.integrable_blockY_window 𝒲 hT
    rw [← hD.integral_backSq_window 𝒲 hT, blockY, ← integral_prod_symm _ hBYi,
      ← integral_const_mul]
    refine integral_mono_ae hB2 (hBYi.const_mul cG) ?_
    filter_upwards [(integrable_dotProduct_of_memLp (memLp_mulVec Gᵀ mU)
      (memLp_mulVec Gᵀ mU)).prod_right_ae] with p hp
    have hU : ∫ e, (fun k => U k p.2 p.1 e) ⬝ᵥ (fun k => U k p.2 p.1 e) ∂ν
        ≤ cG * ∫ e, (Gᵀ *ᵥ fun k => U k p.2 p.1 e) ⬝ᵥ (Gᵀ *ᵥ fun k => U k p.2 p.1 e) ∂ν :=
      hb.integral_le (u := fun e k => U k p.2 p.1 e) hp
    have hZ := hb.sum_le Finset.univ fun j k => Z k p.2 p.1 j
    rw [sum_col_dotProduct_self (fun k => Z k p.2 p.1)] at hZ
    have hY := hb fun k => Y k p.2 p.1
    linarith
  · refine Or.inr ⟨hα, hβ₂, ?_, ?_⟩
    · have mXT : ∀ i, MemLp (X i T) 2 P := fun i => (hD.fwd i).memLp_terminal hT.le
      rw [← integral_dotProduct_self mXT, blockXT, ← integral_const_mul]
      exact integral_mono (integrable_dotProduct_of_memLp mXT mXT)
        ((integrable_dotProduct_of_memLp (memLp_mulVec G mXT) (memLp_mulVec G mXT)).const_mul
          cG) fun ω => hf _
    · have hBXi := hD.integrable_blockX_window 𝒲 hT
      rw [← integral_dotProduct_self_window (x := fun i ω s => X i s ω)
          (fun i => ((hD.fwd i).linearBSDEJ hT.le).measurable_uncurry.comp measurable_swap)
          fun i => (hD.fwd i).energy_lt_top 𝒲 hT,
        blockX, ← integral_prod_symm _ hBXi, ← integral_const_mul]
      exact integral_mono (integrable_dotProduct_of_memLp mX mX) (hBXi.const_mul cG)
        fun p => hf _

end PairDiff

end Dissertation.WellPosedness.Stability
