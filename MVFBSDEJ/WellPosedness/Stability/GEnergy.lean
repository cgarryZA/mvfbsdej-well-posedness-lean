/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Stability.PairDiff
import MVFBSDEJ.WellPosedness.Stability.WindowIntegrable

/-!
# The `G`-energy identity of Lemma 4.3

Step 1 of the proof of Lemma 4.3 of the well-posedness paper pairs `G δX` against `δY`: in
expectation, Itô's product formula for `⟨G δX_t, δY_t⟩` over `[0, T]` reads

`𝔼⟨G δX_T, δY_T⟩ − 𝔼⟨G δξ₀, δY_0⟩ = 𝔼 ∫_0^T (⟨λ δb + q^b, Gᵀ δY⟩ + ⟨λ δσ + q^σ, Gᵀ δZ⟩_F
  + ∫_E ⟨λ δh(e) + q^h(e), Gᵀ δU(e)⟩ ν(de) + ⟨−λ δf − q^f, G δX⟩) dt`.       (4.19)

In coordinates `⟨G x, y⟩ = ∑_k ∑_i G_{k i} x_i y_k`, so (4.19) is the `G_{k i}`-weighted sum
over the pairs `(i, k)` of the expectation of the product of the coordinates `δX_i` and `δY_k`.
Frozen at the horizon, both are Itô–Lévy processes over the same driver, and the bilinear
second-moment identity gives the expected product at `T` directly in expectation form. Its
Brownian and jump cross terms are iterated `𝔼 ∫_0^T`, and the drift term `∫_0^T 𝔼`; all four are
integrals over the window `Ω × [0, T]` of products of square-integrable integrands, so they
combine into one integral over the window, which is then read as `∫_0^T 𝔼` to be paired with
Assumption 2.5 at almost every time. The mark integrals split over the coordinates at almost
every point of the window.

## Main statements

* `integral_mul_eq_add_pairRate` — the scalar pairing identity.
* `integral_mulVec_dotProduct_eq` — the vector `G`-energy identity.
* `PairDiff.integral_mulVec_dotProduct_eq` — (4.19) for the difference system.
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped NNReal ENNReal

namespace MVFBSDEJ.WellPosedness.Stability

open LevyStochCalc.BSDEJ.Solves LevyStochCalc MVFBSDEJ.WellPosedness.BrownianPoisson

universe u v w

/-! ### The `G`-pairing in coordinates -/

section Algebra

variable {n m d : ℕ}

/-- `a ⬝ (Gᵀ c) = ∑_k ∑_i G_{k i} a_i c_k`. -/
theorem dotProduct_transpose_mulVec_eq_sum (G : Matrix (Fin m) (Fin n) ℝ) (a : Fin n → ℝ)
    (c : Fin m → ℝ) : a ⬝ᵥ (Gᵀ *ᵥ c) = ∑ k, ∑ i, G k i * (a i * c k) := by
  simp only [dotProduct, mulVec, transpose_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  ring

/-- `(G x) ⬝ y = ∑_k ∑_i G_{k i} x_i y_k`. -/
theorem mulVec_dotProduct_eq_sum (G : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ)
    (y : Fin m → ℝ) : (G *ᵥ x) ⬝ᵥ y = ∑ k, ∑ i, G k i * (x i * y k) := by
  simp only [dotProduct, mulVec, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  ring

/-- The `G`-pairing of a drift `b`, diffusion columns `s_{· j}`, driver `f` and mark term with
`(x, y, z)` is the `G_{k i}`-weighted sum of the scalar pairings of the coordinates:
`b ⬝ Gᵀy + ∑_j s_{·j} ⬝ Gᵀz_{·j} − f ⬝ Gx + J = ∑_k ∑_i G_{k i} (b_i y_k + ∑_j s_{i j} z_{k j}
− x_i f_k + J_{i k})` whenever `J = ∑_k ∑_i G_{k i} J_{i k}`. -/
theorem gPairing_eq_sum (G : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ) (s : Fin n → Fin d → ℝ)
    (x : Fin n → ℝ) (y f : Fin m → ℝ) (z : Fin m → Fin d → ℝ) (J : Fin n → Fin m → ℝ)
    (Jv : ℝ) (hJ : Jv = ∑ k, ∑ i, G k i * J i k) :
    b ⬝ᵥ (Gᵀ *ᵥ y) + ∑ j, (fun i => s i j) ⬝ᵥ (Gᵀ *ᵥ fun k => z k j) - f ⬝ᵥ (G *ᵥ x) + Jv
      = ∑ k, ∑ i, G k i * (b i * y k + ∑ j, s i j * z k j - x i * f k + J i k) := by
  subst hJ
  rw [dotProduct_transpose_mulVec_eq_sum, dotProduct_comm f, mulVec_dotProduct_eq_sum]
  simp only [dotProduct_transpose_mulVec_eq_sum]
  have hsw : ∑ j, ∑ k, ∑ i, G k i * (s i j * z k j)
      = ∑ k, ∑ i, G k i * ∑ j, s i j * z k j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  rw [hsw]
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]

end Algebra

/-! ### The pairing identities -/

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d n m : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}
  {T : ℝ} {ξ₀ : Ω → ℝ} {b : Ω → ℝ → ℝ} {X : ℝ → Ω → ℝ} {σ : ℝ → Ω → Fin d → ℝ}
  {γ : ℝ → Ω → E → ℝ} {ξ : Ω → ℝ} {φ : Ω → ℝ → ℝ} {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → Fin d → ℝ}
  {U : ℝ → Ω → E → ℝ}

/-- The scalar pairing rate `b Y + ∑_j σ_j Z_j − X φ + ∫_E γ U dν` of a solution `X` of the
linear forward equation (drift `b`, diffusion vector `σ`, jump integrand `γ`) and a solution
`(Y, Z, U)` of the linear backward equation (drift `φ`) is integrable on the window. -/
theorem integrable_pairRate (h₁ : LinearFSDEJ D ℱ hℱW hℱN T ξ₀ b X σ γ)
    (h₂ : LinearBSDEJ D ℱ hℱW hℱN T ξ φ Y Z U) (𝒲 : D.CrossWitness ℱ) (hT : 0 < T) :
    Integrable (fun p : Ω × ℝ => b p.1 p.2 * Y p.2 p.1 + ∑ j, σ p.2 p.1 j * Z p.2 p.1 j
        - X p.2 p.1 * φ p.1 p.2 + ∫ e, γ p.2 p.1 e * U p.2 p.1 e ∂ν)
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := by
  have hXm : Measurable (Function.uncurry fun ω s => X s ω) :=
    (h₁.linearBSDEJ hT.le).measurable_uncurry.comp measurable_swap
  have hYm : Measurable (Function.uncurry fun ω s => Y s ω) :=
    h₂.measurable_uncurry.comp measurable_swap
  exact (((integrable_mul_prod h₁.b_meas hYm h₁.b_sq.lt_top (h₂.energy_lt_top 𝒲 hT)).add
    (integrable_finsetSum _ fun j _ => integrable_mul_prod (h₁.σ_meas j) (h₂.Z_meas j)
      (h₁.σ_sq j).lt_top (h₂.Z_sq j).lt_top)).sub
    (integrable_mul_prod hXm h₂.φ_meas (h₁.energy_lt_top 𝒲 hT) h₂.φ_sq.lt_top)).add
    (integrable_integral_mul_marked (φ := fun ω s e => γ s ω e) (ψ := fun ω s e => U s ω e)
      h₁.γ_meas h₂.U_meas h₁.γ_sq.lt_top h₂.U_sq.lt_top)

/-- **The scalar pairing identity.** For a solution `X` of the linear forward equation from `ξ₀`
with drift `b`, diffusion vector `σ` and jump integrand `γ`, and a solution `(Y, Z, U)` of the
linear backward equation with drift `φ`, over a filtration with a cross witness,

`𝔼[X_T Y_T] = 𝔼[ξ₀ Y_0] + 𝔼 ∫_0^T (b_s Y_s + ∑_j σ_j(s) Z_j(s) − X_s φ_s
  + ∫_E γ_s(e) U_s(e) ν(de)) ds`,

the time integral taken for the product measure on the window. -/
theorem integral_mul_eq_add_pairRate (h₁ : LinearFSDEJ D ℱ hℱW hℱN T ξ₀ b X σ γ)
    (h₂ : LinearBSDEJ D ℱ hℱW hℱN T ξ φ Y Z U) (𝒲 : D.CrossWitness ℱ) (hT : 0 < T) :
    ∫ ω, X T ω * Y T ω ∂P = ∫ ω, ξ₀ ω * Y 0 ω ∂P
      + ∫ p, (b p.1 p.2 * Y p.2 p.1 + ∑ j, σ p.2 p.1 j * Z p.2 p.1 j - X p.2 p.1 * φ p.1 p.2
          + ∫ e, γ p.2 p.1 e * U p.2 p.1 e ∂ν) ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := by
  have hb := h₁.linearBSDEJ hT.le
  have key := Ito.SecondMoment.integral_mul_eq_of_isItoLevyProcess
    (h₁.isItoLevyProcess_clampT hT) (h₂.isItoLevyProcess_clampT hT) 𝒲
    hb.stronglyMeasurable_initial (hb.memLp_initial hT.le) h₁.b_meas h₁.b_prog
    (fun T' _ => drift_sq_int_global h₁.b_vanish h₁.b_sq T')
    h₂.stronglyMeasurable_initial (h₂.memLp_initial hT.le) h₂.φ_meas.neg
    (continuous_neg.comp_progressivelyMeasurable neg_zero h₂.φ_prog)
    (fun T' _ => neg_drift_sq_int_global h₂.φ_vanish h₂.φ_sq T') hT
  set μ₂ := P.prod (volume.restrict (Set.Icc (0 : ℝ) T)) with hμ₂
  have hXm : Measurable (Function.uncurry fun ω s => X s ω) :=
    hb.measurable_uncurry.comp measurable_swap
  have hYm : Measurable (Function.uncurry fun ω s => Y s ω) :=
    h₂.measurable_uncurry.comp measurable_swap
  have hdi : Integrable (fun p : Ω × ℝ => b p.1 p.2 * Y p.2 p.1 - X p.2 p.1 * φ p.1 p.2) μ₂ :=
    (integrable_mul_prod h₁.b_meas hYm h₁.b_sq.lt_top (h₂.energy_lt_top 𝒲 hT)).sub
      (integrable_mul_prod hXm h₂.φ_meas (h₁.energy_lt_top 𝒲 hT) h₂.φ_sq.lt_top)
  have hσZ : ∀ j : Fin d, Integrable (fun p : Ω × ℝ => σ p.2 p.1 j * Z p.2 p.1 j) μ₂ :=
    fun j => integrable_mul_prod (h₁.σ_meas j) (h₂.Z_meas j) (h₁.σ_sq j).lt_top
      (h₂.Z_sq j).lt_top
  have hγU : Integrable (fun p : Ω × ℝ => ∫ e, γ p.2 p.1 e * U p.2 p.1 e ∂ν) μ₂ :=
    integrable_integral_mul_marked (φ := fun ω s e => γ s ω e) (ψ := fun ω s e => U s ω e)
      h₁.γ_meas h₂.U_meas h₁.γ_sq.lt_top h₂.U_sq.lt_top
  have h0 : ∫ ω, X 0 ω * Y 0 ω ∂P = ∫ ω, ξ₀ ω * Y 0 ω ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [h₁.initial_ae_eq hT.le] with ω hω
    rw [hω]
  have hdrift : ∫ s in Set.Icc (0 : ℝ) T,
      ∫ ω, clampT T X s ω * -φ ω s + clampT T Y s ω * b ω s ∂P
      = ∫ p, (b p.1 p.2 * Y p.2 p.1 - X p.2 p.1 * φ p.1 p.2) ∂μ₂ := by
    rw [integral_prod_symm _ hdi]
    refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [clampT_apply, min_eq_left hs.2]
    ring
  have hbrown : ∑ j : Fin d, ∫ ω, ∫ s in Set.Icc (0 : ℝ) T, σ s ω j * Z s ω j ∂volume ∂P
      = ∫ p, ∑ j : Fin d, σ p.2 p.1 j * Z p.2 p.1 j ∂μ₂ := by
    rw [integral_finsetSum _ fun j _ => hσZ j]
    exact Finset.sum_congr rfl fun j _ => (integral_prod _ (hσZ j)).symm
  have hjump : ∫ ω, ∫ s in Set.Icc (0 : ℝ) T, ∫ e, γ s ω e * U s ω e ∂ν ∂volume ∂P
      = ∫ p, ∫ e, γ p.2 p.1 e * U p.2 p.1 e ∂ν ∂μ₂ :=
    (integral_prod _ hγU).symm
  rw [clampT_apply_of_le (le_refl T) X, clampT_apply_of_le (le_refl T) Y] at key
  have hS : Integrable (fun p : Ω × ℝ => ∑ j : Fin d, σ p.2 p.1 j * Z p.2 p.1 j) μ₂ :=
    integrable_finsetSum _ fun j _ => hσZ j
  have hSJ : Integrable (fun p : Ω × ℝ => ∑ j : Fin d, σ p.2 p.1 j * Z p.2 p.1 j
      + ∫ e, γ p.2 p.1 e * U p.2 p.1 e ∂ν) μ₂ := hS.add hγU
  have e3 : ∫ p, (b p.1 p.2 * Y p.2 p.1 + ∑ j, σ p.2 p.1 j * Z p.2 p.1 j - X p.2 p.1 * φ p.1 p.2
        + ∫ e, γ p.2 p.1 e * U p.2 p.1 e ∂ν) ∂μ₂
      = ∫ p, ((b p.1 p.2 * Y p.2 p.1 - X p.2 p.1 * φ p.1 p.2) + (∑ j, σ p.2 p.1 j * Z p.2 p.1 j
        + ∫ e, γ p.2 p.1 e * U p.2 p.1 e ∂ν)) ∂μ₂ :=
    integral_congr_ae (Eventually.of_forall fun p => by ring)
  rw [key, h0, hdrift, hbrown, hjump, e3, integral_add hdi hSJ, integral_add hS hγU]
  ring

/-- **The `G`-energy identity in expectation** (4.19). For `n` solutions `X_i` of the linear
forward equation (initial values `ξ₀_i`, drifts `b_i`, diffusion vectors `σ_i`, jump integrands
`γ_i`), `m` solutions `(Y_k, Z_k, U_k)` of the linear backward equation (drifts `φ_k`) and
`G ∈ ℝ^{m×n}`, over a filtration with a cross witness,

`𝔼⟨G X_T, Y_T⟩ = 𝔼⟨G ξ₀, Y_0⟩ + ∫_0^T 𝔼[⟨b, Gᵀ Y⟩ + ⟨σ, Gᵀ Z⟩_F − ⟨φ, G X⟩
  + ∫_E ⟨γ(e), Gᵀ U(e)⟩ ν(de)] ds`. -/
theorem integral_mulVec_dotProduct_eq {G : Matrix (Fin m) (Fin n) ℝ}
    {ξ₀ : Fin n → Ω → ℝ} {b : Fin n → Ω → ℝ → ℝ} {X : Fin n → ℝ → Ω → ℝ}
    {σ : Fin n → ℝ → Ω → Fin d → ℝ} {γ : Fin n → ℝ → Ω → E → ℝ}
    {ξ : Fin m → Ω → ℝ} {φ : Fin m → Ω → ℝ → ℝ} {Y : Fin m → ℝ → Ω → ℝ}
    {Z : Fin m → ℝ → Ω → Fin d → ℝ} {U : Fin m → ℝ → Ω → E → ℝ}
    (h₁ : ∀ i, LinearFSDEJ D ℱ hℱW hℱN T (ξ₀ i) (b i) (X i) (σ i) (γ i))
    (h₂ : ∀ k, LinearBSDEJ D ℱ hℱW hℱN T (ξ k) (φ k) (Y k) (Z k) (U k))
    (𝒲 : D.CrossWitness ℱ) (hT : 0 < T) :
    ∫ ω, (G *ᵥ fun i => X i T ω) ⬝ᵥ (fun k => Y k T ω) ∂P
      = ∫ ω, (G *ᵥ fun i => ξ₀ i ω) ⬝ᵥ (fun k => Y k 0 ω) ∂P
        + ∫ s in Set.Icc (0 : ℝ) T, ∫ ω, ((fun i => b i ω s) ⬝ᵥ (Gᵀ *ᵥ fun k => Y k s ω)
          + ∑ j, (fun i => σ i s ω j) ⬝ᵥ (Gᵀ *ᵥ fun k => Z k s ω j)
          - (fun k => φ k ω s) ⬝ᵥ (G *ᵥ fun i => X i s ω)
          + ∫ e, (fun i => γ i s ω e) ⬝ᵥ (Gᵀ *ᵥ fun k => U k s ω e) ∂ν) ∂P := by
  set μ₂ := P.prod (volume.restrict (Set.Icc (0 : ℝ) T)) with hμ₂
  set R : Fin n → Fin m → Ω × ℝ → ℝ := fun i k p => b i p.1 p.2 * Y k p.2 p.1
    + ∑ j, σ i p.2 p.1 j * Z k p.2 p.1 j - X i p.2 p.1 * φ k p.1 p.2
    + ∫ e, γ i p.2 p.1 e * U k p.2 p.1 e ∂ν with hR
  have hRi : ∀ i k, Integrable (R i k) μ₂ := fun i k => integrable_pairRate (h₁ i) (h₂ k) 𝒲 hT
  have hpair : ∀ i k, ∫ ω, X i T ω * Y k T ω ∂P = ∫ ω, ξ₀ i ω * Y k 0 ω ∂P + ∫ p, R i k p ∂μ₂ :=
    fun i k => integral_mul_eq_add_pairRate (h₁ i) (h₂ k) 𝒲 hT
  have hexp : ∀ (x : Fin n → Ω → ℝ) (y : Fin m → Ω → ℝ), (∀ i, MemLp (x i) 2 P) →
      (∀ k, MemLp (y k) 2 P) → ∫ ω, (G *ᵥ fun i => x i ω) ⬝ᵥ (fun k => y k ω) ∂P
        = ∑ k, ∑ i, G k i * ∫ ω, x i ω * y k ω ∂P := by
    intro x y hx hy
    have hI : ∀ k i, Integrable (fun ω => G k i * (x i ω * y k ω)) P := fun k i =>
      ((hx i).integrable_mul (hy k)).const_mul _
    simp only [mulVec_dotProduct_eq_sum]
    rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun i _ => hI k i]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_finsetSum _ fun i _ => hI k i]
    exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  have hγU : ∀ᵐ p ∂μ₂, ∀ i k, Integrable (fun e => γ i p.2 p.1 e * U k p.2 p.1 e) ν := by
    refine ae_all_iff.mpr fun i => ae_all_iff.mpr fun k => ?_
    exact ae_integrable_mul_marked (φ := fun ω s e => γ i s ω e) (ψ := fun ω s e => U k s ω e)
      (h₁ i).γ_meas (h₂ k).U_meas (h₁ i).γ_sq.lt_top (h₂ k).U_sq.lt_top
  have hV : ∀ᵐ p ∂μ₂, ((fun i => b i p.1 p.2) ⬝ᵥ (Gᵀ *ᵥ fun k => Y k p.2 p.1)
          + ∑ j, (fun i => σ i p.2 p.1 j) ⬝ᵥ (Gᵀ *ᵥ fun k => Z k p.2 p.1 j)
          - (fun k => φ k p.1 p.2) ⬝ᵥ (G *ᵥ fun i => X i p.2 p.1)
          + ∫ e, (fun i => γ i p.2 p.1 e) ⬝ᵥ (Gᵀ *ᵥ fun k => U k p.2 p.1 e) ∂ν)
        = ∑ k, ∑ i, G k i * R i k p := by
    filter_upwards [hγU] with p hp
    have hI : ∀ k i, Integrable (fun e => G k i * (γ i p.2 p.1 e * U k p.2 p.1 e)) ν :=
      fun k i => (hp i k).const_mul _
    refine gPairing_eq_sum G _ _ _ _ _ _ (fun i k => ∫ e, γ i p.2 p.1 e * U k p.2 p.1 e ∂ν) _ ?_
    simp only [dotProduct_transpose_mulVec_eq_sum]
    rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun i _ => hI k i]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_finsetSum _ fun i _ => hI k i]
    exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  have hRG : ∀ k i, Integrable (fun p => G k i * R i k p) μ₂ := fun k i => (hRi i k).const_mul _
  have hS : Integrable (fun p => ∑ k, ∑ i, G k i * R i k p) μ₂ :=
    integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun i _ => hRG k i
  have hVint := hS.congr (hV.mono fun p hp => hp.symm)
  rw [hexp _ _ (fun i => (h₁ i).memLp_terminal hT.le)
      (fun k => (h₂ k).ξ_sq.ae_eq ((h₂ k).ae_eq_terminal hT.le).symm),
    hexp _ _ (fun i => (h₁ i).ξ₀_sq) (fun k => (h₂ k).memLp_initial hT.le),
    ← integral_prod_symm _ hVint, integral_congr_ae hV,
    integral_finsetSum _ fun k _ => integrable_finsetSum _ fun i _ => hRG k i]
  simp only [hpair, mul_add, Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_finsetSum _ fun i _ => hRG k i]
  exact Finset.sum_congr rfl fun i _ => (integral_const_mul _ _).symm

/-- **The `G`-energy identity (4.19) for the difference system of Lemma 4.3**, over a
filtration with a cross witness. -/
theorem PairDiff.integral_mulVec_dotProduct_eq {K KT lam α β₁ β₂ : ℝ}
    {G : Matrix (Fin m) (Fin n) ℝ} {ξ₀ : Fin n → Ω → ℝ}
    {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ}
    {Z : Fin m → ℝ → Ω → Fin d → ℝ} {U : Fin m → ℝ → Ω → E → ℝ}
    {b : Fin n → Ω → ℝ → ℝ} {σ : Fin n → ℝ → Ω → Fin d → ℝ} {h : Fin n → ℝ → Ω → E → ℝ}
    {f : Fin m → Ω → ℝ → ℝ} {g : Fin m → Ω → ℝ}
    {qb : Fin n → Ω → ℝ → ℝ} {qσ : Fin n → ℝ → Ω → Fin d → ℝ} {qh : Fin n → ℝ → Ω → E → ℝ}
    {qf : Fin m → Ω → ℝ → ℝ} {qg : Fin m → Ω → ℝ}
    (hD : PairDiff D ℱ hℱW hℱN T lam K KT α β₁ β₂ G ξ₀ X Y Z U b σ h f g qb qσ qh qf qg)
    (𝒲 : D.CrossWitness ℱ) (hT : 0 < T) :
    ∫ ω, (G *ᵥ fun i => X i T ω) ⬝ᵥ (fun k => Y k T ω) ∂P
      = ∫ ω, (G *ᵥ fun i => ξ₀ i ω) ⬝ᵥ (fun k => Y k 0 ω) ∂P
        + ∫ s in Set.Icc (0 : ℝ) T, ∫ ω,
          ((fun i => lam * b i ω s + qb i ω s) ⬝ᵥ (Gᵀ *ᵥ fun k => Y k s ω)
          + ∑ j, (fun i => lam * σ i s ω j + qσ i s ω j) ⬝ᵥ (Gᵀ *ᵥ fun k => Z k s ω j)
          - (fun k => lam * f k ω s + qf k ω s) ⬝ᵥ (G *ᵥ fun i => X i s ω)
          + ∫ e, (fun i => lam * h i s ω e + qh i s ω e) ⬝ᵥ (Gᵀ *ᵥ fun k => U k s ω e) ∂ν) ∂P :=
  Stability.integral_mulVec_dotProduct_eq hD.fwd hD.bwd 𝒲 hT

end MVFBSDEJ.WellPosedness.Stability
