/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Stability.GPairing

/-!
# The difference system on the window

The coercivity step of Lemma 4.3 of the well-posedness paper integrates the pairings of (4.19)
over the window `Ω × [0, T]` with `P ⊗ ds`, and the mark integrals over the marked window with
`(P ⊗ ds) ⊗ ν`. This file records that every coordinate of the difference system is square
integrable there: the difference `(δX, δY, δZ, δU)` over a filtration with a cross witness; the
integrands `λ δψ + q^ψ` of (4.15)–(4.16); the forcing differences when the data size is finite;
and the coefficient differences `δψ = λ⁻¹ ((λ δψ + q^ψ) − q^ψ)` when moreover `λ ≠ 0`. It also
identifies the integral of `|δY|² + |δZ|²_F + ‖δU‖²` on the window with
`J = 𝔼 ∫_0^T (|δY|² + |δZ|²_F + ‖δU‖²)`, and shows the integrands of the coercive blocks
`|G δX|²` and `|Gᵀ δY|² + |Gᵀ δZ|²_F + ‖Gᵀ δU‖²` integrable.

## Main statements

* `PairDiff.memLp_window_X` and its companions — square integrability on the window.
* `PairDiff.integral_backSq_window` — the window integral of `|δY|² + |δZ|²_F + ‖δU‖²` is `J`.
* `PairDiff.integrable_blockX_window`, `PairDiff.integrable_blockY_window` — the block
  integrands are integrable.
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped NNReal ENNReal

namespace MVFBSDEJ.WellPosedness.Stability

open LevyStochCalc.BSDEJ.Solves LevyStochCalc MVFBSDEJ.WellPosedness.BrownianPoisson

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d n m : ℕ}

namespace PairDiff

variable {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
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

/-! ### The difference on the window -/

/-- Each coordinate of `δX` is square integrable on the window. -/
theorem memLp_window_X
    (hD : PairDiff D ℱ hℱW hℱN T lam K KT α β₁ β₂ G ξ₀ X Y Z U b σ h f g qb qσ qh qf qg)
    (𝒲 : D.CrossWitness ℱ) (hT : 0 < T) (i : Fin n) :
    MemLp (fun p : Ω × ℝ => X i p.2 p.1) 2 (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) :=
  Ito.SecondMoment.memLp_two_prod (f := fun ω s => X i s ω)
    (((hD.fwd i).linearBSDEJ hT.le).measurable_uncurry.comp measurable_swap)
    ((hD.fwd i).energy_lt_top 𝒲 hT)

/-- Each coordinate of `δY` is square integrable on the window. -/
theorem memLp_window_Y
    (hD : PairDiff D ℱ hℱW hℱN T lam K KT α β₁ β₂ G ξ₀ X Y Z U b σ h f g qb qσ qh qf qg)
    (𝒲 : D.CrossWitness ℱ) (hT : 0 < T) (k : Fin m) :
    MemLp (fun p : Ω × ℝ => Y k p.2 p.1) 2 (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) :=
  Ito.SecondMoment.memLp_two_prod (f := fun ω s => Y k s ω)
    ((hD.bwd k).measurable_uncurry.comp measurable_swap) ((hD.bwd k).energy_lt_top 𝒲 hT)

/-- Each entry of `δZ` is square integrable on the window. -/
theorem memLp_window_Z
    (hD : PairDiff D ℱ hℱW hℱN T lam K KT α β₁ β₂ G ξ₀ X Y Z U b σ h f g qb qσ qh qf qg)
    (k : Fin m) (j : Fin d) :
    MemLp (fun p : Ω × ℝ => Z k p.2 p.1 j) 2 (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) :=
  Ito.SecondMoment.memLp_two_prod ((hD.bwd k).Z_meas j) ((hD.bwd k).Z_sq j).lt_top

/-- Each coordinate of `δU` is square integrable on the marked window. -/
theorem memLp_markedWindow_U
    (hD : PairDiff D ℱ hℱW hℱN T lam K KT α β₁ β₂ G ξ₀ X Y Z U b σ h f g qb qσ qh qf qg)
    (k : Fin m) :
    MemLp (fun q : (Ω × ℝ) × E => U k q.1.2 q.1.1 q.2) 2
      ((P.prod (volume.restrict (Set.Icc (0 : ℝ) T))).prod ν) :=
  memLp_markedWindow (φ := fun ω s e => U k s ω e) (hD.bwd k).U_meas (hD.bwd k).U_sq.lt_top

/-- The integral of `|δY|² + |δZ|²_F + ‖δU‖²_{L²(ν)}` on the window is
`J = 𝔼 ∫_0^T (|δY|² + |δZ|²_F + ‖δU‖²)`. -/
theorem integral_backSq_window
    (hD : PairDiff D ℱ hℱW hℱN T lam K KT α β₁ β₂ G ξ₀ X Y Z U b σ h f g qb qσ qh qf qg)
    (𝒲 : D.CrossWitness ℱ) (hT : 0 < T) :
    ∫ p, ((fun k => Y k p.2 p.1) ⬝ᵥ (fun k => Y k p.2 p.1) + ∑ k, Z k p.2 p.1 ⬝ᵥ Z k p.2 p.1
        + ∫ e, (fun k => U k p.2 p.1 e) ⬝ᵥ (fun k => U k p.2 p.1 e) ∂ν)
        ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T)))
      = (∑ k, Brownian.Ito.energy P T (fun ω s => Y k s ω)
        + ∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z k s ω j)
        + ∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U k s ω e)).toReal := by
  set μ₂ := P.prod (volume.restrict (Set.Icc (0 : ℝ) T)) with hμ₂
  set Ay : Ω × ℝ → ℝ := fun p => (fun k => Y k p.2 p.1) ⬝ᵥ (fun k => Y k p.2 p.1) with hAy
  set Az : Fin m → Ω × ℝ → ℝ := fun k p => Z k p.2 p.1 ⬝ᵥ Z k p.2 p.1 with hAz
  set Au : Ω × ℝ → ℝ := fun p => ∫ e, (fun k => U k p.2 p.1 e) ⬝ᵥ (fun k => U k p.2 p.1 e) ∂ν
    with hAu
  have hY : Integrable Ay μ₂ :=
    integrable_dotProduct_of_memLp (hD.memLp_window_Y 𝒲 hT) (hD.memLp_window_Y 𝒲 hT)
  have hZ : ∀ k, Integrable (Az k) μ₂ := fun k =>
    integrable_dotProduct_of_memLp (hD.memLp_window_Z k) (hD.memLp_window_Z k)
  have hU : Integrable Au μ₂ := (integrable_dotProduct_of_memLp
    (hD.memLp_markedWindow_U (T := T)) hD.memLp_markedWindow_U).integral_prod_left
  have hZs : Integrable (fun p => ∑ k, Az k p) μ₂ := integrable_finsetSum _ fun k _ => hZ k
  have hYf : ∀ k, Brownian.Ito.energy P T (fun ω s => Y k s ω) < ⊤ := fun k =>
    (hD.bwd k).energy_lt_top 𝒲 hT
  have hZf : ∀ k j, Brownian.Ito.energy P T (fun ω s => Z k s ω j) < ⊤ := fun k j =>
    ((hD.bwd k).Z_sq j).lt_top
  have hUf : ∀ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U k s ω e) < ⊤ :=
    fun k => (hD.bwd k).U_sq.lt_top
  have eY : ∫ p, Ay p ∂μ₂ = (∑ k, Brownian.Ito.energy P T (fun ω s => Y k s ω)).toReal :=
    integral_dotProduct_self_window (x := fun k ω s => Y k s ω)
      (fun k => (hD.bwd k).measurable_uncurry.comp measurable_swap) hYf
  have eZ : ∀ k, ∫ p, Az k p ∂μ₂ = (∑ j, Brownian.Ito.energy P T (fun ω s => Z k s ω j)).toReal :=
    fun k => integral_dotProduct_self_window (x := fun j ω s => Z k s ω j)
      (fun j => (hD.bwd k).Z_meas j) (hZf k)
  have eU : ∫ p, Au p ∂μ₂
      = (∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U k s ω e)).toReal :=
    integral_integral_dotProduct_self_markedWindow (x := fun k ω s e => U k s ω e)
      (fun k => (hD.bwd k).U_meas) hUf
  change ∫ p, (Ay p + ∑ k, Az k p + Au p) ∂μ₂ = _
  rw [integral_add (f := fun p => Ay p + ∑ k, Az k p) (hY.add hZs) hU, integral_add hY hZs,
    integral_finsetSum _ fun k _ => hZ k,
    eY, eU, Finset.sum_congr rfl fun k _ => eZ k,
    ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨ENNReal.sum_ne_top.mpr fun k _ => (hYf k).ne,
      ENNReal.sum_ne_top.mpr fun k _ => ENNReal.sum_ne_top.mpr fun j _ => (hZf k j).ne⟩)
      (ENNReal.sum_ne_top.mpr fun k _ => (hUf k).ne),
    ENNReal.toReal_add (ENNReal.sum_ne_top.mpr fun k _ => (hYf k).ne)
      (ENNReal.sum_ne_top.mpr fun k _ => ENNReal.sum_ne_top.mpr fun j _ => (hZf k j).ne),
    ENNReal.toReal_sum fun k _ => ENNReal.sum_ne_top.mpr fun j _ => (hZf k j).ne]

/-! ### The integrands and the forcing on the window -/

/-- Each coordinate of the drift `λ δb + q^b` of `δX` is square integrable on the window. -/
theorem memLp_window_drift
    (hD : PairDiff D ℱ hℱW hℱN T lam K KT α β₁ β₂ G ξ₀ X Y Z U b σ h f g qb qσ qh qf qg)
    (i : Fin n) :
    MemLp (fun p : Ω × ℝ => lam * b i p.1 p.2 + qb i p.1 p.2) 2
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) :=
  Ito.SecondMoment.memLp_two_prod (hD.fwd i).b_meas (hD.fwd i).b_sq.lt_top

/-- Each entry of the diffusion `λ δσ + q^σ` of `δX` is square integrable on the window. -/
theorem memLp_window_diffusion
    (hD : PairDiff D ℱ hℱW hℱN T lam K KT α β₁ β₂ G ξ₀ X Y Z U b σ h f g qb qσ qh qf qg)
    (i : Fin n) (j : Fin d) :
    MemLp (fun p : Ω × ℝ => lam * σ i p.2 p.1 j + qσ i p.2 p.1 j) 2
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) :=
  Ito.SecondMoment.memLp_two_prod ((hD.fwd i).σ_meas j) ((hD.fwd i).σ_sq j).lt_top

/-- Each coordinate of the jump integrand `λ δh + q^h` of `δX` is square integrable on the
marked window. -/
theorem memLp_markedWindow_jump
    (hD : PairDiff D ℱ hℱW hℱN T lam K KT α β₁ β₂ G ξ₀ X Y Z U b σ h f g qb qσ qh qf qg)
    (i : Fin n) :
    MemLp (fun q : (Ω × ℝ) × E => lam * h i q.1.2 q.1.1 q.2 + qh i q.1.2 q.1.1 q.2) 2
      ((P.prod (volume.restrict (Set.Icc (0 : ℝ) T))).prod ν) :=
  memLp_markedWindow (φ := fun ω s e => lam * h i s ω e + qh i s ω e) (hD.fwd i).γ_meas
    (hD.fwd i).γ_sq.lt_top

/-- Each coordinate of the driver `λ δf + q^f` of `δY` is square integrable on the window. -/
theorem memLp_window_driver
    (hD : PairDiff D ℱ hℱW hℱN T lam K KT α β₁ β₂ G ξ₀ X Y Z U b σ h f g qb qσ qh qf qg)
    (k : Fin m) :
    MemLp (fun p : Ω × ℝ => lam * f k p.1 p.2 + qf k p.1 p.2) 2
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) :=
  Ito.SecondMoment.memLp_two_prod (hD.bwd k).φ_meas (hD.bwd k).φ_sq.lt_top

/-- For a finite data size, the drift forcing is square integrable on the window. -/
theorem memLp_window_qb
    (hD : PairDiff D ℱ hℱW hℱN T lam K KT α β₁ β₂ G ξ₀ X Y Z U b σ h f g qb qσ qh qf qg)
    (hP : dataSize P ν T ξ₀ qb qσ qh qf qg ≠ ⊤) (i : Fin n) :
    MemLp (fun p : Ω × ℝ => qb i p.1 p.2) 2 (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) :=
  Ito.SecondMoment.memLp_two_prod (hD.qb_meas i) ((lt_top_of_dataSize_ne_top hP).2.2.1 i)

/-- For a finite data size, the diffusion forcing is square integrable on the window. -/
theorem memLp_window_qσ
    (hD : PairDiff D ℱ hℱW hℱN T lam K KT α β₁ β₂ G ξ₀ X Y Z U b σ h f g qb qσ qh qf qg)
    (hP : dataSize P ν T ξ₀ qb qσ qh qf qg ≠ ⊤) (i : Fin n) (j : Fin d) :
    MemLp (fun p : Ω × ℝ => qσ i p.2 p.1 j) 2 (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) :=
  Ito.SecondMoment.memLp_two_prod (hD.qσ_meas i j) ((lt_top_of_dataSize_ne_top hP).2.2.2.1 i j)

/-- For a finite data size, the jump forcing is square integrable on the marked window. -/
theorem memLp_markedWindow_qh
    (hD : PairDiff D ℱ hℱW hℱN T lam K KT α β₁ β₂ G ξ₀ X Y Z U b σ h f g qb qσ qh qf qg)
    (hP : dataSize P ν T ξ₀ qb qσ qh qf qg ≠ ⊤) (i : Fin n) :
    MemLp (fun q : (Ω × ℝ) × E => qh i q.1.2 q.1.1 q.2) 2
      ((P.prod (volume.restrict (Set.Icc (0 : ℝ) T))).prod ν) :=
  memLp_markedWindow (φ := fun ω s e => qh i s ω e) (hD.qh_meas i)
    ((lt_top_of_dataSize_ne_top hP).2.2.2.2.1 i)

/-- For a finite data size, the driver forcing is square integrable on the window. -/
theorem memLp_window_qf
    (hD : PairDiff D ℱ hℱW hℱN T lam K KT α β₁ β₂ G ξ₀ X Y Z U b σ h f g qb qσ qh qf qg)
    (hP : dataSize P ν T ξ₀ qb qσ qh qf qg ≠ ⊤) (k : Fin m) :
    MemLp (fun p : Ω × ℝ => qf k p.1 p.2) 2 (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) :=
  Ito.SecondMoment.memLp_two_prod (hD.qf_meas k) ((lt_top_of_dataSize_ne_top hP).2.2.2.2.2 k)

/-- For `λ ≠ 0` and a finite data size, the drift difference is square integrable on the
window. -/
theorem memLp_window_b
    (hD : PairDiff D ℱ hℱW hℱN T lam K KT α β₁ β₂ G ξ₀ X Y Z U b σ h f g qb qσ qh qf qg)
    (hl : lam ≠ 0) (hP : dataSize P ν T ξ₀ qb qσ qh qf qg ≠ ⊤) (i : Fin n) :
    MemLp (fun p : Ω × ℝ => b i p.1 p.2) 2 (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) :=
  (((hD.memLp_window_drift i).sub (hD.memLp_window_qb hP i)).const_mul lam⁻¹).ae_eq
    (ae_of_all _ fun _ => (eq_inv_mul_add_sub hl _ _).symm)

/-- For `λ ≠ 0` and a finite data size, the diffusion difference is square integrable on the
window. -/
theorem memLp_window_σ
    (hD : PairDiff D ℱ hℱW hℱN T lam K KT α β₁ β₂ G ξ₀ X Y Z U b σ h f g qb qσ qh qf qg)
    (hl : lam ≠ 0) (hP : dataSize P ν T ξ₀ qb qσ qh qf qg ≠ ⊤) (i : Fin n) (j : Fin d) :
    MemLp (fun p : Ω × ℝ => σ i p.2 p.1 j) 2 (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) :=
  (((hD.memLp_window_diffusion i j).sub (hD.memLp_window_qσ hP i j)).const_mul lam⁻¹).ae_eq
    (ae_of_all _ fun _ => (eq_inv_mul_add_sub hl _ _).symm)

/-- For `λ ≠ 0` and a finite data size, the jump-coefficient difference is square integrable
on the marked window. -/
theorem memLp_markedWindow_h
    (hD : PairDiff D ℱ hℱW hℱN T lam K KT α β₁ β₂ G ξ₀ X Y Z U b σ h f g qb qσ qh qf qg)
    (hl : lam ≠ 0) (hP : dataSize P ν T ξ₀ qb qσ qh qf qg ≠ ⊤) (i : Fin n) :
    MemLp (fun q : (Ω × ℝ) × E => h i q.1.2 q.1.1 q.2) 2
      ((P.prod (volume.restrict (Set.Icc (0 : ℝ) T))).prod ν) :=
  (((hD.memLp_markedWindow_jump i).sub (hD.memLp_markedWindow_qh hP i)).const_mul lam⁻¹).ae_eq
    (ae_of_all _ fun _ => (eq_inv_mul_add_sub hl _ _).symm)

/-- For `λ ≠ 0` and a finite data size, the driver difference is square integrable on the
window. -/
theorem memLp_window_f
    (hD : PairDiff D ℱ hℱW hℱN T lam K KT α β₁ β₂ G ξ₀ X Y Z U b σ h f g qb qσ qh qf qg)
    (hl : lam ≠ 0) (hP : dataSize P ν T ξ₀ qb qσ qh qf qg ≠ ⊤) (k : Fin m) :
    MemLp (fun p : Ω × ℝ => f k p.1 p.2) 2 (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) :=
  (((hD.memLp_window_driver k).sub (hD.memLp_window_qf hP k)).const_mul lam⁻¹).ae_eq
    (ae_of_all _ fun _ => (eq_inv_mul_add_sub hl _ _).symm)

/-! ### The coercive blocks -/

/-- The integrand `|G δX|²` of the forward block is integrable on the window. -/
theorem integrable_blockX_window
    (hD : PairDiff D ℱ hℱW hℱN T lam K KT α β₁ β₂ G ξ₀ X Y Z U b σ h f g qb qσ qh qf qg)
    (𝒲 : D.CrossWitness ℱ) (hT : 0 < T) :
    Integrable (fun p : Ω × ℝ => (G *ᵥ fun i => X i p.2 p.1) ⬝ᵥ (G *ᵥ fun i => X i p.2 p.1))
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) :=
  integrable_dotProduct_of_memLp (memLp_mulVec G (hD.memLp_window_X 𝒲 hT))
    (memLp_mulVec G (hD.memLp_window_X 𝒲 hT))

/-- The integrand `|Gᵀ δY|² + |Gᵀ δZ|²_F + ‖Gᵀ δU‖²_{L²(ν)}` of the backward block is integrable
on the window. -/
theorem integrable_blockY_window
    (hD : PairDiff D ℱ hℱW hℱN T lam K KT α β₁ β₂ G ξ₀ X Y Z U b σ h f g qb qσ qh qf qg)
    (𝒲 : D.CrossWitness ℱ) (hT : 0 < T) :
    Integrable (fun p : Ω × ℝ => (Gᵀ *ᵥ fun k => Y k p.2 p.1) ⬝ᵥ (Gᵀ *ᵥ fun k => Y k p.2 p.1)
      + ∑ j, (Gᵀ *ᵥ fun k => Z k p.2 p.1 j) ⬝ᵥ (Gᵀ *ᵥ fun k => Z k p.2 p.1 j)
      + ∫ e, (Gᵀ *ᵥ fun k => U k p.2 p.1 e) ⬝ᵥ (Gᵀ *ᵥ fun k => U k p.2 p.1 e) ∂ν)
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := by
  have hY2 := integrable_dotProduct_of_memLp (memLp_mulVec Gᵀ (hD.memLp_window_Y 𝒲 hT))
    (memLp_mulVec Gᵀ (hD.memLp_window_Y 𝒲 hT))
  have hZ2 : ∀ j, Integrable (fun p : Ω × ℝ => (Gᵀ *ᵥ fun k => Z k p.2 p.1 j)
      ⬝ᵥ (Gᵀ *ᵥ fun k => Z k p.2 p.1 j)) (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) :=
    fun j => integrable_dotProduct_of_memLp (memLp_mulVec Gᵀ fun k => hD.memLp_window_Z k j)
      (memLp_mulVec Gᵀ fun k => hD.memLp_window_Z k j)
  have hU2 := (integrable_dotProduct_of_memLp (memLp_mulVec Gᵀ (hD.memLp_markedWindow_U (T := T)))
    (memLp_mulVec Gᵀ hD.memLp_markedWindow_U)).integral_prod_left
  exact (hY2.add (integrable_finsetSum Finset.univ fun j _ => hZ2 j)).add hU2

end PairDiff

end MVFBSDEJ.WellPosedness.Stability
