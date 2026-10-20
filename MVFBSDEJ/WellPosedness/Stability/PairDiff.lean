/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Stability.ForwardEq
import MVFBSDEJ.WellPosedness.BrownianPoisson.Estimate

/-!
# The difference system of Lemma 4.3

Let `Θ¹, Θ²` solve the `λ`-scaled forced system (4.1) of the well-posedness paper with initial
data `ξ₀ᵏ` and forcings `qᵏ`. Writing `δ· = ·¹ − ·²`, `q = q¹ − q²` and `δψ` for the coefficient
differences along the pair, the difference `(δX, δY, δZ, δU)` solves the linear system

`dδX_t = (λ δb_t + q^b_t) dt + (λ δσ_t + q^σ_t) dW_t + ∫_E (λ δh_t(e) + q^h_t(e)) Ñ(dt, de)`,
`δX_0 = δξ₀`,                                                                        (4.15)

`dδY_t = −(λ δf_t + q^f_t) dt + δZ_t dW_t + ∫_E δU_t(e) Ñ(dt, de)`,
`δY_T = λ δg_T + q^g_T`.                                                             (4.16)

The proof of Lemma 4.3 uses the coefficients only through the differences along the pair: the
expected Lipschitz bound (3.2) — Assumption 2.3 with the synchronous coupling bound (2.8) — and
Assumption 2.5 at the pair. The structure `PairDiff` records these, law-free and
coefficient-free, in coordinates: `δX = (δX_i)_{i < n}`, `δY = (δY_k)_{k < m}`, the rows
`δZ_k ∈ ℝᵈ` of the `m × d` integrand, the rows `δU_k` of the jump integrand, and likewise for the
coefficient differences and the forcings. Norms are Euclidean, Frobenius and `L²(ν)`, written as
sums of squares of coordinates, and `G ∈ ℝ^{m×n}` acts through `Matrix.mulVec`.

The forcing differences are jointly measurable, as the forcings of (4.1) are progressive. The
expected Lipschitz bound is stated in `ℝ≥0∞` and needs no integrability; the monotonicity at the
pair is stated with Bochner integrals, meaningful at almost every time.

## Main definitions

* `esq` — the squared Euclidean norm of a coordinate vector, in `ℝ≥0∞`.
* `PairDiff` — the difference system (4.15)–(4.16) with (3.2) and Assumption 2.5 at the pair.
* `dataSize` — the data size `P = 𝔼|δξ₀|² + 𝔼|q^g_T|² + 𝔼 ∫_0^T (|q^b|² + |q^σ|²_F + ‖q^h‖² +
  |q^f|²)` of (4.14).
* `diffSize` — `N' = 𝔼|δX_T|² + 𝔼|δY_0|² + 𝔼 ∫_0^T (|δX|² + |δY|² + |δZ|²_F + ‖δU‖²)`.

## Main statements

* `PairDiff.init` — `δX_0 = δξ₀` almost surely.
* `PairDiff.diffSize_lt_top` — `N' < ∞`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped NNReal ENNReal

namespace MVFBSDEJ.WellPosedness.Stability

open LevyStochCalc.BSDEJ.Solves LevyStochCalc MVFBSDEJ.WellPosedness.BrownianPoisson

universe u v w

/-- The squared Euclidean norm `∑ᵢ xᵢ²` of a coordinate vector, in `ℝ≥0∞`. -/
noncomputable def esq {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ≥0∞ :=
  ∑ i, (‖x i‖₊ : ℝ≥0∞) ^ 2

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d n m : ℕ}

/-- **The difference system of Lemma 4.3.** `(δX, δY, δZ, δU)` solves (4.15)–(4.16) at parameter
`λ` over the filtration `ℱ` carrying the driver `D`, with initial difference `δξ₀`, coefficient
differences `(δb, δσ, δh, δf, δg)` along the pair and jointly measurable forcing differences
`(q^b, q^σ, q^h, q^f, q^g)`; the coefficient differences obey the expected Lipschitz bound (3.2)
with constants `K` (interior) and `K_T` (terminal), and the pair obeys Assumption 2.5 with
coupling matrix `G` and constants `α, β₁, β₂`. -/
structure PairDiff (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ) (T lam K KT α β₁ β₂ : ℝ)
    (G : Matrix (Fin m) (Fin n) ℝ) (ξ₀ : Fin n → Ω → ℝ)
    (X : Fin n → ℝ → Ω → ℝ) (Y : Fin m → ℝ → Ω → ℝ)
    (Z : Fin m → ℝ → Ω → Fin d → ℝ) (U : Fin m → ℝ → Ω → E → ℝ)
    (b : Fin n → Ω → ℝ → ℝ) (σ : Fin n → ℝ → Ω → Fin d → ℝ) (h : Fin n → ℝ → Ω → E → ℝ)
    (f : Fin m → Ω → ℝ → ℝ) (g : Fin m → Ω → ℝ)
    (qb : Fin n → Ω → ℝ → ℝ) (qσ : Fin n → ℝ → Ω → Fin d → ℝ) (qh : Fin n → ℝ → Ω → E → ℝ)
    (qf : Fin m → Ω → ℝ → ℝ) (qg : Fin m → Ω → ℝ) : Prop where
  /-- (4.15): each coordinate of `δX` solves the linear forward equation from `δξ₀` with drift
  `λ δb + q^b`, diffusion vector `λ δσ + q^σ` and jump integrand `λ δh + q^h`. -/
  fwd : ∀ i, LinearFSDEJ D ℱ hℱW hℱN T (ξ₀ i) (fun ω s => lam * b i ω s + qb i ω s) (X i)
    (fun s ω j => lam * σ i s ω j + qσ i s ω j) (fun s ω e => lam * h i s ω e + qh i s ω e)
  /-- (4.16): each coordinate of `(δY, δZ, δU)` solves the linear backward equation with terminal
  value `λ δg + q^g` and drift `λ δf + q^f`. -/
  bwd : ∀ k, LinearBSDEJ D ℱ hℱW hℱN T (fun ω => lam * g k ω + qg k ω)
    (fun ω s => lam * f k ω s + qf k ω s) (Y k) (Z k) (U k)
  /-- The drift forcing is jointly measurable. -/
  qb_meas : ∀ i, Measurable (Function.uncurry (qb i))
  /-- The diffusion forcing is jointly measurable. -/
  qσ_meas : ∀ i j, Measurable (Function.uncurry fun ω s => qσ i s ω j)
  /-- The jump forcing is jointly measurable. -/
  qh_meas : ∀ i, Measurable fun p : Ω × ℝ × E => qh i p.2.1 p.1 p.2.2
  /-- The driver forcing is jointly measurable. -/
  qf_meas : ∀ k, Measurable (Function.uncurry (qf k))
  /-- The terminal forcing is almost everywhere strongly measurable. -/
  qg_meas : ∀ k, AEStronglyMeasurable (qg k) P
  /-- (3.2): Assumption 2.3 with the coupling bound (2.8), in expectation along the pair, at
  almost every time. -/
  lip : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
    ∫⁻ ω, (esq (fun i => b i ω s) + ∑ i, esq (σ i s ω)
        + ∑ i, ∫⁻ e, (‖h i s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν + esq (fun k => f k ω s)) ∂P
      ≤ ENNReal.ofReal K * ∫⁻ ω, (esq (fun i => X i s ω) + esq (fun k => Y k s ω)
        + ∑ k, esq (Z k s ω) + ∑ k, ∫⁻ e, (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ∂P
  /-- (2.6) with (2.9), in expectation along the pair. -/
  lipT : ∫⁻ ω, esq (fun k => g k ω) ∂P ≤ ENNReal.ofReal KT * ∫⁻ ω, esq (fun i => X i T ω) ∂P
  /-- Assumption 2.5, interior (2.7), at the pair, at almost every time. -/
  mono : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
    ∫ ω, ((fun i => b i ω s) ⬝ᵥ (Gᵀ *ᵥ fun k => Y k s ω)
        + ∑ j, (fun i => σ i s ω j) ⬝ᵥ (Gᵀ *ᵥ fun k => Z k s ω j)
        - (fun k => f k ω s) ⬝ᵥ (G *ᵥ fun i => X i s ω)
        + ∫ e, (fun i => h i s ω e) ⬝ᵥ (Gᵀ *ᵥ fun k => U k s ω e) ∂ν) ∂P
      ≤ -β₁ * ∫ ω, ((Gᵀ *ᵥ fun k => Y k s ω) ⬝ᵥ (Gᵀ *ᵥ fun k => Y k s ω)
          + ∑ j, (Gᵀ *ᵥ fun k => Z k s ω j) ⬝ᵥ (Gᵀ *ᵥ fun k => Z k s ω j)
          + ∫ e, (Gᵀ *ᵥ fun k => U k s ω e) ⬝ᵥ (Gᵀ *ᵥ fun k => U k s ω e) ∂ν) ∂P
        - β₂ * ∫ ω, (G *ᵥ fun i => X i s ω) ⬝ᵥ (G *ᵥ fun i => X i s ω) ∂P
  /-- Assumption 2.5, terminal, at the pair. -/
  monoT : α * ∫ ω, (G *ᵥ fun i => X i T ω) ⬝ᵥ (G *ᵥ fun i => X i T ω) ∂P
    ≤ ∫ ω, (fun k => g k ω) ⬝ᵥ (G *ᵥ fun i => X i T ω) ∂P

/-- The data size `P = 𝔼|δξ₀|² + 𝔼|q^g|² + 𝔼 ∫_0^T (|q^b|² + |q^σ|²_F + ‖q^h‖²_{L²(ν)} + |q^f|²)`
of (4.14). -/
noncomputable def dataSize (P : Measure Ω) (ν : Measure E) (T : ℝ) (ξ₀ : Fin n → Ω → ℝ)
    (qb : Fin n → Ω → ℝ → ℝ) (qσ : Fin n → ℝ → Ω → Fin d → ℝ) (qh : Fin n → ℝ → Ω → E → ℝ)
    (qf : Fin m → Ω → ℝ → ℝ) (qg : Fin m → Ω → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, esq (fun i => ξ₀ i ω) ∂P + ∫⁻ ω, esq (fun k => qg k ω) ∂P
    + ∑ i, Brownian.Ito.energy P T (qb i)
    + ∑ i, ∑ j, Brownian.Ito.energy P T (fun ω s => qσ i s ω j)
    + ∑ i, Poisson.Compensated.markedEnergy P ν T (fun ω s e => qh i s ω e)
    + ∑ k, Brownian.Ito.energy P T (qf k)

/-- The size `N' = 𝔼|δX_T|² + 𝔼|δY_0|² + 𝔼 ∫_0^T (|δX|² + |δY|² + |δZ|²_F + ‖δU‖²_{L²(ν)})` of a
difference, the quantity absorbed in the closure step of Lemma 4.3. -/
noncomputable def diffSize (P : Measure Ω) (ν : Measure E) (T : ℝ) (X : Fin n → ℝ → Ω → ℝ)
    (Y : Fin m → ℝ → Ω → ℝ) (Z : Fin m → ℝ → Ω → Fin d → ℝ) (U : Fin m → ℝ → Ω → E → ℝ) :
    ℝ≥0∞ :=
  ∫⁻ ω, esq (fun i => X i T ω) ∂P + ∫⁻ ω, esq (fun k => Y k 0 ω) ∂P
    + ∑ i, Brownian.Ito.energy P T (fun ω s => X i s ω)
    + ∑ k, Brownian.Ito.energy P T (fun ω s => Y k s ω)
    + ∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z k s ω j)
    + ∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U k s ω e)

omit [IsProbabilityMeasure P] in
/-- The lower integral of `esq` of finitely many square-integrable coordinates is finite. -/
theorem lintegral_esq_lt_top {ι : Type*} [Fintype ι] {x : ι → Ω → ℝ}
    (hx : ∀ i, MemLp (x i) 2 P) : ∫⁻ ω, esq (fun i => x i ω) ∂P < ⊤ := by
  unfold esq
  rw [lintegral_finsetSum' _ fun i _ =>
    ((hx i).aestronglyMeasurable.aemeasurable.nnnorm.coe_nnreal_ennreal).pow_const 2]
  exact ENNReal.sum_lt_top.mpr fun i _ =>
    Ito.SecondMoment.lintegral_sq_lt_top_of_memLp_two (hx i)

/-- `x = λ⁻¹ ((λ x + q) − q)` for `λ ≠ 0`. -/
theorem eq_inv_mul_add_sub {l : ℝ} (hl : l ≠ 0) (x q : ℝ) : x = l⁻¹ * ((l * x + q) - q) := by
  rw [add_sub_cancel_right, inv_mul_cancel_left₀ hl]

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
  (hD : PairDiff D ℱ hℱW hℱN T lam K KT α β₁ β₂ G ξ₀ X Y Z U b σ h f g qb qσ qh qf qg)
include hD

/-- `δX_0 = δξ₀` almost surely. -/
theorem init (hT : 0 ≤ T) (i : Fin n) : X i 0 =ᵐ[P] ξ₀ i :=
  (hD.fwd i).initial_ae_eq hT

/-! ### Finiteness of `N'` -/

/-- **The size `N'` of the difference is finite**, over a filtration whose null sets lie in its
time-`0` field, whose right-continuation is constant before `0`, and which admits a cross
witness. -/
theorem diffSize_lt_top (𝒲 : D.CrossWitness ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T) :
    diffSize P ν T X Y Z U < ⊤ := by
  have hXT : ∫⁻ ω, esq (fun i => X i T ω) ∂P < ⊤ :=
    lintegral_esq_lt_top fun i => (hD.fwd i).memLp_terminal hT.le
  have hY0 : ∫⁻ ω, esq (fun k => Y k 0 ω) ∂P < ⊤ :=
    lintegral_esq_lt_top fun k => (hD.bwd k).memLp_initial hT.le
  have hX : ∀ i, Brownian.Ito.energy P T (fun ω s => X i s ω) < ⊤ := fun i =>
    energy_le_of_biSup.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (((hD.fwd i).linearBSDEJ hT.le).lintegral_biSup_sq_lt_top 𝒲 hℱ0 hnull hT))
  have hY : ∀ k, Brownian.Ito.energy P T (fun ω s => Y k s ω) < ⊤ := fun k =>
    energy_le_of_biSup.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      ((hD.bwd k).lintegral_biSup_sq_lt_top 𝒲 hℱ0 hnull hT))
  unfold diffSize
  refine ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr
    ⟨ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨hXT, hY0⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact ENNReal.sum_lt_top.mpr fun i _ => hX i
  · exact ENNReal.sum_lt_top.mpr fun k _ => hY k
  · exact ENNReal.sum_lt_top.mpr fun k _ => ENNReal.sum_lt_top.mpr fun j _ =>
      lt_top_iff_ne_top.mpr ((hD.bwd k).Z_sq j)
  · exact ENNReal.sum_lt_top.mpr fun k _ => lt_top_iff_ne_top.mpr (hD.bwd k).U_sq

end PairDiff

end MVFBSDEJ.WellPosedness.Stability
