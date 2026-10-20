/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Stability.DiffWindow

/-!
# The forcing pairings of the coercivity step

After Assumption 2.5 is inserted into the `G`-energy identity (4.19) of the well-posedness paper,
six pairings remain in the proof of (4.22): the initial term `𝔼⟨G δξ₀, δY_0⟩`, the terminal
forcing `𝔼⟨G δX_T, q^g⟩` and the interior forcing
`𝔼 ∫_0^T (⟨q^b, GᵀδY⟩ + ⟨q^σ, GᵀδZ⟩_F − ⟨q^f, GδX⟩ + ∫_E ⟨q^h, GᵀδU⟩ dν) dt`. With a bound
`|G x|² ≤ g² |x|²` and `η > 0`, Young's inequality bounds each by `η` times a piece of
`N' = 𝔼|δX_T|² + 𝔼|δY_0|² + 𝔼 ∫_0^T (|δX|² + |δY|² + |δZ|²_F + ‖δU‖²)` plus `g²/(4η)` times the
matching piece of the data size: `𝔼|δY_0|²` against `𝔼|δξ₀|²`, `𝔼|δX_T|²` against `𝔼|q^g|²`, and
`𝔼 ∫_0^T (|δX|² + |δY|² + |δZ|²_F + ‖δU‖²)` against
`𝔼 ∫_0^T (|q^b|² + |q^σ|²_F + ‖q^h‖² + |q^f|²)`.

## Main statements

* `PairDiff.initial_pairing_le` — the initial term.
* `PairDiff.neg_terminal_forcing_le` — the terminal forcing.
* `PairDiff.integral_forcing_le` — the interior forcing.
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
  {qf : Fin m → Ω → ℝ → ℝ} {qg : Fin m → Ω → ℝ} {gG η : ℝ}

/-- For a finite data size, each coordinate of the terminal forcing is square integrable. -/
theorem memLp_qg
    (hD : PairDiff D ℱ hℱW hℱN T lam K KT α β₁ β₂ G ξ₀ X Y Z U b σ h f g qb qσ qh qf qg)
    (hP : dataSize P ν T ξ₀ qb qσ qh qf qg ≠ ⊤) (k : Fin m) : MemLp (qg k) 2 P :=
  Brownian.Ito.memLp_two_of_lintegral_sq_lt_top (hD.qg_meas k) (lt_of_le_of_lt
    (lintegral_mono fun ω => Finset.single_le_sum (f := fun k => (‖qg k ω‖₊ : ℝ≥0∞) ^ 2)
      (fun _ _ => by positivity) (Finset.mem_univ k)) (lt_top_of_dataSize_ne_top hP).2.1)

/-- **The initial pairing**: `𝔼⟨G δξ₀, δY_0⟩ ≤ η 𝔼|δY_0|² + (g²/(4η)) 𝔼|δξ₀|²`. -/
theorem initial_pairing_le
    (hD : PairDiff D ℱ hℱW hℱN T lam K KT α β₁ β₂ G ξ₀ X Y Z U b σ h f g qb qσ qh qf qg)
    (hT : 0 < T) (hGn : ∀ x : Fin n → ℝ, (G *ᵥ x) ⬝ᵥ (G *ᵥ x) ≤ gG ^ 2 * (x ⬝ᵥ x))
    (hη : 0 < η) :
    ∫ ω, (G *ᵥ fun i => ξ₀ i ω) ⬝ᵥ (fun k => Y k 0 ω) ∂P
      ≤ η * (∫⁻ ω, esq (fun k => Y k 0 ω) ∂P).toReal
        + gG ^ 2 / (4 * η) * (∫⁻ ω, esq (fun i => ξ₀ i ω) ∂P).toReal := by
  have mY0 : ∀ k, MemLp (Y k 0) 2 P := fun k => (hD.bwd k).memLp_initial hT.le
  have mξ : ∀ i, MemLp (ξ₀ i) 2 P := fun i => (hD.fwd i).ξ₀_sq
  have hξY := integrable_dotProduct_of_memLp (memLp_mulVec G mξ) mY0
  have hYY := integrable_dotProduct_of_memLp mY0 mY0
  have hξξ := integrable_dotProduct_of_memLp mξ mξ
  rw [← integral_dotProduct_self mY0, ← integral_dotProduct_self mξ,
    ← integral_const_mul, ← integral_const_mul,
    ← integral_add (hYY.const_mul η) (hξξ.const_mul _)]
  exact integral_mono hξY ((hYY.const_mul η).add (hξξ.const_mul _)) fun ω =>
    mulVec_dotProduct_le hGn hη _ _

/-- **The terminal forcing pairing**: `−𝔼⟨q^g, G δX_T⟩ ≤ η 𝔼|δX_T|² + (g²/(4η)) 𝔼|q^g|²`. -/
theorem neg_terminal_forcing_le
    (hD : PairDiff D ℱ hℱW hℱN T lam K KT α β₁ β₂ G ξ₀ X Y Z U b σ h f g qb qσ qh qf qg)
    (hT : 0 < T) (hP : dataSize P ν T ξ₀ qb qσ qh qf qg ≠ ⊤)
    (hGn : ∀ x : Fin n → ℝ, (G *ᵥ x) ⬝ᵥ (G *ᵥ x) ≤ gG ^ 2 * (x ⬝ᵥ x)) (hη : 0 < η) :
    -∫ ω, (fun k => qg k ω) ⬝ᵥ (G *ᵥ fun i => X i T ω) ∂P
      ≤ η * (∫⁻ ω, esq (fun i => X i T ω) ∂P).toReal
        + gG ^ 2 / (4 * η) * (∫⁻ ω, esq (fun k => qg k ω) ∂P).toReal := by
  have mXT : ∀ i, MemLp (X i T) 2 P := fun i => (hD.fwd i).memLp_terminal hT.le
  have mqg := hD.memLp_qg hP
  have hqgX := integrable_dotProduct_of_memLp mqg (memLp_mulVec G mXT)
  have hXX := integrable_dotProduct_of_memLp mXT mXT
  have hqq := integrable_dotProduct_of_memLp mqg mqg
  rw [← integral_neg, ← integral_dotProduct_self mXT, ← integral_dotProduct_self mqg,
    ← integral_const_mul, ← integral_const_mul,
    ← integral_add (hXX.const_mul η) (hqq.const_mul _)]
  exact integral_mono hqgX.neg ((hXX.const_mul η).add (hqq.const_mul _)) fun ω =>
    neg_dotProduct_mulVec_le hGn hη _ _

/-- **The interior forcing pairing of (4.19)**: over a filtration with a cross witness, for a
finite data size,

`𝔼 ∫_0^T (⟨q^b, GᵀδY⟩ + ⟨q^σ, GᵀδZ⟩_F − ⟨q^f, GδX⟩ + ∫_E ⟨q^h, GᵀδU⟩ dν) dt
  ≤ η (I_X + J) + (g²/(4η)) 𝔼 ∫_0^T (|q^b|² + |q^σ|²_F + ‖q^h‖² + |q^f|²) dt`. -/
theorem integral_forcing_le
    (hD : PairDiff D ℱ hℱW hℱN T lam K KT α β₁ β₂ G ξ₀ X Y Z U b σ h f g qb qσ qh qf qg)
    (𝒲 : D.CrossWitness ℱ) (hT : 0 < T) (hP : dataSize P ν T ξ₀ qb qσ qh qf qg ≠ ⊤)
    (hGn : ∀ x : Fin n → ℝ, (G *ᵥ x) ⬝ᵥ (G *ᵥ x) ≤ gG ^ 2 * (x ⬝ᵥ x)) (hη : 0 < η) :
    ∫ p, ((fun i => qb i p.1 p.2) ⬝ᵥ (Gᵀ *ᵥ fun k => Y k p.2 p.1)
        + ∑ j, (fun i => qσ i p.2 p.1 j) ⬝ᵥ (Gᵀ *ᵥ fun k => Z k p.2 p.1 j)
        - (fun k => qf k p.1 p.2) ⬝ᵥ (G *ᵥ fun i => X i p.2 p.1)
        + ∫ e, (fun i => qh i p.2 p.1 e) ⬝ᵥ (Gᵀ *ᵥ fun k => U k p.2 p.1 e) ∂ν)
        ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T)))
      ≤ η * ((∑ i, Brownian.Ito.energy P T (fun ω s => X i s ω)).toReal
          + (∑ k, Brownian.Ito.energy P T (fun ω s => Y k s ω)
            + ∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z k s ω j)
            + ∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U k s ω e)).toReal)
        + gG ^ 2 / (4 * η) * ((∑ i, Brownian.Ito.energy P T (qb i)).toReal
          + (∑ i, ∑ j, Brownian.Ito.energy P T (fun ω s => qσ i s ω j)).toReal
          + (∑ i, Poisson.Compensated.markedEnergy P ν T (fun ω s e => qh i s ω e)).toReal
          + (∑ k, Brownian.Ito.energy P T (qf k)).toReal) := by
  obtain ⟨-, -, hqbf, hqσf, hqhf, hqff⟩ := lt_top_of_dataSize_ne_top hP
  set μ₂ := P.prod (volume.restrict (Set.Icc (0 : ℝ) T)) with hμ₂
  have mX := hD.memLp_window_X 𝒲 hT
  have mY := hD.memLp_window_Y 𝒲 hT
  have mZ := hD.memLp_window_Z (T := T)
  have mU := hD.memLp_markedWindow_U (T := T)
  have mqb := hD.memLp_window_qb hP
  have mqσ := hD.memLp_window_qσ hP
  have mqf := hD.memLp_window_qf hP
  have mqh := hD.memLp_markedWindow_qh hP
  set Ff : Ω × ℝ → ℝ := fun p => (fun i => qb i p.1 p.2) ⬝ᵥ (Gᵀ *ᵥ fun k => Y k p.2 p.1)
    + ∑ j, (fun i => qσ i p.2 p.1 j) ⬝ᵥ (Gᵀ *ᵥ fun k => Z k p.2 p.1 j)
    - (fun k => qf k p.1 p.2) ⬝ᵥ (G *ᵥ fun i => X i p.2 p.1)
    + ∫ e, (fun i => qh i p.2 p.1 e) ⬝ᵥ (Gᵀ *ᵥ fun k => U k p.2 p.1 e) ∂ν with hFf
  set Wf : Ω × ℝ → ℝ := fun p => (fun i => X i p.2 p.1) ⬝ᵥ (fun i => X i p.2 p.1)
    + ((fun k => Y k p.2 p.1) ⬝ᵥ (fun k => Y k p.2 p.1) + ∑ k, Z k p.2 p.1 ⬝ᵥ Z k p.2 p.1
      + ∫ e, (fun k => U k p.2 p.1 e) ⬝ᵥ (fun k => U k p.2 p.1 e) ∂ν) with hWf
  set Qf : Ω × ℝ → ℝ := fun p => (fun i => qb i p.1 p.2) ⬝ᵥ (fun i => qb i p.1 p.2)
    + ∑ i, qσ i p.2 p.1 ⬝ᵥ qσ i p.2 p.1
    + ∫ e, (fun i => qh i p.2 p.1 e) ⬝ᵥ (fun i => qh i p.2 p.1 e) ∂ν
    + (fun k => qf k p.1 p.2) ⬝ᵥ (fun k => qf k p.1 p.2) with hQf
  have hFi : Integrable Ff μ₂ := by
    have hi := integrable_gPairing (ν := ν) G mqb mqσ mqf mqh mX mY mZ mU
    rw [hFf]
    exact hi
  have hX2 := integrable_dotProduct_of_memLp mX mX
  have hB2 : Integrable (fun p : Ω × ℝ => (fun k => Y k p.2 p.1) ⬝ᵥ (fun k => Y k p.2 p.1)
      + ∑ k, Z k p.2 p.1 ⬝ᵥ Z k p.2 p.1
      + ∫ e, (fun k => U k p.2 p.1 e) ⬝ᵥ (fun k => U k p.2 p.1 e) ∂ν) μ₂ :=
    ((integrable_dotProduct_of_memLp mY mY).add (integrable_finsetSum Finset.univ fun k _ =>
      integrable_dotProduct_of_memLp (mZ k) (mZ k))).add
      (integrable_dotProduct_of_memLp mU mU).integral_prod_left
  have hWi : Integrable Wf μ₂ := by
    have hi := hX2.add hB2
    rw [hWf]
    exact hi
  have hqb2 := integrable_dotProduct_of_memLp mqb mqb
  have hqσ2 : Integrable (fun p : Ω × ℝ => ∑ i, qσ i p.2 p.1 ⬝ᵥ qσ i p.2 p.1) μ₂ :=
    integrable_finsetSum Finset.univ fun i _ => integrable_dotProduct_of_memLp (mqσ i) (mqσ i)
  have hqh2 := (integrable_dotProduct_of_memLp mqh mqh).integral_prod_left
  have hqf2 := integrable_dotProduct_of_memLp mqf mqf
  have hQi : Integrable Qf μ₂ := by
    have hi := ((hqb2.add hqσ2).add hqh2).add hqf2
    rw [hQf]
    exact hi
  -- Young's inequality at almost every point of the window
  have hFW : ∀ᵐ p ∂μ₂, Ff p ≤ η * Wf p + gG ^ 2 / (4 * η) * Qf p := by
    filter_upwards [(integrable_dotProduct_of_memLp mqh (memLp_mulVec Gᵀ mU)).prod_right_ae,
      (integrable_dotProduct_of_memLp mU mU).prod_right_ae,
      (integrable_dotProduct_of_memLp mqh mqh).prod_right_ae] with p h1 h2 h3
    have h1' : Integrable (fun e => (fun i => qh i p.2 p.1 e)
        ⬝ᵥ (Gᵀ *ᵥ fun k => U k p.2 p.1 e)) ν := h1
    have h2' : Integrable (fun e => (fun k => U k p.2 p.1 e) ⬝ᵥ (fun k => U k p.2 p.1 e)) ν := h2
    have h3' : Integrable (fun e => (fun i => qh i p.2 p.1 e) ⬝ᵥ (fun i => qh i p.2 p.1 e)) ν :=
      h3
    have hJ : ∫ e, (fun i => qh i p.2 p.1 e) ⬝ᵥ (Gᵀ *ᵥ fun k => U k p.2 p.1 e) ∂ν
        ≤ η * ∫ e, (fun k => U k p.2 p.1 e) ⬝ᵥ (fun k => U k p.2 p.1 e) ∂ν
          + gG ^ 2 / (4 * η) * ∫ e, (fun i => qh i p.2 p.1 e) ⬝ᵥ (fun i => qh i p.2 p.1 e) ∂ν := by
      rw [← integral_const_mul, ← integral_const_mul,
        ← integral_add (h2'.const_mul η) (h3'.const_mul _)]
      refine integral_mono h1' ((h2'.const_mul η).add (h3'.const_mul _)) fun e => ?_
      beta_reduce
      rw [dotProduct_transpose_mulVec]
      exact mulVec_dotProduct_le hGn hη _ _
    have key := gPairing_le hGn hη (fun i => qb i p.1 p.2) (fun i => qσ i p.2 p.1)
      (fun k => qf k p.1 p.2) (fun i => X i p.2 p.1) (fun k => Y k p.2 p.1)
      (fun k => Z k p.2 p.1) hJ
    rw [hFf, hWf, hQf]
    linarith
  have hFle : ∫ p, Ff p ∂μ₂ ≤ η * ∫ p, Wf p ∂μ₂ + gG ^ 2 / (4 * η) * ∫ p, Qf p ∂μ₂ := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (hWi.const_mul η) (hQi.const_mul _)]
    exact integral_mono_ae hFi ((hWi.const_mul η).add (hQi.const_mul _)) hFW
  -- the window integrals of `W` and `Q`
  have eW : ∫ p, Wf p ∂μ₂ = (∑ i, Brownian.Ito.energy P T (fun ω s => X i s ω)).toReal
      + (∑ k, Brownian.Ito.energy P T (fun ω s => Y k s ω)
        + ∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z k s ω j)
        + ∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U k s ω e)).toReal := by
    rw [hWf, integral_add hX2 hB2, hD.integral_backSq_window 𝒲 hT,
      integral_dotProduct_self_window (x := fun i ω s => X i s ω)
        (fun i => ((hD.fwd i).linearBSDEJ hT.le).measurable_uncurry.comp measurable_swap)
        fun i => (hD.fwd i).energy_lt_top 𝒲 hT]
  have eQ : ∫ p, Qf p ∂μ₂ = (∑ i, Brownian.Ito.energy P T (qb i)).toReal
      + (∑ i, ∑ j, Brownian.Ito.energy P T (fun ω s => qσ i s ω j)).toReal
      + (∑ i, Poisson.Compensated.markedEnergy P ν T (fun ω s e => qh i s ω e)).toReal
      + (∑ k, Brownian.Ito.energy P T (qf k)).toReal := by
    rw [hQf, integral_add (f := fun p => (fun i => qb i p.1 p.2) ⬝ᵥ (fun i => qb i p.1 p.2)
        + ∑ i, qσ i p.2 p.1 ⬝ᵥ qσ i p.2 p.1
        + ∫ e, (fun i => qh i p.2 p.1 e) ⬝ᵥ (fun i => qh i p.2 p.1 e) ∂ν)
        ((hqb2.add hqσ2).add hqh2) hqf2,
      integral_add (f := fun p => (fun i => qb i p.1 p.2) ⬝ᵥ (fun i => qb i p.1 p.2)
        + ∑ i, qσ i p.2 p.1 ⬝ᵥ qσ i p.2 p.1) (hqb2.add hqσ2) hqh2,
      integral_add hqb2 hqσ2,
      integral_finsetSum _ fun i _ => integrable_dotProduct_of_memLp (mqσ i) (mqσ i),
      integral_dotProduct_self_window (x := qb) hD.qb_meas hqbf,
      integral_dotProduct_self_window (x := qf) hD.qf_meas hqff,
      integral_integral_dotProduct_self_markedWindow (x := fun i ω s e => qh i s ω e)
        hD.qh_meas hqhf,
      ENNReal.toReal_sum fun i _ => ENNReal.sum_ne_top.mpr fun j _ => (hqσf i j).ne]
    congr 3
    exact Finset.sum_congr rfl fun i _ => integral_dotProduct_self_window
      (x := fun j ω s => qσ i s ω j) (fun j => hD.qσ_meas i j) (hqσf i)
  rw [← eW, ← eQ]
  exact hFle

end PairDiff

end MVFBSDEJ.WellPosedness.Stability
