/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Stability.GEnergy
import MVFBSDEJ.WellPosedness.Stability.ForcingYoung

/-!
# The coercivity inequality of Lemma 4.3

Step 2 of the proof of Lemma 4.3 of the well-posedness paper inserts Assumption 2.5 into the
`G`-energy identity (4.19). Splitting each integrand of (4.19) as `λ δψ + q^ψ`, the interior
monotonicity (2.7) at the pair bounds the `λ`-part of the time integral by
`−λ β₁ 𝔼 ∫_0^T (|GᵀδY|² + |GᵀδZ|²_F + ‖GᵀδU‖²) − λ β₂ 𝔼 ∫_0^T |GδX|²`, and the terminal
monotonicity bounds `𝔼⟨G δX_T, δY_T⟩ = λ 𝔼⟨G δX_T, δg⟩ + 𝔼⟨G δX_T, q^g⟩` below by
`λ α 𝔼|GδX_T|² + 𝔼⟨G δX_T, q^g⟩`. The remaining six pairings — the initial term
`𝔼⟨G δξ₀, δY_0⟩`, the terminal forcing and the four interior forcings — are bounded by Young's
inequality with `|G v| ≤ ‖G‖ |v|`, each by `η` times a piece of
`N' = 𝔼|δX_T|² + 𝔼|δY_0|² + 𝔼 ∫_0^T (|δX|² + |δY|² + |δZ|²_F + ‖δU‖²)` plus `‖G‖²/(4η)` times
the matching piece of the data size `P`. This is (4.22):

`λ (α 𝔼|GδX_T|² + β₂ 𝔼 ∫_0^T |GδX|² + β₁ 𝔼 ∫_0^T (|GᵀδY|² + |GᵀδZ|²_F + ‖GᵀδU‖²))
  ≤ η N' + (‖G‖²/(4η)) P`   for every `η > 0`,

in the form of the hypothesis of the closure step, with `N' = A + Y₀ + I_X + J` for
`A = 𝔼|δX_T|²`, `Y₀ = 𝔼|δY_0|²`, `I_X = 𝔼 ∫_0^T |δX|²` and
`J = 𝔼 ∫_0^T (|δY|² + |δZ|²_F + ‖δU‖²)`. The operator norm enters only through a bound
`|G x|² ≤ g² |x|²` for every `x`.

## Main definitions

* `blockXT`, `blockX`, `blockY` — the coercive blocks `𝔼|GδX_T|²`, `𝔼 ∫_0^T |GδX|²` and
  `𝔼 ∫_0^T (|GᵀδY|² + |GᵀδZ|²_F + ‖GᵀδU‖²)`.

## Main statements

* `PairDiff.coercivity` — (4.22) for every `η > 0`.
* `PairDiff.rankCase_blocks` — the rank case of Assumption 2.4 bounds `J`, or `A` and `I_X`, by
  the matching blocks.
* `toReal_diffSize` — `N' = A + Y₀ + I_X + J`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped NNReal ENNReal

namespace MVFBSDEJ.WellPosedness.Stability

open LevyStochCalc.BSDEJ.Solves LevyStochCalc MVFBSDEJ.WellPosedness.BrownianPoisson

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d n m : ℕ}

/-- The terminal block `𝔼|G δX_T|²` of (4.22). -/
noncomputable def blockXT (P : Measure Ω) (G : Matrix (Fin m) (Fin n) ℝ)
    (X : Fin n → ℝ → Ω → ℝ) (T : ℝ) : ℝ :=
  ∫ ω, (G *ᵥ fun i => X i T ω) ⬝ᵥ (G *ᵥ fun i => X i T ω) ∂P

/-- The forward block `𝔼 ∫_0^T |G δX_s|² ds` of (4.22). -/
noncomputable def blockX (P : Measure Ω) (G : Matrix (Fin m) (Fin n) ℝ)
    (X : Fin n → ℝ → Ω → ℝ) (T : ℝ) : ℝ :=
  ∫ s in Set.Icc (0 : ℝ) T, ∫ ω, (G *ᵥ fun i => X i s ω) ⬝ᵥ (G *ᵥ fun i => X i s ω) ∂P

/-- The backward block `𝔼 ∫_0^T (|Gᵀ δY_s|² + |Gᵀ δZ_s|²_F + ‖Gᵀ δU_s‖²_{L²(ν)}) ds` of
(4.22). -/
noncomputable def blockY (P : Measure Ω) (ν : Measure E) (G : Matrix (Fin m) (Fin n) ℝ)
    (Y : Fin m → ℝ → Ω → ℝ) (Z : Fin m → ℝ → Ω → Fin d → ℝ) (U : Fin m → ℝ → Ω → E → ℝ)
    (T : ℝ) : ℝ :=
  ∫ s in Set.Icc (0 : ℝ) T, ∫ ω, ((Gᵀ *ᵥ fun k => Y k s ω) ⬝ᵥ (Gᵀ *ᵥ fun k => Y k s ω)
    + ∑ j, (Gᵀ *ᵥ fun k => Z k s ω j) ⬝ᵥ (Gᵀ *ᵥ fun k => Z k s ω j)
    + ∫ e, (Gᵀ *ᵥ fun k => U k s ω e) ⬝ᵥ (Gᵀ *ᵥ fun k => U k s ω e) ∂ν) ∂P

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

/-! ### The coercivity inequality -/

/-- **The coercivity inequality (4.22) of Lemma 4.3.** For the difference system at `λ ≥ 0`
with finite data size `P`, over a filtration with a cross witness, and a coupling matrix with
`|G x|² ≤ g² |x|²`, for every `η > 0`

`λ (α 𝔼|GδX_T|² + β₂ 𝔼 ∫_0^T |GδX|² + β₁ 𝔼 ∫_0^T (|GᵀδY|² + |GᵀδZ|²_F + ‖GᵀδU‖²))
  ≤ η (A + Y₀ + I_X + J) + (g²/(4η)) P`,

with `A = 𝔼|δX_T|²`, `Y₀ = 𝔼|δY_0|²`, `I_X = 𝔼 ∫_0^T |δX|²` and
`J = 𝔼 ∫_0^T (|δY|² + |δZ|²_F + ‖δU‖²)`. -/
theorem coercivity
    (hD : PairDiff D ℱ hℱW hℱN T lam K KT α β₁ β₂ G ξ₀ X Y Z U b σ h f g qb qσ qh qf qg)
    (𝒲 : D.CrossWitness ℱ) (hT : 0 < T) (hlam0 : 0 ≤ lam)
    (hP : dataSize P ν T ξ₀ qb qσ qh qf qg ≠ ⊤) {gG : ℝ}
    (hGn : ∀ x : Fin n → ℝ, (G *ᵥ x) ⬝ᵥ (G *ᵥ x) ≤ gG ^ 2 * (x ⬝ᵥ x)) :
    ∀ η : ℝ, 0 < η →
      lam * (α * blockXT P G X T + β₂ * blockX P G X T + β₁ * blockY P ν G Y Z U T)
        ≤ η * ((∫⁻ ω, esq (fun i => X i T ω) ∂P).toReal
            + (∫⁻ ω, esq (fun k => Y k 0 ω) ∂P).toReal
            + (∑ i, Brownian.Ito.energy P T (fun ω s => X i s ω)).toReal
            + (∑ k, Brownian.Ito.energy P T (fun ω s => Y k s ω)
              + ∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z k s ω j)
              + ∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U k s ω e)).toReal)
          + gG ^ 2 / (4 * η) * (dataSize P ν T ξ₀ qb qσ qh qf qg).toReal := by
  intro η hη
  rcases hlam0.eq_or_lt with hl0 | hlpos
  · rw [← hl0, zero_mul]
    positivity
  have hl : lam ≠ 0 := hlpos.ne'
  set μ₂ := P.prod (volume.restrict (Set.Icc (0 : ℝ) T)) with hμ₂
  have mX := hD.memLp_window_X 𝒲 hT
  have mY := hD.memLp_window_Y 𝒲 hT
  have mZ := hD.memLp_window_Z (T := T)
  have mU := hD.memLp_markedWindow_U (T := T)
  have mh := hD.memLp_markedWindow_h hl hP
  have mqh := hD.memLp_markedWindow_qh hP
  -- the integrands of (4.19) on the window: full, coefficient and forcing parts
  set Hf : Ω × ℝ → ℝ := fun p => (fun i => lam * b i p.1 p.2 + qb i p.1 p.2)
      ⬝ᵥ (Gᵀ *ᵥ fun k => Y k p.2 p.1)
    + ∑ j, (fun i => lam * σ i p.2 p.1 j + qσ i p.2 p.1 j) ⬝ᵥ (Gᵀ *ᵥ fun k => Z k p.2 p.1 j)
    - (fun k => lam * f k p.1 p.2 + qf k p.1 p.2) ⬝ᵥ (G *ᵥ fun i => X i p.2 p.1)
    + ∫ e, (fun i => lam * h i p.2 p.1 e + qh i p.2 p.1 e) ⬝ᵥ (Gᵀ *ᵥ fun k => U k p.2 p.1 e) ∂ν
    with hHf
  set Mf : Ω × ℝ → ℝ := fun p => (fun i => b i p.1 p.2) ⬝ᵥ (Gᵀ *ᵥ fun k => Y k p.2 p.1)
    + ∑ j, (fun i => σ i p.2 p.1 j) ⬝ᵥ (Gᵀ *ᵥ fun k => Z k p.2 p.1 j)
    - (fun k => f k p.1 p.2) ⬝ᵥ (G *ᵥ fun i => X i p.2 p.1)
    + ∫ e, (fun i => h i p.2 p.1 e) ⬝ᵥ (Gᵀ *ᵥ fun k => U k p.2 p.1 e) ∂ν with hMf
  set Ff : Ω × ℝ → ℝ := fun p => (fun i => qb i p.1 p.2) ⬝ᵥ (Gᵀ *ᵥ fun k => Y k p.2 p.1)
    + ∑ j, (fun i => qσ i p.2 p.1 j) ⬝ᵥ (Gᵀ *ᵥ fun k => Z k p.2 p.1 j)
    - (fun k => qf k p.1 p.2) ⬝ᵥ (G *ᵥ fun i => X i p.2 p.1)
    + ∫ e, (fun i => qh i p.2 p.1 e) ⬝ᵥ (Gᵀ *ᵥ fun k => U k p.2 p.1 e) ∂ν with hFf
  have hHi : Integrable Hf μ₂ := by
    have hi := integrable_gPairing (ν := ν) G hD.memLp_window_drift hD.memLp_window_diffusion
      hD.memLp_window_driver hD.memLp_markedWindow_jump mX mY mZ mU
    rw [hHf]
    exact hi
  have hMi : Integrable Mf μ₂ := by
    have hi := integrable_gPairing (ν := ν) G (hD.memLp_window_b hl hP)
      (hD.memLp_window_σ hl hP) (hD.memLp_window_f hl hP) mh mX mY mZ mU
    rw [hMf]
    exact hi
  have hFi : Integrable Ff μ₂ := by
    have hi := integrable_gPairing (ν := ν) G (hD.memLp_window_qb hP) (hD.memLp_window_qσ hP)
      (hD.memLp_window_qf hP) mqh mX mY mZ mU
    rw [hFf]
    exact hi
  have hsplit : ∀ᵐ p ∂μ₂, Hf p = lam * Mf p + Ff p := by
    filter_upwards [(integrable_dotProduct_of_memLp mh (memLp_mulVec Gᵀ mU)).prod_right_ae,
      (integrable_dotProduct_of_memLp mqh (memLp_mulVec Gᵀ mU)).prod_right_ae] with p h1 h2
    have h1' : Integrable (fun e => (fun i => h i p.2 p.1 e)
        ⬝ᵥ (Gᵀ *ᵥ fun k => U k p.2 p.1 e)) ν := h1
    have h2' : Integrable (fun e => (fun i => qh i p.2 p.1 e)
        ⬝ᵥ (Gᵀ *ᵥ fun k => U k p.2 p.1 e)) ν := h2
    simp only [hHf, hMf, hFf, dotProduct_mul_add]
    rw [integral_add (h1'.const_mul lam) h2', integral_const_mul]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  -- (4.19) with the integrand split
  have h419 : ∫ ω, (G *ᵥ fun i => X i T ω) ⬝ᵥ (fun k => Y k T ω) ∂P
      = ∫ ω, (G *ᵥ fun i => ξ₀ i ω) ⬝ᵥ (fun k => Y k 0 ω) ∂P
        + (lam * ∫ p, Mf p ∂μ₂ + ∫ p, Ff p ∂μ₂) := by
    rw [← integral_const_mul, ← integral_add (hMi.const_mul lam) hFi,
      ← integral_congr_ae hsplit, integral_prod_symm Hf hHi, hHf]
    exact hD.integral_mulVec_dotProduct_eq 𝒲 hT
  -- the interior monotonicity (2.7), integrated in time
  set BXf : Ω × ℝ → ℝ := fun p => (G *ᵥ fun i => X i p.2 p.1) ⬝ᵥ (G *ᵥ fun i => X i p.2 p.1)
    with hBXf
  set BYf : Ω × ℝ → ℝ := fun p => (Gᵀ *ᵥ fun k => Y k p.2 p.1) ⬝ᵥ (Gᵀ *ᵥ fun k => Y k p.2 p.1)
    + ∑ j, (Gᵀ *ᵥ fun k => Z k p.2 p.1 j) ⬝ᵥ (Gᵀ *ᵥ fun k => Z k p.2 p.1 j)
    + ∫ e, (Gᵀ *ᵥ fun k => U k p.2 p.1 e) ⬝ᵥ (Gᵀ *ᵥ fun k => U k p.2 p.1 e) ∂ν with hBYf
  have hBXi : Integrable BXf μ₂ := by
    have hi := hD.integrable_blockX_window 𝒲 hT
    rw [hBXf]
    exact hi
  have hBYi : Integrable BYf μ₂ := by
    have hi := hD.integrable_blockY_window 𝒲 hT
    rw [hBYf]
    exact hi
  have hmono : ∫ p, Mf p ∂μ₂ ≤ -β₁ * blockY P ν G Y Z U T - β₂ * blockX P G X T := by
    have hm : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∫ ω, Mf (ω, s) ∂P
        ≤ -β₁ * ∫ ω, BYf (ω, s) ∂P - β₂ * ∫ ω, BXf (ω, s) ∂P := by
      rw [hMf, hBYf, hBXf]
      exact hD.mono
    have hle := integral_mono_ae
      (g := fun s => -β₁ * ∫ ω, BYf (ω, s) ∂P - β₂ * ∫ ω, BXf (ω, s) ∂P)
      hMi.integral_prod_right
      ((hBYi.integral_prod_right.const_mul (-β₁)).sub (hBXi.integral_prod_right.const_mul β₂)) hm
    rw [integral_sub (hBYi.integral_prod_right.const_mul (-β₁))
      (hBXi.integral_prod_right.const_mul β₂), integral_const_mul, integral_const_mul] at hle
    rw [integral_prod_symm Mf hMi]
    refine hle.trans_eq ?_
    rw [hBYf, hBXf]
    rfl
  -- the interior forcing
  have hFle : ∫ p, Ff p ∂μ₂
      ≤ η * ((∑ i, Brownian.Ito.energy P T (fun ω s => X i s ω)).toReal
          + (∑ k, Brownian.Ito.energy P T (fun ω s => Y k s ω)
            + ∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z k s ω j)
            + ∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U k s ω e)).toReal)
        + gG ^ 2 / (4 * η) * ((∑ i, Brownian.Ito.energy P T (qb i)).toReal
          + (∑ i, ∑ j, Brownian.Ito.energy P T (fun ω s => qσ i s ω j)).toReal
          + (∑ i, Poisson.Compensated.markedEnergy P ν T (fun ω s e => qh i s ω e)).toReal
          + (∑ k, Brownian.Ito.energy P T (qf k)).toReal) := by
    rw [hFf]
    exact hD.integral_forcing_le 𝒲 hT hP hGn hη
  -- the terminal monotonicity and pairings
  have mXT : ∀ i, MemLp (X i T) 2 P := fun i => (hD.fwd i).memLp_terminal hT.le
  have mqg := hD.memLp_qg hP
  have mg : ∀ k, MemLp (g k) 2 P := fun k =>
    (((hD.bwd k).ξ_sq.sub (mqg k)).const_mul lam⁻¹).ae_eq
      (ae_of_all _ fun _ => (eq_inv_mul_add_sub hl _ _).symm)
  have hgX := integrable_dotProduct_of_memLp mg (memLp_mulVec G mXT)
  have hqgX := integrable_dotProduct_of_memLp mqg (memLp_mulVec G mXT)
  have hTer : ∫ ω, (G *ᵥ fun i => X i T ω) ⬝ᵥ (fun k => Y k T ω) ∂P
      = lam * ∫ ω, (fun k => g k ω) ⬝ᵥ (G *ᵥ fun i => X i T ω) ∂P
        + ∫ ω, (fun k => qg k ω) ⬝ᵥ (G *ᵥ fun i => X i T ω) ∂P := by
    rw [← integral_const_mul, ← integral_add (hgX.const_mul lam) hqgX]
    refine integral_congr_ae ?_
    filter_upwards [ae_all_iff.mpr fun k => (hD.bwd k).ae_eq_terminal hT.le] with ω hω
    have e : (fun k => Y k T ω) = fun k => lam * g k ω + qg k ω := funext hω
    rw [e, dotProduct_comm, dotProduct_mul_add]
  have hTq := hD.neg_terminal_forcing_le hT hP hGn hη
  have hIni := hD.initial_pairing_le hT hGn hη
  -- assembly
  have hmonoT : α * blockXT P G X T
      ≤ ∫ ω, (fun k => g k ω) ⬝ᵥ (G *ᵥ fun i => X i T ω) ∂P := hD.monoT
  have h1 := mul_le_mul_of_nonneg_left hmonoT hlam0
  have h2 := mul_le_mul_of_nonneg_left hmono hlam0
  rw [toReal_dataSize hP]
  linarith

end PairDiff

end MVFBSDEJ.WellPosedness.Stability
