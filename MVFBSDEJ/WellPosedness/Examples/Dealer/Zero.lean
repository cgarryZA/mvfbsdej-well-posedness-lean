/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Examples.Dealer.Inert

/-!
# Example 5.5: the solution at zero interaction in the specialisation

In the specialisation `β₁ = 1`, `β₂ = 1/2`, `σ_c = 1`, `ε = 0` of the exposure-sensitive dealer
system, with `‖h_x‖ = 1` and `⟨h_x, h_c⟩ = 0`, the decoupling residual `Y − X` has rate

`r = 2 (Y − X)² − (Y − X) ⟨h_x, W⟩ + (2 Z − 1)² + ‖W‖² ≥ (Y − X)² + ¾ ‖W‖² + (2 Z − 1)²`,

`W = 2 U − h_c − X h_x`, so every solution has `Y = X`, `Z = 1/2` and `U = (h_c + X h_x) / 2`.

## Main statements

* `integral_sq_sub_smul_eq_norm_sq` — the square distance of a curve to a multiple of a class,
  through representatives.
* `Solves.dealer_zero_residual` — the solution at zero interaction.
-/

open MeasureTheory Filter MVFBSDEJ.Law
open scoped RealInnerProductSpace ENNReal

namespace MVFBSDEJ.WellPosedness.Existence

open MVFBSDEJ.WellPosedness.System MVFBSDEJ.WellPosedness.Stability
  MVFBSDEJ.WellPosedness.BrownianPoisson LevyStochCalc

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}

omit [MeasurableSpace Ω] in
/-- **The square distance of a curve to a multiple of a class, through representatives.** If
`u ∈ L²(ν; ℝ¹)` coordinatewise and `γ` represents `H ∈ L²(ν; ℝ¹)`, then
`∫_E (u − c γ)² dν = ‖uLift u − c H‖²`. -/
theorem integral_sq_sub_smul_eq_norm_sq {u γf : E → Fin 1 → ℝ}
    {H : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν} (c : ℝ) (hu : ∀ k, MemLp (fun e => u e k) 2 ν)
    (hγ : (fun e => (WithLp.toLp 2 (γf e) : EuclideanSpace ℝ (Fin 1))) =ᵐ[ν] H) :
    ∫ e, (u e 0 - c * γf e 0) ^ 2 ∂ν = ‖uLift ν u - c • H‖ ^ 2 := by
  have hm := memLp_toLp_of_forall hu
  rw [← real_inner_self_eq_norm_sq, L2.inner_def, uLift_of_memLp hm]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub (hm.toLp _) (c • H), hm.coeFn_toLp, Lp.coeFn_smul c H, hγ] with
    e h1 h2 h3 h4
  rw [h1, Pi.sub_apply, h2, h3, Pi.smul_apply, ← h4]
  simp only [PiLp.inner_apply, Fin.sum_univ_one, PiLp.sub_apply, PiLp.smul_apply,
    WithLp.ofLp_toLp, RCLike.inner_apply, conj_trivial, smul_eq_mul]
  ring

variable [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {P : Measure Ω}
  [IsProbabilityMeasure P] {T : ℝ} {σc : EuclideanSpace ℝ (Fin 1 × Fin 1)}
  {hc hx : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν}
  {X : Fin 1 → ℝ → Ω → ℝ} {Y : Fin 1 → ℝ → Ω → ℝ} {Z : Fin 1 → ℝ → Ω → Fin 1 → ℝ}
  {U : Fin 1 → ℝ → Ω → E → ℝ} {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P 1 ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin 1, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {ξ₀ : Fin 1 → Ω → ℝ}
  {γ : Fin 1 → ℝ → Ω → E → ℝ}

/-- **The solution at zero interaction in the specialisation.** For a solution of the dealer
system with `β₁ = 1`, `β₂ = 1/2`, `σ_c = 1`, `ε = 0`, `‖h_x‖ = 1` and `⟨h_x, h_c⟩ = 0`, over a
filtration with a cross witness, and `T > 0`: `Y_t = X_t` almost surely at every `t ∈ [0, T]`,
and at almost every `s ∈ [0, T]`, almost surely, `Z_s = 1/2` and
`U_s = (h_c + X_s h_x) / 2`. -/
theorem Solves.dealer_zero_residual
    (h : Solves D ℱ hℱW hℱN T (dealerExpCoeffs 1 (1 / 2) σc hc hx 0) ξ₀ X Y Z U γ)
    (𝒲 : D.CrossWitness ℱ) (hT : 0 < T) (hσ : σc (0, 0) = 1) (hhx : ‖hx‖ = 1)
    (hxc : ⟪hx, hc⟫ = 0) :
    (∀ t ∈ Set.Icc (0 : ℝ) T, Y 0 t =ᵐ[P] X 0 t)
      ∧ (∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P, Z 0 s ω 0 = 1 / 2)
      ∧ ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P,
        uLift ν (fun e k => U k s ω e) = (1 / 2 : ℝ) • (hc + X 0 s ω • hx) := by
  have hUm := SolvesForced.ae_ae_memLp_jump h
  have hγm := ae_ae_memLp_of_markedEnergy_ne_top (System.Solves.linearFSDEJ h 0).γ_meas
    (System.Solves.linearFSDEJ h 0).γ_sq
  -- the rate, through the jump channel `W = 2 U − h_c − X h_x`
  have hW : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P,
      ∫ e, (U 0 s ω e - 1 * γ 0 s ω e) ^ 2 ∂ν
        = ‖(2 : ℝ) • uLift ν (fun e k => U k s ω e) - hc - X 0 s ω • hx‖ ^ 2 := by
    filter_upwards [hUm, h.jump_rep] with s hs1 hs2
    filter_upwards [hs1, hs2] with ω h1 h2
    rw [integral_sq_sub_smul_eq_norm_sq (u := fun e k => U k s ω e) (γf := fun e i => γ i s ω e)
      1 h1 h2, one_smul]
    have hv : uLift ν (fun e k => U k s ω e) - (dealerExpCoeffs 1 (1 / 2) σc hc hx 0).h s
        (tupleAt ν X Y Z U s ω) (lawP2 P (tupleAt ν X Y Z U s))
        = (2 : ℝ) • uLift ν (fun e k => U k s ω e) - hc - X 0 s ω • hx := by
      rw [dealerExpCoeffs_h]
      change uLift ν (fun e k => U k s ω e) - (hc - (1 : ℝ) • uLift ν (fun e k => U k s ω e)
        - (0 : ℝ) • crowdOp _ (uLift ν (fun e k => U k s ω e)) + X 0 s ω • hx) = _
      module
    rw [hv]
  set W : ℝ → Ω → Lp (EuclideanSpace ℝ (Fin 1)) 2 ν := fun s ω =>
    (2 : ℝ) • uLift ν (fun e k => U k s ω e) - hc - X 0 s ω • hx with hWdef
  have hinner : ∀ s ω, ⟪hx, uLift ν (fun e k => U k s ω e)⟫
      = (1 / 2) * ⟪hx, W s ω⟫ + (1 / 2) * X 0 s ω := by
    intro s ω
    have hu : uLift ν (fun e k => U k s ω e) = (1 / 2 : ℝ) • (W s ω + hc + X 0 s ω • hx) := by
      rw [hWdef]
      module
    rw [hu, inner_smul_right, inner_add_right, inner_add_right, hxc, inner_smul_right,
      real_inner_self_eq_norm_sq, hhx]
    ring
  have hbound : ∀ s ω, (Y 0 s ω - X 0 s ω) ^ 2 + 3 / 4 * ‖W s ω‖ ^ 2 + (2 * Z 0 s ω 0 - 1) ^ 2
      ≤ 2 * (Y 0 s ω - 1 * X 0 s ω)
          * (-(1 / 2 * X 0 s ω + ⟪hx, uLift ν (fun e k => U k s ω e)⟫)
            - 0 * X 0 s ω + 1 * (1 * Y 0 s ω))
        + (Z 0 s ω 0 - 1 * (σc (0, 0) - 1 * Z 0 s ω 0)) ^ 2 + ‖W s ω‖ ^ 2 := by
    intro s ω
    rw [hinner, hσ]
    have hcs := abs_real_inner_le_norm hx (W s ω)
    rw [hhx, one_mul] at hcs
    have hD := sq_nonneg (|Y 0 s ω - X 0 s ω| - 1 / 2 * ‖W s ω‖)
    have h1 : (Y 0 s ω - X 0 s ω) * ⟪hx, W s ω⟫ ≤ |Y 0 s ω - X 0 s ω| * ‖W s ω‖ := by
      calc (Y 0 s ω - X 0 s ω) * ⟪hx, W s ω⟫ ≤ |(Y 0 s ω - X 0 s ω) * ⟪hx, W s ω⟫| :=
            le_abs_self _
        _ = |Y 0 s ω - X 0 s ω| * |⟪hx, W s ω⟫| := abs_mul _ _
        _ ≤ |Y 0 s ω - X 0 s ω| * ‖W s ω‖ := mul_le_mul_of_nonneg_left hcs (abs_nonneg _)
    have habs : |Y 0 s ω - X 0 s ω| ^ 2 = (Y 0 s ω - X 0 s ω) ^ 2 := sq_abs _
    nlinarith
  have hr : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P,
      0 ≤ 2 * (Y 0 s ω - 1 * X 0 s ω)
          * (-(1 / 2 * X 0 s ω + ⟪hx, uLift ν (fun e k => U k s ω e)⟫)
            - 0 * X 0 s ω + 1 * (1 * Y 0 s ω))
        + (Z 0 s ω 0 - 1 * (σc (0, 0) - 1 * Z 0 s ω 0)) ^ 2
        + ∫ e, (U 0 s ω e - 1 * γ 0 s ω e) ^ 2 ∂ν := by
    filter_upwards [hW] with s hs
    filter_upwards [hs] with ω hω
    rw [hω]
    exact le_trans (by positivity) (hbound s ω)
  obtain ⟨hF, hR⟩ := Solves.dealer_residual_eq_zero' (p := fun _ => 1) (p' := fun _ => 0) h 𝒲
    hT continuousOn_const (fun x _ => hasDerivAt_const x 1) continuousOn_const rfl hr
  have hzero : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P,
      (Y 0 s ω - X 0 s ω) ^ 2 + 3 / 4 * ‖W s ω‖ ^ 2 + (2 * Z 0 s ω 0 - 1) ^ 2 = 0 := by
    filter_upwards [hR, hW] with s hs1 hs2
    filter_upwards [hs1, hs2] with ω h1 h2
    rw [h2] at h1
    have := hbound s ω
    have h0 : 0 ≤ (Y 0 s ω - X 0 s ω) ^ 2 + 3 / 4 * ‖W s ω‖ ^ 2 + (2 * Z 0 s ω 0 - 1) ^ 2 := by
      positivity
    linarith
  refine ⟨fun t ht => ?_, ?_, ?_⟩
  · have hX := (System.Solves.linearFSDEJ h 0).memLp_apply ht
    have hY := ((System.Solves.linearBSDEJ h 0).linearFSDEJ (ξ₀ := Y 0 0) (ae_eq_refl _)
      hT.le).memLp_apply ht
    have hDt : MemLp (fun ω => Y 0 t ω - 1 * X 0 t ω) 2 P := hY.sub (hX.const_mul _)
    have h0 := (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _)
      (hDt.integrable_sq)).mp (hF t ht)
    filter_upwards [h0] with ω hω
    have : (Y 0 t ω - 1 * X 0 t ω) ^ 2 = 0 := hω
    have : Y 0 t ω - 1 * X 0 t ω = 0 := pow_eq_zero_iff two_ne_zero |>.mp this
    linarith
  · filter_upwards [hzero] with s hs
    filter_upwards [hs] with ω hω
    have : (2 * Z 0 s ω 0 - 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (Y 0 s ω - X 0 s ω), sq_nonneg ‖W s ω‖]
    have := pow_eq_zero_iff two_ne_zero |>.mp this
    linarith
  · filter_upwards [hzero] with s hs
    filter_upwards [hs] with ω hω
    have h2 : ‖W s ω‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg (Y 0 s ω - X 0 s ω), sq_nonneg (2 * Z 0 s ω 0 - 1)]
    have h3 : W s ω = 0 := norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h2)
    have h4 : (2 : ℝ) • uLift ν (fun e k => U k s ω e) = hc + X 0 s ω • hx := by
      have h5 : (2 : ℝ) • uLift ν (fun e k => U k s ω e) - hc - X 0 s ω • hx = 0 := h3
      rw [sub_sub, sub_eq_zero] at h5
      exact h5
    rw [← h4, smul_smul]
    norm_num

end MVFBSDEJ.WellPosedness.Existence
