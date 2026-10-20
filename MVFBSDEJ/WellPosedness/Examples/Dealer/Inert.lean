/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Examples.Dealer.Decoupling
import MVFBSDEJ.WellPosedness.System.JumpLeftEnergy
import MVFBSDEJ.WellPosedness.System.SolvesMemLp

/-!
# Example 5.5: without the exposure term the interaction is inert

Fix `β₁ > 0`, `β₂`, `σ_c ∈ ℝ`, `h_c ∈ L²(ν)`, `ε ≥ 0` and `p` with `p' = β₁ p² − β₂` on
`[0, T]`, `p(T) = 1` and `p > 0` on `[0, T]`. Every solution `(X, Y, Z, U)` of the dealer system
`dealerExpCoeffs β₁ β₂ σ_c h_c 0 ε` (no exposure term) has `Y_t = p(t) X_t` almost surely at
every `t ∈ [0, T]`, `Z = p σ_c / (1 + β₁ p)` and `U = p h_c / (1 + β₁ p)` for `dt ⊗ dP`; so the
law of `U_t` is a Dirac mass, the crowding correction vanishes along the solution, and the same
tuple solves the system at every interaction strength.

The rate of the decoupling residual `Y − p X` is
`2 β₁ p (Y − p X)² + ((1 + β₁ p) Z − p σ_c)² + ∫_E (U − p γ)² dν ≥ 0`, so the residual and the
rate vanish. Along the solution the jump channel then satisfies
`U + (ε p / (1 + β₁ p)) A_{μ^U}(U) = p h_c / (1 + β₁ p)`, and since `u ↦ u + κ A_λ(u)` is
injective for `κ ≥ 0`, `U_t` is almost surely constant.

## Main statements

* `inner_crowdOp_sub_nonneg` — `u ↦ A_λ(u)` is monotone.
* `eq_of_add_smul_crowdOp_eq` — `u ↦ u + κ A_λ(u)` is injective for `κ ≥ 0`.
* `PaperSolution.congr_h` — a solution remains one when the jump coefficient changes only off
  the solution.
* `PaperSolution.dealer_inert` — the inert solution.
-/

open MeasureTheory Filter MVFBSDEJ.Law
open scoped RealInnerProductSpace ENNReal

namespace MVFBSDEJ.WellPosedness.Existence

open MVFBSDEJ.WellPosedness.System MVFBSDEJ.WellPosedness.Stability
  MVFBSDEJ.WellPosedness.BrownianPoisson LevyStochCalc

universe u v w

/-! ### The crowding operator in the valuation curve -/

section Crowd

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]

/-- **The crowding operator is monotone in the valuation curve**: for a finite measure `Λ`,
`⟨A_Λ(u) − A_Λ(u'), u − u'⟩ ≥ 0`. -/
theorem inner_crowdOp_sub_nonneg (Λ : Measure F) [IsFiniteMeasure Λ] (u u' : F) :
    0 ≤ ⟪crowdOp Λ u - crowdOp Λ u', u - u'⟫ := by
  have hi : Integrable (fun v => crowdGrad (u - v) - crowdGrad (u' - v)) Λ :=
    (integrable_crowdGrad_sub Λ u).sub (integrable_crowdGrad_sub Λ u')
  rw [crowdOp, crowdOp, ← integral_sub (integrable_crowdGrad_sub Λ u)
    (integrable_crowdGrad_sub Λ u'), real_inner_comm, ← integral_inner hi]
  refine integral_nonneg fun v => ?_
  have h := inner_crowdGrad_sub_nonneg (u - v) (u' - v)
  rw [show (u - v) - (u' - v) = u - u' by abel] at h
  change (0 : ℝ) ≤ _
  rw [real_inner_comm]
  exact h

/-- **`u ↦ u + κ A_Λ(u)` is injective for `κ ≥ 0`**, for a finite measure `Λ`. -/
theorem eq_of_add_smul_crowdOp_eq (Λ : Measure F) [IsFiniteMeasure Λ] {κ : ℝ} (hκ : 0 ≤ κ)
    {u u' : F} (h : u + κ • crowdOp Λ u = u' + κ • crowdOp Λ u') : u = u' := by
  have h1 := inner_crowdOp_sub_nonneg Λ u u'
  have e : ⟪(u + κ • crowdOp Λ u) - (u' + κ • crowdOp Λ u'), u - u'⟫
      = ‖u - u'‖ ^ 2 + κ * ⟪crowdOp Λ u - crowdOp Λ u', u - u'⟫ := by
    rw [show (u + κ • crowdOp Λ u) - (u' + κ • crowdOp Λ u')
        = (u - u') + κ • (crowdOp Λ u - crowdOp Λ u') by rw [smul_sub]; abel,
      inner_add_left, real_inner_self_eq_norm_sq, real_inner_smul_left]
  rw [h, sub_self, inner_zero_left] at e
  have h2 : ‖u - u'‖ ^ 2 ≤ 0 := by nlinarith [mul_nonneg hκ h1]
  have h3 : ‖u - u'‖ = 0 := by nlinarith [norm_nonneg (u - u')]
  exact sub_eq_zero.mp (norm_eq_zero.mp h3)

/-- **A random curve solving `u + κ A_Λ(u) = c` almost surely is almost surely constant**, for a
finite measure `Λ` and `κ ≥ 0`. -/
theorem exists_ae_eq_const_of_add_smul_crowdOp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [NeZero P] {U : Ω → F} (Λ : Measure F) [IsFiniteMeasure Λ] {κ : ℝ} (hκ : 0 ≤ κ) {c : F}
    (h : ∀ᵐ ω ∂P, U ω + κ • crowdOp Λ (U ω) = c) :
    ∃ u₀ : F, (U =ᵐ[P] fun _ => u₀) ∧ u₀ + κ • crowdOp Λ u₀ = c := by
  obtain ⟨ω₀, hω₀⟩ := h.exists
  exact ⟨U ω₀, h.mono fun ω hω => eq_of_add_smul_crowdOp_eq Λ hκ (hω.trans hω₀.symm), hω₀⟩

end Crowd

/-! ### Swapping the order of an almost-everywhere statement -/

/-- A property holding for `dP ⊗ ds` on `[0, T]` holds at almost every `s ∈ [0, T]`, almost
surely. -/
theorem ae_ae_of_ae_prod_Icc {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [SFinite P]
    {T : ℝ} {p : Ω × ℝ → Prop}
    (h : ∀ᵐ q ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))), p q) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P, p (ω, s) := by
  rw [← Measure.prod_swap] at h
  exact Measure.ae_ae_of_ae_prod
    ((MeasurableEquiv.prodComm (α := ℝ) (β := Ω)).measurableEmbedding.ae_map_iff.mp h)

/-! ### Changing the jump coefficient off the solution -/

section Congr

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {P : Measure Ω}
  [IsProbabilityMeasure P] {n m d : ℕ} {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {T : ℝ} {ξ₀ : Fin n → Ω → ℝ}
  {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ} {Z : Fin m → ℝ → Ω → Fin d → ℝ}
  {U : Fin m → ℝ → Ω → E → ℝ} {γ : Fin n → ℝ → Ω → E → ℝ}

/-- **A solution remains one when the jump coefficient changes only off the solution.** If `C`
and `C'` have the same drift, diffusion, driver and terminal function, and their jump
coefficients agree at the predictable tuple `(Θ⁻_s, μ⁻_s)` at almost every `s ∈ [0, T]`, almost
surely, then a solution of (1.1) with `C` in the sense of the paper is one with `C'`. -/
theorem PaperSolution.congr_h {C C' : Coeffs ν n m d} (hb : C'.b = C.b) (hσ : C'.σ = C.σ)
    (hf : C'.f = C.f) (hg : C'.g = C.g) (h : PaperSolution D ℱ hℱW hℱN T C ξ₀ X Y Z U γ)
    (hh : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P,
      C'.h s (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s ω)
          (lawP2 P (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s))
        = C.h s (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s ω)
          (lawP2 P (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s))) :
    PaperSolution D ℱ hℱW hℱN T C' ξ₀ X Y Z U γ := by
  obtain ⟨b', σ', h', f', g'⟩ := C'
  simp only at hb hσ hf hg hh
  subst hb hσ hf hg
  exact { h with
    jump_rep := by
      filter_upwards [h.jump_rep, hh] with s hs hhs
      filter_upwards [hs, hhs] with ω h1 h2
      rw [h2]
      exact h1 }

end Congr


/-! ### The inert residual -/

section Residual

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {P : Measure Ω}
  [IsProbabilityMeasure P] {T : ℝ} {β₁ β₂ ε : ℝ} {σc : EuclideanSpace ℝ (Fin 1 × Fin 1)}
  {hc : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν}
  {X : Fin 1 → ℝ → Ω → ℝ} {Y : Fin 1 → ℝ → Ω → ℝ} {Z : Fin 1 → ℝ → Ω → Fin 1 → ℝ}
  {U : Fin 1 → ℝ → Ω → E → ℝ} {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P 1 ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin 1, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {ξ₀ : Fin 1 → Ω → ℝ}
  {γ : Fin 1 → ℝ → Ω → E → ℝ}

/-- **The inert residual.** For a solution of the dealer system without exposure term over a
filtration with a cross witness, `T > 0`, `β₁ > 0`, and `p` with `p' = β₁ p² − β₂` on `[0, T]`,
`p(T) = 1` and `p > 0` on `[0, T]`: `Y_t = p(t) X_t` almost surely at every `t ∈ [0, T]`, and for
`dP ⊗ ds` on `[0, T]`, `Z = p σ_c / (1 + β₁ p)` and `∫_E (U − p γ)² dν = 0`. -/
theorem Solves.dealer_inert_residual
    (h : Solves D ℱ hℱW hℱN T (dealerExpCoeffs β₁ β₂ σc hc 0 ε) ξ₀ X Y Z U γ)
    (𝒲 : D.CrossWitness ℱ) (hT : 0 < T) (hβ₁ : 0 < β₁) {p : ℝ → ℝ}
    (hp : ∀ t ∈ Set.Icc (0 : ℝ) T, HasDerivAt p (β₁ * p t ^ 2 - β₂) t) (hpT : p T = 1)
    (hp0 : ∀ t ∈ Set.Icc (0 : ℝ) T, 0 < p t) :
    (∀ t ∈ Set.Icc (0 : ℝ) T, Y 0 t =ᵐ[P] fun ω => p t * X 0 t ω)
      ∧ (∀ᵐ q ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
          Z 0 q.2 q.1 0 = p q.2 * σc (0, 0) / (1 + β₁ * p q.2))
      ∧ ∀ᵐ q ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
          ∫ e, (U 0 q.2 q.1 e - p q.2 * γ 0 q.2 q.1 e) ^ 2 ∂ν = 0 := by
  have hpc : ContinuousOn p (Set.Icc (0 : ℝ) T) := fun t ht =>
    (hp t ht).continuousAt.continuousWithinAt
  have hpI : ∀ x ∈ Set.Ioo (0 : ℝ) T, HasDerivAt p (β₁ * p x ^ 2 - β₂) x := fun x hx =>
    hp x (Set.Ioo_subset_Icc_self hx)
  have hp'c : ContinuousOn (fun t => β₁ * p t ^ 2 - β₂) (Set.Icc (0 : ℝ) T) :=
    (continuousOn_const.mul (hpc.pow 2)).sub continuousOn_const
  have hr : ∀ᵐ q ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
      0 ≤ 2 * (Y 0 q.2 q.1 - p q.2 * X 0 q.2 q.1)
          * (-(β₂ * X 0 q.2 q.1 + ⟪(0 : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν),
              uLift ν (fun e k => U k q.2 q.1 e)⟫)
            - (β₁ * p q.2 ^ 2 - β₂) * X 0 q.2 q.1 + p q.2 * (β₁ * Y 0 q.2 q.1))
        + (Z 0 q.2 q.1 0 - p q.2 * (σc (0, 0) - β₁ * Z 0 q.2 q.1 0)) ^ 2
        + ∫ e, (U 0 q.2 q.1 e - p q.2 * γ 0 q.2 q.1 e) ^ 2 ∂ν := by
    filter_upwards [LinearFSDEJ.ae_snd_mem_Icc (P := P) T] with q hq
    have hp0' := (hp0 q.2 hq).le
    have key : 2 * (Y 0 q.2 q.1 - p q.2 * X 0 q.2 q.1)
          * (-(β₂ * X 0 q.2 q.1 + ⟪(0 : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν),
              uLift ν (fun e k => U k q.2 q.1 e)⟫)
            - (β₁ * p q.2 ^ 2 - β₂) * X 0 q.2 q.1 + p q.2 * (β₁ * Y 0 q.2 q.1))
        = 2 * β₁ * p q.2 * (Y 0 q.2 q.1 - p q.2 * X 0 q.2 q.1) ^ 2 := by
      rw [inner_zero_left]
      ring
    rw [key]
    have h3 : 0 ≤ ∫ e, (U 0 q.2 q.1 e - p q.2 * γ 0 q.2 q.1 e) ^ 2 ∂ν :=
      integral_nonneg fun _ => sq_nonneg _
    positivity
  obtain ⟨hF, -, hR0⟩ := Solves.dealer_residual_eq_zero h 𝒲 hT hpc hpI hp'c hpT hr
  refine ⟨fun t ht => ?_, ?_, ?_⟩
  · have hX := (System.Solves.linearFSDEJ h 0).memLp_apply ht
    have hY := ((System.Solves.linearBSDEJ h 0).linearFSDEJ (ξ₀ := Y 0 0) (ae_eq_refl _)
      hT.le).memLp_apply ht
    have hD : MemLp (fun ω => Y 0 t ω - p t * X 0 t ω) 2 P := hY.sub (hX.const_mul _)
    have h0 := (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _)
      (hD.integrable_sq)).mp (hF t ht)
    filter_upwards [h0] with ω hω
    have : (Y 0 t ω - p t * X 0 t ω) ^ 2 = 0 := hω
    have : Y 0 t ω - p t * X 0 t ω = 0 := pow_eq_zero_iff two_ne_zero |>.mp this
    linarith
  · filter_upwards [hR0, hr, LinearFSDEJ.ae_snd_mem_Icc (P := P) T] with q h0 h1 hq
    have hp0' := hp0 q.2 hq
    have hA : 0 ≤ 2 * (Y 0 q.2 q.1 - p q.2 * X 0 q.2 q.1)
          * (-(β₂ * X 0 q.2 q.1 + ⟪(0 : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν),
              uLift ν (fun e k => U k q.2 q.1 e)⟫)
            - (β₁ * p q.2 ^ 2 - β₂) * X 0 q.2 q.1 + p q.2 * (β₁ * Y 0 q.2 q.1)) := by
      rw [inner_zero_left]
      nlinarith [sq_nonneg (Y 0 q.2 q.1 - p q.2 * X 0 q.2 q.1), mul_pos hβ₁ hp0']
    have hC : 0 ≤ ∫ e, (U 0 q.2 q.1 e - p q.2 * γ 0 q.2 q.1 e) ^ 2 ∂ν :=
      integral_nonneg fun _ => sq_nonneg _
    have hB : (Z 0 q.2 q.1 0 - p q.2 * (σc (0, 0) - β₁ * Z 0 q.2 q.1 0)) ^ 2 = 0 := by
      nlinarith [sq_nonneg (Z 0 q.2 q.1 0 - p q.2 * (σc (0, 0) - β₁ * Z 0 q.2 q.1 0))]
    have hB' := pow_eq_zero_iff two_ne_zero |>.mp hB
    have hne : 1 + β₁ * p q.2 ≠ 0 := by positivity
    field_simp
    linarith
  · filter_upwards [hR0, hr, LinearFSDEJ.ae_snd_mem_Icc (P := P) T] with q h0 h1 hq
    have hp0' := hp0 q.2 hq
    have hA : 0 ≤ 2 * (Y 0 q.2 q.1 - p q.2 * X 0 q.2 q.1)
          * (-(β₂ * X 0 q.2 q.1 + ⟪(0 : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν),
              uLift ν (fun e k => U k q.2 q.1 e)⟫)
            - (β₁ * p q.2 ^ 2 - β₂) * X 0 q.2 q.1 + p q.2 * (β₁ * Y 0 q.2 q.1)) := by
      rw [inner_zero_left]
      nlinarith [sq_nonneg (Y 0 q.2 q.1 - p q.2 * X 0 q.2 q.1), mul_pos hβ₁ hp0']
    have hC : 0 ≤ ∫ e, (U 0 q.2 q.1 e - p q.2 * γ 0 q.2 q.1 e) ^ 2 ∂ν :=
      integral_nonneg fun _ => sq_nonneg _
    nlinarith [sq_nonneg (Z 0 q.2 q.1 0 - p q.2 * (σc (0, 0) - β₁ * Z 0 q.2 q.1 0))]

end Residual


/-! ### The inert solution -/

section Inert

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {P : Measure Ω}
  [IsProbabilityMeasure P] {T : ℝ} {β₁ β₂ ε : ℝ} {σc : EuclideanSpace ℝ (Fin 1 × Fin 1)}
  {hc : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν}
  {X : Fin 1 → ℝ → Ω → ℝ} {Y : Fin 1 → ℝ → Ω → ℝ} {Z : Fin 1 → ℝ → Ω → Fin 1 → ℝ}
  {U : Fin 1 → ℝ → Ω → E → ℝ} {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P 1 ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin 1, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {ξ₀ : Fin 1 → Ω → ℝ}
  {γ : Fin 1 → ℝ → Ω → E → ℝ}

omit [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
/-- **The class of a curve proportional to a representative.** If `u ∈ L²(ν; ℝ¹)` coordinatewise,
`γ` represents `H ∈ L²(ν; ℝ¹)` and `u = c γ` for `ν`-almost every mark, then
`uLift u = c • H`. -/
theorem uLift_eq_smul_of_ae {u γf : E → Fin 1 → ℝ} {H : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν}
    {c : ℝ} (hu : ∀ k, MemLp (fun e => u e k) 2 ν)
    (hγ : (fun e => (WithLp.toLp 2 (γf e) : EuclideanSpace ℝ (Fin 1))) =ᵐ[ν] H)
    (huγ : ∀ᵐ e ∂ν, u e 0 = c * γf e 0) : uLift ν u = c • H := by
  have hm := memLp_toLp_of_forall hu
  refine Lp.ext ?_
  rw [uLift_of_memLp hm]
  filter_upwards [hm.coeFn_toLp, Lp.coeFn_smul c H, hγ, huγ] with e h1 h2 h3 h4
  rw [h1, h2, Pi.smul_apply, ← h3]
  refine PiLp.ext fun k => ?_
  obtain rfl : k = 0 := Subsingleton.elim _ _
  simp [h4]

/-- **The inert jump channel.** For a solution of the dealer system without exposure term over a
filtration whose null sets lie in its time-`0` field, whose right-continuation is constant before
`0` and which admits a cross witness, `T > 0`, `β₁ > 0`, `ε ≥ 0` and `p` as in
`Solves.dealer_inert_residual`: at almost every `s ∈ [0, T]`,
`U_s = p(s) h_c / (1 + β₁ p(s))` almost surely, and the `U`-marginal of the law of the tuple is the
Dirac mass there. -/
theorem Solves.dealer_inert_curve
    (h : Solves D ℱ hℱW hℱN T (dealerExpCoeffs β₁ β₂ σc hc 0 ε) ξ₀ X Y Z U γ)
    (𝒲 : D.CrossWitness ℱ) (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T)
    (hβ₁ : 0 < β₁) (hε : 0 ≤ ε) {p : ℝ → ℝ}
    (hp : ∀ t ∈ Set.Icc (0 : ℝ) T, HasDerivAt p (β₁ * p t ^ 2 - β₂) t) (hpT : p T = 1)
    (hp0 : ∀ t ∈ Set.Icc (0 : ℝ) T, 0 < p t) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      (∀ᵐ ω ∂P, uLift ν (fun e k => U k s ω e) = (p s / (1 + β₁ * p s)) • hc)
      ∧ (lawP2 P (tupleAt ν X Y Z U s)).margU.law
        = Measure.dirac ((p s / (1 + β₁ * p s)) • hc) := by
  obtain ⟨-, -, hUq⟩ := Solves.dealer_inert_residual h 𝒲 hT hβ₁ hp hpT hp0
  have hU' := ae_ae_of_ae_prod_Icc hUq
  have hUm := SolvesForced.ae_ae_memLp_jump h
  have hγm := ae_ae_memLp_of_markedEnergy_ne_top (System.Solves.linearFSDEJ h 0).γ_meas
    (System.Solves.linearFSDEJ h 0).γ_sq
  have hmT := SolvesForced.ae_memLp_tupleAt h 𝒲 hℱ0 hnull hT
  filter_upwards [hU', hUm, hγm, h.jump_rep, hmT, ae_restrict_mem measurableSet_Icc] with
    s hs1 hs2 hs3 hs4 hs5 hsI
  have hps := hp0 s hsI
  have hne : (1 + β₁ * p s) ≠ 0 := by positivity
  set μ := lawP2 P (tupleAt ν X Y Z U s) with hμ
  have hκ : 0 ≤ ε * p s / (1 + β₁ * p s) := by positivity
  have heq : ∀ᵐ ω ∂P, uLift ν (fun e k => U k s ω e)
      + (ε * p s / (1 + β₁ * p s)) • crowdOp μ.margU.law (uLift ν (fun e k => U k s ω e))
      = (p s / (1 + β₁ * p s)) • hc := by
    filter_upwards [hs1, hs2, hs3, hs4] with ω h1 h2 h3 h4
    have h3' : MemLp (fun e => γ 0 s ω e) 2 ν := by
      simpa only [jumpProc, Set.indicator_of_mem hsI] using h3
    have hint : Integrable (fun e => (U 0 s ω e - p s * γ 0 s ω e) ^ 2) ν :=
      ((h2 0).sub (h3'.const_mul (p s))).integrable_sq
    have hae := (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hint).mp h1
    have hae' : ∀ᵐ e ∂ν, U 0 s ω e = p s * γ 0 s ω e := by
      filter_upwards [hae] with e he
      have : (U 0 s ω e - p s * γ 0 s ω e) ^ 2 = 0 := he
      linarith [pow_eq_zero_iff two_ne_zero |>.mp this]
    have hu := uLift_eq_smul_of_ae (u := fun e k => U k s ω e) (γf := fun e i => γ i s ω e)
      h2 h4 hae'
    rw [dealerExpCoeffs_h] at hu
    change uLift ν (fun e k => U k s ω e) = p s • (hc - β₁ • uLift ν (fun e k => U k s ω e)
      - ε • crowdOp μ.margU.law (uLift ν (fun e k => U k s ω e))
      + (tupleAt ν X Y Z U s ω).1 0 • (0 : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν)) at hu
    rw [smul_zero, add_zero] at hu
    have key : (1 + β₁ * p s) • (uLift ν (fun e k => U k s ω e)
        + (ε * p s / (1 + β₁ * p s)) • crowdOp μ.margU.law (uLift ν (fun e k => U k s ω e))
        - (p s / (1 + β₁ * p s)) • hc) = 0 := by
      rw [smul_sub, smul_add, smul_smul, smul_smul, mul_div_cancel₀ _ hne,
        mul_div_cancel₀ _ hne]
      linear_combination (norm := module) hu
    exact sub_eq_zero.mp ((smul_eq_zero.mp key).resolve_left hne)
  obtain ⟨u₀, hu₀, hu₀eq⟩ := exists_ae_eq_const_of_add_smul_crowdOp μ.margU.law hκ heq
  have hlaw : μ.margU.law = Measure.dirac u₀ := by
    rw [hμ, margU_lawP2 hs5]
    change (lawP2 P fun ω => uLift ν (fun e k => U k s ω e)).law = _
    rw [lawP2_congr hu₀, lawP2_law (memLp_const u₀), Measure.map_const, measure_univ, one_smul]
  rw [hlaw, crowdOp_dirac, sub_self, crowdGrad_zero, smul_zero, add_zero] at hu₀eq
  exact ⟨hu₀.mono fun ω hω => hω.trans hu₀eq, hlaw.trans (by rw [hu₀eq])⟩


/-- **Example 5.5: without the exposure term the interaction is inert.** For a solution
`(X, Y, Z, U)` of the dealer system without exposure term in the sense of the paper, over a
filtration whose null sets lie in its time-`0` field, whose right-continuation is constant before
`0` and which admits a cross witness, with left limits on `(0, T]` along every path, `T > 0`,
`β₁ > 0`, `ε ≥ 0` and `p` with `p' = β₁ p² − β₂` on `[0, T]`, `p(T) = 1`, `p > 0` on `[0, T]`:
`Y_t = p(t) X_t` almost surely at each `t ∈ [0, T]`; `Z − p σ_c / (1 + β₁ p)` has zero energy;
at almost every `s`, `U_s = p(s) h_c / (1 + β₁ p(s))` almost surely, the law of the predictable
tuple has this Dirac mass as `U`-marginal and the crowding correction vanishes almost surely;
and the tuple solves the dealer system at every interaction strength. -/
theorem PaperSolution.dealer_inert
    (hPS : PaperSolution D ℱ hℱW hℱN T (dealerExpCoeffs β₁ β₂ σc hc 0 ε) ξ₀ X Y Z U γ)
    (𝒲 : D.CrossWitness ℱ) (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T)
    (hβ₁ : 0 < β₁) (hε : 0 ≤ ε) {p : ℝ → ℝ}
    (hp : ∀ t ∈ Set.Icc (0 : ℝ) T, HasDerivAt p (β₁ * p t ^ 2 - β₂) t) (hpT : p T = 1)
    (hp0 : ∀ t ∈ Set.Icc (0 : ℝ) T, 0 < p t)
    (hXl : ∀ ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ,
      Tendsto (fun s => X 0 s ω) (nhdsWithin t (Set.Iio t)) (nhds l))
    (hYl : ∀ ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ,
      Tendsto (fun s => Y 0 s ω) (nhdsWithin t (Set.Iio t)) (nhds l)) :
    (∀ t ∈ Set.Icc (0 : ℝ) T, Y 0 t =ᵐ[P] fun ω => p t * X 0 t ω)
      ∧ Brownian.Ito.energy P T
          (fun ω s => Z 0 s ω 0 - p s * σc (0, 0) / (1 + β₁ * p s)) = 0
      ∧ (∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P,
          uLift ν (fun e k => U k s ω e) = (p s / (1 + β₁ * p s)) • hc)
      ∧ (∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
          (lawP2 P (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s)).margU.law
            = Measure.dirac ((p s / (1 + β₁ * p s)) • hc)
          ∧ ∀ᵐ ω ∂P, crowdOp (lawP2 P (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s)).margU.law
              (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s ω).2.2.2 = 0)
      ∧ ∀ ε' : ℝ, PaperSolution D ℱ hℱW hℱN T (dealerExpCoeffs β₁ β₂ σc hc 0 ε') ξ₀ X Y Z U γ := by
  obtain ⟨X', Y', hXX, hYY, hS⟩ := hPS.exists_solves hT.le
  obtain ⟨hF, hZ, -⟩ := Solves.dealer_inert_residual hS 𝒲 hT hβ₁ hp hpT hp0
  have hC := Solves.dealer_inert_curve hS 𝒲 hℱ0 hnull hT hβ₁ hε hp hpT hp0
  -- the predictable tuple of `(X, Y)` is that of `(X', Y')` on `(0, T]`
  have hpred : ∀ s ∈ Set.Ioc (0 : ℝ) T, ∀ ω,
      tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s ω
        = tupleAt ν (leftLimProc X') (leftLimProc Y') Z U s ω := by
    intro s hs ω
    have hx : leftLimProc X 0 s ω = leftLimProc X' 0 s ω :=
      (leftLim_eq_of_eqOn (fun t ht => congrFun (hXX 0 t ht) ω) (hXl ω) hs).symm
    have hy : leftLimProc Y 0 s ω = leftLimProc Y' 0 s ω :=
      (leftLim_eq_of_eqOn (fun t ht => congrFun (hYY 0 t ht) ω) (hYl ω) hs).symm
    have hx' : (fun i => leftLimProc X i s ω) = fun i => leftLimProc X' i s ω := by
      funext i
      obtain rfl : i = 0 := Subsingleton.elim _ _
      exact hx
    have hy' : (fun k => leftLimProc Y k s ω) = fun k => leftLimProc Y' k s ω := by
      funext k
      obtain rfl : k = 0 := Subsingleton.elim _ _
      exact hy
    simp only [tupleAt, hx', hy']
  have hlaw : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      lawP2 P (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s)
        = lawP2 P (tupleAt ν X' Y' Z U s) := by
    filter_upwards [SolvesForced.ae_ae_tupleAt_leftLimProc_eq hS hT.le,
      ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae (Measure.ae_ne volume (0 : ℝ))] with s hs hsI hs0
    have hsI' : s ∈ Set.Ioc (0 : ℝ) T := ⟨lt_of_le_of_ne hsI.1 (Ne.symm hs0), hsI.2⟩
    rw [show tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s
      = tupleAt ν (leftLimProc X') (leftLimProc Y') Z U s from funext (hpred s hsI'),
      lawP2_congr hs]
  have hD : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      (lawP2 P (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s)).margU.law
          = Measure.dirac ((p s / (1 + β₁ * p s)) • hc)
        ∧ ∀ᵐ ω ∂P, crowdOp (lawP2 P (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s)).margU.law
            (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s ω).2.2.2 = 0 := by
    filter_upwards [hC, hlaw] with s ⟨hu, hl⟩ hls
    rw [hls]
    refine ⟨hl, ?_⟩
    filter_upwards [hu] with ω hω
    change crowdOp _ (uLift ν (fun e k => U k s ω e)) = 0
    rw [hl, hω, crowdOp_dirac, sub_self, crowdGrad_zero]
  refine ⟨fun t ht => ?_, ?_, ?_, hD, fun ε' => ?_⟩
  · rw [← hXX 0 t ht, ← hYY 0 t ht]
    exact hF t ht
  · have hZ' := Measure.ae_ae_of_ae_prod hZ
    unfold Brownian.Ito.energy
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hZ'] with ω hω
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hω] with s hs
    simp [hs]
  · filter_upwards [hC] with s hs
    exact hs.1
  · refine PaperSolution.congr_h (C := dealerExpCoeffs β₁ β₂ σc hc 0 ε) rfl rfl rfl rfl hPS ?_
    filter_upwards [hD] with s hs
    filter_upwards [hs.2] with ω hω
    rw [dealerExpCoeffs_h, dealerExpCoeffs_h, hω, smul_zero, smul_zero]
    simp


end Inert


end MVFBSDEJ.WellPosedness.Existence
