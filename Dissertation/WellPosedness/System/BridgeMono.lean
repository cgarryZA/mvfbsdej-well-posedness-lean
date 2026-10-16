/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Dissertation.WellPosedness.System.ChannelCoords
import Dissertation.WellPosedness.System.SolvesMemLp

/-!
# Assumption 2.5 along two solutions

Let `Θ¹, Θ²` solve the `λ`-forced system (4.1) with the same coefficients `(b, σ, h, f, g)`,
satisfying Assumption 2.5 along the diagonal with coupling matrix `G` and constants
`α, β₁, β₂`. At almost every time `s ∈ [0, T]` the tuples `Θ¹_s, Θ²_s` are square integrable and
strongly `ℱ_s`-measurable, so `(Θ¹_s, μ¹_s)` and `(Θ²_s, μ²_s)` are diagonal inputs, and (2.7)
holds at the pair:

`𝔼[⟨δb, Gᵀ δY⟩ + ⟨δσ, Gᵀ δZ⟩_F − ⟨δf, G δX⟩ + ∫_E ⟨δh(e), Gᵀ δU(e)⟩ ν(de)]
  ≤ −β₁ 𝔼[|Gᵀ δY|² + |Gᵀ δZ|²_F + ‖Gᵀ δU‖²_{L²(ν)}] − β₂ 𝔼|G δX|²`.

Assumption 2.5 pairs the channels of `H` through the operators `GX`, `GZ`, `GU` and their
adjoints. Almost surely both jump channels are square integrable and the jump coefficients are
represented by `γ¹, γ²`; there the pairings are, in coordinates:

* on `ℝⁿ` and `ℝᵐ`, `⟨x, Gᵀ y⟩ = x ⬝ᵥ Gᵀ y` and `|G x|² = G x ⬝ᵥ G x`;
* on `ℝ^{n×d}`, `⟨σ, Gᵀ z⟩_F = ∑_j σ_{· j} ⬝ᵥ Gᵀ z_{· j}`, column by column;
* on `L²(ν)`, `⟨δh, Gᵀ δU⟩ = ∫_E δγ(e) ⬝ᵥ Gᵀ δU(e) ν(de)` and
  `‖Gᵀ δU‖² = ∫_E Gᵀ δU(e) ⬝ᵥ Gᵀ δU(e) ν(de)`, with `δγ = γ¹ − γ²`.

Each side of (2.7) is then the expectation of the coordinate expression of `PairMonotone`. On the
right the expectation splits into its backward and forward parts, the squared channels of a
square-integrable tuple being integrable. The terminal inequality
`α 𝔼|G δX_T|² ≤ 𝔼⟨δg_T, G δX_T⟩` is read off in the same way at `X¹_T, X²_T ∈ L²(Ω, ℱ_T; ℝⁿ)`.

The two inequalities hold along any two tuples of coordinate processes that are square integrable
at almost every time, with square-integrable values at the horizon. For two solutions of
`SolvesForced` the filtration is one on which Lemma 4.1 applies, as for the Lipschitz bounds at
the pair.

## Main statements

* `interiorPairing_tupleAt` — the interior pairing of two tuples in coordinates.
* `norm_sq_adjoint_tupleAt`, `norm_sq_GX_tupleAt` — the dissipation of two tuples in
  coordinates.
* `DiagonalMonotone.mono_pair`, `TerminalMonotone.monoT_pair` — (2.7) and the terminal
  inequality along two tuples.
* `SolvesForced.mono_pair` — (2.7) along two solutions.
* `SolvesForced.monoT_pair` — the terminal inequality along two solutions.
* `SolvesForced.pairMonotone` — Assumption 2.5 at the pair.
-/

open MeasureTheory Filter Matrix WithLp Dissertation.Law
open scoped NNReal ENNReal

namespace Dissertation.WellPosedness.System

open Dissertation.WellPosedness.BrownianPoisson Dissertation.WellPosedness.Stability

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}
  {P : Measure Ω} [IsProbabilityMeasure P] {T : ℝ} {C : Coeffs ν n m d}
  {G : Matrix (Fin m) (Fin n) ℝ}
  {X₁ X₂ : Fin n → ℝ → Ω → ℝ} {Y₁ Y₂ : Fin m → ℝ → Ω → ℝ}
  {Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ} {U₁ U₂ : Fin m → ℝ → Ω → E → ℝ}
  {γ₁ γ₂ : Fin n → ℝ → Ω → E → ℝ} {s : ℝ} {ω : Ω}

/-! ### The two sides of (2.7) in coordinates -/

/-- **The interior pairing of two tuples in coordinates**, at a time of the horizon at which the
jump channels are square integrable and `γ¹, γ²` represent the jump coefficients. -/
theorem interiorPairing_tupleAt (hs : s ∈ Set.Icc (0 : ℝ) T)
    (hγ₁ : (fun e => (toLp 2 fun i => γ₁ i s ω e : EuclideanSpace ℝ (Fin n)))
      =ᵐ[ν] C.h s (tupleAt ν X₁ Y₁ Z₁ U₁ s ω) (lawP2 P (tupleAt ν X₁ Y₁ Z₁ U₁ s)))
    (hγ₂ : (fun e => (toLp 2 fun i => γ₂ i s ω e : EuclideanSpace ℝ (Fin n)))
      =ᵐ[ν] C.h s (tupleAt ν X₂ Y₂ Z₂ U₂ s ω) (lawP2 P (tupleAt ν X₂ Y₂ Z₂ U₂ s)))
    (hU₁ : ∀ k, MemLp (fun e => U₁ k s ω e) 2 ν) (hU₂ : ∀ k, MemLp (fun e => U₂ k s ω e) 2 ν) :
    interiorPairing (GX G) (GZ G) (GU G ν)
        (diagDiff C s (tupleAt ν X₁ Y₁ Z₁ U₁ s ω) (tupleAt ν X₂ Y₂ Z₂ U₂ s ω)
          (lawP2 P (tupleAt ν X₁ Y₁ Z₁ U₁ s)) (lawP2 P (tupleAt ν X₂ Y₂ Z₂ U₂ s)))
      = (fun i => driftProc P T C X₁ Y₁ Z₁ U₁ i ω s - driftProc P T C X₂ Y₂ Z₂ U₂ i ω s)
            ⬝ᵥ (Gᵀ *ᵥ fun k => Y₁ k s ω - Y₂ k s ω)
        + ∑ j, (fun i => diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j
            - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j) ⬝ᵥ (Gᵀ *ᵥ fun k => Z₁ k s ω j - Z₂ k s ω j)
        - (fun k => driverProc P T C X₁ Y₁ Z₁ U₁ k ω s - driverProc P T C X₂ Y₂ Z₂ U₂ k ω s)
            ⬝ᵥ (G *ᵥ fun i => X₁ i s ω - X₂ i s ω)
        + ∫ e, (fun i => jumpProc T γ₁ i s ω e - jumpProc T γ₂ i s ω e)
            ⬝ᵥ (Gᵀ *ᵥ fun k => U₁ k s ω e - U₂ k s ω e) ∂ν := by
  have hU : ∀ k, MemLp (fun e => U₁ k s ω e - U₂ k s ω e) 2 ν := fun k => (hU₁ k).sub (hU₂ k)
  simp only [interiorPairing, diagDiff]
  rw [b_sub_eq_toLp hs, σ_sub_eq_toLp hs, f_sub_eq_toLp hs, tupleAt_fst_sub, tupleAt_Y_sub,
    tupleAt_Z_sub, tupleAt_U_sub hU₁ hU₂, adjoint_GX_toLp, adjoint_GZ_toLp, GX_toLp,
    inner_toLp_eq_dotProduct, inner_toLp_eq_dotProduct, inner_neg_left, inner_toLp_eq_dotProduct,
    inner_eq_integral_dotProduct (coeFn_h_sub hs hγ₁ hγ₂)
      (coeFn_adjoint_GU_uLift G (u := fun e k => U₁ k s ω e - U₂ k s ω e) hU),
    dotProduct_prod]
  ring

omit [MeasurableSpace Ω] [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
/-- **The backward half of the dissipation of two tuples in coordinates**, at a time at which the
jump channels are square integrable. -/
theorem norm_sq_adjoint_tupleAt (hU₁ : ∀ k, MemLp (fun e => U₁ k s ω e) 2 ν)
    (hU₂ : ∀ k, MemLp (fun e => U₂ k s ω e) 2 ν) :
    ‖ContinuousLinearMap.adjoint (GX G)
          ((tupleAt ν X₁ Y₁ Z₁ U₁ s ω).2.1 - (tupleAt ν X₂ Y₂ Z₂ U₂ s ω).2.1)‖ ^ 2
        + ‖ContinuousLinearMap.adjoint (GZ G)
          ((tupleAt ν X₁ Y₁ Z₁ U₁ s ω).2.2.1 - (tupleAt ν X₂ Y₂ Z₂ U₂ s ω).2.2.1)‖ ^ 2
        + ‖ContinuousLinearMap.adjoint (GU G ν)
          ((tupleAt ν X₁ Y₁ Z₁ U₁ s ω).2.2.2 - (tupleAt ν X₂ Y₂ Z₂ U₂ s ω).2.2.2)‖ ^ 2
      = (Gᵀ *ᵥ fun k => Y₁ k s ω - Y₂ k s ω) ⬝ᵥ (Gᵀ *ᵥ fun k => Y₁ k s ω - Y₂ k s ω)
        + ∑ j, (Gᵀ *ᵥ fun k => Z₁ k s ω j - Z₂ k s ω j) ⬝ᵥ (Gᵀ *ᵥ fun k => Z₁ k s ω j - Z₂ k s ω j)
        + ∫ e, (Gᵀ *ᵥ fun k => U₁ k s ω e - U₂ k s ω e)
            ⬝ᵥ (Gᵀ *ᵥ fun k => U₁ k s ω e - U₂ k s ω e) ∂ν := by
  have hU : ∀ k, MemLp (fun e => U₁ k s ω e - U₂ k s ω e) 2 ν := fun k => (hU₁ k).sub (hU₂ k)
  rw [tupleAt_Y_sub, tupleAt_Z_sub, tupleAt_U_sub hU₁ hU₂, adjoint_GX_toLp, adjoint_GZ_toLp,
    norm_toLp_sq_eq_dotProduct, norm_toLp_sq_eq_dotProduct, dotProduct_prod,
    norm_sq_eq_integral_dotProduct
      (coeFn_adjoint_GU_uLift G (u := fun e k => U₁ k s ω e - U₂ k s ω e) hU)]

omit [MeasurableSpace Ω] [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
/-- **The forward half of the dissipation of two tuples in coordinates.** -/
theorem norm_sq_GX_tupleAt :
    ‖GX G ((tupleAt ν X₁ Y₁ Z₁ U₁ s ω).1 - (tupleAt ν X₂ Y₂ Z₂ U₂ s ω).1)‖ ^ 2
      = (G *ᵥ fun i => X₁ i s ω - X₂ i s ω) ⬝ᵥ (G *ᵥ fun i => X₁ i s ω - X₂ i s ω) := by
  rw [tupleAt_fst_sub, GX_toLp, norm_toLp_sq_eq_dotProduct]

/-! ### Assumption 2.5 along two solutions -/

variable {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {lam : ℝ}
  {ξ₁ ξ₂ : Fin n → Ω → ℝ}
  {qb₁ qb₂ : Fin n → Ω → ℝ → ℝ} {qσ₁ qσ₂ : Fin n → ℝ → Ω → Fin d → ℝ}
  {qh₁ qh₂ : Fin n → ℝ → Ω → E → ℝ} {qf₁ qf₂ : Fin m → Ω → ℝ → ℝ} {qg₁ qg₂ : Fin m → Ω → ℝ}
  {α β₁ β₂ : ℝ}

/-- **(2.7) along two tuples.** For coefficients satisfying Assumption 2.5 along the diagonal,
and two tuples of coordinate processes that are strongly `ℱ_s`-measurable at every time, square
integrable at almost every time of `[0, T]`, whose jump channels are almost surely square
integrable at almost every time and along which `γ¹, γ²` represent the jump coefficient, at almost
every time `s ∈ [0, T]`,
`𝔼[⟨δb, Gᵀ δY⟩ + ⟨δσ, Gᵀ δZ⟩_F − ⟨δf, G δX⟩ + ∫_E ⟨δh(e), Gᵀ δU(e)⟩ ν(de)]
  ≤ −β₁ 𝔼[|Gᵀ δY|² + |Gᵀ δZ|²_F + ‖Gᵀ δU‖²] − β₂ 𝔼|G δX|²`, in coordinates. -/
theorem DiagonalMonotone.mono_pair (hM : DiagonalMonotone ℱ P T G β₁ β₂ C)
    (hsm₁ : ∀ s, StronglyMeasurable[ℱ s] (tupleAt ν X₁ Y₁ Z₁ U₁ s))
    (hsm₂ : ∀ s, StronglyMeasurable[ℱ s] (tupleAt ν X₂ Y₂ Z₂ U₂ s))
    (hm₁ : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), MemLp (tupleAt ν X₁ Y₁ Z₁ U₁ s) 2 P)
    (hm₂ : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), MemLp (tupleAt ν X₂ Y₂ Z₂ U₂ s) 2 P)
    (hU₁ : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P, ∀ k,
      MemLp (fun e => U₁ k s ω e) 2 ν)
    (hU₂ : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P, ∀ k,
      MemLp (fun e => U₂ k s ω e) 2 ν)
    (hr₁ : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P,
      (fun e => (toLp 2 fun i => γ₁ i s ω e : EuclideanSpace ℝ (Fin n)))
        =ᵐ[ν] C.h s (tupleAt ν X₁ Y₁ Z₁ U₁ s ω) (lawP2 P (tupleAt ν X₁ Y₁ Z₁ U₁ s)))
    (hr₂ : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P,
      (fun e => (toLp 2 fun i => γ₂ i s ω e : EuclideanSpace ℝ (Fin n)))
        =ᵐ[ν] C.h s (tupleAt ν X₂ Y₂ Z₂ U₂ s ω) (lawP2 P (tupleAt ν X₂ Y₂ Z₂ U₂ s))) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      ∫ ω, ((fun i => driftProc P T C X₁ Y₁ Z₁ U₁ i ω s - driftProc P T C X₂ Y₂ Z₂ U₂ i ω s)
            ⬝ᵥ (Gᵀ *ᵥ fun k => Y₁ k s ω - Y₂ k s ω)
          + ∑ j, (fun i => diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j
            - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j) ⬝ᵥ (Gᵀ *ᵥ fun k => Z₁ k s ω j - Z₂ k s ω j)
          - (fun k => driverProc P T C X₁ Y₁ Z₁ U₁ k ω s - driverProc P T C X₂ Y₂ Z₂ U₂ k ω s)
            ⬝ᵥ (G *ᵥ fun i => X₁ i s ω - X₂ i s ω)
          + ∫ e, (fun i => jumpProc T γ₁ i s ω e - jumpProc T γ₂ i s ω e)
            ⬝ᵥ (Gᵀ *ᵥ fun k => U₁ k s ω e - U₂ k s ω e) ∂ν) ∂P
        ≤ -β₁ * ∫ ω, ((Gᵀ *ᵥ fun k => Y₁ k s ω - Y₂ k s ω)
              ⬝ᵥ (Gᵀ *ᵥ fun k => Y₁ k s ω - Y₂ k s ω)
            + ∑ j, (Gᵀ *ᵥ fun k => Z₁ k s ω j - Z₂ k s ω j)
              ⬝ᵥ (Gᵀ *ᵥ fun k => Z₁ k s ω j - Z₂ k s ω j)
            + ∫ e, (Gᵀ *ᵥ fun k => U₁ k s ω e - U₂ k s ω e)
              ⬝ᵥ (Gᵀ *ᵥ fun k => U₁ k s ω e - U₂ k s ω e) ∂ν) ∂P
          - β₂ * ∫ ω, (G *ᵥ fun i => X₁ i s ω - X₂ i s ω)
              ⬝ᵥ (G *ᵥ fun i => X₁ i s ω - X₂ i s ω) ∂P := by
  filter_upwards [hM, ae_restrict_mem measurableSet_Icc, hr₁, hr₂, hm₁, hm₂, hU₁, hU₂]
    with s hMs hs hr₁ hr₂ hm₁ hm₂ hU₁ hU₂
  have hle := hMs _ _ (hsm₁ s) (hsm₂ s) hm₁ hm₂
  set Θ₁ := tupleAt ν X₁ Y₁ Z₁ U₁ s
  set Θ₂ := tupleAt ν X₂ Y₂ Z₂ U₂ s
  have iY : Integrable (fun ω => ‖ContinuousLinearMap.adjoint (GX G)
      ((Θ₁ ω).2.1 - (Θ₂ ω).2.1)‖ ^ 2) P := by
    have hπ : MemLp (fun ω => (Θ₁ ω).2.1 - (Θ₂ ω).2.1) 2 P := hm₁.snd.fst.sub hm₂.snd.fst
    exact (hπ.continuousLinearMap_comp _).integrable_norm_pow two_ne_zero
  have iZ : Integrable (fun ω => ‖ContinuousLinearMap.adjoint (GZ G)
      ((Θ₁ ω).2.2.1 - (Θ₂ ω).2.2.1)‖ ^ 2) P := by
    have hπ : MemLp (fun ω => (Θ₁ ω).2.2.1 - (Θ₂ ω).2.2.1) 2 P :=
      hm₁.snd.snd.fst.sub hm₂.snd.snd.fst
    exact (hπ.continuousLinearMap_comp _).integrable_norm_pow two_ne_zero
  have iU : Integrable (fun ω => ‖ContinuousLinearMap.adjoint (GU G ν)
      ((Θ₁ ω).2.2.2 - (Θ₂ ω).2.2.2)‖ ^ 2) P := by
    have hπ : MemLp (fun ω => (Θ₁ ω).2.2.2 - (Θ₂ ω).2.2.2) 2 P :=
      hm₁.snd.snd.snd.sub hm₂.snd.snd.snd
    exact (hπ.continuousLinearMap_comp _).integrable_norm_pow two_ne_zero
  have iX : Integrable (fun ω => ‖GX G ((Θ₁ ω).1 - (Θ₂ ω).1)‖ ^ 2) P := by
    have hπ : MemLp (fun ω => (Θ₁ ω).1 - (Θ₂ ω).1) 2 P := hm₁.fst.sub hm₂.fst
    exact (hπ.continuousLinearMap_comp _).integrable_norm_pow two_ne_zero
  have iA : Integrable (fun ω =>
      ‖ContinuousLinearMap.adjoint (GX G) ((Θ₁ ω).2.1 - (Θ₂ ω).2.1)‖ ^ 2
        + ‖ContinuousLinearMap.adjoint (GZ G) ((Θ₁ ω).2.2.1 - (Θ₂ ω).2.2.1)‖ ^ 2
        + ‖ContinuousLinearMap.adjoint (GU G ν) ((Θ₁ ω).2.2.2 - (Θ₂ ω).2.2.2)‖ ^ 2) P :=
    (iY.add iZ).add iU
  have hA : (fun ω => ‖ContinuousLinearMap.adjoint (GX G) ((Θ₁ ω).2.1 - (Θ₂ ω).2.1)‖ ^ 2
        + ‖ContinuousLinearMap.adjoint (GZ G) ((Θ₁ ω).2.2.1 - (Θ₂ ω).2.2.1)‖ ^ 2
        + ‖ContinuousLinearMap.adjoint (GU G ν) ((Θ₁ ω).2.2.2 - (Θ₂ ω).2.2.2)‖ ^ 2)
      =ᵐ[P] fun ω => (Gᵀ *ᵥ fun k => Y₁ k s ω - Y₂ k s ω)
          ⬝ᵥ (Gᵀ *ᵥ fun k => Y₁ k s ω - Y₂ k s ω)
        + ∑ j, (Gᵀ *ᵥ fun k => Z₁ k s ω j - Z₂ k s ω j)
          ⬝ᵥ (Gᵀ *ᵥ fun k => Z₁ k s ω j - Z₂ k s ω j)
        + ∫ e, (Gᵀ *ᵥ fun k => U₁ k s ω e - U₂ k s ω e)
          ⬝ᵥ (Gᵀ *ᵥ fun k => U₁ k s ω e - U₂ k s ω e) ∂ν := by
    filter_upwards [hU₁, hU₂] with ω hω₁ hω₂
    exact norm_sq_adjoint_tupleAt hω₁ hω₂
  calc _ = ∫ ω, interiorPairing (GX G) (GZ G) (GU G ν)
          (diagDiff C s (Θ₁ ω) (Θ₂ ω) (lawP2 P Θ₁) (lawP2 P Θ₂)) ∂P := by
        refine integral_congr_ae ?_
        filter_upwards [hr₁, hr₂, hU₁, hU₂] with ω hω₁ hω₂ hω₃ hω₄
        exact (interiorPairing_tupleAt hs hω₁ hω₂ hω₃ hω₄).symm
    _ ≤ ∫ ω, dissipation (GX G) (GZ G) (GU G ν) β₁ β₂
          (diagDiff C s (Θ₁ ω) (Θ₂ ω) (lawP2 P Θ₁) (lawP2 P Θ₂)) ∂P := hle
    _ = ∫ ω, (-β₁ * (‖ContinuousLinearMap.adjoint (GX G) ((Θ₁ ω).2.1 - (Θ₂ ω).2.1)‖ ^ 2
            + ‖ContinuousLinearMap.adjoint (GZ G) ((Θ₁ ω).2.2.1 - (Θ₂ ω).2.2.1)‖ ^ 2
            + ‖ContinuousLinearMap.adjoint (GU G ν) ((Θ₁ ω).2.2.2 - (Θ₂ ω).2.2.2)‖ ^ 2)
          - β₂ * ‖GX G ((Θ₁ ω).1 - (Θ₂ ω).1)‖ ^ 2) ∂P :=
        integral_congr_ae (ae_of_all _ fun ω => rfl)
    _ = -β₁ * ∫ ω, (‖ContinuousLinearMap.adjoint (GX G) ((Θ₁ ω).2.1 - (Θ₂ ω).2.1)‖ ^ 2
            + ‖ContinuousLinearMap.adjoint (GZ G) ((Θ₁ ω).2.2.1 - (Θ₂ ω).2.2.1)‖ ^ 2
            + ‖ContinuousLinearMap.adjoint (GU G ν) ((Θ₁ ω).2.2.2 - (Θ₂ ω).2.2.2)‖ ^ 2) ∂P
          - β₂ * ∫ ω, ‖GX G ((Θ₁ ω).1 - (Θ₂ ω).1)‖ ^ 2 ∂P := by
        rw [integral_sub (iA.const_mul _) (iX.const_mul _), integral_const_mul,
          integral_const_mul]
    _ = _ := by
        rw [integral_congr_ae hA,
          integral_congr_ae (ae_of_all _ fun ω => norm_sq_GX_tupleAt (G := G) (ω := ω))]

/-- **The terminal inequality of Assumption 2.5 along two processes.** For a terminal function
satisfying the terminal inequality along the diagonal, and two processes whose values at the
horizon are `ℱ_T`-measurable and square integrable, `α 𝔼|G δX_T|² ≤ 𝔼⟨δg_T, G δX_T⟩`, in
coordinates. -/
theorem TerminalMonotone.monoT_pair (hMT : TerminalMonotone ℱ P T G α C.g)
    (hX₁ : ∀ i, Measurable[ℱ T] (X₁ i T)) (hX₂ : ∀ i, Measurable[ℱ T] (X₂ i T))
    (hq₁ : ∀ i, MemLp (X₁ i T) 2 P) (hq₂ : ∀ i, MemLp (X₂ i T) 2 P) :
    α * ∫ ω, (G *ᵥ fun i => X₁ i T ω - X₂ i T ω) ⬝ᵥ (G *ᵥ fun i => X₁ i T ω - X₂ i T ω) ∂P
      ≤ ∫ ω, (fun k => terminalVal P T C X₁ k ω - terminalVal P T C X₂ k ω)
          ⬝ᵥ (G *ᵥ fun i => X₁ i T ω - X₂ i T ω) ∂P := by
  have hL₁ : MemLp (fun ω => (toLp 2 fun i => X₁ i T ω : EuclideanSpace ℝ (Fin n))) 2 P :=
    memLp_toLp_of_forall (u := fun ω i => X₁ i T ω) hq₁
  have hL₂ : MemLp (fun ω => (toLp 2 fun i => X₂ i T ω : EuclideanSpace ℝ (Fin n))) 2 P :=
    memLp_toLp_of_forall (u := fun ω i => X₂ i T ω) hq₂
  have h := hMT _ _ (measurable_toLp_of_forall (mΩ := ℱ T) hX₁).stronglyMeasurable
    (measurable_toLp_of_forall (mΩ := ℱ T) hX₂).stronglyMeasurable hL₁ hL₂
  simp only [g_sub_eq_toLp, ← toLp_sub, GX_toLp, norm_toLp_sq_eq_dotProduct,
    inner_toLp_eq_dotProduct] at h
  exact h

/-- **(2.7) along two solutions.** For two solutions of the `λ`-forced system with the same
coefficients, satisfying Assumption 2.5 along the diagonal, at almost every time `s ∈ [0, T]`,
`𝔼[⟨δb, Gᵀ δY⟩ + ⟨δσ, Gᵀ δZ⟩_F − ⟨δf, G δX⟩ + ∫_E ⟨δh(e), Gᵀ δU(e)⟩ ν(de)]
  ≤ −β₁ 𝔼[|Gᵀ δY|² + |Gᵀ δZ|²_F + ‖Gᵀ δU‖²] − β₂ 𝔼|G δX|²`, in coordinates. -/
theorem SolvesForced.mono_pair
    (h₁ : SolvesForced D ℱ hℱW hℱN T lam C ξ₁ qb₁ qσ₁ qh₁ qf₁ qg₁ X₁ Y₁ Z₁ U₁ γ₁)
    (h₂ : SolvesForced D ℱ hℱW hℱN T lam C ξ₂ qb₂ qσ₂ qh₂ qf₂ qg₂ X₂ Y₂ Z₂ U₂ γ₂)
    (𝒲 : D.CrossWitness ℱ) (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T)
    (hM : DiagonalMonotone ℱ P T G β₁ β₂ C) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      ∫ ω, ((fun i => driftProc P T C X₁ Y₁ Z₁ U₁ i ω s - driftProc P T C X₂ Y₂ Z₂ U₂ i ω s)
            ⬝ᵥ (Gᵀ *ᵥ fun k => Y₁ k s ω - Y₂ k s ω)
          + ∑ j, (fun i => diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j
            - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j) ⬝ᵥ (Gᵀ *ᵥ fun k => Z₁ k s ω j - Z₂ k s ω j)
          - (fun k => driverProc P T C X₁ Y₁ Z₁ U₁ k ω s - driverProc P T C X₂ Y₂ Z₂ U₂ k ω s)
            ⬝ᵥ (G *ᵥ fun i => X₁ i s ω - X₂ i s ω)
          + ∫ e, (fun i => jumpProc T γ₁ i s ω e - jumpProc T γ₂ i s ω e)
            ⬝ᵥ (Gᵀ *ᵥ fun k => U₁ k s ω e - U₂ k s ω e) ∂ν) ∂P
        ≤ -β₁ * ∫ ω, ((Gᵀ *ᵥ fun k => Y₁ k s ω - Y₂ k s ω)
              ⬝ᵥ (Gᵀ *ᵥ fun k => Y₁ k s ω - Y₂ k s ω)
            + ∑ j, (Gᵀ *ᵥ fun k => Z₁ k s ω j - Z₂ k s ω j)
              ⬝ᵥ (Gᵀ *ᵥ fun k => Z₁ k s ω j - Z₂ k s ω j)
            + ∫ e, (Gᵀ *ᵥ fun k => U₁ k s ω e - U₂ k s ω e)
              ⬝ᵥ (Gᵀ *ᵥ fun k => U₁ k s ω e - U₂ k s ω e) ∂ν) ∂P
          - β₂ * ∫ ω, (G *ᵥ fun i => X₁ i s ω - X₂ i s ω)
              ⬝ᵥ (G *ᵥ fun i => X₁ i s ω - X₂ i s ω) ∂P :=
  hM.mono_pair h₁.stronglyMeasurable_tupleAt h₂.stronglyMeasurable_tupleAt
    (h₁.ae_memLp_tupleAt 𝒲 hℱ0 hnull hT) (h₂.ae_memLp_tupleAt 𝒲 hℱ0 hnull hT)
    h₁.ae_ae_memLp_jump h₂.ae_ae_memLp_jump h₁.jump_rep h₂.jump_rep

/-- **The terminal inequality of Assumption 2.5 along two solutions.** For two solutions of the
`λ`-forced system with the same terminal function, satisfying the terminal inequality along the
diagonal, `α 𝔼|G δX_T|² ≤ 𝔼⟨δg_T, G δX_T⟩`, in coordinates. -/
theorem SolvesForced.monoT_pair
    (h₁ : SolvesForced D ℱ hℱW hℱN T lam C ξ₁ qb₁ qσ₁ qh₁ qf₁ qg₁ X₁ Y₁ Z₁ U₁ γ₁)
    (h₂ : SolvesForced D ℱ hℱW hℱN T lam C ξ₂ qb₂ qσ₂ qh₂ qf₂ qg₂ X₂ Y₂ Z₂ U₂ γ₂)
    (hT : 0 ≤ T) (hMT : TerminalMonotone ℱ P T G α C.g) :
    α * ∫ ω, (G *ᵥ fun i => X₁ i T ω - X₂ i T ω) ⬝ᵥ (G *ᵥ fun i => X₁ i T ω - X₂ i T ω) ∂P
      ≤ ∫ ω, (fun k => terminalVal P T C X₁ k ω - terminalVal P T C X₂ k ω)
          ⬝ᵥ (G *ᵥ fun i => X₁ i T ω - X₂ i T ω) ∂P :=
  hMT.monoT_pair (fun i => (h₁.fwd i).X_adapted T) (fun i => (h₂.fwd i).X_adapted T)
    (fun i => (h₁.fwd i).memLp_terminal hT) (fun i => (h₂.fwd i).memLp_terminal hT)

/-- **Assumption 2.5 at the pair.** Two solutions of the `λ`-forced system with the same
coefficients, satisfying Assumption 2.5 along the diagonal with coupling matrix `G` and
constants `α, β₁, β₂`, satisfy `PairMonotone` with the same `G, α, β₁, β₂`, over a filtration
whose null sets lie in its time-`0` field, whose right-continuation is constant before `0` and
which admits a cross witness. -/
theorem SolvesForced.pairMonotone
    (h₁ : SolvesForced D ℱ hℱW hℱN T lam C ξ₁ qb₁ qσ₁ qh₁ qf₁ qg₁ X₁ Y₁ Z₁ U₁ γ₁)
    (h₂ : SolvesForced D ℱ hℱW hℱN T lam C ξ₂ qb₂ qσ₂ qh₂ qf₂ qg₂ X₂ Y₂ Z₂ U₂ γ₂)
    (𝒲 : D.CrossWitness ℱ) (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T)
    (hM : DiagonalMonotone ℱ P T G β₁ β₂ C) (hMT : TerminalMonotone ℱ P T G α C.g) :
    PairMonotone P ν T G α β₁ β₂ (fun i t ω => X₁ i t ω - X₂ i t ω)
      (fun k t ω => Y₁ k t ω - Y₂ k t ω) (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j)
      (fun k t ω e => U₁ k t ω e - U₂ k t ω e)
      (fun i ω s => driftProc P T C X₁ Y₁ Z₁ U₁ i ω s - driftProc P T C X₂ Y₂ Z₂ U₂ i ω s)
      (fun i s ω j => diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j
        - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j)
      (fun i s ω e => jumpProc T γ₁ i s ω e - jumpProc T γ₂ i s ω e)
      (fun k ω s => driverProc P T C X₁ Y₁ Z₁ U₁ k ω s - driverProc P T C X₂ Y₂ Z₂ U₂ k ω s)
      (fun k ω => terminalVal P T C X₁ k ω - terminalVal P T C X₂ k ω) where
  mono := h₁.mono_pair h₂ 𝒲 hℱ0 hnull hT hM
  monoT := h₁.monoT_pair h₂ hT.le hMT

end Dissertation.WellPosedness.System
