/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.System.Coefficients
import Mathlib.Algebra.Ring.IsFormallyReal

/-!
# Dissipativity margins and perturbation pairing bounds

Remark 2.11 of the well-posedness paper says that the interior inequality (2.7) holds with a
dissipativity margin `c` if, along the diagonal,

`𝔼[⟨δb, Gᵀ δY⟩ + ⟨δσ, Gᵀ δZ⟩_F − ⟨δf, G δX⟩ + ∫_E ⟨δh(e), Gᵀ δU(e)⟩ ν(de)]`
`  ≤ −β₁ 𝔼[|Gᵀ δY|² + |Gᵀ δZ|²_F + ‖Gᵀ δU‖²_{L²(ν)}] − β₂ 𝔼|G δX|² − c 𝔼 Q`,

with `Q` the weighted quantity `|Gᵀ δY|² + |Gᵀ δZ|²_F + ‖Gᵀ δU‖²_{L²(ν)} + |G δX|²` in (2.12),
or, when `m = n`, the unweighted quantity `|δY|² + |δZ|²_F + ‖δU‖²_{L²(ν)} + |δX|²` in (2.13).
Corollary 3.6 bounds the pairing of a perturbation by (3.4),

`𝔼[⟨δp_b, Gᵀ δY⟩ + ⟨δp_σ, Gᵀ δZ⟩_F − ⟨δp_f, G δX⟩ + ∫_E ⟨δp_h(e), Gᵀ δU(e)⟩ ν(de)]`
`  ≤ c_pert 𝔼[|δX|² + |δY|² + |δZ|²_F + ‖δU‖²_{L²(ν)}]`,

and Remark 3.7 by the same bound in the weighted quantity.

The expectations are Bochner integrals, and a Bochner integral of a function that is not
integrable is `0`. The right-hand sides are integrable along square-integrable tuples, but the
pairing need not be, so (3.4) is recorded together with the integrability of the pairing. For the
margins no such clause is needed: with `c > 0` and `β₁, β₂ ≥ 0` a margin forces the pairing to be
integrable. Were it not, its integral would vanish, forcing `𝔼 Q = 0`, hence `Q = 0` almost
surely, and the pairing vanishes wherever `Q` does.

## Main definitions

* `gWeightSq` — the weighted quantity of (2.12).
* `DiagonalMonotoneMargin` — (2.13), the margin in the unweighted form, along the diagonal.
* `DiagonalMonotoneWeightedMargin` — (2.12), the margin in the weighted form, along the diagonal.
* `DiagonalPairingBound` — (3.4), with the integrability of the pairing.
* `DiagonalWeightedPairingBound` — (3.4) in the weighted quantity, with the integrability of the
  pairing.

## Main statements

* `integrable_norm_sq_comp_sub`, `integrable_norm_sq_comp_sub_X`, `integrable_norm_sq_comp_sub_Y`,
  `integrable_norm_sq_comp_sub_Z`, `integrable_norm_sq_comp_sub_U`, `integrable_channelSq_sub`,
  `integrable_dissipation_diagDiff`, `integrable_gWeightSq_diagDiff` — integrability along two
  square-integrable tuples.
* `integrable_of_integral_le_sub_mul` — an integral bound with a positive margin forces
  integrability.
* `DiagonalMonotoneMargin.diagonalMonotone`, `DiagonalMonotoneWeightedMargin.diagonalMonotone` —
  a nonnegative margin gives Assumption 2.5, interior.
* `DiagonalMonotoneMargin.integrable`, `DiagonalMonotoneWeightedMargin.integrable` — a positive
  margin forces the pairing to be integrable.
-/

open MeasureTheory Filter MVFBSDEJ.Law
open scoped ENNReal

namespace MVFBSDEJ.WellPosedness.System

/-! ### The weighted quantity -/

section Weight

variable {HX HY HZX HZY HUX HUY : Type*}
  [NormedAddCommGroup HX] [InnerProductSpace ℝ HX] [CompleteSpace HX]
  [NormedAddCommGroup HY] [InnerProductSpace ℝ HY] [CompleteSpace HY]
  [NormedAddCommGroup HZX] [InnerProductSpace ℝ HZX] [CompleteSpace HZX]
  [NormedAddCommGroup HZY] [InnerProductSpace ℝ HZY] [CompleteSpace HZY]
  [NormedAddCommGroup HUX] [InnerProductSpace ℝ HUX] [CompleteSpace HUX]
  [NormedAddCommGroup HUY] [InnerProductSpace ℝ HUY] [CompleteSpace HUY]
  (A : HX →L[ℝ] HY) (AZ : HZX →L[ℝ] HZY) (AU : HUX →L[ℝ] HUY)

/-- The weighted quantity of (2.12), `|Gᵀ δY|² + |Gᵀ δZ|²_F + ‖Gᵀ δU‖²_{L²(ν)} + |G δX|²`. -/
noncomputable def gWeightSq (c : ChannelDiff HX HY HZX HZY HUX HUY) : ℝ :=
  ‖ContinuousLinearMap.adjoint A c.δY‖ ^ 2 + ‖ContinuousLinearMap.adjoint AZ c.δZ‖ ^ 2
    + ‖ContinuousLinearMap.adjoint AU c.δU‖ ^ 2 + ‖A c.δX‖ ^ 2

/-- The weighted quantity is nonnegative. -/
theorem gWeightSq_nonneg (c : ChannelDiff HX HY HZX HZY HUX HUY) : 0 ≤ gWeightSq A AZ AU c := by
  unfold gWeightSq
  positivity

/-- The right-hand side of (2.7) is nonpositive for `β₁, β₂ ≥ 0`. -/
theorem dissipation_nonpos {β₁ β₂ : ℝ} (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂)
    (c : ChannelDiff HX HY HZX HZY HUX HUY) : dissipation A AZ AU β₁ β₂ c ≤ 0 := by
  unfold dissipation
  have h1 : 0 ≤ β₁ * (‖ContinuousLinearMap.adjoint A c.δY‖ ^ 2
      + ‖ContinuousLinearMap.adjoint AZ c.δZ‖ ^ 2 + ‖ContinuousLinearMap.adjoint AU c.δU‖ ^ 2) :=
    mul_nonneg hβ₁ (by positivity)
  have h2 : 0 ≤ β₂ * ‖A c.δX‖ ^ 2 := mul_nonneg hβ₂ (by positivity)
  linarith

/-- **The interior pairing vanishes with the weighted quantity**: every term of the pairing has a
factor `Gᵀ δY`, `Gᵀ δZ`, `Gᵀ δU` or `G δX`. -/
theorem interiorPairing_eq_zero_of_gWeightSq_eq_zero {c : ChannelDiff HX HY HZX HZY HUX HUY}
    (h : gWeightSq A AZ AU c = 0) : interiorPairing A AZ AU c = 0 := by
  unfold gWeightSq at h
  have h1 := sq_nonneg ‖ContinuousLinearMap.adjoint A c.δY‖
  have h2 := sq_nonneg ‖ContinuousLinearMap.adjoint AZ c.δZ‖
  have h3 := sq_nonneg ‖ContinuousLinearMap.adjoint AU c.δU‖
  have h4 := sq_nonneg ‖A c.δX‖
  have eY : ContinuousLinearMap.adjoint A c.δY = 0 := by
    rw [← norm_eq_zero]; exact pow_eq_zero_iff two_ne_zero |>.mp (by linarith)
  have eZ : ContinuousLinearMap.adjoint AZ c.δZ = 0 := by
    rw [← norm_eq_zero]; exact pow_eq_zero_iff two_ne_zero |>.mp (by linarith)
  have eU : ContinuousLinearMap.adjoint AU c.δU = 0 := by
    rw [← norm_eq_zero]; exact pow_eq_zero_iff two_ne_zero |>.mp (by linarith)
  have eX : A c.δX = 0 := by
    rw [← norm_eq_zero]; exact pow_eq_zero_iff two_ne_zero |>.mp (by linarith)
  simp only [interiorPairing, eY, eZ, eU, eX, inner_zero_right, add_zero]

end Weight

/-! ### Integrability along two square-integrable tuples -/

section Integrable

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} {n m d : ℕ}
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Θ Θ' : Ω → TupleH ν n m d}

/-- For a continuous linear map `A` on the tuple space and two square-integrable tuples,
`ω ↦ ‖A (Θ ω − Θ' ω)‖²` is integrable. -/
theorem integrable_norm_sq_comp_sub {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : TupleH ν n m d →L[ℝ] F) (hΘ : MemLp Θ 2 P) (hΘ' : MemLp Θ' 2 P) :
    Integrable (fun ω => ‖A (Θ ω - Θ' ω)‖ ^ 2) P := by
  have h := (A.comp_memLp' (hΘ.sub hΘ')).integrable_norm_pow two_ne_zero
  simpa only [Function.comp_apply, Pi.sub_apply] using h

/-- For a continuous linear map `B` on the forward channel and two square-integrable tuples,
`ω ↦ ‖B δX‖²` is integrable. -/
theorem integrable_norm_sq_comp_sub_X {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] F) (hΘ : MemLp Θ 2 P) (hΘ' : MemLp Θ' 2 P) :
    Integrable (fun ω => ‖B ((Θ ω).1 - (Θ' ω).1)‖ ^ 2) P :=
  integrable_norm_sq_comp_sub (B.comp (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin n))
    (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m × Fin d)
      × Lp (EuclideanSpace ℝ (Fin m)) 2 ν))) hΘ hΘ'

/-- For a continuous linear map `B` on the backward channel and two square-integrable tuples,
`ω ↦ ‖B δY‖²` is integrable. -/
theorem integrable_norm_sq_comp_sub_Y {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (B : EuclideanSpace ℝ (Fin m) →L[ℝ] F) (hΘ : MemLp Θ 2 P) (hΘ' : MemLp Θ' 2 P) :
    Integrable (fun ω => ‖B ((Θ ω).2.1 - (Θ' ω).2.1)‖ ^ 2) P :=
  integrable_norm_sq_comp_sub (B.comp ((ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin m))
    (EuclideanSpace ℝ (Fin m × Fin d) × Lp (EuclideanSpace ℝ (Fin m)) 2 ν)).comp
    (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m × Fin d)
        × Lp (EuclideanSpace ℝ (Fin m)) 2 ν)))) hΘ hΘ'

/-- For a continuous linear map `B` on the Brownian channel and two square-integrable tuples,
`ω ↦ ‖B δZ‖²` is integrable. -/
theorem integrable_norm_sq_comp_sub_Z {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (B : EuclideanSpace ℝ (Fin m × Fin d) →L[ℝ] F) (hΘ : MemLp Θ 2 P) (hΘ' : MemLp Θ' 2 P) :
    Integrable (fun ω => ‖B ((Θ ω).2.2.1 - (Θ' ω).2.2.1)‖ ^ 2) P :=
  integrable_norm_sq_comp_sub (B.comp ((ContinuousLinearMap.fst ℝ
    (EuclideanSpace ℝ (Fin m × Fin d)) (Lp (EuclideanSpace ℝ (Fin m)) 2 ν)).comp
    ((ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin m))
      (EuclideanSpace ℝ (Fin m × Fin d) × Lp (EuclideanSpace ℝ (Fin m)) 2 ν)).comp
      (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n))
        (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m × Fin d)
          × Lp (EuclideanSpace ℝ (Fin m)) 2 ν))))) hΘ hΘ'

/-- For a continuous linear map `B` on the jump channel and two square-integrable tuples,
`ω ↦ ‖B δU‖²` is integrable. -/
theorem integrable_norm_sq_comp_sub_U {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (B : Lp (EuclideanSpace ℝ (Fin m)) 2 ν →L[ℝ] F) (hΘ : MemLp Θ 2 P) (hΘ' : MemLp Θ' 2 P) :
    Integrable (fun ω => ‖B ((Θ ω).2.2.2 - (Θ' ω).2.2.2)‖ ^ 2) P :=
  integrable_norm_sq_comp_sub (B.comp ((ContinuousLinearMap.snd ℝ
    (EuclideanSpace ℝ (Fin m × Fin d)) (Lp (EuclideanSpace ℝ (Fin m)) 2 ν)).comp
    ((ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin m))
      (EuclideanSpace ℝ (Fin m × Fin d) × Lp (EuclideanSpace ℝ (Fin m)) 2 ν)).comp
      (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n))
        (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m × Fin d)
          × Lp (EuclideanSpace ℝ (Fin m)) 2 ν))))) hΘ hΘ'

/-- For two square-integrable tuples, `ω ↦ |δX|² + |δY|² + |δZ|²_F + ‖δU‖²_{L²(ν)}` is
integrable. -/
theorem integrable_channelSq_sub (hΘ : MemLp Θ 2 P) (hΘ' : MemLp Θ' 2 P) :
    Integrable (fun ω => channelSq (Θ ω - Θ' ω)) P := by
  refine ((((integrable_norm_sq_comp_sub_X (ContinuousLinearMap.id ℝ _) hΘ hΘ').add
    (integrable_norm_sq_comp_sub_Y (ContinuousLinearMap.id ℝ _) hΘ hΘ')).add
    (integrable_norm_sq_comp_sub_Z (ContinuousLinearMap.id ℝ _) hΘ hΘ')).add
    (integrable_norm_sq_comp_sub_U (ContinuousLinearMap.id ℝ _) hΘ hΘ')).congr
    (ae_of_all _ fun ω => ?_)
  simp only [channelSq, Prod.fst_sub, Prod.snd_sub, ContinuousLinearMap.id_apply, Pi.add_apply]

/-- For any three coupling operators and two square-integrable tuples, the right-hand side of
(2.7) along them is integrable. -/
theorem integrable_dissipation_diagDiff
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (AZ : EuclideanSpace ℝ (Fin n × Fin d) →L[ℝ] EuclideanSpace ℝ (Fin m × Fin d))
    (AU : Lp (EuclideanSpace ℝ (Fin n)) 2 ν →L[ℝ] Lp (EuclideanSpace ℝ (Fin m)) 2 ν)
    (β₁ β₂ : ℝ) (C : Coeffs ν n m d) (t : ℝ) (μ μ' : P2 (TupleH ν n m d)) (hΘ : MemLp Θ 2 P)
    (hΘ' : MemLp Θ' 2 P) :
    Integrable (fun ω => dissipation A AZ AU β₁ β₂ (diagDiff C t (Θ ω) (Θ' ω) μ μ')) P :=
  ((((integrable_norm_sq_comp_sub_Y (ContinuousLinearMap.adjoint A) hΘ hΘ').add
    (integrable_norm_sq_comp_sub_Z (ContinuousLinearMap.adjoint AZ) hΘ hΘ')).add
    (integrable_norm_sq_comp_sub_U (ContinuousLinearMap.adjoint AU) hΘ hΘ')).const_mul
      (-β₁)).sub ((integrable_norm_sq_comp_sub_X A hΘ hΘ').const_mul β₂)

/-- For any three coupling operators and two square-integrable tuples, the weighted quantity of
(2.12) along them is integrable. -/
theorem integrable_gWeightSq_diagDiff
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (AZ : EuclideanSpace ℝ (Fin n × Fin d) →L[ℝ] EuclideanSpace ℝ (Fin m × Fin d))
    (AU : Lp (EuclideanSpace ℝ (Fin n)) 2 ν →L[ℝ] Lp (EuclideanSpace ℝ (Fin m)) 2 ν)
    (C : Coeffs ν n m d) (t : ℝ) (μ μ' : P2 (TupleH ν n m d)) (hΘ : MemLp Θ 2 P)
    (hΘ' : MemLp Θ' 2 P) :
    Integrable (fun ω => gWeightSq A AZ AU (diagDiff C t (Θ ω) (Θ' ω) μ μ')) P :=
  (((integrable_norm_sq_comp_sub_Y (ContinuousLinearMap.adjoint A) hΘ hΘ').add
    (integrable_norm_sq_comp_sub_Z (ContinuousLinearMap.adjoint AZ) hΘ hΘ')).add
    (integrable_norm_sq_comp_sub_U (ContinuousLinearMap.adjoint AU) hΘ hΘ')).add
    (integrable_norm_sq_comp_sub_X A hΘ hΘ')

/-- **The interior pairing vanishes with the unweighted quantity**: if
`|δX|² + |δY|² + |δZ|²_F + ‖δU‖²_{L²(ν)} = 0`, the pairing is `0`. -/
theorem interiorPairing_diagDiff_eq_zero_of_channelSq_eq_zero
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (AZ : EuclideanSpace ℝ (Fin n × Fin d) →L[ℝ] EuclideanSpace ℝ (Fin m × Fin d))
    (AU : Lp (EuclideanSpace ℝ (Fin n)) 2 ν →L[ℝ] Lp (EuclideanSpace ℝ (Fin m)) 2 ν)
    (C : Coeffs ν n m d) (t : ℝ) {θ θ' : TupleH ν n m d} (μ μ' : P2 (TupleH ν n m d))
    (h : channelSq (θ - θ') = 0) :
    interiorPairing A AZ AU (diagDiff C t θ θ' μ μ') = 0 := by
  refine interiorPairing_eq_zero_of_gWeightSq_eq_zero A AZ AU ?_
  replace h : ‖θ.1 - θ'.1‖ ^ 2 + ‖θ.2.1 - θ'.2.1‖ ^ 2 + ‖θ.2.2.1 - θ'.2.2.1‖ ^ 2
      + ‖θ.2.2.2 - θ'.2.2.2‖ ^ 2 = 0 := h
  have h1 := sq_nonneg ‖θ.1 - θ'.1‖
  have h2 := sq_nonneg ‖θ.2.1 - θ'.2.1‖
  have h3 := sq_nonneg ‖θ.2.2.1 - θ'.2.2.1‖
  have h4 := sq_nonneg ‖θ.2.2.2 - θ'.2.2.2‖
  have eX : θ.1 - θ'.1 = 0 := by
    rw [← norm_eq_zero]; exact pow_eq_zero_iff two_ne_zero |>.mp (by linarith)
  have eY : θ.2.1 - θ'.2.1 = 0 := by
    rw [← norm_eq_zero]; exact pow_eq_zero_iff two_ne_zero |>.mp (by linarith)
  have eZ : θ.2.2.1 - θ'.2.2.1 = 0 := by
    rw [← norm_eq_zero]; exact pow_eq_zero_iff two_ne_zero |>.mp (by linarith)
  have eU : θ.2.2.2 - θ'.2.2.2 = 0 := by
    rw [← norm_eq_zero]; exact pow_eq_zero_iff two_ne_zero |>.mp (by linarith)
  simp [gWeightSq, diagDiff, eX, eY, eZ, eU]

/-- **An integral bound with a positive margin forces integrability.** If `diss ≤ 0`, `Q ≥ 0` is
integrable, `pair` vanishes wherever `Q` does, and `∫ pair ≤ ∫ diss − c ∫ Q` with `c > 0`, then
`pair` is integrable. -/
theorem integrable_of_integral_le_sub_mul {pair diss Q : Ω → ℝ} {c : ℝ} (hc : 0 < c)
    (hdiss : ∀ ω, diss ω ≤ 0) (hQ : ∀ ω, 0 ≤ Q ω) (hQi : Integrable Q P)
    (hzero : ∀ ω, Q ω = 0 → pair ω = 0)
    (h : ∫ ω, pair ω ∂P ≤ ∫ ω, diss ω ∂P - c * ∫ ω, Q ω ∂P) : Integrable pair P := by
  by_contra hni
  rw [integral_undef hni] at h
  have h1 : ∫ ω, diss ω ∂P ≤ 0 := integral_nonpos hdiss
  have h2 : 0 ≤ ∫ ω, Q ω ∂P := integral_nonneg hQ
  have h3 : ∫ ω, Q ω ∂P = 0 := by nlinarith
  have h4 : Q =ᵐ[P] 0 := (integral_eq_zero_iff_of_nonneg hQ hQi).mp h3
  have h5 : pair =ᵐ[P] 0 := h4.mono fun ω hω => hzero ω hω
  exact hni ((integrable_zero Ω ℝ P).congr h5.symm)

end Integrable

/-! ### The predicates -/

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} {n m d : ℕ}
  {Ω : Type*} [MeasurableSpace Ω] [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]

/-- **(2.13), the margin `c` in the unweighted form, along the diagonal**: for almost every
`t ∈ [0, T]` and any two strongly `ℱ_t`-measurable square-integrable tuples `Θ, Θ'` with laws
`μ, μ'`,
`𝔼[⟨δb, Gᵀ δY⟩ + ⟨δσ, Gᵀ δZ⟩_F − ⟨δf, G δX⟩ + ∫_E ⟨δh(e), Gᵀ δU(e)⟩ ν(de)]
  ≤ −β₁ 𝔼[|Gᵀ δY|² + |Gᵀ δZ|²_F + ‖Gᵀ δU‖²_{L²(ν)}] − β₂ 𝔼|G δX|²
    − c 𝔼[|δY|² + |δZ|²_F + ‖δU‖²_{L²(ν)} + |δX|²]`. -/
def DiagonalMonotoneMargin (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (P : Measure Ω)
    [IsProbabilityMeasure P] (T : ℝ) (G : Matrix (Fin m) (Fin n) ℝ) (β₁ β₂ c : ℝ)
    (C : Coeffs ν n m d) : Prop :=
  ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ Θ Θ' : Ω → TupleH ν n m d,
    StronglyMeasurable[ℱ t] Θ → StronglyMeasurable[ℱ t] Θ' → MemLp Θ 2 P → MemLp Θ' 2 P →
    ∫ ω, interiorPairing (GX G) (GZ G) (GU G ν)
        (diagDiff C t (Θ ω) (Θ' ω) (lawP2 P Θ) (lawP2 P Θ')) ∂P
      ≤ ∫ ω, dissipation (GX G) (GZ G) (GU G ν) β₁ β₂
          (diagDiff C t (Θ ω) (Θ' ω) (lawP2 P Θ) (lawP2 P Θ')) ∂P
        - c * ∫ ω, channelSq (Θ ω - Θ' ω) ∂P

/-- **(2.12), the margin `c` in the weighted form, along the diagonal**: for almost every
`t ∈ [0, T]` and any two strongly `ℱ_t`-measurable square-integrable tuples `Θ, Θ'` with laws
`μ, μ'`,
`𝔼[⟨δb, Gᵀ δY⟩ + ⟨δσ, Gᵀ δZ⟩_F − ⟨δf, G δX⟩ + ∫_E ⟨δh(e), Gᵀ δU(e)⟩ ν(de)]
  ≤ −β₁ 𝔼[|Gᵀ δY|² + |Gᵀ δZ|²_F + ‖Gᵀ δU‖²_{L²(ν)}] − β₂ 𝔼|G δX|²
    − c 𝔼[|Gᵀ δY|² + |Gᵀ δZ|²_F + ‖Gᵀ δU‖²_{L²(ν)} + |G δX|²]`. -/
def DiagonalMonotoneWeightedMargin (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (P : Measure Ω)
    [IsProbabilityMeasure P] (T : ℝ) (G : Matrix (Fin m) (Fin n) ℝ) (β₁ β₂ c : ℝ)
    (C : Coeffs ν n m d) : Prop :=
  ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ Θ Θ' : Ω → TupleH ν n m d,
    StronglyMeasurable[ℱ t] Θ → StronglyMeasurable[ℱ t] Θ' → MemLp Θ 2 P → MemLp Θ' 2 P →
    ∫ ω, interiorPairing (GX G) (GZ G) (GU G ν)
        (diagDiff C t (Θ ω) (Θ' ω) (lawP2 P Θ) (lawP2 P Θ')) ∂P
      ≤ ∫ ω, dissipation (GX G) (GZ G) (GU G ν) β₁ β₂
          (diagDiff C t (Θ ω) (Θ' ω) (lawP2 P Θ) (lawP2 P Θ')) ∂P
        - c * ∫ ω, gWeightSq (GX G) (GZ G) (GU G ν)
          (diagDiff C t (Θ ω) (Θ' ω) (lawP2 P Θ) (lawP2 P Θ')) ∂P

/-- **(3.4), the pairing bound of a perturbation, along the diagonal**: for almost every
`t ∈ [0, T]` and any two strongly `ℱ_t`-measurable square-integrable tuples `Θ, Θ'` with laws
`μ, μ'`, the pairing of the perturbation differences `δp_ψ` is integrable and
`𝔼[⟨δp_b, Gᵀ δY⟩ + ⟨δp_σ, Gᵀ δZ⟩_F − ⟨δp_f, G δX⟩ + ∫_E ⟨δp_h(e), Gᵀ δU(e)⟩ ν(de)]
  ≤ c 𝔼[|δX|² + |δY|² + |δZ|²_F + ‖δU‖²_{L²(ν)}]`. -/
def DiagonalPairingBound (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (P : Measure Ω)
    [IsProbabilityMeasure P] (T : ℝ) (G : Matrix (Fin m) (Fin n) ℝ) (c : ℝ)
    (p : Coeffs ν n m d) : Prop :=
  ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ Θ Θ' : Ω → TupleH ν n m d,
    StronglyMeasurable[ℱ t] Θ → StronglyMeasurable[ℱ t] Θ' → MemLp Θ 2 P → MemLp Θ' 2 P →
    Integrable (fun ω => interiorPairing (GX G) (GZ G) (GU G ν)
        (diagDiff p t (Θ ω) (Θ' ω) (lawP2 P Θ) (lawP2 P Θ'))) P
      ∧ ∫ ω, interiorPairing (GX G) (GZ G) (GU G ν)
          (diagDiff p t (Θ ω) (Θ' ω) (lawP2 P Θ) (lawP2 P Θ')) ∂P
        ≤ c * ∫ ω, channelSq (Θ ω - Θ' ω) ∂P

/-- **(3.4) in the weighted quantity of (2.12), along the diagonal**: for almost every
`t ∈ [0, T]` and any two strongly `ℱ_t`-measurable square-integrable tuples `Θ, Θ'` with laws
`μ, μ'`, the pairing of the perturbation differences `δp_ψ` is integrable and
`𝔼[⟨δp_b, Gᵀ δY⟩ + ⟨δp_σ, Gᵀ δZ⟩_F − ⟨δp_f, G δX⟩ + ∫_E ⟨δp_h(e), Gᵀ δU(e)⟩ ν(de)]
  ≤ c 𝔼[|Gᵀ δY|² + |Gᵀ δZ|²_F + ‖Gᵀ δU‖²_{L²(ν)} + |G δX|²]`. -/
def DiagonalWeightedPairingBound (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (P : Measure Ω)
    [IsProbabilityMeasure P] (T : ℝ) (G : Matrix (Fin m) (Fin n) ℝ) (c : ℝ)
    (p : Coeffs ν n m d) : Prop :=
  ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ Θ Θ' : Ω → TupleH ν n m d,
    StronglyMeasurable[ℱ t] Θ → StronglyMeasurable[ℱ t] Θ' → MemLp Θ 2 P → MemLp Θ' 2 P →
    Integrable (fun ω => interiorPairing (GX G) (GZ G) (GU G ν)
        (diagDiff p t (Θ ω) (Θ' ω) (lawP2 P Θ) (lawP2 P Θ'))) P
      ∧ ∫ ω, interiorPairing (GX G) (GZ G) (GU G ν)
          (diagDiff p t (Θ ω) (Θ' ω) (lawP2 P Θ) (lawP2 P Θ')) ∂P
        ≤ c * ∫ ω, gWeightSq (GX G) (GZ G) (GU G ν)
          (diagDiff p t (Θ ω) (Θ' ω) (lawP2 P Θ) (lawP2 P Θ')) ∂P

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {P : Measure Ω} [IsProbabilityMeasure P]
  {T β₁ β₂ c : ℝ} {G : Matrix (Fin m) (Fin n) ℝ} {C : Coeffs ν n m d}

/-- **A nonnegative unweighted margin gives Assumption 2.5, interior.** -/
theorem DiagonalMonotoneMargin.diagonalMonotone (h : DiagonalMonotoneMargin ℱ P T G β₁ β₂ c C)
    (hc : 0 ≤ c) : DiagonalMonotone ℱ P T G β₁ β₂ C := by
  filter_upwards [h] with t ht Θ Θ' hΘ hΘ' hΘ2 hΘ2'
  have h0 : 0 ≤ ∫ ω, channelSq (Θ ω - Θ' ω) ∂P := integral_nonneg fun ω => channelSq_nonneg _
  have := ht Θ Θ' hΘ hΘ' hΘ2 hΘ2'
  nlinarith

/-- **A nonnegative weighted margin gives Assumption 2.5, interior.** -/
theorem DiagonalMonotoneWeightedMargin.diagonalMonotone
    (h : DiagonalMonotoneWeightedMargin ℱ P T G β₁ β₂ c C) (hc : 0 ≤ c) :
    DiagonalMonotone ℱ P T G β₁ β₂ C := by
  filter_upwards [h] with t ht Θ Θ' hΘ hΘ' hΘ2 hΘ2'
  have h0 : 0 ≤ ∫ ω, gWeightSq (GX G) (GZ G) (GU G ν)
      (diagDiff C t (Θ ω) (Θ' ω) (lawP2 P Θ) (lawP2 P Θ')) ∂P :=
    integral_nonneg fun ω => gWeightSq_nonneg _ _ _ _
  have := ht Θ Θ' hΘ hΘ' hΘ2 hΘ2'
  nlinarith

/-- **A positive unweighted margin forces the pairing to be integrable**, for `β₁, β₂ ≥ 0`: for
almost every `t ∈ [0, T]` the interior pairing along any two strongly `ℱ_t`-measurable
square-integrable tuples is integrable. -/
theorem DiagonalMonotoneMargin.integrable (h : DiagonalMonotoneMargin ℱ P T G β₁ β₂ c C)
    (hc : 0 < c) (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂) :
    ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ Θ Θ' : Ω → TupleH ν n m d,
      StronglyMeasurable[ℱ t] Θ → StronglyMeasurable[ℱ t] Θ' → MemLp Θ 2 P → MemLp Θ' 2 P →
      Integrable (fun ω => interiorPairing (GX G) (GZ G) (GU G ν)
        (diagDiff C t (Θ ω) (Θ' ω) (lawP2 P Θ) (lawP2 P Θ'))) P := by
  filter_upwards [h] with t ht Θ Θ' hΘ hΘ' hΘ2 hΘ2'
  exact integrable_of_integral_le_sub_mul hc
    (fun ω => dissipation_nonpos _ _ _ hβ₁ hβ₂ _) (fun ω => channelSq_nonneg _)
    (integrable_channelSq_sub hΘ2 hΘ2')
    (fun ω hω => interiorPairing_diagDiff_eq_zero_of_channelSq_eq_zero _ _ _ C t _ _ hω)
    (ht Θ Θ' hΘ hΘ' hΘ2 hΘ2')

/-- **A positive weighted margin forces the pairing to be integrable**, for `β₁, β₂ ≥ 0`: for
almost every `t ∈ [0, T]` the interior pairing along any two strongly `ℱ_t`-measurable
square-integrable tuples is integrable. -/
theorem DiagonalMonotoneWeightedMargin.integrable
    (h : DiagonalMonotoneWeightedMargin ℱ P T G β₁ β₂ c C) (hc : 0 < c) (hβ₁ : 0 ≤ β₁)
    (hβ₂ : 0 ≤ β₂) :
    ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ Θ Θ' : Ω → TupleH ν n m d,
      StronglyMeasurable[ℱ t] Θ → StronglyMeasurable[ℱ t] Θ' → MemLp Θ 2 P → MemLp Θ' 2 P →
      Integrable (fun ω => interiorPairing (GX G) (GZ G) (GU G ν)
        (diagDiff C t (Θ ω) (Θ' ω) (lawP2 P Θ) (lawP2 P Θ'))) P := by
  filter_upwards [h] with t ht Θ Θ' hΘ hΘ' hΘ2 hΘ2'
  exact integrable_of_integral_le_sub_mul hc
    (fun ω => dissipation_nonpos _ _ _ hβ₁ hβ₂ _) (fun ω => gWeightSq_nonneg _ _ _ _)
    (integrable_gWeightSq_diagDiff _ _ _ C t _ _ hΘ2 hΘ2')
    (fun ω hω => interiorPairing_eq_zero_of_gWeightSq_eq_zero _ _ _ hω)
    (ht Θ Θ' hΘ hΘ' hΘ2 hΘ2')

end MVFBSDEJ.WellPosedness.System
