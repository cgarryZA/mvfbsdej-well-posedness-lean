/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Robustness.Example

/-!
# What a dissipativity margin demands of the jump channel

After Corollary 3.6 the well-posedness paper observes, by the reduction of Remark 2.10, that an
additive jump coefficient `h₀ = h₀(t, x, e)` can never serve as a baseline with a margin in
(2.13), and that jump feedback entering through finitely many functionals of `u` supplies no
margin either.

**Deterministic inputs.** At deterministic inputs `Θ = θ`, `Θ' = θ'`, whose laws are the Dirac
masses `δ_θ, δ_θ'`, (2.13) with margin `c` holds pointwise. Along two such inputs that differ in
the jump channel only, `δX = δY = δZ = 0`, it reduces to the strict dissipativity of the jump
channel,

`⟨δh, Gᵀ δu⟩_{L²(ν)} ≤ −β₁ ‖Gᵀ δu‖²_{L²(ν)} − c ‖δu‖²_{L²(ν)}`.

**Feedback through a linear map.** Say the jump coefficient depends on `u` only through a linear
map `ℓ` on `L²(ν; ℝᵐ)` along deterministic inputs: `h(t, θ, δ_θ) = h(t, θ', δ_θ')` whenever `θ, θ'`
share `x, y, z` and `ℓ u = ℓ u'`. If `ℓ` has a nonzero kernel element `u`, the two deterministic
inputs `(0, 0, 0, u)` and `0` have `δh = 0`, `δX = δY = δZ = 0` and `δU = u`, and (2.13) gives
`0 ≤ −β₁ ‖Gᵀ u‖² − c ‖u‖² < 0` for `c > 0`, `β₁ ≥ 0`, at any time of a horizon `T > 0`: no margin.
An additive `h₀ = h₀(t, x, e)` is the case `ℓ = 0`, whose kernel is all of `L²(ν; ℝᵐ)`,
nonzero when `ν ≠ 0` and `m > 0`, the setting of Remark 2.10. For `ℓ` with values in a
finite-dimensional space (finitely many functionals) the kernel is nonzero when `L²(ν; ℝᵐ)` is
infinite dimensional.

**A single atom.** When `ν` is a single atom, `L²(ν; ℝ)` is one dimensional and a single
functional is injective on it, so every jump coefficient enters through one functional of `u`.

## Main statements

* `lawP2_const`, `DiagonalMonotoneMargin.dirac` — (2.13) at deterministic inputs.
* `DiagonalMonotoneMargin.jump_dissipative_dirac` — a margin needs jump feedback dissipative on
  the whole of `L²(ν; ℝᵐ)`.
* `not_diagonalMonotoneMargin_of_factor` — jump feedback through a linear map with a nonzero
  kernel supplies no margin.
* `exists_Lp_ne_zero`, `not_diagonalMonotoneMargin_of_additive` — an additive jump coefficient
  supplies no margin.
* `not_diagonalMonotoneMargin_of_not_finiteDimensional` — nor do finitely many functionals on an
  infinite-dimensional `L²(ν; ℝᵐ)`.
* `inner_Lp_dirac`, `exists_injective_functional_dirac` — with a single atom, one functional of
  `u` is injective.
-/

open MeasureTheory Filter Dissertation.Law
open scoped ENNReal

namespace Dissertation.WellPosedness.System

/-! ### Deterministic inputs -/

/-- **The law of a constant random element** is the Dirac mass at its value. -/
theorem lawP2_const {F : Type*} [NormedAddCommGroup F] [MeasurableSpace F] [BorelSpace F]
    [MeasurableSingletonClass F] {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (a : F) : lawP2 P (fun _ : Ω => a) = P2.dirac a :=
  P2.ext_law (by rw [lawP2_law (memLp_const a), Measure.map_const, measure_univ, one_smul]; rfl)

section Dirac

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} {n m d : ℕ}
  {Ω : Type*} [MeasurableSpace Ω] [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {P : Measure Ω} [IsProbabilityMeasure P]
  {T β₁ β₂ c : ℝ} {G : Matrix (Fin m) (Fin n) ℝ} {C : Coeffs ν n m d}

/-- **(2.13) at deterministic inputs**: for almost every `t ∈ [0, T]` and all `θ, θ'`, with the
Dirac masses `δ_θ, δ_θ'` as laws, the interior pairing is at most the right-hand side of (2.7)
minus `c (|δX|² + |δY|² + |δZ|²_F + ‖δU‖²_{L²(ν)})`. -/
theorem DiagonalMonotoneMargin.dirac (h : DiagonalMonotoneMargin ℱ P T G β₁ β₂ c C) :
    ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ θ θ' : TupleH ν n m d,
      interiorPairing (GX G) (GZ G) (GU G ν) (diagDiff C t θ θ' (P2.dirac θ) (P2.dirac θ'))
        ≤ dissipation (GX G) (GZ G) (GU G ν) β₁ β₂
            (diagDiff C t θ θ' (P2.dirac θ) (P2.dirac θ')) - c * channelSq (θ - θ') := by
  filter_upwards [h] with t ht θ θ'
  have key := ht (fun _ => θ) (fun _ => θ') stronglyMeasurable_const stronglyMeasurable_const
    (memLp_const θ) (memLp_const θ')
  simpa only [lawP2_const, integral_const, probReal_univ, one_smul] using key

/-- **A margin needs jump feedback dissipative on the whole of `L²(ν)`**: for almost every
`t ∈ [0, T]`, all `x, y, z` and all `u, u' ∈ L²(ν; ℝᵐ)`, with `θ = (x, y, z, u)` and
`θ' = (x, y, z, u')`,
`⟨h(t, θ, δ_θ) − h(t, θ', δ_θ'), Gᵀ (u − u')⟩_{L²(ν)} ≤ −β₁ ‖Gᵀ (u − u')‖² − c ‖u − u'‖²`. -/
theorem DiagonalMonotoneMargin.jump_dissipative_dirac
    (h : DiagonalMonotoneMargin ℱ P T G β₁ β₂ c C) :
    ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ (x : EuclideanSpace ℝ (Fin n))
      (y : EuclideanSpace ℝ (Fin m)) (z : EuclideanSpace ℝ (Fin m × Fin d))
      (u u' : Lp (EuclideanSpace ℝ (Fin m)) 2 ν),
      inner ℝ (C.h t (x, y, z, u) (P2.dirac ((x, y, z, u) : TupleH ν n m d))
          - C.h t (x, y, z, u') (P2.dirac ((x, y, z, u') : TupleH ν n m d)))
          (ContinuousLinearMap.adjoint (GU G ν) (u - u'))
        ≤ -β₁ * ‖ContinuousLinearMap.adjoint (GU G ν) (u - u')‖ ^ 2 - c * ‖u - u'‖ ^ 2 := by
  filter_upwards [h.dirac] with t ht x y z u u'
  have key := ht ((x, y, z, u) : TupleH ν n m d) (x, y, z, u')
  have hchan : channelSq (((x, y, z, u) : TupleH ν n m d) - (x, y, z, u')) = ‖u - u'‖ ^ 2 := by
    simp [channelSq]
  rw [hchan] at key
  simpa [interiorPairing, dissipation, diagDiff] using key

/-- **Jump feedback through a linear map with a nonzero kernel supplies no margin.** Let the
horizon be `T > 0`, `c > 0`, `β₁ ≥ 0`, and let the jump coefficient depend on `u` only through a
linear map `ℓ` on `L²(ν; ℝᵐ)` along deterministic inputs:
`h(t, (x, y, z, u), δ_{(x,y,z,u)}) = h(t, (x, y, z, u'), δ_{(x,y,z,u')})` whenever
`ℓ u = ℓ u'`. If the kernel of `ℓ` is nonzero, (2.13) fails for every margin `c > 0`. -/
theorem not_diagonalMonotoneMargin_of_factor {F : Type*} [AddCommGroup F] [Module ℝ F]
    (hT : 0 < T) (hc : 0 < c) (hβ₁ : 0 ≤ β₁) (ℓ : Lp (EuclideanSpace ℝ (Fin m)) 2 ν →ₗ[ℝ] F)
    (hker : LinearMap.ker ℓ ≠ ⊥)
    (hfac : ∀ (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin m))
      (z : EuclideanSpace ℝ (Fin m × Fin d)) (u u' : Lp (EuclideanSpace ℝ (Fin m)) 2 ν),
      ℓ u = ℓ u' → C.h t (x, y, z, u) (P2.dirac ((x, y, z, u) : TupleH ν n m d))
        = C.h t (x, y, z, u') (P2.dirac ((x, y, z, u') : TupleH ν n m d))) :
    ¬ DiagonalMonotoneMargin ℱ P T G β₁ β₂ c C := by
  intro hM
  obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).mp hker
  have hℓ : ℓ u = ℓ 0 := by rw [LinearMap.mem_ker.mp hu, map_zero]
  haveI : (ae (volume.restrict (Set.Icc (0 : ℝ) T))).NeBot := by
    refine ae_restrict_neBot.mpr ?_
    rw [Real.volume_Icc, sub_zero]
    exact (ENNReal.ofReal_pos.mpr hT).ne'
  obtain ⟨t, ht⟩ := hM.jump_dissipative_dirac.exists
  have key := ht 0 0 0 u 0
  rw [hfac t 0 0 0 u 0 hℓ, sub_self, inner_zero_left, sub_zero] at key
  have hu2 : 0 < ‖u‖ ^ 2 := pow_pos (norm_pos_iff.mpr hu0) 2
  have hGu := sq_nonneg ‖ContinuousLinearMap.adjoint (GU G ν) u‖
  nlinarith [mul_nonneg hβ₁ hGu]

omit [MeasurableSpace.CountablyGenerated E] in
/-- `L²(ν; ℝᵐ)` has a nonzero element when `ν ≠ 0` is σ-finite and `m > 0`. -/
theorem exists_Lp_ne_zero {m : ℕ} (hν : ν ≠ 0) (hm : 0 < m) :
    ∃ u : Lp (EuclideanSpace ℝ (Fin m)) 2 ν, u ≠ 0 := by
  obtain ⟨i, hi⟩ : ∃ i, ν (spanningSets ν i) ≠ 0 := by
    by_contra hcon
    simp only [ne_eq, not_exists, not_not] at hcon
    apply hν
    rw [← Measure.measure_univ_eq_zero, ← iUnion_spanningSets ν]
    exact measure_iUnion_null hcon
  set v : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 fun _ => 1
  have hv : v ≠ 0 := fun h => by
    have := congrArg (fun w : EuclideanSpace ℝ (Fin m) => w ⟨0, hm⟩) h
    simp [v] at this
  refine ⟨indicatorConstLp 2 (measurableSet_spanningSets ν i)
    (measure_spanningSets_lt_top ν i).ne v, fun h0 => ?_⟩
  have hn := congrArg norm h0
  rw [norm_indicatorConstLp two_ne_zero ENNReal.ofNat_ne_top, norm_zero] at hn
  have hpos : 0 < ν.real (spanningSets ν i) :=
    ENNReal.toReal_pos hi (measure_spanningSets_lt_top ν i).ne
  rcases mul_eq_zero.mp hn with h | h
  · exact hv (norm_eq_zero.mp h)
  · exact (Real.rpow_pos_of_pos hpos _).ne' h

/-- **An additive jump coefficient supplies no margin** (Remark 2.10): if `h(t, θ, μ)` depends on
`t` and the forward state `x` only, `ν ≠ 0` and `m > 0`, then (2.13) fails for every margin
`c > 0`, on a horizon `T > 0` and with `β₁ ≥ 0`. -/
theorem not_diagonalMonotoneMargin_of_additive (hT : 0 < T) (hc : 0 < c) (hβ₁ : 0 ≤ β₁)
    (hν : ν ≠ 0) (hm : 0 < m)
    (hadd : ∀ (t : ℝ) (θ θ' : TupleH ν n m d) (μ μ' : P2 (TupleH ν n m d)), θ.1 = θ'.1 →
      C.h t θ μ = C.h t θ' μ') :
    ¬ DiagonalMonotoneMargin ℱ P T G β₁ β₂ c C := by
  obtain ⟨u, hu⟩ := exists_Lp_ne_zero hν hm
  refine not_diagonalMonotoneMargin_of_factor hT hc hβ₁
    (0 : Lp (EuclideanSpace ℝ (Fin m)) 2 ν →ₗ[ℝ] ℝ) ?_ fun t x y z u u' _ => hadd t _ _ _ _ rfl
  rw [LinearMap.ker_zero, Submodule.ne_bot_iff]
  exact ⟨u, Submodule.mem_top, hu⟩

/-- **Finitely many functionals supply no margin on an infinite-dimensional `L²(ν; ℝᵐ)`**: if
`L²(ν; ℝᵐ)` is infinite dimensional and the jump coefficient depends on `u` only through a linear
map `ℓ` into a finite-dimensional space, along deterministic inputs, then (2.13) fails for every
margin `c > 0`, on a horizon `T > 0` and with `β₁ ≥ 0`. -/
theorem not_diagonalMonotoneMargin_of_not_finiteDimensional {F : Type*} [AddCommGroup F]
    [Module ℝ F] [FiniteDimensional ℝ F]
    (hinf : ¬ FiniteDimensional ℝ (Lp (EuclideanSpace ℝ (Fin m)) 2 ν))
    (hT : 0 < T) (hc : 0 < c) (hβ₁ : 0 ≤ β₁) (ℓ : Lp (EuclideanSpace ℝ (Fin m)) 2 ν →ₗ[ℝ] F)
    (hfac : ∀ (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin m))
      (z : EuclideanSpace ℝ (Fin m × Fin d)) (u u' : Lp (EuclideanSpace ℝ (Fin m)) 2 ν),
      ℓ u = ℓ u' → C.h t (x, y, z, u) (P2.dirac ((x, y, z, u) : TupleH ν n m d))
        = C.h t (x, y, z, u') (P2.dirac ((x, y, z, u') : TupleH ν n m d))) :
    ¬ DiagonalMonotoneMargin ℱ P T G β₁ β₂ c C := by
  refine not_diagonalMonotoneMargin_of_factor hT hc hβ₁ ℓ (fun hbot => hinf ?_) hfac
  exact FiniteDimensional.of_injective ℓ (LinearMap.ker_eq_bot.mp hbot)

end Dirac

/-! ### A single atom -/

section Atom

variable {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E]

/-- On `L²` of the Dirac mass at a point `e₀`, the inner product is that of the values at
`e₀`. -/
theorem inner_Lp_dirac {k : ℕ} (e₀ : E) (u v : Lp (EuclideanSpace ℝ (Fin k)) 2 (Measure.dirac e₀)) :
    inner ℝ u v = inner ℝ (u e₀) (v e₀) := by
  rw [L2.inner_def, integral_dirac]

/-- **One functional is injective on `L²` of a single atom**: `L²(δ_{e₀}; ℝ)` is one
dimensional. -/
theorem exists_injective_functional_dirac (e₀ : E) :
    ∃ ℓ : Lp (EuclideanSpace ℝ (Fin 1)) 2 (Measure.dirac e₀) →ₗ[ℝ] ℝ, Function.Injective ℓ := by
  obtain ⟨w, hw⟩ := exists_Lp_ne_zero (ν := Measure.dirac e₀) (m := 1)
    (Measure.dirac_ne_zero) one_pos
  have e1 : ∀ a b : EuclideanSpace ℝ (Fin 1), inner ℝ a b = a 0 * b 0 := fun a b => by
    simp [PiLp.inner_apply]; ring
  have hw0 : w e₀ 0 ≠ 0 := fun h => hw <| inner_self_eq_zero.mp <| by
    rw [inner_Lp_dirac, e1, h, zero_mul]
  refine ⟨(innerSL ℝ w).toLinearMap, (injective_iff_map_eq_zero _).mpr fun u hu => ?_⟩
  change inner ℝ w u = 0 at hu
  rw [inner_Lp_dirac, e1] at hu
  have hu0 : u e₀ 0 = 0 := (mul_eq_zero.mp hu).resolve_left hw0
  exact inner_self_eq_zero.mp (by rw [inner_Lp_dirac, e1, hu0, zero_mul])

end Atom

end Dissertation.WellPosedness.System
