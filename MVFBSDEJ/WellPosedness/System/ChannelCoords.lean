/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Stability.LipschitzRate
import MVFBSDEJ.WellPosedness.System.Solves

/-!
# The channel differences of two tuples in coordinates

Assumptions 2.3 and 2.5 are stated on `H` and `L²(ν)` in the Euclidean, Frobenius and `L²(ν)` norms
and inner products, while the difference system `MVFBSDEJ.WellPosedness.Stability.PairDiff` is
written in the coordinates of the unknowns and of the coefficient processes. This file identifies
the two at a time `s ∈ [0, T]`, for the tuples `Θ_s = tupleAt ν X Y Z U s`,
`Θ'_s = tupleAt ν X' Y' Z' U' s` and their laws `μ_s, μ'_s`:

* the coefficient differences `b(s, Θ_s, μ_s) − b(s, Θ'_s, μ'_s)`, and likewise for `σ` and `f`,
  are the vectors of the differences of the coefficient processes, and the terminal difference
  `g(X_T, Law X_T) − g(X'_T, Law X'_T)` is the vector of the differences of the terminal values;
* when `γ, γ'` represent `h(s, Θ_s, ·, μ_s)` and `h(s, Θ'_s, ·, μ'_s)` in `L²(ν)`, the
  difference of the jump coefficients is represented by `e ↦ γ_s(e) − γ'_s(e)`;
* the channel differences of the tuples are the vectors of the coordinate differences, the jump
  channel being the `L²(ν)` class of `e ↦ U_s(e) − U'_s(e)` when both are square integrable.

On the Euclidean channels, norms and inner products become sums of squares and dot products;
on `ℝ^{n×d}` the inner product is the sum over the columns `j` of the dot products of the
`j`-th columns, and on `L²(ν)` the squared norm and the inner product are integrals over the marks
of the pointwise ones.

## Main statements

* `driftProc_of_mem` and its companions — the coefficient processes on `[0, T]`.
* `b_sub_eq_toLp`, `σ_sub_eq_toLp`, `f_sub_eq_toLp`, `coeFn_h_sub`, `g_sub_eq_toLp` — the
  coefficient differences along two tuples in coordinates.
* `tupleAt_fst_sub`, `tupleAt_Y_sub`, `tupleAt_Z_sub`, `tupleAt_U_sub` — the channel differences
  of two tuples.
* `inner_toLp_eq_dotProduct`, `dotProduct_prod`, `esq_eq_enorm_sq`, `sum_esq_eq_enorm_sq`,
  `measurable_toLp_of_forall`, `adjoint_GZ_toLp` — the Euclidean channels.
* `sum_lintegral_le_enorm_sq`, `coeFn_uLift`, `norm_sq_eq_integral_dotProduct`,
  `inner_eq_integral_dotProduct`, `coeFn_adjoint_GU_uLift` — the `L²(ν)` channel.
-/

open MeasureTheory Filter Matrix WithLp MVFBSDEJ.Law
open scoped NNReal ENNReal

namespace MVFBSDEJ.WellPosedness.System

open MVFBSDEJ.WellPosedness.Stability

/-! ### Euclidean channels -/

section Euclidean

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The inner product of two coordinate vectors is their dot product. -/
theorem inner_toLp_eq_dotProduct (x y : ι → ℝ) :
    inner ℝ (toLp 2 x : EuclideanSpace ℝ ι) (toLp 2 y) = x ⬝ᵥ y := by
  rw [EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct_comm]

/-- The dot product on `ℝ^{ι × κ}` is the sum over `j ∈ κ` of the dot products of the `j`-th
columns. -/
theorem dotProduct_prod (a b : ι × κ → ℝ) :
    a ⬝ᵥ b = ∑ j, (fun i => a (i, j)) ⬝ᵥ (fun i => b (i, j)) := by
  simp only [dotProduct, Fintype.sum_prod_type]
  exact Finset.sum_comm

/-- `esq` of a coordinate vector is its squared extended Euclidean norm. -/
theorem esq_eq_enorm_sq (x : ι → ℝ) : esq x = ‖(toLp 2 x : EuclideanSpace ℝ ι)‖ₑ ^ 2 :=
  (enorm_toLp_sq x).symm

/-- The sum over the rows of `esq` of the rows of a `ι × κ` array is its squared extended
Frobenius norm. -/
theorem sum_esq_eq_enorm_sq (a : ι → κ → ℝ) :
    ∑ i, esq (a i) = ‖(toLp 2 fun p : ι × κ => a p.1 p.2 : EuclideanSpace ℝ (ι × κ))‖ₑ ^ 2 := by
  rw [enorm_toLp_sq, Fintype.sum_prod_type]
  rfl

omit [Fintype ι] in
/-- A vector of measurable coordinates is measurable. -/
theorem measurable_toLp_of_forall {Ω : Type*} {mΩ : MeasurableSpace Ω} {x : ι → Ω → ℝ}
    (hx : ∀ i, Measurable (x i)) :
    Measurable fun ω => (toLp 2 fun i => x i ω : EuclideanSpace ℝ ι) :=
  (measurable_toLp 2 _).comp (measurable_pi_iff.mpr hx)

variable {n m d : ℕ} (G : Matrix (Fin m) (Fin n) ℝ)

/-- The adjoint of `GZ` in coordinates: column `j` of `Gᵀ z` is `Gᵀ` applied to column `j` of
`z`. -/
theorem adjoint_GZ_toLp (z : Fin m × Fin d → ℝ) :
    ContinuousLinearMap.adjoint (GZ G) (toLp 2 z)
      = toLp 2 fun p : Fin n × Fin d => (Gᵀ *ᵥ fun k => z (k, p.2)) p.1 :=
  (toLp_ofLp 2 _).symm.trans
    (congrArg (toLp 2) (funext fun p => adjoint_GZ_toLp_apply G z p.1 p.2))

end Euclidean

/-! ### The `L²(ν)` channel -/

section Marks

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} {ι : Type*} [Fintype ι]

/-- **The `L²(ν)` channel by a representative**: if `e ↦ (v_i(e))_i` represents `u ∈ L²(ν; ℝ^ι)`,
then `∑_i ∫_E v_i(e)² ν(de) ≤ ‖u‖²`. -/
theorem sum_lintegral_le_enorm_sq {v : ι → E → ℝ} {u : Lp (EuclideanSpace ℝ ι) 2 ν}
    (h : (fun e => (toLp 2 fun i => v i e : EuclideanSpace ℝ ι)) =ᵐ[ν] u) :
    ∑ i, ∫⁻ e, (‖v i e‖₊ : ℝ≥0∞) ^ 2 ∂ν ≤ ‖u‖ₑ ^ 2 := by
  have hc : (fun e => ‖(toLp 2 fun i => v i e : EuclideanSpace ℝ ι)‖ₑ ^ 2)
      =ᵐ[ν] fun e => ‖u e‖ₑ ^ 2 := by
    filter_upwards [h] with e he
    rw [he]
  rw [Lp.enorm_def, eLpNorm_two_sq, ← lintegral_congr_ae hc]
  simp only [enorm_toLp_sq]
  exact sum_lintegral_le _ _

/-- The `L²(ν)` class of a vector with square-integrable coordinates is represented by it. -/
theorem coeFn_uLift {u : E → ι → ℝ} (hu : ∀ k, MemLp (fun e => u e k) 2 ν) :
    uLift ν u =ᵐ[ν] fun e => (toLp 2 (u e) : EuclideanSpace ℝ ι) := by
  rw [uLift_of_memLp (memLp_toLp_of_forall hu)]
  exact MemLp.coeFn_toLp _

/-- The squared norm of an element of `L²(ν; ℝ^ι)` represented by `e ↦ w(e)` is
`∫_E w(e) ⬝ᵥ w(e) ν(de)`. -/
theorem norm_sq_eq_integral_dotProduct {u : Lp (EuclideanSpace ℝ ι) 2 ν} {w : E → ι → ℝ}
    (h : u =ᵐ[ν] fun e => (toLp 2 (w e) : EuclideanSpace ℝ ι)) :
    ‖u‖ ^ 2 = ∫ e, w e ⬝ᵥ w e ∂ν := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [h] with e he
  rw [he, inner_toLp_eq_dotProduct]

/-- The inner product of two elements of `L²(ν; ℝ^ι)` represented by `e ↦ a(e)` and
`e ↦ b(e)` is `∫_E a(e) ⬝ᵥ b(e) ν(de)`. -/
theorem inner_eq_integral_dotProduct {u v : Lp (EuclideanSpace ℝ ι) 2 ν} {a b : E → ι → ℝ}
    (hu : u =ᵐ[ν] fun e => (toLp 2 (a e) : EuclideanSpace ℝ ι))
    (hv : v =ᵐ[ν] fun e => (toLp 2 (b e) : EuclideanSpace ℝ ι)) :
    inner ℝ u v = ∫ e, a e ⬝ᵥ b e ∂ν := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hu, hv] with e hue hve
  rw [hue, hve, inner_toLp_eq_dotProduct]

variable {n m : ℕ} (G : Matrix (Fin m) (Fin n) ℝ)

/-- The adjoint of `GU` on the `L²(ν)` class of a vector with square-integrable coordinates is
represented by `e ↦ Gᵀ u(e)`. -/
theorem coeFn_adjoint_GU_uLift {u : E → Fin m → ℝ} (hu : ∀ k, MemLp (fun e => u e k) 2 ν) :
    ContinuousLinearMap.adjoint (GU G ν) (uLift ν u)
      =ᵐ[ν] fun e => (toLp 2 (Gᵀ *ᵥ u e) : EuclideanSpace ℝ (Fin n)) := by
  filter_upwards [coeFn_adjoint_GU G ν (uLift ν u), coeFn_uLift hu] with e h₁ h₂
  rw [h₁, h₂, GX_toLp]

end Marks

/-! ### The coefficient processes on the horizon -/

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}
  {P : Measure Ω} [IsProbabilityMeasure P] {T : ℝ} {C : Coeffs ν n m d}
  {X X' : Fin n → ℝ → Ω → ℝ} {Y Y' : Fin m → ℝ → Ω → ℝ}
  {Z Z' : Fin m → ℝ → Ω → Fin d → ℝ} {U U' : Fin m → ℝ → Ω → E → ℝ}
  {γ γ' : Fin n → ℝ → Ω → E → ℝ} {s : ℝ} {ω : Ω}

/-- On the horizon the drift process is the coordinate of the drift along the tuple. -/
theorem driftProc_of_mem (hs : s ∈ Set.Icc (0 : ℝ) T) (i : Fin n) :
    driftProc P T C X Y Z U i ω s
      = C.b s (tupleAt ν X Y Z U s ω) (lawP2 P (tupleAt ν X Y Z U s)) i :=
  Set.indicator_of_mem hs _

/-- On the horizon the diffusion process is the entry of the diffusion along the tuple. -/
theorem diffusionProc_of_mem (hs : s ∈ Set.Icc (0 : ℝ) T) (i : Fin n) (j : Fin d) :
    diffusionProc P T C X Y Z U i s ω j
      = C.σ s (tupleAt ν X Y Z U s ω) (lawP2 P (tupleAt ν X Y Z U s)) (i, j) :=
  Set.indicator_of_mem hs _

/-- On the horizon the driver process is the coordinate of the driver along the tuple. -/
theorem driverProc_of_mem (hs : s ∈ Set.Icc (0 : ℝ) T) (k : Fin m) :
    driverProc P T C X Y Z U k ω s
      = C.f s (tupleAt ν X Y Z U s ω) (lawP2 P (tupleAt ν X Y Z U s)) k :=
  Set.indicator_of_mem hs _

omit [MeasurableSpace Ω] [MeasurableSpace E] [SigmaFinite ν]
  [MeasurableSpace.CountablyGenerated E] in
/-- On the horizon the jump process is the representative. -/
theorem jumpProc_of_mem (hs : s ∈ Set.Icc (0 : ℝ) T) (i : Fin n) (e : E) :
    jumpProc T γ i s ω e = γ i s ω e :=
  Set.indicator_of_mem hs _

/-! ### The coefficient differences along two tuples -/

/-- **The drift difference along two tuples** is the vector of the differences of the drift
processes. -/
theorem b_sub_eq_toLp (hs : s ∈ Set.Icc (0 : ℝ) T) :
    C.b s (tupleAt ν X Y Z U s ω) (lawP2 P (tupleAt ν X Y Z U s))
        - C.b s (tupleAt ν X' Y' Z' U' s ω) (lawP2 P (tupleAt ν X' Y' Z' U' s))
      = toLp 2 fun i => driftProc P T C X Y Z U i ω s - driftProc P T C X' Y' Z' U' i ω s :=
  (toLp_ofLp 2 _).symm.trans (congrArg (toLp 2) (funext fun i => by
    rw [driftProc_of_mem hs, driftProc_of_mem hs]
    exact PiLp.sub_apply _ _ _ i))

/-- **The diffusion difference along two tuples** is the array of the differences of the
diffusion processes. -/
theorem σ_sub_eq_toLp (hs : s ∈ Set.Icc (0 : ℝ) T) :
    C.σ s (tupleAt ν X Y Z U s ω) (lawP2 P (tupleAt ν X Y Z U s))
        - C.σ s (tupleAt ν X' Y' Z' U' s ω) (lawP2 P (tupleAt ν X' Y' Z' U' s))
      = toLp 2 fun p : Fin n × Fin d =>
          diffusionProc P T C X Y Z U p.1 s ω p.2 - diffusionProc P T C X' Y' Z' U' p.1 s ω p.2 :=
  (toLp_ofLp 2 _).symm.trans (congrArg (toLp 2) (funext fun p => by
    rw [diffusionProc_of_mem hs, diffusionProc_of_mem hs]
    exact PiLp.sub_apply _ _ _ p))

/-- **The driver difference along two tuples** is the vector of the differences of the driver
processes. -/
theorem f_sub_eq_toLp (hs : s ∈ Set.Icc (0 : ℝ) T) :
    C.f s (tupleAt ν X Y Z U s ω) (lawP2 P (tupleAt ν X Y Z U s))
        - C.f s (tupleAt ν X' Y' Z' U' s ω) (lawP2 P (tupleAt ν X' Y' Z' U' s))
      = toLp 2 fun k => driverProc P T C X Y Z U k ω s - driverProc P T C X' Y' Z' U' k ω s :=
  (toLp_ofLp 2 _).symm.trans (congrArg (toLp 2) (funext fun k => by
    rw [driverProc_of_mem hs, driverProc_of_mem hs]
    exact PiLp.sub_apply _ _ _ k))

omit [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
/-- **The terminal difference along two solutions** is the vector of the differences of the
terminal values. -/
theorem g_sub_eq_toLp :
    C.g (toLp 2 fun i => X i T ω) (lawP2 P fun ω' => toLp 2 fun i => X i T ω')
        - C.g (toLp 2 fun i => X' i T ω) (lawP2 P fun ω' => toLp 2 fun i => X' i T ω')
      = toLp 2 fun k => terminalVal P T C X k ω - terminalVal P T C X' k ω :=
  (toLp_ofLp 2 _).symm.trans (congrArg (toLp 2) (funext fun k => PiLp.sub_apply _ _ _ k))

/-- **The jump-coefficient difference along two tuples** is represented in `L²(ν)` by the
difference of the jump processes, when `γ` and `γ'` represent the two jump coefficients. -/
theorem coeFn_h_sub (hs : s ∈ Set.Icc (0 : ℝ) T)
    (hγ : (fun e => (toLp 2 fun i => γ i s ω e : EuclideanSpace ℝ (Fin n)))
      =ᵐ[ν] C.h s (tupleAt ν X Y Z U s ω) (lawP2 P (tupleAt ν X Y Z U s)))
    (hγ' : (fun e => (toLp 2 fun i => γ' i s ω e : EuclideanSpace ℝ (Fin n)))
      =ᵐ[ν] C.h s (tupleAt ν X' Y' Z' U' s ω) (lawP2 P (tupleAt ν X' Y' Z' U' s))) :
    (C.h s (tupleAt ν X Y Z U s ω) (lawP2 P (tupleAt ν X Y Z U s))
        - C.h s (tupleAt ν X' Y' Z' U' s ω) (lawP2 P (tupleAt ν X' Y' Z' U' s)) :
          Lp (EuclideanSpace ℝ (Fin n)) 2 ν)
      =ᵐ[ν] fun e => toLp 2 fun i => jumpProc T γ i s ω e - jumpProc T γ' i s ω e := by
  filter_upwards [Lp.coeFn_sub (C.h s (tupleAt ν X Y Z U s ω) (lawP2 P (tupleAt ν X Y Z U s)))
    (C.h s (tupleAt ν X' Y' Z' U' s ω) (lawP2 P (tupleAt ν X' Y' Z' U' s))), hγ, hγ']
    with e h₀ h₁ h₂
  rw [h₀, Pi.sub_apply, ← h₁, ← h₂, ← toLp_sub]
  simp only [jumpProc_of_mem hs]
  rfl

/-! ### The channel differences of two tuples -/

omit [MeasurableSpace Ω] [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
/-- The forward channel difference of two tuples. -/
theorem tupleAt_fst_sub :
    (tupleAt ν X Y Z U s ω).1 - (tupleAt ν X' Y' Z' U' s ω).1
      = toLp 2 fun i => X i s ω - X' i s ω :=
  (toLp_sub 2 _ _).symm

omit [MeasurableSpace Ω] [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
/-- The backward channel difference of two tuples. -/
theorem tupleAt_Y_sub :
    (tupleAt ν X Y Z U s ω).2.1 - (tupleAt ν X' Y' Z' U' s ω).2.1
      = toLp 2 fun k => Y k s ω - Y' k s ω :=
  (toLp_sub 2 _ _).symm

omit [MeasurableSpace Ω] [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
/-- The Brownian channel difference of two tuples. -/
theorem tupleAt_Z_sub :
    (tupleAt ν X Y Z U s ω).2.2.1 - (tupleAt ν X' Y' Z' U' s ω).2.2.1
      = toLp 2 fun p : Fin m × Fin d => Z p.1 s ω p.2 - Z' p.1 s ω p.2 :=
  (toLp_sub 2 _ _).symm

omit [MeasurableSpace Ω] [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
/-- The jump channel difference of two tuples, when both jump channels are square
integrable. -/
theorem tupleAt_U_sub (hU : ∀ k, MemLp (fun e => U k s ω e) 2 ν)
    (hU' : ∀ k, MemLp (fun e => U' k s ω e) 2 ν) :
    (tupleAt ν X Y Z U s ω).2.2.2 - (tupleAt ν X' Y' Z' U' s ω).2.2.2
      = uLift ν fun e k => U k s ω e - U' k s ω e :=
  uLift_sub (u := fun e k => U k s ω e) (u' := fun e k => U' k s ω e) hU hU'

end MVFBSDEJ.WellPosedness.System
