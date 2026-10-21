/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import MVFBSDEJ.WellPosedness.Assumptions

/-!
# The tuple space of the well-posedness paper

The unknowns of the well-posedness paper take values in the tuple space
`H = ℝⁿ × ℝᵐ × ℝ^{m×d} × L²(ν; ℝᵐ)`: the forward state, the backward value, the Brownian
integrand with the Frobenius norm, and the jump integrand as an element of `L²(ν)`. This file
realises `H` as the product `Tuple` of Euclidean spaces and `L²(ν; ℝᵐ)`, and reads the
coordinate processes of a solution into it:

`tupleAt ν X Y Z U s ω = (X_s(ω), Y_s(ω), Z_s(ω), U_s(ω, ·))`,

with the jump channel the `L²(ν)` class `uLift` of the mark-indexed vector `e ↦ U_s(ω, e)`,
taken to be `0` when that vector is not square integrable.

To carry laws, `L²(ν; F)` is given its Borel σ-algebra. That instance, and the fact `2 ≠ ∞` under
which a countably generated mark space and a σ-finite `ν` make `L²(ν; F)` second countable, are
scoped to `MVFBSDEJ.WellPosedness.System`; with them, for such `E` and `ν`, `H` is a
second-countable Borel space, on which `MVFBSDEJ.Law.lawP2` takes laws.

The paper's `H` carries the Hilbert norm `(|x|² + |y|² + |z|²_F + ‖u‖²)^{1/2}`; the product here
carries the maximum of the four channel norms, which is within a factor `2` of it, so `W₂` on the
laws of `H` agrees with the paper's up to that factor. Since the norm is the maximum,
`‖θ‖² ≤ |x|² + |y|² + |z|²_F + ‖u‖²_{L²(ν)}`, and the sum of the channel norms of Assumption 2.3
satisfies `(|x| + |y| + |z|_F + ‖u‖)² ≤ 4 (|x|² + |y|² + |z|²_F + ‖u‖²)`. At the tuple of the
coordinate processes the right-hand side is at most the sum of the squares of the coordinates,
the `L²(ν)` channel contributing `∑_k ∫_E U_{k,s}(ω, e)² ν(de)`.

## Main definitions

* `TupleH` — the tuple space `H`.
* `lpMeasurableSpace`, `lpBorelSpace` — the Borel σ-algebra on `L²(ν; F)`, a scoped instance.
* `channelSq` — the sum `|x|² + |y|² + |z|²_F + ‖u‖²` of the squared channel norms.
* `uLift` — the `L²(ν)` class of a mark-indexed vector.
* `tupleAt` — the tuple of the coordinate processes at a time.

## Main statements

* `norm_sq_le_channelSq`, `tupleNorm_sq_le` — the two norms of `H` against the channel norms.
* `enorm_uLift_sq_le`, `uLift_sub` — the `L²(ν)` channel.
* `tupleAt_sub` — the difference of two tuples is the tuple of the differences.
* `ofReal_channelSq_tupleAt_le` — the channel norms by the coordinates.
* `ofReal_norm_tupleAt_sub_sq_le`, `ofReal_tupleNorm_tupleAt_sub_sq_le` — the norm comparison for
  the difference of two tuples.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace MVFBSDEJ.WellPosedness.System

/-! ### The scoped measurable structure of `L²(ν; F)` -/

/-- The exponent of `L²` is finite. -/
scoped instance fact_two_ne_top : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩

/-- The Borel σ-algebra on `L²(ν; F)`. -/
noncomputable scoped instance lpMeasurableSpace {E F : Type*} [MeasurableSpace E]
    [NormedAddCommGroup F] {ν : Measure E} : MeasurableSpace (Lp F 2 ν) :=
  borel _

/-- `L²(ν; F)` with its Borel σ-algebra is a Borel space. -/
scoped instance lpBorelSpace {E F : Type*} [MeasurableSpace E] [NormedAddCommGroup F]
    {ν : Measure E} : BorelSpace (Lp F 2 ν) :=
  ⟨rfl⟩

/-! ### The tuple space -/

section Channels

variable {HX HY HZY HUY : Type*} [NormedAddCommGroup HX] [InnerProductSpace ℝ HX]
  [NormedAddCommGroup HY] [InnerProductSpace ℝ HY] [NormedAddCommGroup HZY]
  [InnerProductSpace ℝ HZY] [NormedAddCommGroup HUY] [InnerProductSpace ℝ HUY]

/-- The sum `|x|² + |y|² + |z|² + ‖u‖²` of the squared channel norms of a tuple. -/
noncomputable def channelSq (θ : Tuple HX HY HZY HUY) : ℝ :=
  ‖θ.1‖ ^ 2 + ‖θ.2.1‖ ^ 2 + ‖θ.2.2.1‖ ^ 2 + ‖θ.2.2.2‖ ^ 2

/-- The sum of the squared channel norms is nonnegative. -/
theorem channelSq_nonneg (θ : Tuple HX HY HZY HUY) : 0 ≤ channelSq θ := by
  unfold channelSq
  positivity

/-- The squared norm of a tuple, the maximum of its channel norms, is at most the sum of the
squared channel norms. -/
theorem norm_sq_le_channelSq (θ : Tuple HX HY HZY HUY) : ‖θ‖ ^ 2 ≤ channelSq θ := by
  have hS := channelSq_nonneg θ
  have hle : ‖θ‖ ≤ Real.sqrt (channelSq θ) := by
    have key : ∀ t : ℝ, t ^ 2 ≤ channelSq θ → t ≤ Real.sqrt (channelSq θ) := fun t ht =>
      (le_abs_self t).trans (Real.abs_le_sqrt ht)
    have h1 := sq_nonneg ‖θ.1‖
    have h2 := sq_nonneg ‖θ.2.1‖
    have h3 := sq_nonneg ‖θ.2.2.1‖
    have h4 := sq_nonneg ‖θ.2.2.2‖
    simp only [Prod.norm_def]
    refine max_le (key _ ?_) (max_le (key _ ?_) (max_le (key _ ?_) (key _ ?_))) <;>
      unfold channelSq <;> linarith
  calc ‖θ‖ ^ 2 ≤ Real.sqrt (channelSq θ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
    _ = channelSq θ := Real.sq_sqrt hS

/-- The square of the sum of the channel norms of Assumption 2.3 is at most four times the sum
of the squared channel norms. -/
theorem tupleNorm_sq_le (θ : Tuple HX HY HZY HUY) : tupleNorm θ ^ 2 ≤ 4 * channelSq θ := by
  unfold tupleNorm channelSq
  nlinarith [sq_nonneg (‖θ.1‖ - ‖θ.2.1‖), sq_nonneg (‖θ.1‖ - ‖θ.2.2.1‖),
    sq_nonneg (‖θ.1‖ - ‖θ.2.2.2‖), sq_nonneg (‖θ.2.1‖ - ‖θ.2.2.1‖),
    sq_nonneg (‖θ.2.1‖ - ‖θ.2.2.2‖), sq_nonneg (‖θ.2.2.1‖ - ‖θ.2.2.2‖)]

/-- The sum of the squared channel norms, as an extended real, is the sum of the squared
extended channel norms. -/
theorem ofReal_channelSq (θ : Tuple HX HY HZY HUY) :
    ENNReal.ofReal (channelSq θ)
      = ‖θ.1‖ₑ ^ 2 + ‖θ.2.1‖ₑ ^ 2 + ‖θ.2.2.1‖ₑ ^ 2 + ‖θ.2.2.2‖ₑ ^ 2 := by
  unfold channelSq
  rw [ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_pow (norm_nonneg _),
    ENNReal.ofReal_pow (norm_nonneg _), ENNReal.ofReal_pow (norm_nonneg _),
    ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, ofReal_norm, ofReal_norm, ofReal_norm]

end Channels

variable {E : Type*} [MeasurableSpace E]

/-- The tuple space `H = ℝⁿ × ℝᵐ × ℝ^{m×d} × L²(ν; ℝᵐ)` of the well-posedness paper, with the
Frobenius norm on the `m × d` channel and the maximum of the channel norms on `H`. -/
abbrev TupleH (ν : Measure E) (n m d : ℕ) : Type _ :=
  Tuple (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m × Fin d))
    (Lp (EuclideanSpace ℝ (Fin m)) 2 ν)

/-! ### Euclidean channels -/

section Euclidean

variable {ι : Type*} [Fintype ι]

/-- The squared Euclidean norm of a coordinate vector is the sum of the squares of its
coordinates. -/
theorem norm_toLp_sq (v : ι → ℝ) :
    ‖(WithLp.toLp 2 v : EuclideanSpace ℝ ι)‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]

/-- The squared extended Euclidean norm of a coordinate vector is the sum of the squares of its
coordinates. -/
theorem enorm_toLp_sq (v : ι → ℝ) :
    ‖(WithLp.toLp 2 v : EuclideanSpace ℝ ι)‖ₑ ^ 2 = ∑ i, (‖v i‖₊ : ℝ≥0∞) ^ 2 := by
  rw [enorm_eq_nnnorm, EuclideanSpace.nnnorm_eq, ← ENNReal.coe_pow, NNReal.sq_sqrt]
  push_cast
  simp

end Euclidean

/-! ### The `L²(ν)` channel -/

section Marks

variable {ν : Measure E} {ι : Type*} [Fintype ι]

/-- The square of the `L²` seminorm is the lower integral of the squared norm. -/
theorem eLpNorm_two_sq {F : Type*} [NormedAddCommGroup F] (f : E → F) :
    eLpNorm f 2 ν ^ 2 = ∫⁻ e, ‖f e‖ₑ ^ 2 ∂ν := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := ν) (p := 2) two_ne_zero
  simpa only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_two] using h

/-- A mark-indexed vector with square-integrable coordinates is square integrable as a
Euclidean vector. -/
theorem memLp_toLp_of_forall {u : E → ι → ℝ} (hu : ∀ k, MemLp (fun e => u e k) 2 ν) :
    MemLp (fun e => (WithLp.toLp 2 (u e) : EuclideanSpace ℝ ι)) 2 ν := by
  have hm : AEMeasurable u ν :=
    aemeasurable_pi_iff.mpr fun k => (hu k).aestronglyMeasurable.aemeasurable
  have hae : AEStronglyMeasurable (fun e => (WithLp.toLp 2 (u e) : EuclideanSpace ℝ ι)) ν :=
    ((WithLp.measurable_toLp 2 (ι → ℝ)).comp_aemeasurable hm).aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq_norm hae).mpr ?_
  refine (integrable_finsetSum Finset.univ fun k _ =>
    (hu k).integrable_norm_pow two_ne_zero).congr (ae_of_all _ fun e => ?_)
  exact (norm_toLp_sq (u e)).symm

/-- The `L²(ν)` class of a mark-indexed vector `u : E → ℝ^ι`, and `0` when `u` is not square
integrable. -/
noncomputable def uLift (ν : Measure E) (u : E → ι → ℝ) : Lp (EuclideanSpace ℝ ι) 2 ν := by
  classical
  exact if h : MemLp (fun e => (WithLp.toLp 2 (u e) : EuclideanSpace ℝ ι)) 2 ν then h.toLp _
    else 0

/-- For a square-integrable vector, `uLift` is its `L²(ν)` class. -/
theorem uLift_of_memLp {u : E → ι → ℝ}
    (h : MemLp (fun e => (WithLp.toLp 2 (u e) : EuclideanSpace ℝ ι)) 2 ν) :
    uLift ν u = h.toLp _ := by
  unfold uLift
  rw [dif_pos h]

/-- **The `L²(ν)` channel by the coordinates**: `‖uLift u‖² ≤ ∑_k ∫_E u_k(e)² ν(de)`, with
equality when `u` is square integrable. -/
theorem enorm_uLift_sq_le (u : E → ι → ℝ) :
    ‖uLift ν u‖ₑ ^ 2 ≤ ∑ k, ∫⁻ e, (‖u e k‖₊ : ℝ≥0∞) ^ 2 ∂ν := by
  by_cases h : MemLp (fun e => (WithLp.toLp 2 (u e) : EuclideanSpace ℝ ι)) 2 ν
  · rw [uLift_of_memLp h, Lp.enorm_toLp, eLpNorm_two_sq]
    simp only [enorm_toLp_sq]
    rw [lintegral_finsetSum' _ fun k _ => ?_]
    have hk : AEStronglyMeasurable (fun e => u e k) ν :=
      (EuclideanSpace.proj k : EuclideanSpace ℝ ι →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable
        h.aestronglyMeasurable
    exact (hk.aemeasurable.nnnorm.coe_nnreal_ennreal).pow_const 2
  · unfold uLift
    rw [dif_neg h, enorm_zero, zero_pow two_ne_zero]
    exact zero_le

/-- **The `L²(ν)` class of a difference** of two vectors with square-integrable coordinates is the
difference of their classes. -/
theorem uLift_sub {u u' : E → ι → ℝ} (hu : ∀ k, MemLp (fun e => u e k) 2 ν)
    (hu' : ∀ k, MemLp (fun e => u' e k) 2 ν) :
    uLift ν u - uLift ν u' = uLift ν fun e k => u e k - u' e k := by
  have h := memLp_toLp_of_forall hu
  have h' := memLp_toLp_of_forall hu'
  have h'' : MemLp (fun e => (WithLp.toLp 2 fun k => u e k - u' e k : EuclideanSpace ℝ ι)) 2 ν :=
    memLp_toLp_of_forall (u := fun e k => u e k - u' e k) fun k => (hu k).sub (hu' k)
  rw [uLift_of_memLp h, uLift_of_memLp h', uLift_of_memLp h'', ← MemLp.toLp_sub]
  refine (MemLp.toLp_eq_toLp_iff _ _).mpr (ae_of_all _ fun e => ?_)
  simp only [Pi.sub_apply, ← WithLp.toLp_sub]
  rfl

end Marks

/-! ### The tuple of the coordinate processes -/

section Processes

variable {Ω : Type*} {ν : Measure E} {n m d : ℕ}
  {X X' : Fin n → ℝ → Ω → ℝ} {Y Y' : Fin m → ℝ → Ω → ℝ}
  {Z Z' : Fin m → ℝ → Ω → Fin d → ℝ} {U U' : Fin m → ℝ → Ω → E → ℝ}

/-- The tuple `(X_s(ω), Y_s(ω), Z_s(ω), U_s(ω, ·)) ∈ H` of the coordinate processes at time
`s`, with the rows `Z_{k,s}(ω) ∈ ℝᵈ` forming the `m × d` channel and the jump channel the
`L²(ν)` class of `e ↦ (U_{k,s}(ω, e))_k`. -/
noncomputable def tupleAt (ν : Measure E) (X : Fin n → ℝ → Ω → ℝ) (Y : Fin m → ℝ → Ω → ℝ)
    (Z : Fin m → ℝ → Ω → Fin d → ℝ) (U : Fin m → ℝ → Ω → E → ℝ) (s : ℝ) (ω : Ω) :
    TupleH ν n m d :=
  (WithLp.toLp 2 fun i => X i s ω, WithLp.toLp 2 fun k => Y k s ω,
    WithLp.toLp 2 fun p : Fin m × Fin d => Z p.1 s ω p.2, uLift ν fun e k => U k s ω e)

/-- **The difference of two tuples is the tuple of the differences**, when both jump channels are
square integrable. -/
theorem tupleAt_sub {s : ℝ} {ω : Ω} (hU : ∀ k, MemLp (fun e => U k s ω e) 2 ν)
    (hU' : ∀ k, MemLp (fun e => U' k s ω e) 2 ν) :
    tupleAt ν X Y Z U s ω - tupleAt ν X' Y' Z' U' s ω
      = tupleAt ν (fun i t ω => X i t ω - X' i t ω) (fun k t ω => Y k t ω - Y' k t ω)
          (fun k t ω j => Z k t ω j - Z' k t ω j) (fun k t ω e => U k t ω e - U' k t ω e) s ω := by
  simp only [tupleAt, Prod.mk_sub_mk, ← WithLp.toLp_sub,
    uLift_sub (u := fun e k => U k s ω e) (u' := fun e k => U' k s ω e) hU hU']
  rfl

/-- **The channel norms of the tuple by the coordinates**:
`|X_s|² + |Y_s|² + |Z_s|²_F + ‖U_s‖²_{L²(ν)}` is at most
`∑_i X_{i,s}² + ∑_k Y_{k,s}² + ∑_{k,j} Z_{kj,s}² + ∑_k ∫_E U_{k,s}(e)² ν(de)`. -/
theorem ofReal_channelSq_tupleAt_le (s : ℝ) (ω : Ω) :
    ENNReal.ofReal (channelSq (tupleAt ν X Y Z U s ω))
      ≤ ∑ i, (‖X i s ω‖₊ : ℝ≥0∞) ^ 2 + ∑ k, (‖Y k s ω‖₊ : ℝ≥0∞) ^ 2
        + ∑ k, ∑ j, (‖Z k s ω j‖₊ : ℝ≥0∞) ^ 2
        + ∑ k, ∫⁻ e, (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν := by
  rw [ofReal_channelSq]
  simp only [tupleAt, enorm_toLp_sq]
  rw [Fintype.sum_prod_type]
  gcongr
  exact enorm_uLift_sq_le _

/-- **The norm comparison for a difference of tuples**: when both jump channels are square
integrable, `‖Θ_s(ω) − Θ'_s(ω)‖²` is at most the sum of the squares of the coordinate
differences. -/
theorem ofReal_norm_tupleAt_sub_sq_le {s : ℝ} {ω : Ω}
    (hU : ∀ k, MemLp (fun e => U k s ω e) 2 ν) (hU' : ∀ k, MemLp (fun e => U' k s ω e) 2 ν) :
    ENNReal.ofReal (‖tupleAt ν X Y Z U s ω - tupleAt ν X' Y' Z' U' s ω‖ ^ 2)
      ≤ ∑ i, (‖X i s ω - X' i s ω‖₊ : ℝ≥0∞) ^ 2 + ∑ k, (‖Y k s ω - Y' k s ω‖₊ : ℝ≥0∞) ^ 2
        + ∑ k, ∑ j, (‖Z k s ω j - Z' k s ω j‖₊ : ℝ≥0∞) ^ 2
        + ∑ k, ∫⁻ e, (‖U k s ω e - U' k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν := by
  rw [tupleAt_sub hU hU']
  exact (ENNReal.ofReal_le_ofReal (norm_sq_le_channelSq _)).trans
    (ofReal_channelSq_tupleAt_le s ω)

/-- **The norm comparison of Assumption 2.3 for a difference of tuples**: when both jump
channels are square integrable, the square of the sum of the channel norms of
`Θ_s(ω) − Θ'_s(ω)` is at most four times the sum of the squares of the coordinate
differences. -/
theorem ofReal_tupleNorm_tupleAt_sub_sq_le {s : ℝ} {ω : Ω}
    (hU : ∀ k, MemLp (fun e => U k s ω e) 2 ν) (hU' : ∀ k, MemLp (fun e => U' k s ω e) 2 ν) :
    ENNReal.ofReal (tupleNorm (tupleAt ν X Y Z U s ω - tupleAt ν X' Y' Z' U' s ω) ^ 2)
      ≤ 4 * (∑ i, (‖X i s ω - X' i s ω‖₊ : ℝ≥0∞) ^ 2 + ∑ k, (‖Y k s ω - Y' k s ω‖₊ : ℝ≥0∞) ^ 2
        + ∑ k, ∑ j, (‖Z k s ω j - Z' k s ω j‖₊ : ℝ≥0∞) ^ 2
        + ∑ k, ∫⁻ e, (‖U k s ω e - U' k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν) := by
  rw [tupleAt_sub hU hU']
  calc ENNReal.ofReal (tupleNorm _ ^ 2) ≤ ENNReal.ofReal (4 * channelSq _) :=
        ENNReal.ofReal_le_ofReal (tupleNorm_sq_le _)
    _ = 4 * ENNReal.ofReal (channelSq _) := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    _ ≤ _ := by
        gcongr
        exact ofReal_channelSq_tupleAt_le s ω

end Processes

end MVFBSDEJ.WellPosedness.System
