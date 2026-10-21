/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.System.Coefficients
import Dissertation.WellPosedness.System.HilbertW2Space

/-!
# Example 5.2: the tuple space at zero jump intensity

Example 5.2 of the well-posedness paper removes the Poisson channel and deletes the
`U`-coordinate, reducing the tuple space to `ℝⁿ × ℝᵐ × ℝ^{m×d}`. Inside the paper's own model
this is the zero intensity `ν = 0`, which §2 admits since the zero measure is σ-finite: every
function on the mark space vanishes `ν`-almost everywhere, so `L²(0; F)` has a single point, and

`H = ℝⁿ × ℝᵐ × ℝ^{m×d} × L²(0; ℝᵐ)`

is the reduced space with a trivial fourth channel.

The reduced space `ReducedTuple n m d` is `ℝⁿ × ℝᵐ × ℝ^{m×d}` with its Hilbert norm
`(|x|² + |y|² + |z|²_F)^{1/2}`, realised as an iterated `L²` product, so that `W₂` on its laws of
finite second moment is `w2P`. Dropping the jump channel, `projB`, and inserting a zero one,
`liftB`, identify `H` at `ν = 0` with the reduced space. The image `projP2` of a law of finite
second moment on `H` under `projB` has `W₂` distances at most the Hilbert-norm `W₂` on `P₂(H)`,
`w2H`, with equality at `ν = 0`.

## Main definitions

* `ReducedTuple` — the reduced tuple space `ℝⁿ × ℝᵐ × ℝ^{m×d}` with its Hilbert norm.
* `projB`, `liftB` — dropping the jump channel and inserting a zero one.
* `projP2` — the image of a law under `projB`.

## Main statements

* `lp_zero_subsingleton` — `L^p(0; F)` has a single point.
* `liftB_projB` — at `ν = 0`, inserting a zero jump channel after dropping it is the identity.
* `w2P_projP2_le` — dropping the jump channel does not increase `W₂`.
* `w2P_projP2` — at `ν = 0` the map of laws `projP2` preserves `W₂`.
-/

open MeasureTheory Filter Dissertation.Law
open scoped ENNReal Matrix

namespace Dissertation.WellPosedness.System

variable {E : Type*} [MeasurableSpace E] {n m d : ℕ}

/-! ### The zero intensity -/

/-- **`L^p(0; F)` has a single point**: every function vanishes almost everywhere for the zero
measure. -/
instance lp_zero_subsingleton {F : Type*} [NormedAddCommGroup F] {p : ℝ≥0∞} :
    Subsingleton (Lp F p (0 : Measure E)) :=
  ⟨fun _ _ => Lp.ext_iff.2 (by simp [Filter.EventuallyEq])⟩

/-! ### The reduced tuple space -/

variable (n m d) in
/-- The reduced tuple space `ℝⁿ × ℝᵐ × ℝ^{m×d}` of Example 5.2 with the Hilbert norm
`(|x|² + |y|² + |z|²_F)^{1/2}`: a point `w` has forward state `w.fst`, backward value
`w.snd.fst` and Brownian integrand `w.snd.snd`. -/
abbrev ReducedTuple : Type :=
  WithLp 2 (EuclideanSpace ℝ (Fin n) ×
    WithLp 2 (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m × Fin d)))

/-- The squared norm of a reduced tuple is `|x|² + |y|² + |z|²_F`. -/
theorem norm_reducedTuple_sq (w : ReducedTuple n m d) :
    ‖w‖ ^ 2 = ‖w.fst‖ ^ 2 + ‖w.snd.fst‖ ^ 2 + ‖w.snd.snd‖ ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
  ring

variable {ν : Measure E}

/-- Dropping the jump channel, `(x, y, z, u) ↦ (x, y, z)`. -/
def projB (θ : TupleH ν n m d) : ReducedTuple n m d :=
  WithLp.toLp 2 (θ.1, WithLp.toLp 2 (θ.2.1, θ.2.2.1))

/-- Inserting a zero jump channel, `(x, y, z) ↦ (x, y, z, 0)`. -/
noncomputable def liftB (w : ReducedTuple n m d) : TupleH ν n m d :=
  (w.fst, w.snd.fst, w.snd.snd, 0)

/-- **At `ν = 0`, inserting a zero jump channel after dropping it is the identity.** -/
@[simp]
theorem liftB_projB (θ : TupleH (0 : Measure E) n m d) : liftB (projB θ) = θ :=
  Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (Subsingleton.elim _ _)))

/-- `projB` commutes with differences. -/
theorem projB_sub (θ θ' : TupleH ν n m d) : projB (θ - θ') = projB θ - projB θ' :=
  rfl

/-- `liftB` commutes with differences. -/
theorem liftB_sub (w w' : ReducedTuple n m d) :
    liftB (ν := ν) (w - w') = liftB w - liftB w' := by
  simp [liftB]

/-- The squared norm of the reduced tuple is `|x|² + |y|² + |z|²_F`. -/
theorem norm_projB_sq (θ : TupleH ν n m d) :
    ‖projB θ‖ ^ 2 = ‖θ.1‖ ^ 2 + ‖θ.2.1‖ ^ 2 + ‖θ.2.2.1‖ ^ 2 := by
  rw [norm_reducedTuple_sq]
  rfl

/-- Dropping the jump channel does not increase the Hilbert norm. -/
theorem norm_projB_le_norm_toL2 (θ : TupleH ν n m d) : ‖projB θ‖ ≤ ‖toL2 θ‖ := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp ?_
  rw [norm_projB_sq, norm_toL2_sq, channelSq]
  nlinarith [sq_nonneg ‖θ.2.2.2‖]

/-- The Hilbert norm of the reduced tuple is at most twice the maximum of the channel norms. -/
theorem norm_projB_le (θ : TupleH ν n m d) : ‖projB θ‖ ≤ 2 * ‖θ‖ :=
  (norm_projB_le_norm_toL2 θ).trans (norm_toL2_le θ)

/-- The Hilbert norm of a tuple with a zero jump channel is the norm of the reduced tuple. -/
theorem norm_toL2_liftB (w : ReducedTuple n m d) : ‖toL2 (liftB (ν := ν) w)‖ = ‖w‖ := by
  refine (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp ?_
  rw [norm_toL2_sq, channelSq, norm_reducedTuple_sq]
  simp [liftB]

/-- `projB` is measurable. -/
theorem measurable_projB : Measurable (projB : TupleH ν n m d → ReducedTuple n m d) :=
  (WithLp.measurable_toLp 2 _).comp (measurable_fst.prodMk ((WithLp.measurable_toLp 2 _).comp
    (measurable_snd.fst.prodMk measurable_snd.snd.fst)))

/-- `liftB` is measurable. -/
theorem measurable_liftB : Measurable (liftB : ReducedTuple n m d → TupleH ν n m d) := by
  have h1 : Measurable fun w : ReducedTuple n m d => w.fst :=
    measurable_fst.comp (WithLp.measurable_ofLp 2 _)
  have h2 : Measurable fun w : ReducedTuple n m d => w.snd :=
    measurable_snd.comp (WithLp.measurable_ofLp 2 _)
  have h3 : Measurable fun w : ReducedTuple n m d => w.snd.fst :=
    (measurable_fst.comp (WithLp.measurable_ofLp 2 _)).comp h2
  have h4 : Measurable fun w : ReducedTuple n m d => w.snd.snd :=
    (measurable_snd.comp (WithLp.measurable_ofLp 2 _)).comp h2
  exact h1.prodMk (h3.prodMk (h4.prodMk measurable_const))

/-! ### Laws -/

variable [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]

/-- The image of a law of finite second moment on `H` under `projB`. -/
noncomputable def projP2 (μ : P2 (TupleH ν n m d)) : P2 (ReducedTuple n m d) :=
  μ.mapOfLe measurable_projB norm_projB_le

section Wasserstein

/-- Dropping the jump channel from a point of the Hilbert-norm tuple space does not increase
distances. -/
theorem norm_projB_ofL2_sub_le (v v' : TupleL2 (EuclideanSpace ℝ (Fin n))
    (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m × Fin d))
    (Lp (EuclideanSpace ℝ (Fin m)) 2 ν)) :
    ‖projB (ofL2 v) - projB (ofL2 v')‖ ≤ ‖v - v'‖ := by
  have h := norm_projB_le_norm_toL2 (ofL2 v - ofL2 v')
  rwa [projB_sub, toL2_sub, toL2_ofL2, toL2_ofL2] at h

/-- **Dropping the jump channel does not increase `W₂`**: `W₂` of the reduced laws is at most the
Hilbert-norm `W₂` of the laws on `H`. -/
theorem w2P_projP2_le (μ μ' : P2 (TupleH ν n m d)) :
    w2P (projP2 μ) (projP2 μ') ≤ w2H μ μ' := by
  have hK : Measurable fun v : TupleL2 (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m))
      (EuclideanSpace ℝ (Fin m × Fin d)) (Lp (EuclideanSpace ℝ (Fin m)) 2 ν) =>
      projB (ofL2 v) :=
    measurable_projB.comp measurable_ofL2
  have h := w2_map_le_of_norm_sub_le hK norm_projB_ofL2_sub_le (μ.law.map toL2)
    (μ'.law.map toL2) (w2sq_map_toL2_ne_top μ μ')
  rwa [Measure.map_map hK measurable_toL2, Measure.map_map hK measurable_toL2] at h

/-- **At `ν = 0`, `projP2` preserves `W₂`**: `W₂` of the reduced laws is the Hilbert-norm `W₂` of
the laws on `H`. -/
theorem w2P_projP2 (μ μ' : P2 (TupleH (0 : Measure E) n m d)) :
    w2P (projP2 μ) (projP2 μ') = w2H μ μ' := by
  refine le_antisymm (w2P_projP2_le μ μ') ?_
  have hJ : Measurable fun w : ReducedTuple n m d => toL2 (liftB (ν := (0 : Measure E)) w) :=
    measurable_toL2.comp measurable_liftB
  have hJlip : ∀ w w' : ReducedTuple n m d,
      ‖toL2 (liftB (ν := (0 : Measure E)) w) - toL2 (liftB w')‖ ≤ ‖w - w'‖ := fun w w' => by
    rw [← toL2_sub, ← liftB_sub, norm_toL2_liftB]
  have h := w2_map_le_of_norm_sub_le hJ hJlip (projP2 μ).law (projP2 μ').law
    (w2sq_ne_top (projP2 μ) (projP2 μ'))
  have hmap : ∀ ρ : P2 (TupleH (0 : Measure E) n m d),
      (projP2 ρ).law.map (fun w => toL2 (liftB (ν := (0 : Measure E)) w)) = ρ.law.map toL2 := by
    intro ρ
    simp only [projP2, P2.mapOfLe_law]
    rw [Measure.map_map hJ measurable_projB]
    congr 1
    funext θ
    simp
  rwa [hmap, hmap] at h

end Wasserstein

end Dissertation.WellPosedness.System
