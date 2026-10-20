/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Existence.CoeffBorel
import MVFBSDEJ.WellPosedness.System.HilbertW2Space

/-!
# The joint Borel measurability (2.3) of the coefficients

The well-posedness paper asks the coefficients `b, σ, f` on `[0, T] × H × P₂(H)` to be jointly
Borel measurable, and the jump coefficient `h` to be Borel measurable as a map
`[0, T] × H × P₂(H) → L²(ν; ℝⁿ)`, its (2.3), with `P₂(H)` the metric space of the laws of finite
second moment on `H` under the 2-Wasserstein distance of the Hilbert norm of `H`.
`CoeffBorelW2 T C` states this: each of `(t, θ, μ) ↦ ψ(t, θ, μ)`, `ψ ∈ {b, σ, h, f}`, is
measurable from the Borel σ-algebra of the product topology on `[0, T] × H × P₂(H)`, with
`P₂(H) = TupleP2WH ν n m d` carrying the Hilbert-norm `W₂`, to the Borel σ-algebra of the value
space.

`CoeffBorelW2` implies `CoeffBorel`, the same measurability with `P₂(H)` carrying the evaluation
σ-algebra, for the coefficients cut off to `[0, T]` on `ℝ × H × P₂(H)`. The Borel σ-algebra of
the product topology is the product of the Borel σ-algebras of the factors, since `[0, T]` and
`H` are second countable; every Borel set of `(P₂(H), W₂)` is in the evaluation σ-algebra
(`measurable_toP2WH`); and `[0, T]` is a measurable subset of `ℝ`.

## Main definitions

* `CoeffBorelW2` — the joint Borel measurability (2.3) of the coefficients on `[0, T] × H × P₂(H)`.

## Main statements

* `borelSpace_Icc_prod` — the product σ-algebra on `[0, T] × H × P₂(H)` is the Borel σ-algebra of
  the product topology.
* `measurable_borelW2_of_measurable` — a coefficient measurable on `ℝ × H × P₂(H)` is Borel
  measurable on `[0, T] × H × P₂(H)`.
* `measurable_cutoff_of_borelW2` — a coefficient Borel measurable on `[0, T] × H × P₂(H)` has a
  measurable cut-off on `ℝ × H × P₂(H)`, for the evaluation σ-algebra on `P₂(H)`.
* `CoeffBorelW2.toCoeffBorel` — (2.3) with the Hilbert-norm `W₂` implies `CoeffBorel`.
-/

open MeasureTheory Filter MVFBSDEJ.Law

namespace MVFBSDEJ.WellPosedness.Existence

open MVFBSDEJ.WellPosedness.System

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} {n m d : ℕ}

variable [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]

/-- **The joint Borel measurability (2.3) of the coefficients**: each of
`(t, θ, μ) ↦ ψ(t, θ, μ)`, `ψ ∈ {b, σ, h, f}`, is measurable from the Borel σ-algebra of the
product topology on `[0, T] × H × P₂(H)`, with `P₂(H)` carrying the 2-Wasserstein distance of the
Hilbert norm of `H`, to the Borel σ-algebra of the value space (`L²(ν; ℝⁿ)` for `h`). -/
structure CoeffBorelW2 (T : ℝ) (C : Coeffs ν n m d) : Prop where
  /-- The drift is Borel measurable on `[0, T] × H × P₂(H)`. -/
  b_meas : Measurable[borel (Set.Icc (0 : ℝ) T × TupleH ν n m d × TupleP2WH ν n m d),
    borel (EuclideanSpace ℝ (Fin n))] fun p => C.b p.1 p.2.1 p.2.2.toP2
  /-- The diffusion is Borel measurable on `[0, T] × H × P₂(H)`. -/
  σ_meas : Measurable[borel (Set.Icc (0 : ℝ) T × TupleH ν n m d × TupleP2WH ν n m d),
    borel (EuclideanSpace ℝ (Fin n × Fin d))] fun p => C.σ p.1 p.2.1 p.2.2.toP2
  /-- The jump coefficient is Borel measurable on `[0, T] × H × P₂(H)` into `L²(ν; ℝⁿ)`. -/
  h_meas : Measurable[borel (Set.Icc (0 : ℝ) T × TupleH ν n m d × TupleP2WH ν n m d),
    borel (Lp (EuclideanSpace ℝ (Fin n)) 2 ν)] fun p => C.h p.1 p.2.1 p.2.2.toP2
  /-- The driver is Borel measurable on `[0, T] × H × P₂(H)`. -/
  f_meas : Measurable[borel (Set.Icc (0 : ℝ) T × TupleH ν n m d × TupleP2WH ν n m d),
    borel (EuclideanSpace ℝ (Fin m))] fun p => C.f p.1 p.2.1 p.2.2.toP2

/-- The σ-algebra of `[0, T] × H × P₂(H)`, the product of those of the factors, is the Borel
σ-algebra of the product topology, `[0, T]` and `H` being second countable. -/
instance borelSpace_Icc_prod (T : ℝ) :
    BorelSpace (Set.Icc (0 : ℝ) T × TupleH ν n m d × TupleP2WH ν n m d) :=
  haveI : BorelSpace (TupleH ν n m d × TupleP2WH ν n m d) := Prod.borelSpace
  haveI : SecondCountableTopologyEither (Set.Icc (0 : ℝ) T)
      (TupleH ν n m d × TupleP2WH ν n m d) :=
    secondCountableTopologyEither_of_left _ _
  Prod.borelSpace

/-- **A coefficient measurable on `ℝ × H × P₂(H)` is Borel measurable on `[0, T] × H × P₂(H)`**,
for `P₂(H)` carrying the Borel σ-algebra of the Hilbert-norm 2-Wasserstein distance. -/
theorem measurable_borelW2_of_measurable {T : ℝ} {W : Type*} [TopologicalSpace W]
    [MeasurableSpace W] [BorelSpace W] {ψ : ℝ → TupleH ν n m d → P2 (TupleH ν n m d) → W}
    (hψ : Measurable fun p : ℝ × TupleH ν n m d × TupleP2WH ν n m d => ψ p.1 p.2.1 p.2.2.toP2) :
    Measurable[borel (Set.Icc (0 : ℝ) T × TupleH ν n m d × TupleP2WH ν n m d), borel W]
      fun p => ψ p.1 p.2.1 p.2.2.toP2 := by
  rw [← BorelSpace.measurable_eq (α := W),
    ← BorelSpace.measurable_eq (α := Set.Icc (0 : ℝ) T × TupleH ν n m d × TupleP2WH ν n m d)]
  exact hψ.comp ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)

/-- **A coefficient Borel measurable on `[0, T] × H × P₂(H)` has a measurable cut-off**: if
`(t, θ, μ) ↦ ψ(t, θ, μ)` is measurable from the Borel σ-algebra of the product topology on
`[0, T] × H × P₂(H)`, with the Hilbert-norm `W₂` on `P₂(H)`, then
`(t, θ, μ) ↦ 1_{[0, T]}(t) ψ(t, θ, μ)` is measurable on `ℝ × H × P₂(H)` with the evaluation
σ-algebra on `P₂(H)`. -/
theorem measurable_cutoff_of_borelW2 {T : ℝ} {W : Type*} [TopologicalSpace W]
    [MeasurableSpace W] [BorelSpace W] [Zero W]
    {ψ : ℝ → TupleH ν n m d → P2 (TupleH ν n m d) → W}
    (hψ : Measurable[borel (Set.Icc (0 : ℝ) T × TupleH ν n m d × TupleP2WH ν n m d), borel W]
      fun p => ψ p.1 p.2.1 p.2.2.toP2) :
    Measurable fun p : ℝ × TupleH ν n m d × P2 (TupleH ν n m d) =>
      (Set.Icc (0 : ℝ) T).indicator (fun t => ψ t p.2.1 p.2.2) p.1 := by
  classical
  rw [← BorelSpace.measurable_eq (α := W),
    ← BorelSpace.measurable_eq (α := Set.Icc (0 : ℝ) T × TupleH ν n m d × TupleP2WH ν n m d)]
    at hψ
  set S : Set (ℝ × TupleH ν n m d × P2 (TupleH ν n m d)) := {p | p.1 ∈ Set.Icc (0 : ℝ) T}
  have hS : MeasurableSet S := measurable_fst measurableSet_Icc
  have hφ : Measurable fun q : S =>
      ((⟨q.1.1, q.2⟩ : Set.Icc (0 : ℝ) T), q.1.2.1, q.1.2.2.toP2WH) :=
    (Measurable.subtype_mk (measurable_fst.comp measurable_subtype_coe)).prodMk
      ((measurable_snd.fst.comp measurable_subtype_coe).prodMk
        (measurable_toP2WH.comp (measurable_snd.snd.comp measurable_subtype_coe)))
  have hG : Measurable fun q : S => ψ q.1.1 q.1.2.1 q.1.2.2 := hψ.comp hφ
  have heq : (fun p : ℝ × TupleH ν n m d × P2 (TupleH ν n m d) =>
        (Set.Icc (0 : ℝ) T).indicator (fun t => ψ t p.2.1 p.2.2) p.1)
      = fun p => if hp : p ∈ S then (fun q : S => ψ q.1.1 q.1.2.1 q.1.2.2) ⟨p, hp⟩
        else (fun _ : (Sᶜ : Set _) => (0 : W)) ⟨p, hp⟩ := by
    funext p
    by_cases hp : p ∈ S
    · rw [dif_pos hp, Set.indicator_of_mem (show p.1 ∈ Set.Icc (0 : ℝ) T from hp)]
    · rw [dif_neg hp, Set.indicator_of_notMem (show p.1 ∉ Set.Icc (0 : ℝ) T from hp)]
  rw [heq]
  exact hG.dite measurable_const hS

/-- **(2.3) with the Hilbert-norm `W₂` implies `CoeffBorel`**: joint Borel measurability on
`[0, T] × H × P₂(H)` for the product topology, `P₂(H)` carrying the Hilbert-norm 2-Wasserstein
distance, gives joint measurability of the cut-off coefficients on `ℝ × H × P₂(H)` with the
evaluation σ-algebra on `P₂(H)`. -/
theorem CoeffBorelW2.toCoeffBorel {T : ℝ} {C : Coeffs ν n m d} (hC : CoeffBorelW2 T C) :
    CoeffBorel T C where
  b_meas := measurable_cutoff_of_borelW2 hC.b_meas
  σ_meas := measurable_cutoff_of_borelW2 hC.σ_meas
  h_meas := measurable_cutoff_of_borelW2 hC.h_meas
  f_meas := measurable_cutoff_of_borelW2 hC.f_meas

end MVFBSDEJ.WellPosedness.Existence
