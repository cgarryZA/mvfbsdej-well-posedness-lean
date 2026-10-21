/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.Law.Triangle

/-!
# The 2-Wasserstein pseudometric on the laws of finite second moment

On a separable Banach space `E` the 2-Wasserstein distance `w2P` vanishes on the diagonal, is
symmetric and satisfies the triangle inequality, so it is a pseudometric on the laws of finite
second moment. The type synonym `P2W E` of `P2 E` carries that pseudometric, its topology and the
Borel σ-algebra of that topology. The synonym keeps these structures apart from the evaluation
σ-algebra on `P2 E` (`Dissertation.Law.P2.instMeasurableSpace`): the two σ-algebras are compared
through the identity map `P2.toP2W`, not identified by instance search. The structure here is a
pseudometric; separation, the vanishing of the distance forcing the two laws to agree, is the
instance `Dissertation.Law.P2W.instT0Space` of `Dissertation/Law/P2Separation.lean`.

## Main definitions

* `Dissertation.Law.P2W`: the laws of finite second moment with the 2-Wasserstein pseudometric.
* `Dissertation.Law.P2.toP2W`, `Dissertation.Law.P2W.toP2`: the identity maps between `P2 E` and
  `P2W E`.
* `Dissertation.Law.P2W.instPseudoMetricSpace`: the pseudometric `w2P` on `P2W E`.
* `Dissertation.Law.P2W.instMeasurableSpace`: the Borel σ-algebra of the 2-Wasserstein topology.

## Main statements

* `Dissertation.Law.P2W.dist_toP2W`: the distance on `P2W E` is `w2P`.
* `Dissertation.Law.P2W.tendsto_toP2W_iff`: convergence in `P2W E` is convergence of `w2P` to
  `0`.
-/

namespace Dissertation.Law

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]

variable (E) in
/-- The laws of finite second moment on `E`, with the 2-Wasserstein pseudometric. -/
def P2W : Type _ := P2 E

/-- A law of finite second moment, as a point of the 2-Wasserstein space. -/
def P2.toP2W (μ : P2 E) : P2W E := μ

/-- A point of the 2-Wasserstein space, as a law of finite second moment. -/
def P2W.toP2 (μ : P2W E) : P2 E := μ

variable [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- The 2-Wasserstein pseudometric on the laws of finite second moment. -/
noncomputable instance P2W.instPseudoMetricSpace : PseudoMetricSpace (P2W E) where
  dist μ ν := w2P μ.toP2 ν.toP2
  dist_self μ := w2P_self μ.toP2
  dist_comm μ ν := w2P_comm μ.toP2 ν.toP2
  dist_triangle μ ν ρ := w2P_triangle μ.toP2 ν.toP2 ρ.toP2

/-- The Borel σ-algebra of the 2-Wasserstein topology. -/
noncomputable instance P2W.instMeasurableSpace : MeasurableSpace (P2W E) :=
  borel (P2W E)

/-- The σ-algebra of `P2W E` is the Borel σ-algebra of its topology. -/
instance P2W.instBorelSpace : BorelSpace (P2W E) :=
  ⟨rfl⟩

/-- The distance on `P2W E` is the 2-Wasserstein distance. -/
theorem P2W.dist_toP2W (μ ν : P2 E) : dist μ.toP2W ν.toP2W = w2P μ ν :=
  rfl

/-- A sequence of laws converges in the 2-Wasserstein space exactly when its 2-Wasserstein
distance to the limit tends to `0`. -/
theorem P2W.tendsto_toP2W_iff {ι : Type*} {l : Filter ι} {μ : ι → P2 E} {μ₀ : P2 E} :
    Tendsto (fun i => (μ i).toP2W) l (𝓝 μ₀.toP2W) ↔ Tendsto (fun i => w2P (μ i) μ₀) l (𝓝 0) :=
  tendsto_iff_dist_tendsto_zero

end Dissertation.Law
