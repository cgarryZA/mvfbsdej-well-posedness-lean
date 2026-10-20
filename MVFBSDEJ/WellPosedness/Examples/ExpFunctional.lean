/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.Law.ExpectationFunctional
import MVFBSDEJ.WellPosedness.System.HilbertLipschitz

/-!
# Expectation-functional interactions on the tuple space

Example 5.3 of the well-posedness paper takes a kernel `φ̄ : ℝ × H × H → F` on the tuple space
`H`, Lipschitz in `(θ, θ')` uniformly in the time,

`‖φ̄(t, θ₁, θ'₁) − φ̄(t, θ₂, θ'₂)‖ ≤ K (|θ₁ − θ₂|_H + |θ'₁ − θ'₂|_H)`,

with `|·|_H` the Hilbert norm `(|x|² + |y|² + |z|²_F + ‖u‖²_{L²(ν)})^{1/2}`, and the coefficient
`φ(t, θ, μ) = ∫_H φ̄(t, θ, θ') μ(dθ')`, the Bochner mean of the kernel `φ̄(t, θ, ·)` against a law
of finite second moment. The Hilbert norm is at most twice the norm of the tuple space, so such a
kernel is jointly continuous in `(θ, θ')` at each time.

## Main definitions

* `KernelLipschitzH` — a kernel Lipschitz in `(θ, θ')` uniformly in the time, for the Hilbert
  norm.

## Main statements

* `KernelLipschitzH.continuous` — such a kernel is jointly continuous in `(θ, θ')` at each time.
-/

open MeasureTheory MVFBSDEJ.Law
open scoped ENNReal

namespace MVFBSDEJ.WellPosedness.System

variable {HX HY HZY HUY : Type*} [NormedAddCommGroup HX] [InnerProductSpace ℝ HX]
  [NormedAddCommGroup HY] [InnerProductSpace ℝ HY] [NormedAddCommGroup HZY]
  [InnerProductSpace ℝ HZY] [NormedAddCommGroup HUY] [InnerProductSpace ℝ HUY]

/-- A kernel `φ̄ : ℝ × H × H → F` is Lipschitz in `(θ, θ')` uniformly in the time with constant
`K`, for the Hilbert norm of the tuple space:
`‖φ̄(t, θ₁, θ'₁) − φ̄(t, θ₂, θ'₂)‖ ≤ K (|θ₁ − θ₂|_H + |θ'₁ − θ'₂|_H)`. -/
def KernelLipschitzH {F : Type*} [NormedAddCommGroup F] (K : ℝ)
    (φ : ℝ → Tuple HX HY HZY HUY → Tuple HX HY HZY HUY → F) : Prop :=
  ∀ t θ₁ θ₂ θ'₁ θ'₂, ‖φ t θ₁ θ'₁ - φ t θ₂ θ'₂‖
    ≤ K * (‖toL2 θ₁ - toL2 θ₂‖ + ‖toL2 θ'₁ - toL2 θ'₂‖)

/-- A kernel Lipschitz for the Hilbert norm is jointly continuous in `(θ, θ')` at each time. -/
theorem KernelLipschitzH.continuous {F : Type*} [NormedAddCommGroup F] {K : ℝ}
    {φ : ℝ → Tuple HX HY HZY HUY → Tuple HX HY HZY HUY → F} (hK : 0 ≤ K)
    (hφ : KernelLipschitzH K φ) (t : ℝ) :
    Continuous fun q : Tuple HX HY HZY HUY × Tuple HX HY HZY HUY => φ t q.1 q.2 := by
  have hL : LipschitzWith (Real.toNNReal (4 * K))
      fun q : Tuple HX HY HZY HUY × Tuple HX HY HZY HUY => φ t q.1 q.2 := by
    refine LipschitzWith.of_dist_le_mul fun q r => ?_
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
    have h1 := norm_toL2_le (q.1 - r.1)
    have h2 := norm_toL2_le (q.2 - r.2)
    rw [toL2_sub] at h1 h2
    have h3 : ‖q.1 - r.1‖ ≤ ‖q - r‖ := norm_fst_le (q - r)
    have h4 : ‖q.2 - r.2‖ ≤ ‖q - r‖ := norm_snd_le (q - r)
    calc ‖φ t q.1 q.2 - φ t r.1 r.2‖
        ≤ K * (‖toL2 q.1 - toL2 r.1‖ + ‖toL2 q.2 - toL2 r.2‖) := hφ t q.1 r.1 q.2 r.2
      _ ≤ K * (2 * ‖q - r‖ + 2 * ‖q - r‖) := by gcongr <;> linarith
      _ = 4 * K * ‖q - r‖ := by ring
  exact hL.continuous

end MVFBSDEJ.WellPosedness.System
