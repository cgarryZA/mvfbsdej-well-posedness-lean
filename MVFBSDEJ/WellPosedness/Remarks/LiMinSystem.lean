/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Examples.MeanField
import Mathlib.AlgebraicTopology.SimplexCategory.Basic

/-!
# The linear mean-field system of Li and Min

Example 3.2 of Li and Min is the mean-field system with jumps, with `m = n = d = 1`,

`dx(t) = 𝔼[y(t)] dt + dB_t + ∫_E k(t, e) Ñ(dt, de)`,
`−dy(t) = 𝔼[x(t)] dt − z(t) dB_t − ∫_E k(t, e) Ñ(dt, de)`,
`x(0) = 1`, `y(T) = −𝔼[x(T)]`,

the jump integrand `k` of the forward equation being that of the backward one. On the tuple space
`H = ℝ × ℝ × ℝ^{1×1} × L²(ν; ℝ)`, with `θ = (x, y, z, u)`, it is the system (1.1) with

`b(t, θ, μ) = m_Y(μ)`, `σ = 1`, `h(t, θ, μ) = u`, `f(t, θ, μ) = m_X(μ)`, `g(x, ρ) = −𝔟(ρ)`,

where `m_X(μ), m_Y(μ)` are the `X`- and `Y`-channels of the mean `∫_H θ μ(dθ)`, the means of the
`X`- and `Y`-marginals of `μ`, and `𝔟(ρ)` is the barycentre of `ρ`. The backward equation of
(1.1), `Y_t = g(X_T, Law X_T) + ∫_t^T f ds − ∫_t^T Z dW − ∫_t^T ∫_E U Ñ(ds, de)`, is
`−dY = f dt − Z dW − U dÑ` with `Y_T = g(X_T, Law X_T)`, so the signs are those of Li and Min,
with `Z = z` and `U = k`. The mark space and the σ-finite intensity `ν` are arbitrary.

The coefficients are linear in `(θ, μ)` and Lipschitz. The mean is `1`-Lipschitz for the
Hilbert-norm `W₂` and the sum of its channel norms is at most twice the Hilbert norm, so the
system satisfies Assumption 2.3 with `L = 2` for the Hilbert-norm `W₂` on `P₂(H)`; the terminal
function satisfies (2.6) with `L = 1`, the barycentre being `1`-Lipschitz for `W₂`. The origin
values `b, h, f = 0` and `σ = 1` are independent of the time, which gives Assumption 2.2, and the
coefficients are continuous on `[0, T] × H × P₂(H)`, which gives (2.3).

## Main definitions

* `liMinCoeffs` — the coefficients of Example 3.2 of Li and Min.

## Main statements

* `lipschitzCoefficients_liMin`, `lipschitzTerminalP2_liMin` — Assumption 2.3, pointwise.
* `diagonalLipschitzH_liMin`, `terminalLipschitz_liMin` — Assumption 2.3 along the diagonal.
* `coeffOrigin_liMin` — Assumption 2.2.
* `coeffBorelW2_liMin` — (2.3).
-/

open MeasureTheory Filter MVFBSDEJ.Law
open scoped ENNReal

namespace MVFBSDEJ.WellPosedness.System

open MVFBSDEJ.WellPosedness.Existence

variable {E : Type*} [MeasurableSpace E]

variable (ν : Measure E) in
/-- The coefficients of Example 3.2 of Li and Min on `H = ℝ × ℝ × ℝ^{1×1} × L²(ν; ℝ)`: for
`θ = (x, y, z, u)`, `b = m_Y(μ)`, `σ = 1`, `h = u`, `f = m_X(μ)`, with `m_X(μ), m_Y(μ)` the `X`-
and `Y`-channels of the mean `∫_H θ μ(dθ)`, and `g(x, ρ) = −𝔟(ρ)`, with `𝔟(ρ)` the barycentre
of `ρ`. -/
noncomputable def liMinCoeffs : Coeffs ν 1 1 1 where
  b _ _ μ := (tupleMean μ).2.1
  σ _ _ _ := WithLp.toLp 2 fun _ => 1
  h _ θ _ := θ.2.2.2
  f _ _ μ := (tupleMean μ).1
  g _ ρ := -barycentre ρ

variable {ν : Measure E}

/-- **Assumption 2.3, terminal, pointwise, for Example 3.2 of Li and Min**, with any constant
`L ≥ 1`: `|g(x, ρ) − g(x', ρ')| = |𝔟(ρ) − 𝔟(ρ')| ≤ L (|x − x'| + W₂(ρ, ρ'))`. -/
theorem lipschitzTerminalP2_liMin {L : ℝ} (hL : 1 ≤ L) :
    LipschitzTerminalP2 L (liMinCoeffs ν).g := by
  intro x x' ρ ρ'
  have h1 : ‖-barycentre ρ - -barycentre ρ'‖ ≤ w2P ρ ρ' := by
    rw [neg_sub_neg, norm_sub_rev]
    exact norm_barycentre_sub_le ρ ρ'
  have h2 := norm_nonneg (x - x')
  have h3 := w2P_nonneg ρ ρ'
  simp only [liMinCoeffs]
  nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {P : Measure Ω}
  [IsProbabilityMeasure P] {T : ℝ}

/-- Assumption 2.3, terminal, along the diagonal, for Example 3.2 of Li and Min, with any constant
`L ≥ 1`. -/
theorem terminalLipschitz_liMin {L : ℝ} (hL : 1 ≤ L) :
    TerminalLipschitz ℱ P T L (liMinCoeffs ν).g :=
  terminalLipschitz_of_lipschitzTerminalP2 (lipschitzTerminalP2_liMin hL)

variable [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]

/-- **Assumption 2.3, interior, pointwise, for Example 3.2 of Li and Min, at `L = 2`**, with `W₂`
the 2-Wasserstein distance of the Hilbert norm: at every time, pair of points and pair of laws,
`|δb| + |δσ|_F + ‖δh‖_{L²(ν)} + |δf| = |δm_Y| + ‖δu‖_{L²(ν)} + |δm_X|
  ≤ 2 (|δX| + |δY| + |δZ|_F + ‖δU‖_{L²(ν)} + W₂(μ, μ'))`. -/
theorem lipschitzCoefficients_liMin :
    LipschitzCoefficients 2 (w2H (HX := EuclideanSpace ℝ (Fin 1))
        (HY := EuclideanSpace ℝ (Fin 1)) (HZY := EuclideanSpace ℝ (Fin 1 × Fin 1))
        (HUY := Lp (EuclideanSpace ℝ (Fin 1)) 2 ν))
      (liMinCoeffs ν).b (liMinCoeffs ν).σ (liMinCoeffs ν).h (liMinCoeffs ν).f := by
  intro t θ θ' μ μ'
  have hm := tupleNorm_tupleMean_sub_le μ μ'
  have htn : tupleNorm (θ - θ')
      = ‖θ.1 - θ'.1‖ + ‖θ.2.1 - θ'.2.1‖ + ‖θ.2.2.1 - θ'.2.2.1‖ + ‖θ.2.2.2 - θ'.2.2.2‖ := rfl
  have hmn : tupleNorm (tupleMean μ - tupleMean μ')
      = ‖(tupleMean μ).1 - (tupleMean μ').1‖ + ‖(tupleMean μ).2.1 - (tupleMean μ').2.1‖
        + ‖(tupleMean μ).2.2.1 - (tupleMean μ').2.2.1‖
        + ‖(tupleMean μ).2.2.2 - (tupleMean μ').2.2.2‖ := rfl
  have h1 := norm_nonneg (θ.1 - θ'.1)
  have h2 := norm_nonneg (θ.2.1 - θ'.2.1)
  have h3 := norm_nonneg (θ.2.2.1 - θ'.2.2.1)
  have h4 := norm_nonneg ((tupleMean μ).2.2.1 - (tupleMean μ').2.2.1)
  have h5 := norm_nonneg ((tupleMean μ).2.2.2 - (tupleMean μ').2.2.2)
  have h6 := w2H_nonneg μ μ'
  have h7 := norm_nonneg (θ.2.2.2 - θ'.2.2.2)
  simp only [liMinCoeffs, sub_self, norm_zero, add_zero]
  rw [htn]
  linarith

/-- **Assumption 2.3, interior, along the diagonal, for Example 3.2 of Li and Min, at `L = 2`**,
with the Hilbert-norm `W₂` on `P₂(H)`. -/
theorem diagonalLipschitzH_liMin : DiagonalLipschitzH ℱ P T 2 (liMinCoeffs ν) :=
  Eventually.of_forall fun t Θ Θ' _ _ _ _ => Eventually.of_forall fun ω =>
    lipschitzCoefficients_liMin t (Θ ω) (Θ' ω) _ _

/-- **Assumption 2.2 for Example 3.2 of Li and Min**: the origin values
`b = h = f = 0` and `σ = 1` at `(t, 0, δ₀)` are independent of the time, hence square integrable
over `[0, T]`. -/
theorem coeffOrigin_liMin (T : ℝ) : CoeffOrigin T (liMinCoeffs ν) :=
  originIntegrable_const T _ _ _ _

/-- **(2.3) for Example 3.2 of Li and Min**: the coefficients are Borel measurable on
`[0, T] × H × P₂(H)`, with the Hilbert-norm `W₂` on `P₂(H)`. They are continuous there, the mean
being `1`-Lipschitz. -/
theorem coeffBorelW2_liMin (T : ℝ) : CoeffBorelW2 T (liMinCoeffs ν) := by
  have hθ : Continuous fun p : Set.Icc (0 : ℝ) T × TupleH ν 1 1 1 × TupleP2WH ν 1 1 1 => p.2.1 :=
    continuous_fst.comp continuous_snd
  have hm : Continuous fun p : Set.Icc (0 : ℝ) T × TupleH ν 1 1 1 × TupleP2WH ν 1 1 1 =>
      tupleMean p.2.2.toP2 :=
    lipschitzWith_tupleMean.continuous.comp (continuous_snd.comp continuous_snd)
  exact
    { b_meas := Continuous.borel_measurable hm.snd.fst
      σ_meas := Continuous.borel_measurable continuous_const
      h_meas := Continuous.borel_measurable hθ.snd.snd.snd
      f_meas := Continuous.borel_measurable hm.fst }

end MVFBSDEJ.WellPosedness.System
