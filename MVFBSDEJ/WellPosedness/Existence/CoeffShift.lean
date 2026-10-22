/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Existence.Step

/-!
# A solution of the `λ = 0` system as a solution at every `λ`

At `λ = 0` the forced system (4.1) does not see its coefficients. A solution `Θ` of it with
forcing `q`, along which the coefficient processes
`Ψ(Θ) = (b(s, Θ_s, μ_s), σ(s, Θ_s, μ_s), γ, f(s, Θ_s, μ_s), g(X_T, Law X_T))` form a forcing,
solves the `λ`-forced system with forcing `q − λ Ψ(Θ)`, for every real `λ`: the forced integrands
`λ ψ(Θ) + (q^ψ − λ ψ(Θ)) = q^ψ` are those of the `λ = 0` system.

## Main statements

* `SolvesForced.of_zero_sub_coeff` — a solution at `λ = 0` with forcing `q` solves the system at
  `λ` with forcing `q − λ Ψ(Θ)`.
-/

open MeasureTheory

namespace MVFBSDEJ.WellPosedness.System

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}
  {P : Measure Ω} [IsProbabilityMeasure P] {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {T : ℝ} {C : Coeffs ν n m d}
  {ξ₀ : Fin n → Ω → ℝ}
  {qb : Fin n → Ω → ℝ → ℝ} {qσ : Fin n → ℝ → Ω → Fin d → ℝ} {qh : Fin n → ℝ → Ω → E → ℝ}
  {qf : Fin m → Ω → ℝ → ℝ} {qg : Fin m → Ω → ℝ}
  {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ}
  {Z : Fin m → ℝ → Ω → Fin d → ℝ} {U : Fin m → ℝ → Ω → E → ℝ} {γ : Fin n → ℝ → Ω → E → ℝ}

/-- **A solution of the `λ = 0` system solves the system at every `λ`.** If `Θ` solves the
forced system (4.1) at `λ = 0` with forcing `q` and representative `γ`, and the coefficient
processes `Ψ(Θ)` along `Θ`, with `γ` as jump component, form a forcing, then for every real `λ`,
`Θ` solves the `λ`-forced system with forcing `q − λ Ψ(Θ)` and the same `γ`. -/
theorem SolvesForced.of_zero_sub_coeff
    (h : SolvesForced D ℱ hℱW hℱN T 0 C ξ₀ qb qσ qh qf qg X Y Z U γ)
    (hΨ : Forcing ℱ P ν T (driftProc P T C X Y Z U) (diffusionProc P T C X Y Z U)
      (jumpProc T γ) (driverProc P T C X Y Z U) (terminalVal P T C X)) (lam : ℝ) :
    SolvesForced D ℱ hℱW hℱN T lam C ξ₀
      (fun i ω s => qb i ω s - lam * driftProc P T C X Y Z U i ω s)
      (fun i s ω j => qσ i s ω j - lam * diffusionProc P T C X Y Z U i s ω j)
      (fun i s ω e => qh i s ω e - lam * jumpProc T γ i s ω e)
      (fun k ω s => qf k ω s - lam * driverProc P T C X Y Z U k ω s)
      (fun k ω => qg k ω - lam * terminalVal P T C X k ω) X Y Z U γ := by
  have hq := h.forcing.sub (hΨ.smul lam)
  have h' : SolvesForced D ℱ hℱW hℱN T 0 C ξ₀
      (fun i ω s => (qb i ω s - lam * driftProc P T C X Y Z U i ω s)
        + lam * driftProc P T C X Y Z U i ω s)
      (fun i s ω j => (qσ i s ω j - lam * diffusionProc P T C X Y Z U i s ω j)
        + lam * diffusionProc P T C X Y Z U i s ω j)
      (fun i s ω e => (qh i s ω e - lam * jumpProc T γ i s ω e) + lam * jumpProc T γ i s ω e)
      (fun k ω s => (qf k ω s - lam * driverProc P T C X Y Z U k ω s)
        + lam * driverProc P T C X Y Z U k ω s)
      (fun k ω => (qg k ω - lam * terminalVal P T C X k ω) + lam * terminalVal P T C X k ω)
      X Y Z U γ := by
    simp only [sub_add_cancel]
    exact h
  simpa only [zero_add] using h'.add_coeff hq

end MVFBSDEJ.WellPosedness.System
