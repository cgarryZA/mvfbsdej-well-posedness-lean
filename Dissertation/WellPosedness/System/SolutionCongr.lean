/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.System.PaperWeakSolutionInt
import Dissertation.WellPosedness.Examples.Dealer.ExposureCoeffs

/-!
# Solutions under a change of the jump coefficient along the solution

The jump coefficient `h` enters the solution predicates of (1.1) only through the requirement
that the jump integrand `γ` represent `e ↦ h(s, Θ_s(ω), e, μ_s)` in `L²(ν)` for almost every
`s ∈ [0, T]`, almost surely: at the tuple `Θ_s` and its law `μ_s` in `SolvesForced`, and at the
predictable tuple `Θ⁻_s` and its law `μ⁻_s` in `PaperSolution`. The drift, diffusion and driver
processes and the terminal value are built from `b, σ, f, g` alone. So if two coefficient systems
`C, C'` have the same `b, σ, f, g`, and `C'.h = C.h` at `(s, Θ_s(ω), μ_s)` (respectively at
`(s, Θ⁻_s(ω), μ⁻_s)`) for almost every `s ∈ [0, T]`, almost surely, then `(X, Y, Z, U)` with the
representative `γ` solves the system with coefficients `C` exactly when it solves the system with
coefficients `C'`.

In the exposure-sensitive dealer system of Example 5.5 the interaction strength `ε` enters only
the jump coefficient, through the crowding correction:

`h^ε(t, θ, μ) = h^0(t, θ, μ) − ε A_{μ^U}(u)`.

Hence a tuple is a solution in the sense of the paper at strength `ε` exactly when it is one at
`ε = 0`, provided the crowding correction `ε A_{μ⁻_s^U}(U_s)` vanishes along its predictable tuple
for almost every `s ∈ [0, T]`, almost surely.

## Main statements

* `SolvesForced.of_h_ae_eq`, `solvesForced_iff_of_h_ae_eq` — the `λ`-forced system (4.1), and so
  the system (1.1).
* `PaperSolution.of_h_ae_eq`, `paperSolution_iff_of_h_ae_eq` — solutions in the sense of the
  paper.
* `dealerExpCoeffs_h_eq_sub`, `dealerExpCoeffs_h_eq_iff` — `h^ε = h^0 − ε A_{μ^U}(u)`.
* `paperSolution_dealerExp_iff` — along a tuple on which the crowding correction vanishes, the
  exposure-sensitive dealer system at strength `ε` and at `ε = 0` have the same solutions in the
  sense of the paper.
-/

open MeasureTheory Filter Dissertation.Law

namespace Dissertation.WellPosedness.System

open LevyStochCalc

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}
  {P : Measure Ω} [IsProbabilityMeasure P] {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {T lam : ℝ} {C C' : Coeffs ν n m d}
  {ξ₀ : Fin n → Ω → ℝ}
  {qb : Fin n → Ω → ℝ → ℝ} {qσ : Fin n → ℝ → Ω → Fin d → ℝ} {qh : Fin n → ℝ → Ω → E → ℝ}
  {qf : Fin m → Ω → ℝ → ℝ} {qg : Fin m → Ω → ℝ}
  {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ}
  {Z : Fin m → ℝ → Ω → Fin d → ℝ} {U : Fin m → ℝ → Ω → E → ℝ} {γ : Fin n → ℝ → Ω → E → ℝ}

/-! ### The `λ`-forced system -/

/-- **A change of the jump coefficient along the solution, for the `λ`-forced system (4.1).**
Let `C, C'` have the same `b, σ, f, g`, and `C'.h(s, Θ_s(ω), μ_s) = C.h(s, Θ_s(ω), μ_s)` for
almost every `s ∈ [0, T]`, almost surely, with `Θ_s` the tuple of `(X, Y, Z, U)` and `μ_s` its
law. If `(X, Y, Z, U)` solves (4.1) with coefficients `C` and the representative `γ`, it solves
(4.1) with coefficients `C'` and the same representative. -/
theorem SolvesForced.of_h_ae_eq (hb : C'.b = C.b) (hσ : C'.σ = C.σ) (hf : C'.f = C.f)
    (hg : C'.g = C.g)
    (hh : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P,
      C'.h s (tupleAt ν X Y Z U s ω) (lawP2 P (tupleAt ν X Y Z U s))
        = C.h s (tupleAt ν X Y Z U s ω) (lawP2 P (tupleAt ν X Y Z U s)))
    (h : SolvesForced D ℱ hℱW hℱN T lam C ξ₀ qb qσ qh qf qg X Y Z U γ) :
    SolvesForced D ℱ hℱW hℱN T lam C' ξ₀ qb qσ qh qf qg X Y Z U γ := by
  obtain ⟨b, σ, hC, f, g⟩ := C
  obtain ⟨b', σ', hC', f', g'⟩ := C'
  obtain rfl : b' = b := hb
  obtain rfl : σ' = σ := hσ
  obtain rfl : f' = f := hf
  obtain rfl : g' = g := hg
  refine { h with jump_rep := ?_ }
  filter_upwards [h.jump_rep, hh] with s hs hs'
  filter_upwards [hs, hs'] with ω hω hω'
  rw [hω']
  exact hω

/-- **The `λ`-forced system (4.1) under a change of the jump coefficient along the solution.**
If `C, C'` have the same `b, σ, f, g`, and `C'.h = C.h` at `(s, Θ_s(ω), μ_s)` for almost every
`s ∈ [0, T]`, almost surely, then `(X, Y, Z, U)` with the representative `γ` solves (4.1) with
coefficients `C` if and only if it solves (4.1) with coefficients `C'`. -/
theorem solvesForced_iff_of_h_ae_eq (hb : C'.b = C.b) (hσ : C'.σ = C.σ) (hf : C'.f = C.f)
    (hg : C'.g = C.g)
    (hh : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P,
      C'.h s (tupleAt ν X Y Z U s ω) (lawP2 P (tupleAt ν X Y Z U s))
        = C.h s (tupleAt ν X Y Z U s ω) (lawP2 P (tupleAt ν X Y Z U s))) :
    SolvesForced D ℱ hℱW hℱN T lam C ξ₀ qb qσ qh qf qg X Y Z U γ
      ↔ SolvesForced D ℱ hℱW hℱN T lam C' ξ₀ qb qσ qh qf qg X Y Z U γ :=
  ⟨SolvesForced.of_h_ae_eq hb hσ hf hg hh,
    SolvesForced.of_h_ae_eq hb.symm hσ.symm hf.symm hg.symm
      (hh.mono fun _ hs => hs.mono fun _ hω => hω.symm)⟩

/-! ### Solutions in the sense of the paper -/

/-- **A change of the jump coefficient along the solution, for solutions in the sense of the
paper.** Let `C, C'` have the same `b, σ, f, g`, and
`C'.h(s, Θ⁻_s(ω), μ⁻_s) = C.h(s, Θ⁻_s(ω), μ⁻_s)` for almost every `s ∈ [0, T]`, almost surely,
with `Θ⁻_s` the predictable tuple of `(X, Y, Z, U)` and `μ⁻_s` its law. If `(X, Y, Z, U)` is a
solution of (1.1) with coefficients `C` in the sense of the paper, with the representative `γ`,
it is one with coefficients `C'` and the same representative. -/
theorem PaperSolution.of_h_ae_eq (hb : C'.b = C.b) (hσ : C'.σ = C.σ) (hf : C'.f = C.f)
    (hg : C'.g = C.g)
    (hh : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P,
      C'.h s (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s ω)
          (lawP2 P (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s))
        = C.h s (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s ω)
          (lawP2 P (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s)))
    (h : PaperSolution D ℱ hℱW hℱN T C ξ₀ X Y Z U γ) :
    PaperSolution D ℱ hℱW hℱN T C' ξ₀ X Y Z U γ := by
  obtain ⟨b, σ, hC, f, g⟩ := C
  obtain ⟨b', σ', hC', f', g'⟩ := C'
  obtain rfl : b' = b := hb
  obtain rfl : σ' = σ := hσ
  obtain rfl : f' = f := hf
  obtain rfl : g' = g := hg
  refine { h with jump_rep := ?_ }
  filter_upwards [h.jump_rep, hh] with s hs hs'
  filter_upwards [hs, hs'] with ω hω hω'
  rw [hω']
  exact hω

/-- **Solutions in the sense of the paper under a change of the jump coefficient along the
solution.** If `C, C'` have the same `b, σ, f, g`, and `C'.h = C.h` at `(s, Θ⁻_s(ω), μ⁻_s)` for
almost every `s ∈ [0, T]`, almost surely, then `(X, Y, Z, U)` with the representative `γ` is a
solution of (1.1) with coefficients `C` in the sense of the paper if and only if it is one with
coefficients `C'`. -/
theorem paperSolution_iff_of_h_ae_eq (hb : C'.b = C.b) (hσ : C'.σ = C.σ) (hf : C'.f = C.f)
    (hg : C'.g = C.g)
    (hh : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P,
      C'.h s (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s ω)
          (lawP2 P (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s))
        = C.h s (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s ω)
          (lawP2 P (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s))) :
    PaperSolution D ℱ hℱW hℱN T C ξ₀ X Y Z U γ ↔ PaperSolution D ℱ hℱW hℱN T C' ξ₀ X Y Z U γ :=
  ⟨PaperSolution.of_h_ae_eq hb hσ hf hg hh,
    PaperSolution.of_h_ae_eq hb.symm hσ.symm hf.symm hg.symm
      (hh.mono fun _ hs => hs.mono fun _ hω => hω.symm)⟩

end Dissertation.WellPosedness.System

namespace Dissertation.WellPosedness.Existence

open Dissertation.WellPosedness.System LevyStochCalc

universe u v w

/-! ### The interaction strength of the exposure-sensitive dealer market -/

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n d : ℕ} {β₁ β₂ ε : ℝ}
  {σc : EuclideanSpace ℝ (Fin n × Fin d)} {hc : Lp (EuclideanSpace ℝ (Fin n)) 2 ν}
  {hx : Lp ℝ 2 ν}

omit [MeasurableSpace Ω] in
/-- **The interaction strength enters only through the crowding correction**: the jump
coefficient of the exposure-sensitive dealer system at strength `ε` is the one at `ε = 0` minus
the crowding correction, `h^ε(t, θ, μ) = h^0(t, θ, μ) − ε A_{μ^U}(u)`. -/
theorem dealerExpCoeffs_h_eq_sub (t : ℝ) (θ : TupleH ν n n d) (μ : P2 (TupleH ν n n d)) :
    (dealerExpCoeffs β₁ β₂ σc hc hx ε).h t θ μ
      = (dealerExpCoeffs β₁ β₂ σc hc hx 0).h t θ μ - ε • crowdOp μ.margU.law θ.2.2.2 := by
  rw [dealerExpCoeffs_h, dealerExpCoeffs_h, zero_smul, sub_zero]

omit [MeasurableSpace Ω] in
/-- The jump coefficients of the exposure-sensitive dealer system at strength `ε` and at `ε = 0`
agree at `(t, θ, μ)` exactly when the crowding correction `ε A_{μ^U}(u)` vanishes there. -/
theorem dealerExpCoeffs_h_eq_iff (t : ℝ) (θ : TupleH ν n n d) (μ : P2 (TupleH ν n n d)) :
    (dealerExpCoeffs β₁ β₂ σc hc hx ε).h t θ μ = (dealerExpCoeffs β₁ β₂ σc hc hx 0).h t θ μ
      ↔ ε • crowdOp μ.margU.law θ.2.2.2 = 0 := by
  rw [dealerExpCoeffs_h_eq_sub, sub_eq_self]

variable {P : Measure Ω} [IsProbabilityMeasure P]
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {T : ℝ} {ξ₀ : Fin n → Ω → ℝ}
  {X : Fin n → ℝ → Ω → ℝ} {Y : Fin n → ℝ → Ω → ℝ} {Z : Fin n → ℝ → Ω → Fin d → ℝ}
  {U : Fin n → ℝ → Ω → E → ℝ} {γ : Fin n → ℝ → Ω → E → ℝ}

/-- **The exposure-sensitive dealer system along a tuple without crowding correction, for
solutions in the sense of the paper.** If `ε A_{μ⁻_s^U}(U_s) = 0` for almost every
`s ∈ [0, T]`, almost surely, with `U_s` the jump channel of the predictable tuple `Θ⁻_s` and
`μ⁻_s^U` the `U`-marginal of its law, then `(X, Y, Z, U)` with the representative `γ` is a
solution of (1.1) in the sense of the paper for the exposure-sensitive dealer system at strength
`ε` if and only if it is one at `ε = 0`. -/
theorem paperSolution_dealerExp_iff
    (hA : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P,
      ε • crowdOp (lawP2 P (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s)).margU.law
        (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s ω).2.2.2 = 0) :
    PaperSolution D ℱ hℱW hℱN T (dealerExpCoeffs β₁ β₂ σc hc hx ε) ξ₀ X Y Z U γ
      ↔ PaperSolution D ℱ hℱW hℱN T (dealerExpCoeffs β₁ β₂ σc hc hx 0) ξ₀ X Y Z U γ :=
  paperSolution_iff_of_h_ae_eq (C := dealerExpCoeffs β₁ β₂ σc hc hx ε)
    (C' := dealerExpCoeffs β₁ β₂ σc hc hx 0) rfl rfl rfl rfl
    (hA.mono fun _ hs => hs.mono fun _ hω => ((dealerExpCoeffs_h_eq_iff _ _ _).mpr hω).symm)

end Dissertation.WellPosedness.Existence
