/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.System.Coefficients

/-!
# Perturbed coefficient systems

Corollary 3.6 of the well-posedness paper perturbs a baseline coefficient system
`(b₀, σ₀, h₀, f₀, g)` by interior perturbations `(p_b, p_σ, p_h, p_f)` into

`(b, σ, h, f, g) = (b₀ + p_b, σ₀ + p_σ, h₀ + p_h, f₀ + p_f, g)`,

with the terminal function unchanged. A perturbation is recorded as a coefficient system `p`
whose terminal function is not used. Along two inputs `(θ, μ)`, `(θ', μ')` at time `t` every
coefficient difference splits, `δψ = δψ₀ + δp_ψ` for `ψ ∈ {b, σ, h, f}`, while the tuple
differences are shared. So the interior pairing of (2.7) splits into a baseline bracket and a
perturbation bracket,

`⟨δb, Gᵀ δY⟩ + ⟨δσ, Gᵀ δZ⟩_F − ⟨δf, G δX⟩ + ⟨δh, Gᵀ δU⟩_{L²(ν)}`
`  = [⟨δb₀, Gᵀ δY⟩ + … + ⟨δh₀, Gᵀ δU⟩] + [⟨δp_b, Gᵀ δY⟩ + … + ⟨δp_h, Gᵀ δU⟩]`,

and the right-hand side of (2.7), a function of the tuple differences alone, is that of the
baseline.

The perturbations of the second half of Corollary 3.6 are independent of the tuple: their four
interior coefficients depend on time and the law only (`Coeffs.TupleIndep`). `Coeffs.ofLaw` builds
such a perturbation from four functions of time and law.

## Main definitions

* `Coeffs.perturb` — the perturbed system `(b₀ + p_b, σ₀ + p_σ, h₀ + p_h, f₀ + p_f, g)`.
* `Coeffs.TupleIndep` — the interior coefficients do not depend on the tuple.
* `Coeffs.ofLaw` — the coefficient system of four functions of time and law, with terminal
  function `0`.

## Main statements

* `interiorPairing_diagDiff_perturb` — the interior pairing splits into the baseline and the
  perturbation brackets.
* `dissipation_diagDiff_perturb` — the right-hand side of (2.7) is that of the baseline.
* `Coeffs.tupleIndep_ofLaw` — `Coeffs.ofLaw` is independent of the tuple.
-/

open MeasureTheory Dissertation.Law

namespace Dissertation.WellPosedness.System

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} {n m d : ℕ}

/-- The perturbed coefficient system `(b₀ + p_b, σ₀ + p_σ, h₀ + p_h, f₀ + p_f, g)` of the
baseline `C = (b₀, σ₀, h₀, f₀, g)` by the interior coefficients of `p`; the terminal function is
that of the baseline. -/
noncomputable def Coeffs.perturb (C p : Coeffs ν n m d) : Coeffs ν n m d where
  b t θ μ := C.b t θ μ + p.b t θ μ
  σ t θ μ := C.σ t θ μ + p.σ t θ μ
  h t θ μ := C.h t θ μ + p.h t θ μ
  f t θ μ := C.f t θ μ + p.f t θ μ
  g := C.g

/-- **The interior pairing of a perturbed system splits** into the baseline bracket and the
perturbation bracket, for any three coupling operators. -/
theorem interiorPairing_diagDiff_perturb
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (AZ : EuclideanSpace ℝ (Fin n × Fin d) →L[ℝ] EuclideanSpace ℝ (Fin m × Fin d))
    (AU : Lp (EuclideanSpace ℝ (Fin n)) 2 ν →L[ℝ] Lp (EuclideanSpace ℝ (Fin m)) 2 ν)
    (C p : Coeffs ν n m d) (t : ℝ) (θ θ' : TupleH ν n m d) (μ μ' : P2 (TupleH ν n m d)) :
    interiorPairing A AZ AU (diagDiff (C.perturb p) t θ θ' μ μ')
      = interiorPairing A AZ AU (diagDiff C t θ θ' μ μ')
        + interiorPairing A AZ AU (diagDiff p t θ θ' μ μ') := by
  simp only [interiorPairing, diagDiff, Coeffs.perturb, add_sub_add_comm, inner_add_left,
    neg_add, inner_neg_left]
  ring

/-- **The right-hand side of (2.7) for a perturbed system** is that of the baseline: it depends
on the tuple differences alone. -/
theorem dissipation_diagDiff_perturb
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (AZ : EuclideanSpace ℝ (Fin n × Fin d) →L[ℝ] EuclideanSpace ℝ (Fin m × Fin d))
    (AU : Lp (EuclideanSpace ℝ (Fin n)) 2 ν →L[ℝ] Lp (EuclideanSpace ℝ (Fin m)) 2 ν)
    (β₁ β₂ : ℝ) (C p : Coeffs ν n m d) (t : ℝ) (θ θ' : TupleH ν n m d)
    (μ μ' : P2 (TupleH ν n m d)) :
    dissipation A AZ AU β₁ β₂ (diagDiff (C.perturb p) t θ θ' μ μ')
      = dissipation A AZ AU β₁ β₂ (diagDiff C t θ θ' μ μ') :=
  rfl

/-- The interior coefficients of `p` do not depend on the tuple:
`p_ψ(t, θ, μ) = p_ψ(t, θ', μ)` for `ψ ∈ {b, σ, h, f}`. -/
structure Coeffs.TupleIndep (p : Coeffs ν n m d) : Prop where
  /-- `p_b` does not depend on the tuple. -/
  b : ∀ t θ θ' μ, p.b t θ μ = p.b t θ' μ
  /-- `p_σ` does not depend on the tuple. -/
  σ : ∀ t θ θ' μ, p.σ t θ μ = p.σ t θ' μ
  /-- `p_h` does not depend on the tuple. -/
  h : ∀ t θ θ' μ, p.h t θ μ = p.h t θ' μ
  /-- `p_f` does not depend on the tuple. -/
  f : ∀ t θ θ' μ, p.f t θ μ = p.f t θ' μ

/-- The coefficient system `(p_b(t, μ), p_σ(t, μ), p_h(t, μ), p_f(t, μ), 0)` of four functions
of time and law. -/
noncomputable def Coeffs.ofLaw (pb : ℝ → P2 (TupleH ν n m d) → EuclideanSpace ℝ (Fin n))
    (pσ : ℝ → P2 (TupleH ν n m d) → EuclideanSpace ℝ (Fin n × Fin d))
    (ph : ℝ → P2 (TupleH ν n m d) → Lp (EuclideanSpace ℝ (Fin n)) 2 ν)
    (pf : ℝ → P2 (TupleH ν n m d) → EuclideanSpace ℝ (Fin m)) : Coeffs ν n m d where
  b t _ μ := pb t μ
  σ t _ μ := pσ t μ
  h t _ μ := ph t μ
  f t _ μ := pf t μ
  g _ _ := 0

/-- A coefficient system of time and law is independent of the tuple. -/
theorem Coeffs.tupleIndep_ofLaw (pb : ℝ → P2 (TupleH ν n m d) → EuclideanSpace ℝ (Fin n))
    (pσ : ℝ → P2 (TupleH ν n m d) → EuclideanSpace ℝ (Fin n × Fin d))
    (ph : ℝ → P2 (TupleH ν n m d) → Lp (EuclideanSpace ℝ (Fin n)) 2 ν)
    (pf : ℝ → P2 (TupleH ν n m d) → EuclideanSpace ℝ (Fin m)) :
    (Coeffs.ofLaw pb pσ ph pf).TupleIndep :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

end Dissertation.WellPosedness.System
