/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.PaperSpec.A.Sec3
import Dissertation.PaperSpec.A.Sec2Remarks

/-!
# Remark 3.7 of the well-posedness paper: general rank

Statement and equation numbers refer to the well-posedness paper at `f598204`, in the standing
setting of §2. Corollary 3.6 is stated for `m = n` with the margin and the pairing bound (3.4)
recorded in the unweighted quantity `|δX|² + |δY|² + |δZ|²_F + ‖δU‖²_{L²(ν)}`. Remark 3.7: with
both recorded in the weighted quantity `|Gᵀ δY|² + |Gᵀ δZ|²_F + ‖Gᵀ δU‖²_{L²(ν)} + |G δX|²` of
(2.12), the conclusion of Corollary 3.6 holds for arbitrary `m, n`.

## Main definitions

* `Dissertation.PaperSpec.A.PairingBound34W` — (3.4) in the weighted quantity of (2.12).
* `Dissertation.PaperSpec.A.rem_generalrank` — the assumptions of the perturbed system.
* `Dissertation.PaperSpec.A.rem_generalrank_wp` — its well-posedness.
-/

open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal Matrix

namespace Dissertation.PaperSpec.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence
  Dissertation.WellPosedness.Enlarged Dissertation.WellPosedness.Stability
  Dissertation.WellPosedness.Spec

universe u v w

/-- **(3.4) in the weighted quantity of (2.12)**, the pairing bound of the perturbation `p` with
the constant `c`: for almost every `t ∈ [0, T]` and all `(Θ, μ), (Θ', μ') ∈ 𝒟_t`, the
expectation of the pairing of the perturbation differences exists and is at most
`c 𝔼[|Gᵀ δY|² + |Gᵀ δZ|²_F + ‖Gᵀ δU‖²_{L²(ν)} + |G δX|²]`. -/
def PairingBound34W {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E]
    {ν : Measure E} [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (P : Measure Ω) [IsProbabilityMeasure P]
    (T : ℝ) (G : Matrix (Fin m) (Fin n) ℝ) (c : ℝ) (p : Coeffs ν n m d) : Prop :=
  ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
    ∀ q ∈ diagonalInputs ν n m d ℱ P t, ∀ q' ∈ diagonalInputs ν n m d ℱ P t,
      Integrable (fun ω => pairing27 G p t (q.1 ω) (q'.1 ω) q.2 q'.2) P
        ∧ ∫ ω, pairing27 G p t (q.1 ω) (q'.1 ω) q.2 q'.2 ∂P
          ≤ c * ∫ ω, (‖GX Gᵀ ((q.1 ω).2.1 - (q'.1 ω).2.1)‖ ^ 2
              + ‖GZ Gᵀ ((q.1 ω).2.2.1 - (q'.1 ω).2.2.1)‖ ^ 2
              + ‖GU Gᵀ ν ((q.1 ω).2.2.2 - (q'.1 ω).2.2.2)‖ ^ 2
              + ‖GX G ((q.1 ω).1 - (q'.1 ω).1)‖ ^ 2) ∂P

/-- Remark 3.7, the assumptions of the perturbed system. In the standing setting with
`n, m, d ≥ 1`, for every horizon `T > 0`, let the baseline system `C` with initial datum `ξ₀`
satisfy (2.3) and Assumptions 2.2–2.5 with constants `L₀, α, β₁, β₂` and coupling matrix
`G ∈ ℝ^{m×n}`, and the weighted margin (2.12) with `c_diss > 0`; let the perturbation `p` satisfy
the origin values of Assumption 2.2, the interior bound of Assumption 2.3 with a constant
`L_p ≥ 0`, and (3.4) in the weighted quantity of (2.12) with a constant `c_pert ≥ 0`; let the
perturbed system satisfy (2.3); and let `c_pert < c_diss`. Then the perturbed system with initial
datum `ξ₀` satisfies Assumptions 2.2–2.5 with the same `G, α, β₁, β₂` and some Lipschitz
constant, and (2.12) with the margin `c_diss − c_pert`. -/
def rem_generalrank : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (_ : Indep 𝒢₀ (⨆ t, D.filtration t) P),
    0 < n → 0 < m → 0 < d → ∀ T : ℝ, 0 < T →
    ∀ (L₀ Lₚ α β₁ β₂ cdiss cpert : ℝ) (G : Matrix (Fin m) (Fin n) ℝ) (C p : Coeffs ν n m d)
      (ξ₀ : Ω → EuclideanSpace ℝ (Fin n)),
    JointBorel T C → Assumption22 (enlJoint 𝒢₀ D h𝒢₀) P T C ξ₀ →
    Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L₀ C → G.rank = min m n →
    Assumption25 (enlJoint 𝒢₀ D h𝒢₀) P T G α β₁ β₂ C →
    Margin212 (enlJoint 𝒢₀ D h𝒢₀) P T G β₁ β₂ cdiss C → 0 < cdiss →
    OriginValues T p → LipInterior (enlJoint 𝒢₀ D h𝒢₀) P T Lₚ p → 0 ≤ Lₚ →
    PairingBound34W (enlJoint 𝒢₀ D h𝒢₀) P T G cpert p → 0 ≤ cpert →
    JointBorel T (C.perturb p) → cpert < cdiss →
    Assumption22 (enlJoint 𝒢₀ D h𝒢₀) P T (C.perturb p) ξ₀
      ∧ (∃ L : ℝ, Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L (C.perturb p)) ∧ G.rank = min m n
      ∧ Assumption25 (enlJoint 𝒢₀ D h𝒢₀) P T G α β₁ β₂ (C.perturb p)
      ∧ Margin212 (enlJoint 𝒢₀ D h𝒢₀) P T G β₁ β₂ (cdiss - cpert) (C.perturb p)

/-- Remark 3.7, well-posedness of the perturbed system. There is a function `C_stab` of
`(T, L, ‖G‖, c_G, α, β₁, β₂)` such that: under the hypotheses of `rem_generalrank`, the
perturbed system with initial datum `ξ₀` has a solution in `ℍ`; any two tuples of `ℍ_weak`
satisfying it with the same initial datum are equal in `ℍ_weak`; and for every constant `L` with
which the perturbed system satisfies Assumption 2.3, (3.1) holds with the constant
`C_stab(T, L, ‖G‖, s_min(G)⁻², α, β₁, β₂)` for its solutions against the solutions of every
system `2` satisfying (2.3) and Assumptions 2.2–2.3. -/
def rem_generalrank_wp : Prop :=
  ∃ Cstab : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ,
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P),
    0 < n → 0 < m → 0 < d → ∀ T : ℝ, 0 < T →
    ∀ (L₀ Lₚ α β₁ β₂ cdiss cpert : ℝ) (G : Matrix (Fin m) (Fin n) ℝ) (C p : Coeffs ν n m d)
      (ξ₀ : Ω → EuclideanSpace ℝ (Fin n)),
    JointBorel T C → Assumption22 (enlJoint 𝒢₀ D h𝒢₀) P T C ξ₀ →
    Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L₀ C → G.rank = min m n →
    Assumption25 (enlJoint 𝒢₀ D h𝒢₀) P T G α β₁ β₂ C →
    Margin212 (enlJoint 𝒢₀ D h𝒢₀) P T G β₁ β₂ cdiss C → 0 < cdiss →
    OriginValues T p → LipInterior (enlJoint 𝒢₀ D h𝒢₀) P T Lₚ p → 0 ≤ Lₚ →
    PairingBound34W (enlJoint 𝒢₀ D h𝒢₀) P T G cpert p → 0 ≤ cpert →
    JointBorel T (C.perturb p) → cpert < cdiss →
    (∃ (X : Fin n → ℝ → Ω → ℝ) (Y : Fin m → ℝ → Ω → ℝ) (Z : Fin m → ℝ → Ω → Fin d → ℝ)
      (U : Fin m → ℝ → Ω → E → ℝ), Solution D h𝒢₀ hind₀ T (C.perturb p) ξ₀ X Y Z U)
    ∧ (∀ (X₁ X₂ : Fin n → ℝ → Ω → ℝ) (Y₁ Y₂ : Fin m → ℝ → Ω → ℝ)
        (Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ) (U₁ U₂ : Fin m → ℝ → Ω → E → ℝ),
        WeakSolution D h𝒢₀ hind₀ T (C.perturb p) ξ₀ X₁ Y₁ Z₁ U₁ →
        WeakSolution D h𝒢₀ hind₀ T (C.perturb p) ξ₀ X₂ Y₂ Z₂ U₂ →
        (∀ i, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, X₁ i t ω = X₂ i t ω)
          ∧ (∀ k, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, Y₁ k t ω = Y₂ k t ω)
          ∧ (∀ k j, LevyStochCalc.Brownian.Ito.energy P T
              (fun ω s => Z₁ k s ω j - Z₂ k s ω j) = 0)
          ∧ ∀ k, LevyStochCalc.Poisson.Compensated.markedEnergy P ν T
              (fun ω s e => U₁ k s ω e - U₂ k s ω e) = 0)
    ∧ ∀ L : ℝ, Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L (C.perturb p) →
      ∀ (L₂ : ℝ) (C₂ : Coeffs ν n m d) (ξ₂ : Ω → EuclideanSpace ℝ (Fin n)),
        JointBorel T C₂ → Assumption22 (enlJoint 𝒢₀ D h𝒢₀) P T C₂ ξ₂ →
        Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L₂ C₂ →
        ∀ (X₁ X₂ : Fin n → ℝ → Ω → ℝ) (Y₁ Y₂ : Fin m → ℝ → Ω → ℝ)
          (Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ) (U₁ U₂ : Fin m → ℝ → Ω → E → ℝ),
        Solution D h𝒢₀ hind₀ T (C.perturb p) ξ₀ X₁ Y₁ Z₁ U₁ →
        Solution D h𝒢₀ hind₀ T C₂ ξ₂ X₂ Y₂ Z₂ U₂ →
        supSize P ν T (fun i t ω => X₁ i t ω - X₂ i t ω) (fun k t ω => Y₁ k t ω - Y₂ k t ω)
            (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j)
            (fun k t ω e => U₁ k t ω e - U₂ k t ω e)
          ≤ ENNReal.ofReal (Cstab T L ‖GX G‖ (sMin G ^ 2)⁻¹ α β₁ β₂)
            * dataSize P ν T (fun i ω => ξ₀ ω i - ξ₂ ω i)
              (fun i ω s => driftProc P T (C.perturb p) X₂ Y₂ Z₂ U₂ i ω s
                - driftProc P T C₂ X₂ Y₂ Z₂ U₂ i ω s)
              (fun i s ω j => diffusionProc P T (C.perturb p) X₂ Y₂ Z₂ U₂ i s ω j
                - diffusionProc P T C₂ X₂ Y₂ Z₂ U₂ i s ω j)
              (fun i s ω e =>
                jumpProc T (coeffJump P T (C.perturb p) (leftLimProc X₂) (leftLimProc Y₂) Z₂ U₂)
                  i s ω e
                - jumpProc T (coeffJump P T C₂ (leftLimProc X₂) (leftLimProc Y₂) Z₂ U₂) i s ω e)
              (fun k ω s => driverProc P T (C.perturb p) X₂ Y₂ Z₂ U₂ k ω s
                - driverProc P T C₂ X₂ Y₂ Z₂ U₂ k ω s)
              (fun k ω => terminalVal P T (C.perturb p) X₂ k ω - terminalVal P T C₂ X₂ k ω)

end Dissertation.PaperSpec.A
