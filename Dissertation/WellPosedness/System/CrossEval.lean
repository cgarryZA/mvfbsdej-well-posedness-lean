/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.System.Perturbation

/-!
# A solution of one system as a forced solution of another

Theorem 3.1 of the well-posedness paper compares solutions of two coefficient systems
`C¹ = (b¹, σ¹, h¹, f¹, g¹)` and `C² = (b², σ², h², f², g²)`. Its proof reads a solution `Θ²` of
(1.1) for `C²` as a solution of the `λ`-forced system (4.1) for `C¹` at `λ = 1`, with forcing

`q^ψ = ψ²(s, Θ²_s, μ²_s) − ψ¹(s, Θ²_s, μ²_s)` (`ψ ∈ {b, σ, h, f}`),
`q^g_T = g²(X²_T, Law X²_T) − g¹(X²_T, Law X²_T)`,

the negated coefficient differences evaluated along solution 2: the equations of `Θ²` are linear
in their integrands, and `1 · ψ¹ + q^ψ = ψ²`.

That `q` is a forcing needs the coefficients of system 1 evaluated along solution 2 to be
measurable and square integrable. The terminal term is a function of `X²_T` alone, measurable
once `g¹` and `g²` are Borel measurable in the state, as the paper's standing joint measurability
of the coefficients gives. The interior terms are processes, whose joint and progressive
measurability — (2.5) for a cross-evaluation — the paper derives from Lemma A.1; `CrossEval`
takes it as a hypothesis, with a jointly measurable, marked progressively measurable
representative `γ` of `e ↦ h¹(s, Θ²_s, e, μ²_s)` in `L²(ν)`. It holds along every progressive
tuple, with a canonical `γ`, when the coefficients of system 1 are jointly measurable with the
evaluation σ-algebra on `P₂(H)` (`CoeffBorel.crossEval`). Given measurability, `q` is square
integrable exactly when the coefficient-difference terms of the right-hand side of (3.1) are
finite.

## Main definitions

* `CrossEval` — the coefficient processes of one system along a tuple are jointly and
  progressively measurable, with a representative of its jump coefficient.

## Main statements

* `stronglyMeasurable_terminalVal` — the terminal value is measurable when `g` is Borel
  measurable in the state.
* `energy_sub_comm`, `markedEnergy_sub_comm` — the energy of `a − b` is that of `b − a`.
* `Solves.solvesForced_of_crossEval` — a solution of system 2 is a forced solution of system 1.
-/

open MeasureTheory Filter Dissertation.Law
open scoped NNReal ENNReal

namespace Dissertation.WellPosedness.System

open Dissertation.WellPosedness.BrownianPoisson Dissertation.WellPosedness.Stability

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  {n m d : ℕ}

/-! ### Auxiliary facts -/

section Aux

variable {P : Measure Ω} {T : ℝ}

/-- The energy of `a − b` is the energy of `b − a`. -/
theorem energy_sub_comm (a b : Ω → ℝ → ℝ) :
    LevyStochCalc.Brownian.Ito.energy P T (fun ω s => a ω s - b ω s)
      = LevyStochCalc.Brownian.Ito.energy P T (fun ω s => b ω s - a ω s) := by
  unfold LevyStochCalc.Brownian.Ito.energy
  refine lintegral_congr fun ω => lintegral_congr fun s => ?_
  rw [← nnnorm_neg, neg_sub]

/-- The marked energy of `a − b` is the marked energy of `b − a`. -/
theorem markedEnergy_sub_comm (a b : Ω → ℝ → E → ℝ) :
    LevyStochCalc.Poisson.Compensated.markedEnergy P ν T (fun ω s e => a ω s e - b ω s e)
      = LevyStochCalc.Poisson.Compensated.markedEnergy P ν T (fun ω s e => b ω s e - a ω s e) := by
  unfold LevyStochCalc.Poisson.Compensated.markedEnergy
  refine lintegral_congr fun ω => lintegral_congr fun s => lintegral_congr fun e => ?_
  rw [← nnnorm_neg, neg_sub]

variable [IsProbabilityMeasure P] [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]

/-- **The terminal value is measurable** when `g` is Borel measurable in the state: for
`X_T` measurable for the time-`T` field of a filtration, so is `ω ↦ g(X_T(ω), Law X_T)`,
coordinatewise. -/
theorem stronglyMeasurable_terminalVal {C : Coeffs ν n m d}
    (hg : ∀ ρ, Measurable fun x => C.g x ρ) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {X : Fin n → ℝ → Ω → ℝ} (hX : ∀ i, Measurable[ℱ T] (X i T)) (k : Fin m) :
    StronglyMeasurable[ℱ T] (terminalVal P T C X k) :=
  (((EuclideanSpace.proj k : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ).continuous.measurable.comp
    ((hg _).comp (measurable_toLp_of_forall hX))).stronglyMeasurable)

end Aux

/-! ### Cross-evaluation -/

variable [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
  {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Cross-evaluation of a coefficient system along a tuple**, (2.5) for coefficients other than
those the tuple solves: the drift, diffusion and driver processes of `C` along
`Θ = (X, Y, Z, U)` are jointly and progressively measurable, and `γ` is a jointly measurable,
marked progressively measurable representative of `e ↦ h(s, Θ_s(ω), e, μ_s)` in `L²(ν)`, at
almost every time of `[0, T]`, almost surely. -/
structure CrossEval (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (P : Measure Ω) [IsProbabilityMeasure P]
    (T : ℝ) (C : Coeffs ν n m d) (X : Fin n → ℝ → Ω → ℝ) (Y : Fin m → ℝ → Ω → ℝ)
    (Z : Fin m → ℝ → Ω → Fin d → ℝ) (U : Fin m → ℝ → Ω → E → ℝ)
    (γ : Fin n → ℝ → Ω → E → ℝ) : Prop where
  /-- `γ` represents the jump coefficient along the tuple in `L²(ν)`. -/
  jump_rep : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P,
    (fun e => (WithLp.toLp 2 fun i => γ i s ω e : EuclideanSpace ℝ (Fin n)))
      =ᵐ[ν] C.h s (tupleAt ν X Y Z U s ω) (lawP2 P (tupleAt ν X Y Z U s))
  /-- The drift process is jointly measurable. -/
  b_meas : ∀ i, Measurable (Function.uncurry (driftProc P T C X Y Z U i))
  /-- The drift process is progressively measurable. -/
  b_prog : ∀ i, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ (driftProc P T C X Y Z U i)
  /-- The diffusion process is jointly measurable. -/
  σ_meas : ∀ i j, Measurable (Function.uncurry fun ω s => diffusionProc P T C X Y Z U i s ω j)
  /-- The diffusion process is progressively measurable. -/
  σ_prog : ∀ i j, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ
    fun ω s => diffusionProc P T C X Y Z U i s ω j
  /-- The jump process is jointly measurable in the sample point, the time and the mark. -/
  h_meas : ∀ i, Measurable fun p : Ω × ℝ × E => jumpProc T γ i p.2.1 p.1 p.2.2
  /-- The jump process is marked progressively measurable. -/
  h_prog : ∀ i, LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ
    fun ω s e => jumpProc T γ i s ω e
  /-- The driver process is jointly measurable. -/
  f_meas : ∀ k, Measurable (Function.uncurry (driverProc P T C X Y Z U k))
  /-- The driver process is progressively measurable. -/
  f_prog : ∀ k, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ (driverProc P T C X Y Z U k)

variable {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {T : ℝ} {C₁ C₂ : Coeffs ν n m d}
  {ξ : Fin n → Ω → ℝ} {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ}
  {Z : Fin m → ℝ → Ω → Fin d → ℝ} {U : Fin m → ℝ → Ω → E → ℝ} {γ₁ γ₂ : Fin n → ℝ → Ω → E → ℝ}

/-- **A solution of system 2 is a forced solution of system 1.** Let `(X, Y, Z, U)` solve (1.1)
for `C²` with jump representative `γ²`, let `C¹` have the cross-evaluation along it with jump
representative `γ¹`, let `g¹, g²` be Borel measurable in the state, and let the coefficient
differences `δψ = ψ¹ − ψ²` along the solution have finite energy and `δg_T` be square
integrable. Then `(X, Y, Z, U)` solves the forced system (4.1) for `C¹` at `λ = 1` with the forcing
`−δψ`, `−δg_T`. -/
theorem Solves.solvesForced_of_crossEval (h : Solves D ℱ hℱW hℱN T C₂ ξ X Y Z U γ₂)
    (hX : CrossEval ℱ P T C₁ X Y Z U γ₁) (hg₁ : ∀ ρ, Measurable fun x => C₁.g x ρ)
    (hg₂ : ∀ ρ, Measurable fun x => C₂.g x ρ)
    (hb : ∀ i, LevyStochCalc.Brownian.Ito.energy P T
      (fun ω s => driftProc P T C₁ X Y Z U i ω s - driftProc P T C₂ X Y Z U i ω s) ≠ ⊤)
    (hσ : ∀ i j, LevyStochCalc.Brownian.Ito.energy P T
      (fun ω s => diffusionProc P T C₁ X Y Z U i s ω j - diffusionProc P T C₂ X Y Z U i s ω j)
        ≠ ⊤)
    (hh : ∀ i, LevyStochCalc.Poisson.Compensated.markedEnergy P ν T
      (fun ω s e => jumpProc T γ₁ i s ω e - jumpProc T γ₂ i s ω e) ≠ ⊤)
    (hf : ∀ k, LevyStochCalc.Brownian.Ito.energy P T
      (fun ω s => driverProc P T C₁ X Y Z U k ω s - driverProc P T C₂ X Y Z U k ω s) ≠ ⊤)
    (hg : ∀ k, ∫⁻ ω, (‖terminalVal P T C₁ X k ω - terminalVal P T C₂ X k ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≠ ⊤) :
    SolvesForced D ℱ hℱW hℱN T 1 C₁ ξ
      (fun i ω s => driftProc P T C₂ X Y Z U i ω s - driftProc P T C₁ X Y Z U i ω s)
      (fun i s ω j => diffusionProc P T C₂ X Y Z U i s ω j - diffusionProc P T C₁ X Y Z U i s ω j)
      (fun i s ω e => jumpProc T γ₂ i s ω e - jumpProc T γ₁ i s ω e)
      (fun k ω s => driverProc P T C₂ X Y Z U k ω s - driverProc P T C₁ X Y Z U k ω s)
      (fun k ω => terminalVal P T C₂ X k ω - terminalVal P T C₁ X k ω) X Y Z U γ₁ where
  forcing :=
    { qb_meas := fun i => (h.linearFSDEJ i).b_meas.sub (hX.b_meas i)
      qb_prog := fun i => (h.linearFSDEJ i).b_prog.sub (hX.b_prog i)
      qb_vanish := fun i ω s hs => by
        simp only [driftProc, Set.indicator_of_notMem hs, sub_self]
      qb_sq := fun i => by rw [energy_sub_comm]; exact hb i
      qσ_meas := fun i j => ((h.linearFSDEJ i).σ_meas j).sub (hX.σ_meas i j)
      qσ_prog := fun i j => ((h.linearFSDEJ i).σ_prog j).sub (hX.σ_prog i j)
      qσ_vanish := fun i ω s hs => by
        funext j
        simp only [diffusionProc, Set.indicator_of_notMem hs, sub_self, Pi.zero_apply]
      qσ_sq := fun i j => by rw [energy_sub_comm]; exact hσ i j
      qh_meas := fun i => (h.linearFSDEJ i).γ_meas.sub (hX.h_meas i)
      qh_prog := fun i => by
        simpa only [neg_one_mul, ← sub_eq_add_neg] using
          LevyStochCalc.Poisson.Compensated.markedProgressivelyMeasurable_add
            (h.linearFSDEJ i).γ_prog
            (LevyStochCalc.Poisson.Compensated.markedProgressivelyMeasurable_const_mul
              (hX.h_prog i) (-1))
      qh_vanish := fun i ω s e hs => by
        simp only [jumpProc, Set.indicator_of_notMem hs, sub_self]
      qh_sq := fun i => by rw [markedEnergy_sub_comm]; exact hh i
      qf_meas := fun k => (h.linearBSDEJ k).φ_meas.sub (hX.f_meas k)
      qf_prog := fun k => (h.linearBSDEJ k).φ_prog.sub (hX.f_prog k)
      qf_vanish := fun k ω s hs => by
        simp only [driverProc, Set.indicator_of_notMem hs, sub_self]
      qf_sq := fun k => by rw [energy_sub_comm]; exact hf k
      qg_meas := fun k =>
        (stronglyMeasurable_terminalVal hg₂ (fun i => (h.fwd i).X_adapted T) k).sub
          (stronglyMeasurable_terminalVal hg₁ (fun i => (h.fwd i).X_adapted T) k)
      qg_sq := fun k => by
        have hm : AEStronglyMeasurable (fun ω => terminalVal P T C₁ X k ω
            - terminalVal P T C₂ X k ω) P :=
          (((stronglyMeasurable_terminalVal hg₁ (fun i => (h.fwd i).X_adapted T) k).sub
            (stronglyMeasurable_terminalVal hg₂ (fun i => (h.fwd i).X_adapted T) k)).mono
              (ℱ.le T)).aestronglyMeasurable
        have hL := LevyStochCalc.Brownian.Ito.memLp_two_of_lintegral_sq_lt_top hm
          (lt_top_iff_ne_top.mpr (hg k))
        have he : (fun ω => terminalVal P T C₂ X k ω - terminalVal P T C₁ X k ω)
            = -fun ω => terminalVal P T C₁ X k ω - terminalVal P T C₂ X k ω :=
          funext fun ω => (neg_sub _ _).symm
        rw [he]
        exact hL.neg }
  jump_rep := hX.jump_rep
  fwd i := by
    convert h.linearFSDEJ i using 1 <;> ext <;> ring
  bwd k := by
    convert h.linearBSDEJ k using 1 <;> ext <;> ring

end Dissertation.WellPosedness.System
