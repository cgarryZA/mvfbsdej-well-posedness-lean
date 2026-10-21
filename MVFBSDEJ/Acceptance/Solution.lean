/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.PaperSpec.Setting
import MVFBSDEJ.WellPosedness.Spec.Bridge22
import MVFBSDEJ.WellPosedness.Existence.CoeffPredictable
import MVFBSDEJ.WellPosedness.Existence.PaperAdmissible

/-!
# The solutions of the well-posedness paper and those of the implementation

A solution of (1.1) in `𝕊` (`PaperSpec.Solution`) is a solution in `ℍ²` with
`𝔼 sup_{t ≤ T} |X_t|² < ∞` and `𝔼 sup_{t ≤ T} |Y_t|² < ∞`; its drift and driver integrals are
pathwise. The implementation's solutions (`MVFBSDEJ.WellPosedness.Existence.PaperSolutionEnl`,
`MVFBSDEJ.WellPosedness.System.PaperSolutionForced`) also ask the drift and driver processes to
have finite energy on `[0, T]`. Under (2.3) and Assumptions 2.2–2.3 the two notions coincide, since
the coefficient processes along a tuple of `ℍ²` then have finite energy ((4.2)).

## Main statements

* `MVFBSDEJ.Acceptance.solution_of_paperSolutionEnl`,
  `MVFBSDEJ.Acceptance.Solution.paperSolutionEnl` — the two directions for (1.1).
* `MVFBSDEJ.Acceptance.forcedSolution_of_paperSolutionForced`,
  `MVFBSDEJ.Acceptance.ForcedSolution.paperSolutionForced` — the two directions for (4.1).
-/

open MeasureTheory Filter ProbabilityTheory
open scoped Topology

namespace MVFBSDEJ.Acceptance

open MVFBSDEJ.WellPosedness.System MVFBSDEJ.WellPosedness.Existence
  MVFBSDEJ.WellPosedness.Enlarged MVFBSDEJ.WellPosedness.Spec
  MVFBSDEJ.WellPosedness.Stability LevyStochCalc

universe u v w

variable {Ω : Type u} {𝒢₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {E : Type v}
  [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
  {n m d : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {h𝒢₀ : 𝒢₀ ≤ mΩ}
  {hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P} {T L lam : ℝ} {C : Coeffs ν n m d}
  {ξ₀ : Ω → EuclideanSpace ℝ (Fin n)} {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ}
  {Z : Fin m → ℝ → Ω → Fin d → ℝ} {U : Fin m → ℝ → Ω → E → ℝ} {γ : Fin n → ℝ → Ω → E → ℝ}
  {qb : Fin n → Ω → ℝ → ℝ} {qσ : Fin n → ℝ → Ω → Fin d → ℝ} {qh : Fin n → ℝ → Ω → E → ℝ}
  {qf : Fin m → Ω → ℝ → ℝ} {qg : Fin m → Ω → ℝ}

/-- For `T ≥ 0`, a solution of (1.1) in the sense of `PaperSolutionEnl` whose every path of `X`
and of `Y` has left limits on `(0, T]` is a solution in `𝕊`. -/
theorem solution_of_paperSolutionEnl (hT : 0 ≤ T)
    (h : PaperSolutionEnl D h𝒢₀ hind₀ T C (fun i ω => ξ₀ ω i) X Y Z U γ)
    (hX : ∀ i ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => X i s ω) (𝓝[<] t) (𝓝 l))
    (hY : ∀ k ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => Y k s ω) (𝓝[<] t) (𝓝 l)) :
    PaperSpec.Solution D h𝒢₀ hind₀ T C ξ₀ X Y Z U :=
  ⟨⟨⟨γ, h.toWeakInt hT⟩, hX, hY⟩, h.X_sup, h.Y_sup⟩

/-- For `T ≥ 0` and coefficients with (2.3), the origin bounds of Assumption 2.2 and Assumption 2.3
with a constant `L`, a solution of (1.1) in `𝕊` is a solution in the sense of `PaperSolutionEnl`
whose every path of `X` and of `Y` has left limits on `(0, T]`. -/
theorem Solution.paperSolutionEnl (hT : 0 ≤ T) (hJ : JointBorel T C) (horig : OriginValues T C)
    (h23 : Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L C)
    (h : PaperSpec.Solution D h𝒢₀ hind₀ T C ξ₀ X Y Z U) :
    (∃ γ : Fin n → ℝ → Ω → E → ℝ,
        PaperSolutionEnl D h𝒢₀ hind₀ T C (fun i ω => ξ₀ ω i) X Y Z U γ)
      ∧ (∀ i ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => X i s ω) (𝓝[<] t) (𝓝 l))
      ∧ ∀ k ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => Y k s ω) (𝓝[<] t) (𝓝 l) := by
  obtain ⟨⟨⟨γ, hw⟩, hXl, hYl⟩, hXs, hYs⟩ := h
  obtain ⟨γ', hadm⟩ := hw.toPaperWeakTuple.exists_paperAdmissible hT (hJ.coeffRegular _ P)
    (originValues_iff_coeffOrigin.mp horig) h23.interior.diagonalLipschitz_two_mul
  have hpw : PaperWeakSolution D (enlJoint 𝒢₀ D h𝒢₀) (isBrownianFiltration_enlJoint D h𝒢₀ hind₀)
      (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) T C (fun i ω => ξ₀ ω i) X Y Z U γ :=
    { toPaperWeakTuple := hw.toPaperWeakTuple
      toPaperAdmissible := { hw.toPaperAdmissibleInt with b_sq := hadm.b_sq, f_sq := hadm.f_sq }
      fwd := hw.fwd
      bwd := hw.bwd }
  exact ⟨⟨γ, hpw.paperSolution hXs hYs⟩, hXl, hYl⟩

/-- For `T ≥ 0`, a solution of the `λ`-forced system (4.1) in the sense of `PaperSolutionForced`
is one in `ℍ²` with `X_T` square integrable. -/
theorem paperWeakSolutionForcedInt_of_paperSolutionForced (hT : 0 ≤ T)
    (h : PaperSolutionForced D (enlJoint 𝒢₀ D h𝒢₀) (isBrownianFiltration_enlJoint D h𝒢₀ hind₀)
      (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) T lam C (fun i ω => ξ₀ ω i) qb qσ qh qf qg
      X Y Z U γ) :
    PaperWeakSolutionForcedInt D (enlJoint 𝒢₀ D h𝒢₀) (isBrownianFiltration_enlJoint D h𝒢₀ hind₀)
      (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) T lam C (fun i ω => ξ₀ ω i) qb qσ qh qf qg
      X Y Z U γ where
  toPaperWeakTuple := h.toPaperWeakTuple
  forcing := h.forcing
  b_meas := h.b_meas
  b_prog := h.b_prog
  b_int i := BSDEJ.Solves.ae_mem_integrablePaths (h.b_meas i) (h.b_sq i)
  σ_meas := h.σ_meas
  σ_prog := h.σ_prog
  σ_sq := h.σ_sq
  γ_meas := h.γ_meas
  γ_prog := h.γ_prog
  γ_sq := h.γ_sq
  f_meas := h.f_meas
  f_prog := h.f_prog
  f_int k := BSDEJ.Solves.ae_mem_integrablePaths (h.f_meas k) (h.f_sq k)
  jump_rep := h.jump_rep
  XT_sq i := memLp_of_lintegral_biSup_esq_lt_top h.X_sup ⟨hT, le_rfl⟩ i
    ((h.X_adapted i T ⟨hT, le_rfl⟩).mono ((enlJoint 𝒢₀ D h𝒢₀).le T) le_rfl).aestronglyMeasurable
  fwd := h.fwd
  bwd := h.bwd

/-- For `T ≥ 0`, a solution of the `λ`-forced system (4.1) in the sense of `PaperSolutionForced`
whose every path of `X` and of `Y` has left limits on `(0, T]` is a solution in `𝕊`. -/
theorem forcedSolution_of_paperSolutionForced (hT : 0 ≤ T)
    (h : PaperSolutionForced D (enlJoint 𝒢₀ D h𝒢₀) (isBrownianFiltration_enlJoint D h𝒢₀ hind₀)
      (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) T lam C (fun i ω => ξ₀ ω i) qb qσ qh qf qg
      X Y Z U γ)
    (hX : ∀ i ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => X i s ω) (𝓝[<] t) (𝓝 l))
    (hY : ∀ k ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => Y k s ω) (𝓝[<] t) (𝓝 l)) :
    PaperSpec.ForcedSolution D h𝒢₀ hind₀ T lam C ξ₀ qb qσ qh qf qg X Y Z U :=
  ⟨⟨⟨γ, paperWeakSolutionForcedInt_of_paperSolutionForced (hind₀ := hind₀) hT h⟩, hX, hY⟩, h.X_sup,
    h.Y_sup⟩

/-- For `T ≥ 0` and coefficients with (2.3), the origin bounds of Assumption 2.2 and Assumption 2.3
with a constant `L`, a solution of the `λ`-forced system (4.1) in `𝕊` is a solution in the sense of
`PaperSolutionForced` whose every path of `X` and of `Y` has left limits on `(0, T]`. -/
theorem ForcedSolution.paperSolutionForced (hT : 0 ≤ T) (hJ : JointBorel T C)
    (horig : OriginValues T C)
    (h23 : Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L C)
    (h : PaperSpec.ForcedSolution D h𝒢₀ hind₀ T lam C ξ₀ qb qσ qh qf qg X Y Z U) :
    (∃ γ : Fin n → ℝ → Ω → E → ℝ,
        PaperSolutionForced D (enlJoint 𝒢₀ D h𝒢₀) (isBrownianFiltration_enlJoint D h𝒢₀ hind₀)
          (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) T lam C (fun i ω => ξ₀ ω i) qb qσ qh qf qg
          X Y Z U γ)
      ∧ (∀ i ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => X i s ω) (𝓝[<] t) (𝓝 l))
      ∧ ∀ k ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => Y k s ω) (𝓝[<] t) (𝓝 l) := by
  obtain ⟨⟨⟨γ, hw⟩, hXl, hYl⟩, hXs, hYs⟩ := h
  obtain ⟨γ', hadm⟩ := hw.toPaperWeakTuple.exists_paperAdmissible hT (hJ.coeffRegular _ P)
    (originValues_iff_coeffOrigin.mp horig) h23.interior.diagonalLipschitz_two_mul
  refine ⟨⟨γ, ?_⟩, hXl, hYl⟩
  exact
    { forcing := hw.forcing
      X_adapted := hw.X_adapted
      X_rightCont := hw.X_rightCont
      X_leftLim := hw.X_leftLim
      X_sup := hXs
      Y_adapted := hw.Y_adapted
      Y_rightCont := hw.Y_rightCont
      Y_leftLim := hw.Y_leftLim
      Y_sup := hYs
      Z_pred := hw.Z_pred
      Z_vanish := hw.Z_vanish
      Z_sq := hw.Z_sq
      U_pred := hw.U_pred
      U_vanish := hw.U_vanish
      U_sq := hw.U_sq
      b_meas := hw.b_meas
      b_prog := hw.b_prog
      b_sq := fun i => Brownian.Ito.energy_add_ne_top ((hadm.b_meas i).const_mul lam)
        (hw.forcing.qb_meas i) (Brownian.Ito.energy_const_mul_ne_top (hadm.b_meas i)
          (hadm.b_sq i) lam) (hw.forcing.qb_sq i)
      σ_meas := hw.σ_meas
      σ_prog := hw.σ_prog
      σ_sq := hw.σ_sq
      γ_meas := hw.γ_meas
      γ_prog := hw.γ_prog
      γ_sq := hw.γ_sq
      f_meas := hw.f_meas
      f_prog := hw.f_prog
      f_sq := fun k => Brownian.Ito.energy_add_ne_top ((hadm.f_meas k).const_mul lam)
        (hw.forcing.qf_meas k) (Brownian.Ito.energy_const_mul_ne_top (hadm.f_meas k)
          (hadm.f_sq k) lam) (hw.forcing.qf_sq k)
      jump_rep := hw.jump_rep
      fwd := hw.fwd
      bwd := hw.bwd }

end MVFBSDEJ.Acceptance
