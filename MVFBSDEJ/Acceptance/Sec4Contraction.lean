/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.PaperSpec.Sec4Contraction
import MVFBSDEJ.Acceptance.Sec4Frozen
import MVFBSDEJ.Acceptance.Sec4Small
import MVFBSDEJ.WellPosedness.System.FrozenDifference

/-!
# The contraction chain in the proof of Lemma 4.2: proofs

Statement and equation numbers refer to the well-posedness paper at `1f67672`.

* (4.10): along each trial the integrals of (1.1) exist with the canonical representative
  `MVFBSDEJ.WellPosedness.Existence.coeffJump` of the jump coefficient at the tuple, which also
  represents it at the predictable tuple
  (`MVFBSDEJ.WellPosedness.System.PaperWeakTuple.paperAdmissible_coeffJump`), so the frozen
  forward equation (4.7) holds with the jump integrand `λ coeffJump + q^h`
  (`MVFBSDEJ.WellPosedness.System.ae_forcedJump_eq_of_rep`,
  `MVFBSDEJ.WellPosedness.Stability.LinearFSDEJ.congr_jump`). The difference of the two forward
  equations is the linear forward equation from `0` with integrands `λ δb, λ δσ, λ δh`
  (`MVFBSDEJ.WellPosedness.Stability.LinearFSDEJ.sub`); its running supremum is bounded by those
  of its three legs
  (`MVFBSDEJ.WellPosedness.Stability.LinearFSDEJ.lintegral_biSup_esq_le_legs`), Cauchy–Schwarz
  bounds the drift leg (`MVFBSDEJ.WellPosedness.System.lintegral_sq_lintegral_toLp_le`) and
  Doob's inequality with the isometries the two stochastic legs, with the constant `4 ≤ c`
  (`MVFBSDEJ.WellPosedness.System.lintegral_biSup_esq_brownian_le`,
  `MVFBSDEJ.WellPosedness.System.lintegral_biSup_esq_compensated_le`). The energies of the
  coordinate differences are at most `𝔼 ∫_0^T S_s² ds` (`sum_energy_le_coeffDiffNorm`), and (4.9)
  gives the last link.
* (4.12): the difference of the two backward equations (4.8) is the linear backward equation with
  terminal value `δξ̄` and drift `λ δf`
  (`MVFBSDEJ.WellPosedness.BrownianPoisson.LinearBSDEJ.sub`), and Lemma 4.1
  (`MVFBSDEJ.WellPosedness.BrownianPoisson.LinearBSDEJ.brownianPoisson_estimate`, with
  `13 e^T + 3T ≤ C_BP`) gives the first link; (4.11), (4.9) and (4.10) the others.
* (4.13): the sum of (4.10) and (4.12).

## Main statements

* `MVFBSDEJ.Acceptance.sum_energy_le_coeffDiffNorm` — the energies of the coefficient
  differences against `𝔼 ∫_0^T S_s² ds`.
* `MVFBSDEJ.Acceptance.frozenStep_fwd_sub` — the forward difference of two frozen steps
  solves the linear forward equation from `0`.
* `MVFBSDEJ.Acceptance.eq_fwddiff_identity` — the forward difference before (4.10).
* `MVFBSDEJ.Acceptance.eq_fwddiff` — (4.10).
* `MVFBSDEJ.Acceptance.eq_bwddiff` — (4.12).
* `MVFBSDEJ.Acceptance.eq_contract` — (4.13).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace MVFBSDEJ.Acceptance

open MVFBSDEJ.WellPosedness.System MVFBSDEJ.WellPosedness.Existence
  MVFBSDEJ.WellPosedness.Enlarged MVFBSDEJ.WellPosedness.Stability
  MVFBSDEJ.WellPosedness.Spec MVFBSDEJ.WellPosedness.BrownianPoisson
  MVFBSDEJ.PaperSpec MVFBSDEJ.Law LevyStochCalc LevyStochCalc.BSDEJ.Solves

universe u v w

/-- `a² + b² + c² + e² ≤ (a + b + c + e)²` in `ℝ≥0∞`. -/
theorem sq_add_sq_add_sq_add_sq_le (a b c e : ℝ≥0∞) :
    a ^ 2 + b ^ 2 + c ^ 2 + e ^ 2 ≤ (a + b + c + e) ^ 2 := by
  have h2 : ∀ x y : ℝ≥0∞, x ^ 2 + y ^ 2 ≤ (x + y) ^ 2 := fun x y => by
    rw [add_sq]
    exact add_le_add (le_self_add : x ^ 2 ≤ x ^ 2 + 2 * x * y) le_rfl
  calc a ^ 2 + b ^ 2 + c ^ 2 + e ^ 2 ≤ (a + b) ^ 2 + c ^ 2 + e ^ 2 := by
        gcongr
        exact h2 a b
    _ ≤ (a + b + c) ^ 2 + e ^ 2 := by
        gcongr
        exact h2 _ _
    _ ≤ (a + b + c + e) ^ 2 := h2 _ _

/-- **The coefficient differences against `S`.** Along two tuples at which the integrals of (1.1)
exist with `coeffJump`, the energies of the coordinate differences of the drift, diffusion, jump
and driver processes are at most `𝔼 ∫_0^T S_s² ds`, with `S_s` the sum of the norms of the
coefficient differences (`coeffDiffNorm`). -/
theorem sum_energy_le_coeffDiffNorm {Ω : Type u} [MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    {n m d : ℕ} {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {T : ℝ} {C : Coeffs ν n m d} {X₁ X₂ : Fin n → ℝ → Ω → ℝ} {Y₁ Y₂ : Fin m → ℝ → Ω → ℝ}
    {Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ} {U₁ U₂ : Fin m → ℝ → Ω → E → ℝ}
    (hA₁ : PaperAdmissible ℱ P T C X₁ Y₁ Z₁ U₁ (coeffJump P T C X₁ Y₁ Z₁ U₁))
    (hA₂ : PaperAdmissible ℱ P T C X₂ Y₂ Z₂ U₂ (coeffJump P T C X₂ Y₂ Z₂ U₂)) :
    ∑ i, Brownian.Ito.energy P T
          (fun ω s => driftProc P T C X₁ Y₁ Z₁ U₁ i ω s - driftProc P T C X₂ Y₂ Z₂ U₂ i ω s)
        + ∑ i, ∑ j, Brownian.Ito.energy P T
          (fun ω s => diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j
            - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j)
        + ∑ i, Poisson.Compensated.markedEnergy P ν T
          (fun ω s e => coeffJump P T C X₁ Y₁ Z₁ U₁ i s ω e
            - coeffJump P T C X₂ Y₂ Z₂ U₂ i s ω e)
        + ∑ k, Brownian.Ito.energy P T
          (fun ω s => driverProc P T C X₁ Y₁ Z₁ U₁ k ω s - driverProc P T C X₂ Y₂ Z₂ U₂ k ω s)
      ≤ ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ ω,
          coeffDiffNorm P C (tupleAt ν X₁ Y₁ Z₁ U₁) (tupleAt ν X₂ Y₂ Z₂ U₂) s ω ^ 2 ∂P := by
  have hbm : ∀ i, Measurable (Function.uncurry fun ω s =>
      driftProc P T C X₁ Y₁ Z₁ U₁ i ω s - driftProc P T C X₂ Y₂ Z₂ U₂ i ω s) := fun i =>
    (hA₁.b_meas i).sub (hA₂.b_meas i)
  have hσm : ∀ i j, Measurable (Function.uncurry fun ω s =>
      diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j) :=
    fun i j => (hA₁.σ_meas i j).sub (hA₂.σ_meas i j)
  have hhm : ∀ i, Measurable fun p : Ω × ℝ × E =>
      coeffJump P T C X₁ Y₁ Z₁ U₁ i p.2.1 p.1 p.2.2
        - coeffJump P T C X₂ Y₂ Z₂ U₂ i p.2.1 p.1 p.2.2 := fun i => by
    have h1 := hA₁.γ_meas i
    have h2 := hA₂.γ_meas i
    simp only [jumpProc_coeffJump] at h1 h2
    exact h1.sub h2
  have hfm : ∀ k, Measurable (Function.uncurry fun ω s =>
      driverProc P T C X₁ Y₁ Z₁ U₁ k ω s - driverProc P T C X₂ Y₂ Z₂ U₂ k ω s) := fun k =>
    (hA₁.f_meas k).sub (hA₂.f_meas k)
  rw [← lintegral_sampleEnergy_add (P := P) (ν := ν)
      (x := fun i ω s => driftProc P T C X₁ Y₁ Z₁ U₁ i ω s - driftProc P T C X₂ Y₂ Z₂ U₂ i ω s)
      (z := fun i j ω s => diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j
        - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j)
      (u := fun i ω s e => coeffJump P T C X₁ Y₁ Z₁ U₁ i s ω e
        - coeffJump P T C X₂ Y₂ Z₂ U₂ i s ω e) hbm hσm hhm T,
    ← lintegral_sampleEnergy (P := P)
      (x := fun k ω s => driverProc P T C X₁ Y₁ Z₁ U₁ k ω s - driverProc P T C X₂ Y₂ Z₂ U₂ k ω s)
      hfm T,
    ← lintegral_add_left (measurable_sampleEnergy_add hbm hσm hhm)]
  refine lintegral_mono_ae ((ae_restrict_mem measurableSet_Icc).mono fun s hs => ?_)
  simp only [sampleEnergy, markedSampleEnergy]
  -- the pointwise bound at the time `s`
  have hpt : ∀ ω, esq (fun i =>
        driftProc P T C X₁ Y₁ Z₁ U₁ i ω s - driftProc P T C X₂ Y₂ Z₂ U₂ i ω s)
      + ∑ i, esq (fun j =>
        diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j)
      + ∑ i, ∫⁻ e, (‖coeffJump P T C X₁ Y₁ Z₁ U₁ i s ω e
          - coeffJump P T C X₂ Y₂ Z₂ U₂ i s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν
      + esq (fun k =>
        driverProc P T C X₁ Y₁ Z₁ U₁ k ω s - driverProc P T C X₂ Y₂ Z₂ U₂ k ω s)
      ≤ coeffDiffNorm P C (tupleAt ν X₁ Y₁ Z₁ U₁) (tupleAt ν X₂ Y₂ Z₂ U₂) s ω ^ 2 := fun ω => by
    have hh := coeFn_h_sub (P := P) (C := C) hs (coeffJump_ae_eq (P := P) (C := C) (X := X₁)
      (Y := Y₁) (Z := Z₁) (U := U₁) hs ω) (coeffJump_ae_eq (P := P) (C := C) (X := X₂)
      (Y := Y₂) (Z := Z₂) (U := U₂) hs ω)
    simp only [jumpProc_coeffJump] at hh
    have hjump := sum_lintegral_le_enorm_sq hh.symm
    rw [esq_eq_enorm_sq, ← b_sub_eq_toLp hs, sum_esq_eq_enorm_sq (fun i j =>
        diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j),
      ← σ_sub_eq_toLp hs, esq_eq_enorm_sq, ← f_sub_eq_toLp hs]
    refine le_trans ?_ (sq_add_sq_add_sq_add_sq_le _ _ _ _)
    gcongr
  calc ∑ i, ∫⁻ ω, (‖driftProc P T C X₁ Y₁ Z₁ U₁ i ω s
          - driftProc P T C X₂ Y₂ Z₂ U₂ i ω s‖₊ : ℝ≥0∞) ^ 2 ∂P
        + ∑ i, ∑ j, ∫⁻ ω, (‖diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j
          - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P
        + ∑ i, ∫⁻ ω, ∫⁻ e, (‖coeffJump P T C X₁ Y₁ Z₁ U₁ i s ω e
          - coeffJump P T C X₂ Y₂ Z₂ U₂ i s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P
        + ∑ k, ∫⁻ ω, (‖driverProc P T C X₁ Y₁ Z₁ U₁ k ω s
          - driverProc P T C X₂ Y₂ Z₂ U₂ k ω s‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ ∫⁻ ω, esq (fun i =>
            driftProc P T C X₁ Y₁ Z₁ U₁ i ω s - driftProc P T C X₂ Y₂ Z₂ U₂ i ω s) ∂P
        + ∫⁻ ω, ∑ i, esq (fun j => diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j
            - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j) ∂P
        + ∫⁻ ω, ∑ i, ∫⁻ e, (‖coeffJump P T C X₁ Y₁ Z₁ U₁ i s ω e
            - coeffJump P T C X₂ Y₂ Z₂ U₂ i s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P
        + ∫⁻ ω, esq (fun k =>
            driverProc P T C X₁ Y₁ Z₁ U₁ k ω s - driverProc P T C X₂ Y₂ Z₂ U₂ k ω s) ∂P := by
        gcongr
        · exact le_lintegral_finsetSum _ _
        · exact (Finset.sum_le_sum fun i _ => le_lintegral_finsetSum _ _).trans
            (le_lintegral_finsetSum _ _)
        · exact le_lintegral_finsetSum _ _
        · exact le_lintegral_finsetSum _ _
    _ ≤ ∫⁻ ω, (esq (fun i =>
            driftProc P T C X₁ Y₁ Z₁ U₁ i ω s - driftProc P T C X₂ Y₂ Z₂ U₂ i ω s)
          + ∑ i, esq (fun j => diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j
            - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j)
          + ∑ i, ∫⁻ e, (‖coeffJump P T C X₁ Y₁ Z₁ U₁ i s ω e
            - coeffJump P T C X₂ Y₂ Z₂ U₂ i s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν
          + esq (fun k =>
            driverProc P T C X₁ Y₁ Z₁ U₁ k ω s - driverProc P T C X₂ Y₂ Z₂ U₂ k ω s)) ∂P :=
        (add_le_add (add_le_add (le_lintegral_add _ _) le_rfl) le_rfl).trans
          ((add_le_add (le_lintegral_add _ _) le_rfl).trans (le_lintegral_add _ _))
    _ ≤ _ := lintegral_mono hpt

/-- **The forward difference of two frozen steps.** Under the hypotheses of Lemma 4.2, for two
trials of `𝕊` and their frozen steps, the integrals of (1.1) exist along each trial with the
representative `coeffJump` of the jump coefficient, and each coordinate of `δX̄` solves the linear
forward equation from `0` with integrands `λ δb, λ δσ, λ δh`. -/
theorem frozenStep_fwd_sub {Ω : Type u} {𝒢₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]
    [MeasurableSpace.CountablyGenerated E] {n m d : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P) {T : ℝ} (hT : 0 < T) {L : ℝ}
    {C : Coeffs ν n m d} {ξ₀ : Ω → EuclideanSpace ℝ (Fin n)} (hJ : JointBorel T C)
    (h22 : Assumption22 (enlJoint 𝒢₀ D h𝒢₀) P T C ξ₀)
    (h23 : Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L C) {lam : ℝ}
    {qb : Fin n → Ω → ℝ → ℝ} {qσ : Fin n → ℝ → Ω → Fin d → ℝ} {qh : Fin n → ℝ → Ω → E → ℝ}
    {qf : Fin m → Ω → ℝ → ℝ} {qg : Fin m → Ω → ℝ}
    (hq : PredForcing (enlJoint 𝒢₀ D h𝒢₀) P ν T qb qσ qh qf qg)
    {X₁ X₂ : Fin n → ℝ → Ω → ℝ} {Y₁ Y₂ : Fin m → ℝ → Ω → ℝ}
    {Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ} {U₁ U₂ : Fin m → ℝ → Ω → E → ℝ}
    (hΘ₁ : HTuple (enlJoint 𝒢₀ D h𝒢₀) P ν T X₁ Y₁ Z₁ U₁)
    (hΘ₂ : HTuple (enlJoint 𝒢₀ D h𝒢₀) P ν T X₂ Y₂ Z₂ U₂)
    {X₁' X₂' : Fin n → ℝ → Ω → ℝ} {Y₁' Y₂' : Fin m → ℝ → Ω → ℝ}
    {Z₁' Z₂' : Fin m → ℝ → Ω → Fin d → ℝ} {U₁' U₂' : Fin m → ℝ → Ω → E → ℝ}
    (hS₁ : FrozenStep D h𝒢₀ hind₀ T lam C ξ₀ qb qσ qh qf qg X₁ Y₁ Z₁ U₁ X₁' Y₁' Z₁' U₁')
    (hS₂ : FrozenStep D h𝒢₀ hind₀ T lam C ξ₀ qb qσ qh qf qg X₂ Y₂ Z₂ U₂ X₂' Y₂' Z₂' U₂') :
    PaperAdmissible (enlJoint 𝒢₀ D h𝒢₀) P T C X₁ Y₁ Z₁ U₁ (coeffJump P T C X₁ Y₁ Z₁ U₁)
    ∧ PaperAdmissible (enlJoint 𝒢₀ D h𝒢₀) P T C X₂ Y₂ Z₂ U₂ (coeffJump P T C X₂ Y₂ Z₂ U₂)
    ∧ ∀ i, LinearFSDEJ D (enlJoint 𝒢₀ D h𝒢₀) (isBrownianFiltration_enlJoint D h𝒢₀ hind₀)
      (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) T (fun _ => 0)
      (fun ω s => lam * (driftProc P T C X₁ Y₁ Z₁ U₁ i ω s - driftProc P T C X₂ Y₂ Z₂ U₂ i ω s))
      (fun t ω => X₁' i t ω - X₂' i t ω)
      (fun s ω j => lam * (diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j
        - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j))
      (fun s ω e => lam * (coeffJump P T C X₁ Y₁ Z₁ U₁ i s ω e
        - coeffJump P T C X₂ Y₂ Z₂ U₂ i s ω e)) := by
  have hB : CoeffBorel T C := (jointBorel_iff.mp hJ).1.toCoeffBorel
  have horig := originValues_iff_coeffOrigin.mp h22.origin
  have hL2 := h23.interior.diagonalLipschitz_two_mul
  -- the integrals of (1.1) along the trials, with `coeffJump`
  have hA₁ := hΘ₁.1.paperAdmissible_coeffJump hT.le hB horig hL2
  have hA₂ := hΘ₂.1.paperAdmissible_coeffJump hT.le hB horig hL2
  -- the frozen forward equations with the jump coefficient through `coeffJump`
  obtain ⟨⟨γ₁, hr₁, hf₁⟩, -, -⟩ := hS₁
  obtain ⟨⟨γ₂, hr₂, hf₂⟩, -, -⟩ := hS₂
  have hF₁ := (hA₁.forcing.smul lam).add hq.toForcing
  have hF₂ := (hA₂.forcing.smul lam).add hq.toForcing
  have hg₁ : ∀ i, LinearFSDEJ D (enlJoint 𝒢₀ D h𝒢₀) (isBrownianFiltration_enlJoint D h𝒢₀ hind₀)
      (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) T (fun ω => ξ₀ ω i)
      (fun ω s => lam * driftProc P T C X₁ Y₁ Z₁ U₁ i ω s + qb i ω s) (X₁' i)
      (fun s ω j => lam * diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j + qσ i s ω j)
      (fun s ω e => lam * jumpProc T (coeffJump P T C X₁ Y₁ Z₁ U₁) i s ω e + qh i s ω e) :=
    fun i => (hf₁ i).congr_jump (hF₁.qh_meas i) (hF₁.qh_prog i) (hF₁.qh_vanish i) (hF₁.qh_sq i)
      (ae_forcedJump_eq_of_rep (F := fun s ω =>
          ⇑(C.h s (tupleAt ν (leftLimProc X₁) (leftLimProc Y₁) Z₁ U₁ s ω)
            (lawP2 P (tupleAt ν (leftLimProc X₁) (leftLimProc Y₁) Z₁ U₁ s)))) lam qh i hr₁
        hA₁.jump_rep (measurableSet_eq_fun (hf₁ i).γ_meas (hF₁.qh_meas i)))
  have hg₂ : ∀ i, LinearFSDEJ D (enlJoint 𝒢₀ D h𝒢₀) (isBrownianFiltration_enlJoint D h𝒢₀ hind₀)
      (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) T (fun ω => ξ₀ ω i)
      (fun ω s => lam * driftProc P T C X₂ Y₂ Z₂ U₂ i ω s + qb i ω s) (X₂' i)
      (fun s ω j => lam * diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j + qσ i s ω j)
      (fun s ω e => lam * jumpProc T (coeffJump P T C X₂ Y₂ Z₂ U₂) i s ω e + qh i s ω e) :=
    fun i => (hf₂ i).congr_jump (hF₂.qh_meas i) (hF₂.qh_prog i) (hF₂.qh_vanish i) (hF₂.qh_sq i)
      (ae_forcedJump_eq_of_rep (F := fun s ω =>
          ⇑(C.h s (tupleAt ν (leftLimProc X₂) (leftLimProc Y₂) Z₂ U₂ s ω)
            (lawP2 P (tupleAt ν (leftLimProc X₂) (leftLimProc Y₂) Z₂ U₂ s)))) lam qh i hr₂
        hA₂.jump_rep (measurableSet_eq_fun (hf₂ i).γ_meas (hF₂.qh_meas i)))
  -- the forward difference
  have hδ : ∀ i, LinearFSDEJ D (enlJoint 𝒢₀ D h𝒢₀) (isBrownianFiltration_enlJoint D h𝒢₀ hind₀)
      (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) T (fun _ => 0)
      (fun ω s => lam * (driftProc P T C X₁ Y₁ Z₁ U₁ i ω s - driftProc P T C X₂ Y₂ Z₂ U₂ i ω s))
      (fun t ω => X₁' i t ω - X₂' i t ω)
      (fun s ω j => lam * (diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j
        - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j))
      (fun s ω e => lam * (coeffJump P T C X₁ Y₁ Z₁ U₁ i s ω e
        - coeffJump P T C X₂ Y₂ Z₂ U₂ i s ω e)) := fun i => by
    have h := (hg₁ i).sub (hg₂ i) hT.le
    beta_reduce at h
    have e1 : (fun ω => ξ₀ ω i - ξ₀ ω i) = fun _ => (0 : ℝ) := funext fun ω => sub_self _
    have e2 : (fun ω s => lam * driftProc P T C X₁ Y₁ Z₁ U₁ i ω s + qb i ω s
        - (lam * driftProc P T C X₂ Y₂ Z₂ U₂ i ω s + qb i ω s))
        = fun ω s => lam * (driftProc P T C X₁ Y₁ Z₁ U₁ i ω s
          - driftProc P T C X₂ Y₂ Z₂ U₂ i ω s) := by
      funext ω s
      ring
    have e3 : (fun s ω j => lam * diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j + qσ i s ω j
        - (lam * diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j + qσ i s ω j))
        = fun s ω j => lam * (diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j
          - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j) := by
      funext s ω j
      ring
    have e4 : (fun s ω e => lam * jumpProc T (coeffJump P T C X₁ Y₁ Z₁ U₁) i s ω e + qh i s ω e
        - (lam * jumpProc T (coeffJump P T C X₂ Y₂ Z₂ U₂) i s ω e + qh i s ω e))
        = fun s ω e => lam * (coeffJump P T C X₁ Y₁ Z₁ U₁ i s ω e
          - coeffJump P T C X₂ Y₂ Z₂ U₂ i s ω e) := by
      funext s ω e
      simp only [jumpProc_coeffJump]
      ring
    rwa [e1, e2, e3, e4] at h
  exact ⟨hA₁, hA₂, hδ⟩

/-- The forward difference before (4.10). -/
theorem eq_fwddiff_identity : PaperSpec.eq_fwddiff_identity.{u, v, w} := by
  rintro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ hind₀ hn hm hd T hT L C ξ₀ hJ h22 h23 lam hl0 hl1
    qb qσ qh qf qg hq X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ hΘ₁ hΘ₂ X₁' X₂' Y₁' Y₂' Z₁' Z₂' U₁' U₂' hS₁ hS₂
  obtain ⟨hA₁, hA₂, hδ⟩ := frozenStep_fwd_sub D h𝒢₀ hind₀ hT hJ h22 h23 hq hΘ₁ hΘ₂ hS₁ hS₂
  have hD := hA₁.forcing.sub hA₂.forcing
  have ejump : (fun i s ω e => jumpProc T (coeffJump P T C X₁ Y₁ Z₁ U₁) i s ω e
      - jumpProc T (coeffJump P T C X₂ Y₂ Z₂ U₂) i s ω e)
      = fun i s ω e => coeffJump P T C X₁ Y₁ Z₁ U₁ i s ω e - coeffJump P T C X₂ Y₂ Z₂ U₂ i s ω e :=
    by funext i s ω e; simp only [jumpProc_coeffJump]
  rw [ejump] at hD
  have hσq := fun i => sq_int_global_of_vanishing (hD.qσ_vanish i) (hD.qσ_sq i)
  have hhq := fun i => marked_sq_int_global_of_vanishing (hD.qh_vanish i) (hD.qh_sq i)
  -- the identity at each time
  have hid : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P,
      X₁' i t ω - X₂' i t ω
        = lam * (∫ s in Set.Icc (0 : ℝ) t,
            driftProc P T C X₁ Y₁ Z₁ U₁ i ω s - driftProc P T C X₂ Y₂ Z₂ U₂ i ω s)
          + lam * Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W
              (enlJoint 𝒢₀ D h𝒢₀) (isBrownianFiltration_enlJoint D h𝒢₀ hind₀)
              (fun s ω j => diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j
                - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j) (hD.qσ_meas i) (hD.qσ_prog i)
              (hσq i) t ω
          + lam * Poisson.Compensated.stochasticIntegral D.N (enlJoint 𝒢₀ D h𝒢₀)
              (isPoissonFiltration_enlJoint D h𝒢₀ hind₀)
              (fun ω s e => coeffJump P T C X₁ Y₁ Z₁ U₁ i s ω e
                - coeffJump P T C X₂ Y₂ Z₂ U₂ i s ω e) (hD.qh_meas i) (hD.qh_prog i)
              (hhq i) t ω := by
    intro i t ht
    filter_upwards [(hδ i).eqn t ht,
      multidimStochasticIntegral_const_mul_ae D.W (isBrownianFiltration_enlJoint D h𝒢₀ hind₀)
        (Z := fun s ω j => diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j
          - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j) lam (hD.qσ_meas i) (hD.qσ_prog i) (hσq i)
        (hδ i).σ_meas (hδ i).σ_prog (sq_int_global_of_vanishing (hδ i).σ_vanish (hδ i).σ_sq) t,
      compensatedIntegral_const_mul_ae D.N (isPoissonFiltration_enlJoint D h𝒢₀ hind₀)
        (φ := fun ω s e => coeffJump P T C X₁ Y₁ Z₁ U₁ i s ω e
          - coeffJump P T C X₂ Y₂ Z₂ U₂ i s ω e) lam (hD.qh_meas i) (hD.qh_prog i) (hhq i)
        (hδ i).γ_meas (hδ i).γ_prog
        (marked_sq_int_global_of_vanishing (hδ i).γ_vanish (hδ i).γ_sq) t] with ω e1 e2 e3
    rw [e1, e2, e3, integral_const_mul]
    ring
  refine ⟨hD.qσ_meas, hD.qσ_prog, hσq, hD.qh_meas, hD.qh_prog, hhq,
    fun i => (ae_mem_integrablePaths (hD.qb_meas i) (hD.qb_sq i)).mono fun _ h => h, hid, ?_⟩
  -- the identity at every time at once, with a right-continuous version of the Brownian leg
  intro Mσ hMv hMc i
  have hR := ae_forall_Icc_eq_of_ae_rightCont (P := P) (T := T)
    (Y := fun t ω => X₁' i t ω - X₂' i t ω)
    (R := fun t ω => lam * driftLeg (fun ω s =>
        driftProc P T C X₁ Y₁ Z₁ U₁ i ω s - driftProc P T C X₂ Y₂ Z₂ U₂ i ω s) T t ω
      + lam * Mσ i t ω
      + lam * Poisson.Compensated.stochasticIntegral D.N (enlJoint 𝒢₀ D h𝒢₀)
          (isPoissonFiltration_enlJoint D h𝒢₀ hind₀)
          (fun ω s e => coeffJump P T C X₁ Y₁ Z₁ U₁ i s ω e
            - coeffJump P T C X₂ Y₂ Z₂ U₂ i s ω e) (hD.qh_meas i) (hD.qh_prog i) (hhq i) t ω)
    hT.le (fun t ht => ?_) (ae_of_all _ fun ω t _ => (hδ i).X_rightCont ω t) ?_
  · filter_upwards [hR, ae_mem_integrablePaths (hD.qb_meas i) (hD.qb_sq i)] with ω hω hg t ht
    rw [hω t ht, driftLeg_of_mem hg]
  · filter_upwards [hid i t ht, hMv i t ht, driftLeg_ae_eq (hD.qb_meas i) (hD.qb_sq i) t]
      with ω e1 e2 e3
    rw [e1, e2, e3]
  · filter_upwards [hMc i, Poisson.Compensated.stochasticIntegral_cadlag D.N (enlJoint 𝒢₀ D h𝒢₀)
      (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) _ (hD.qh_meas i) (hD.qh_prog i) (hhq i)]
      with ω hM hN t ht
    have hA := ((continuous_driftLeg (hD.qb_vanish i) ω).tendsto t).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi t))
    exact ((hA.const_mul lam).add ((hM t ht).const_mul lam)).add ((hN t).1.const_mul lam)

/-- (4.10). -/
theorem eq_fwddiff : PaperSpec.eq_fwddiff.{u, v, w} := by
  intro c hc
  rintro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ hind₀ hn hm hd T hT L C ξ₀ hJ h22 h23 lam hl0 hl1
    qb qσ qh qf qg hq X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ hΘ₁ hΘ₂ X₁' X₂' Y₁' Y₂' Z₁' Z₂' U₁' U₂' hS₁ hS₂
  have hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[enlJoint 𝒢₀ D h𝒢₀ 0] s :=
    fun _ hs h0 => measurableSet_enlJoint_of_null D h𝒢₀ hs h0
  have hℱ0 := hF0_enlJoint D h𝒢₀
  have 𝒲 := crossWitnessEnl D h𝒢₀ hind₀
  -- the integrals of (1.1) along the trials, with `coeffJump`, and the forward difference
  obtain ⟨hA₁, hA₂, hδ⟩ := frozenStep_fwd_sub D h𝒢₀ hind₀ hT hJ h22 h23 hq hΘ₁ hΘ₂ hS₁ hS₂
  have hD := hA₁.forcing.sub hA₂.forcing
  have ejump : (fun i s ω e => jumpProc T (coeffJump P T C X₁ Y₁ Z₁ U₁) i s ω e
      - jumpProc T (coeffJump P T C X₂ Y₂ Z₂ U₂) i s ω e)
      = fun i s ω e => coeffJump P T C X₁ Y₁ Z₁ U₁ i s ω e - coeffJump P T C X₂ Y₂ Z₂ U₂ i s ω e :=
    by funext i s ω e; simp only [jumpProc_coeffJump]
  rw [ejump] at hD
  have hσq := fun i => sq_int_global_of_vanishing (hD.qσ_vanish i) (hD.qσ_sq i)
  have hhq := fun i => marked_sq_int_global_of_vanishing (hD.qh_vanish i) (hD.qh_sq i)
  -- the energies against `S`, and (4.9)
  have hS := sum_energy_le_coeffDiffNorm hA₁ hA₂
  obtain ⟨h91, h92, h93⟩ := MVFBSDEJ.Acceptance.eq_coeffdiff.{u, v, w} 𝒢₀ ν n m d P D h𝒢₀
    hind₀ hn hm hd T hT L C ξ₀ hJ h22 h23 X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ hΘ₁ hΘ₂
  have h4c : (4 : ℝ≥0∞) ≤ ENNReal.ofReal c := by
    rw [← ENNReal.ofReal_ofNat 4]
    exact ENNReal.ofReal_le_ofReal hc
  refine ⟨hD.qσ_meas, hD.qσ_prog, hσq, hD.qh_meas, hD.qh_prog, hhq, ?_, ?_, ?_, ?_, ?_⟩
  -- a càdlàg version of the Brownian leg
  · choose MW _ _ hMWae hMWc _ _ _ using fun i =>
      exists_cadlag_vectorIntegral_supBound D.W (enlJoint 𝒢₀ D h𝒢₀)
        (isBrownianFiltration_enlJoint D h𝒢₀ hind₀) _ (hD.qσ_meas i) (hD.qσ_prog i) (hσq i)
        hℱ0 hnull T hT.le
    exact ⟨MW, fun i t _ => hMWae i t, fun i => ae_of_all _ fun ω =>
      ⟨fun t _ => (hMWc i ω t).1, fun t _ => (hMWc i ω t).2⟩⟩
  -- the first two links
  · intro Mσ hMv hMc
    refine ⟨LinearFSDEJ.lintegral_biSup_esq_le_legs hℱ0 hnull hT lam hD.qb_meas hD.qb_vanish
      hD.qb_sq hD.qσ_meas hD.qσ_prog hσq hD.qh_meas hD.qh_prog hhq hδ Mσ hMv
      (fun i => (hMc i).mono fun ω hω => hω.1), ?_⟩
    gcongr ENNReal.ofReal (3 * lam ^ 2) * ?_
    gcongr
    · exact lintegral_sq_lintegral_toLp_le hD.qb_meas T
    · exact (lintegral_biSup_esq_brownian_le (hℱN := isPoissonFiltration_enlJoint D h𝒢₀ hind₀)
        𝒲 hℱ0 hnull hT hD.qσ_meas hD.qσ_prog hσq Mσ hMv
        (fun i => (hMc i).mono fun ω hω => hω.1)).trans (mul_le_mul_of_nonneg_right h4c zero_le)
    · exact (lintegral_biSup_esq_compensated_le hℱ0 hnull hT hD.qh_meas hD.qh_prog hhq).trans
        (mul_le_mul_of_nonneg_right h4c zero_le)
  -- the third link
  · rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 3 * lam ^ 2), mul_assoc]
    gcongr ENNReal.ofReal (3 * lam ^ 2) * ?_
    rw [mul_add, mul_add]
    gcongr
    · exact le_max_left T c
    · exact le_max_right T c
    · exact le_max_right T c
  -- the fourth link
  · gcongr
    exact le_self_add.trans hS
  -- the fifth link, by (4.9)
  · have h9 := h91.trans (h92.trans h93)
    have hK : (0 : ℝ) ≤ 3 * lam ^ 2 * max T c := by
      have : 0 ≤ max T c := le_trans hT.le (le_max_left T c)
      positivity
    calc ENNReal.ofReal (3 * lam ^ 2 * max T c) * ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ ω,
            coeffDiffNorm P C (tupleAt ν X₁ Y₁ Z₁ U₁) (tupleAt ν X₂ Y₂ Z₂ U₂) s ω ^ 2 ∂P
        ≤ ENNReal.ofReal (3 * lam ^ 2 * max T c) * (ENNReal.ofReal (10 * L ^ 2 * max T 1)
          * supSize P ν T (fun i t ω => X₁ i t ω - X₂ i t ω) (fun k t ω => Y₁ k t ω - Y₂ k t ω)
            (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j)
            (fun k t ω e => U₁ k t ω e - U₂ k t ω e)) := by gcongr
      _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hK]
        congr 2
        ring

/-- `B (a λ⁴ + b λ²) ≤ B (a + b) λ²` for `B, a ≥ 0` and `λ ∈ [0, 1]`. -/
theorem mul_add_pow_four_le {B a b l : ℝ} (hB : 0 ≤ B) (ha : 0 ≤ a) (hl0 : 0 ≤ l)
    (hl1 : l ≤ 1) : B * (a * l ^ 4 + b * l ^ 2) ≤ B * (a + b) * l ^ 2 := by
  have h4 : l ^ 4 ≤ l ^ 2 := by
    have h2 : l ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg l]
  nlinarith [mul_le_mul_of_nonneg_left h4 (mul_nonneg hB ha)]

/-- (4.12). -/
theorem eq_bwddiff : PaperSpec.eq_bwddiff.{u, v, w} := by
  have hfwd := eq_fwddiff.{u, v, w}
  intro c hc
  rintro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ hind₀ hn hm hd T hT L C ξ₀ hJ h22 h23 lam hl0 hl1
    qb qσ qh qf qg hq X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ hΘ₁ hΘ₂ X₁' X₂' Y₁' Y₂' Z₁' Z₂' U₁' U₂' hS₁ hS₂
  have hc4 : 4 ≤ c := hc
  have hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[enlJoint 𝒢₀ D h𝒢₀ 0] s :=
    fun _ hs h0 => measurableSet_enlJoint_of_null D h𝒢₀ hs h0
  have hℱ0 := hF0_enlJoint D h𝒢₀
  have 𝒲 := crossWitnessEnl D h𝒢₀ hind₀
  have hB : CoeffBorel T C := (jointBorel_iff.mp hJ).1.toCoeffBorel
  have horig := originValues_iff_coeffOrigin.mp h22.origin
  have hL2 := h23.interior.diagonalLipschitz_two_mul
  have hL : 0 ≤ L := h23.nonneg
  -- (4.10) at the same constant
  obtain ⟨_, _, _, _, _, _, ⟨Mσ, hMv, hMc⟩, hab, hl3, hl4, hl5⟩ :=
    hfwd c hc 𝒢₀ ν n m d P D h𝒢₀ hind₀ hn hm hd T hT L C ξ₀ hJ h22
      h23 lam hl0 hl1 qb qσ qh qf qg hq X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ hΘ₁ hΘ₂ X₁' X₂' Y₁' Y₂' Z₁' Z₂'
      U₁' U₂' hS₁ hS₂
  obtain ⟨hl1', hl2⟩ := hab Mσ hMv hMc
  have hXsup := hl1'.trans (hl2.trans (hl3.trans (hl4.trans hl5)))
  -- (4.9), and the driver difference against `S`
  obtain ⟨h91, h92, h93⟩ := MVFBSDEJ.Acceptance.eq_coeffdiff.{u, v, w} 𝒢₀ ν n m d P D h𝒢₀
    hind₀ hn hm hd T hT L C ξ₀ hJ h22 h23 X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ hΘ₁ hΘ₂
  have h9 := h91.trans (h92.trans h93)
  have hA₁ := hΘ₁.1.paperAdmissible_coeffJump hT.le hB horig hL2
  have hA₂ := hΘ₂.1.paperAdmissible_coeffJump hT.le hB horig hL2
  have hF := le_add_self.trans ((sum_energy_le_coeffDiffNorm hA₁ hA₂).trans h9)
  obtain ⟨⟨γ₁, -, hf₁⟩, hb₁, -⟩ := hS₁
  obtain ⟨⟨γ₂, -, hf₂⟩, hb₂, -⟩ := hS₂
  -- the backward difference
  have hδ : ∀ k, LinearBSDEJ D (enlJoint 𝒢₀ D h𝒢₀) (isBrownianFiltration_enlJoint D h𝒢₀ hind₀)
      (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) T
      (fun ω => lam * (terminalVal P T C X₁' k ω - terminalVal P T C X₂' k ω))
      (fun ω s => lam * (driverProc P T C X₁ Y₁ Z₁ U₁ k ω s - driverProc P T C X₂ Y₂ Z₂ U₂ k ω s))
      (fun t ω => Y₁' k t ω - Y₂' k t ω) (fun s ω j => Z₁' k s ω j - Z₂' k s ω j)
      (fun s ω e => U₁' k s ω e - U₂' k s ω e) := fun k => by
    have h := (hb₁ k).sub (hb₂ k)
    beta_reduce at h
    have e1 : (fun ω => lam * terminalVal P T C X₁' k ω + qg k ω
        - (lam * terminalVal P T C X₂' k ω + qg k ω))
        = fun ω => lam * (terminalVal P T C X₁' k ω - terminalVal P T C X₂' k ω) := by
      funext ω
      ring
    have e2 : (fun ω s => lam * driverProc P T C X₁ Y₁ Z₁ U₁ k ω s + qf k ω s
        - (lam * driverProc P T C X₂ Y₂ Z₂ U₂ k ω s + qf k ω s))
        = fun ω s => lam * (driverProc P T C X₁ Y₁ Z₁ U₁ k ω s
          - driverProc P T C X₂ Y₂ Z₂ U₂ k ω s) := by
      funext ω s
      ring
    rwa [e1, e2] at h
  -- Lemma 4.1 in each coordinate
  have hest : ∀ k, ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖Y₁' k t ω - Y₂' k t ω‖₊ : ℝ≥0∞) ^ 2) ∂P
        + (∑ j, Brownian.Ito.energy P T (fun ω s => Z₁' k s ω j - Z₂' k s ω j))
        + Poisson.Compensated.markedEnergy P ν T (fun ω s e => U₁' k s ω e - U₂' k s ω e)
      ≤ ENNReal.ofReal (13 * Real.exp T + 3 * T)
        * (∫⁻ ω, (‖lam * (terminalVal P T C X₁' k ω - terminalVal P T C X₂' k ω)‖₊ : ℝ≥0∞) ^ 2 ∂P
          + Brownian.Ito.energy P T (fun ω s => lam * (driverProc P T C X₁ Y₁ Z₁ U₁ k ω s
            - driverProc P T C X₂ Y₂ Z₂ U₂ k ω s))) :=
    fun k => (hδ k).brownianPoisson_estimate 𝒲 hℱ0 hnull hT
  have hYsup : ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun k => Y₁' k t ω - Y₂' k t ω)) ∂P
      ≤ ∑ k, ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖Y₁' k t ω - Y₂' k t ω‖₊ : ℝ≥0∞) ^ 2) ∂P :=
    lintegral_biSup_esq_le hT.le
      (fun k t => ((hδ k).Y_adapted t).mono ((enlJoint 𝒢₀ D h𝒢₀).le t) le_rfl)
      fun k => (hδ k).Y_rightCont
  have hesq : ∫⁻ ω, esq (fun k => lam * (terminalVal P T C X₁' k ω - terminalVal P T C X₂' k ω)) ∂P
      = ∑ k, ∫⁻ ω,
        (‖lam * (terminalVal P T C X₁' k ω - terminalVal P T C X₂' k ω)‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    unfold esq
    exact lintegral_finsetSum' _ fun k _ =>
      (((hδ k).ξ_sq.aestronglyMeasurable.aemeasurable.nnnorm.coe_nnreal_ennreal).pow_const 2)
  have hBP : (0 : ℝ) ≤ 2 * Real.exp T * (5 + 4 * c) + 4 * T := by
    have := Real.exp_pos T
    nlinarith
  have hCX : (0 : ℝ) ≤ 3 * max T c * (10 * L ^ 2 * max T 1) := by
    have h1 : 0 ≤ max T c := le_trans hT.le (le_max_left _ _)
    have h2 : 0 ≤ max T 1 := le_trans zero_le_one (le_max_right _ _)
    positivity
  -- the terminal difference, by (4.11)
  set XT₁ : Ω → EuclideanSpace ℝ (Fin n) := fun ω => WithLp.toLp 2 fun i => X₁' i T ω with hXT₁
  set XT₂ : Ω → EuclideanSpace ℝ (Fin n) := fun ω => WithLp.toLp 2 fun i => X₂' i T ω with hXT₂
  have hsm₁ : StronglyMeasurable[enlJoint 𝒢₀ D h𝒢₀ T] XT₁ :=
    (measurable_toLp_of_forall fun i => (hf₁ i).X_adapted T).stronglyMeasurable
  have hsm₂ : StronglyMeasurable[enlJoint 𝒢₀ D h𝒢₀ T] XT₂ :=
    (measurable_toLp_of_forall fun i => (hf₂ i).X_adapted T).stronglyMeasurable
  have hL₁ : MemLp XT₁ 2 P := MemLp.of_eval_piLp fun i => (hf₁ i).memLp_terminal hT.le
  have hL₂ : MemLp XT₂ 2 P := MemLp.of_eval_piLp fun i => (hf₂ i).memLp_terminal hT.le
  obtain ⟨t1, t2, t3⟩ := MVFBSDEJ.Acceptance.eq_terdiff.{u} (enlJoint 𝒢₀ D h𝒢₀) P n m T L
    lam C.g h23.terminal XT₁ XT₂ hsm₁ hsm₂ hL₁ hL₂
  have eL : ∫⁻ ω, esq (fun k => lam * (terminalVal P T C X₁' k ω - terminalVal P T C X₂' k ω)) ∂P
      = ∫⁻ ω, ‖lam • (C.g (XT₁ ω) (lawP2 P XT₁) - C.g (XT₂ ω) (lawP2 P XT₂))‖ₑ ^ 2 ∂P :=
    lintegral_congr fun ω => by
      rw [esq_eq_enorm_sq]
      congr 2
  have eR : ∫⁻ ω, ‖XT₁ ω - XT₂ ω‖ₑ ^ 2 ∂P = ∫⁻ ω, esq (fun i => X₁' i T ω - X₂' i T ω) ∂P :=
    lintegral_congr fun ω => by
      rw [esq_eq_enorm_sq]
      congr 2
  have hterm : ∫⁻ ω, esq (fun k => lam * (terminalVal P T C X₁' k ω
        - terminalVal P T C X₂' k ω)) ∂P
      ≤ ENNReal.ofReal (4 * L ^ 2 * lam ^ 2) * ∫⁻ ω, esq (fun i => X₁' i T ω - X₂' i T ω) ∂P := by
    rw [eL, ← eR]
    exact t1.trans (t2.trans t3)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  -- the first link: Lemma 4.1
  · calc ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun k => Y₁' k t ω - Y₂' k t ω)) ∂P
          + ((∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z₁' k s ω j - Z₂' k s ω j))
            + ∑ k, Poisson.Compensated.markedEnergy P ν T
              (fun ω s e => U₁' k s ω e - U₂' k s ω e))
        ≤ ∑ k, (∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T,
              (‖Y₁' k t ω - Y₂' k t ω‖₊ : ℝ≥0∞) ^ 2) ∂P
            + (∑ j, Brownian.Ito.energy P T (fun ω s => Z₁' k s ω j - Z₂' k s ω j))
            + Poisson.Compensated.markedEnergy P ν T (fun ω s e => U₁' k s ω e - U₂' k s ω e)) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, add_assoc]
          gcongr
      _ ≤ ∑ k, ENNReal.ofReal (13 * Real.exp T + 3 * T)
            * (∫⁻ ω, (‖lam * (terminalVal P T C X₁' k ω
                - terminalVal P T C X₂' k ω)‖₊ : ℝ≥0∞) ^ 2 ∂P
              + Brownian.Ito.energy P T (fun ω s => lam * (driverProc P T C X₁ Y₁ Z₁ U₁ k ω s
                - driverProc P T C X₂ Y₂ Z₂ U₂ k ω s))) := Finset.sum_le_sum fun k _ => hest k
      _ = ENNReal.ofReal (13 * Real.exp T + 3 * T)
            * (∫⁻ ω, esq (fun k => lam * (terminalVal P T C X₁' k ω
                - terminalVal P T C X₂' k ω)) ∂P
              + ENNReal.ofReal (lam ^ 2) * ∑ k, Brownian.Ito.energy P T
                (fun ω s => driverProc P T C X₁ Y₁ Z₁ U₁ k ω s
                  - driverProc P T C X₂ Y₂ Z₂ U₂ k ω s)) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, hesq]
          simp only [energy_const_mul]
          rw [← Finset.mul_sum]
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le
          nlinarith [mul_le_mul_of_nonneg_right hc4 (Real.exp_pos T).le, Real.exp_pos T]
  -- the second link: (4.11) and (4.9)
  · gcongr ENNReal.ofReal (2 * Real.exp T * (5 + 4 * c) + 4 * T) * ?_
    refine add_le_add hterm ?_
    calc ENNReal.ofReal (lam ^ 2) * ∑ k, Brownian.Ito.energy P T
          (fun ω s => driverProc P T C X₁ Y₁ Z₁ U₁ k ω s - driverProc P T C X₂ Y₂ Z₂ U₂ k ω s)
        ≤ ENNReal.ofReal (lam ^ 2) * (ENNReal.ofReal (10 * L ^ 2 * max T 1)
          * supSize P ν T (fun i t ω => X₁ i t ω - X₂ i t ω) (fun k t ω => Y₁ k t ω - Y₂ k t ω)
            (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j)
            (fun k t ω e => U₁ k t ω e - U₂ k t ω e)) := by gcongr
      _ = _ := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg lam)]
          congr 2
          ring
  -- the third link
  · gcongr ENNReal.ofReal _ * (ENNReal.ofReal _ * ?_ + _)
    exact lintegral_mono fun ω => le_iSup₂ (f := fun t (_ : t ∈ Set.Icc (0 : ℝ) T) =>
      esq (fun i => X₁' i t ω - X₂' i t ω)) T ⟨hT.le, le_rfl⟩
  -- the fourth link: (4.10)
  · gcongr ENNReal.ofReal (2 * Real.exp T * (5 + 4 * c) + 4 * T) * ?_
    calc ENNReal.ofReal (4 * L ^ 2 * lam ^ 2)
          * ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => X₁' i t ω - X₂' i t ω)) ∂P
          + ENNReal.ofReal (10 * L ^ 2 * max T 1 * lam ^ 2)
            * supSize P ν T (fun i t ω => X₁ i t ω - X₂ i t ω)
              (fun k t ω => Y₁ k t ω - Y₂ k t ω) (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j)
              (fun k t ω e => U₁ k t ω e - U₂ k t ω e)
        ≤ ENNReal.ofReal (4 * L ^ 2 * lam ^ 2)
          * (ENNReal.ofReal (3 * max T c * (10 * L ^ 2 * max T 1) * lam ^ 2)
            * supSize P ν T (fun i t ω => X₁ i t ω - X₂ i t ω)
              (fun k t ω => Y₁ k t ω - Y₂ k t ω) (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j)
              (fun k t ω e => U₁ k t ω e - U₂ k t ω e))
          + ENNReal.ofReal (10 * L ^ 2 * max T 1 * lam ^ 2)
            * supSize P ν T (fun i t ω => X₁ i t ω - X₂ i t ω)
              (fun k t ω => Y₁ k t ω - Y₂ k t ω) (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j)
              (fun k t ω e => U₁ k t ω e - U₂ k t ω e) := by
          gcongr ENNReal.ofReal _ * ?_ + _
      _ = _ := by
          have h1 : (0 : ℝ) ≤ 4 * L ^ 2 * lam ^ 2 := by positivity
          have h2 : (0 : ℝ)
              ≤ 4 * L ^ 2 * lam ^ 2 * (3 * max T c * (10 * L ^ 2 * max T 1) * lam ^ 2) :=
            mul_nonneg h1 (mul_nonneg hCX (sq_nonneg lam))
          have h3 : (0 : ℝ) ≤ 10 * L ^ 2 * max T 1 * lam ^ 2 := by
            have : 0 ≤ max T 1 := le_trans zero_le_one (le_max_right _ _)
            positivity
          rw [← mul_assoc, ← ENNReal.ofReal_mul h1, ← add_mul, ← ENNReal.ofReal_add h2 h3]
          congr 2
          ring
  -- the fifth link: `λ⁴ ≤ λ²`
  · rw [← mul_assoc, ← ENNReal.ofReal_mul hBP]
    gcongr ?_ * _
    exact ENNReal.ofReal_le_ofReal (mul_add_pow_four_le hBP (by positivity) hl0 hl1)

/-- (4.13). -/
theorem eq_contract : PaperSpec.eq_contract.{u, v, w} := by
  have hfwd := eq_fwddiff.{u, v, w}
  have hbwd := eq_bwddiff.{u, v, w}
  intro c hc
  rintro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ hind₀ hn hm hd T hT L C ξ₀ hJ h22 h23 lam hl0 hl1
    qb qσ qh qf qg hq X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ hΘ₁ hΘ₂ X₁' X₂' Y₁' Y₂' Z₁' Z₂' U₁' U₂' hS₁ hS₂
  have hc0 : 0 < c := by linarith
  have hL : 0 ≤ L := h23.nonneg
  obtain ⟨_, _, _, _, _, _, ⟨Mσ, hMv, hMc⟩, hab, hl3, hl4, hl5⟩ :=
    hfwd c hc 𝒢₀ ν n m d P D h𝒢₀ hind₀ hn hm hd T hT L C ξ₀ hJ h22
      h23 lam hl0 hl1 qb qσ qh qf qg hq X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ hΘ₁ hΘ₂ X₁' X₂' Y₁' Y₂' Z₁' Z₂'
      U₁' U₂' hS₁ hS₂
  obtain ⟨hl1', hl2⟩ := hab Mσ hMv hMc
  have hX := hl1'.trans (hl2.trans (hl3.trans (hl4.trans hl5)))
  obtain ⟨k1, k2, k3, k4, k5⟩ :=
    hbwd c hc 𝒢₀ ν n m d P D h𝒢₀ hind₀ hn hm hd T hT L C ξ₀ hJ h22
      h23 lam hl0 hl1 qb qσ qh qf qg hq X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ hΘ₁ hΘ₂ X₁' X₂' Y₁' Y₂' Z₁' Z₂'
      U₁' U₂' hS₁ hS₂
  have hY := k1.trans (k2.trans (k3.trans (k4.trans k5)))
  have hCX : (0 : ℝ) ≤ 3 * max T c * (10 * L ^ 2 * max T 1) := by
    have h1 : 0 ≤ max T c := le_trans hT.le (le_max_left _ _)
    have h2 : 0 ≤ max T 1 := le_trans zero_le_one (le_max_right _ _)
    positivity
  have hCY : (0 : ℝ) ≤ (2 * Real.exp T * (5 + 4 * c) + 4 * T)
      * (4 * L ^ 2 * (3 * max T c * (10 * L ^ 2 * max T 1)) + 10 * L ^ 2 * max T 1) := by
    have h1 : 0 ≤ max T 1 := le_trans zero_le_one (le_max_right _ _)
    have h2 : (0 : ℝ) ≤ 2 * Real.exp T * (5 + 4 * c) + 4 * T := by
      have := Real.exp_pos T
      nlinarith
    exact mul_nonneg h2 (add_nonneg (mul_nonneg (by positivity) hCX) (by positivity))
  have hsum : supSize P ν T (fun i t ω => X₁' i t ω - X₂' i t ω)
      (fun k t ω => Y₁' k t ω - Y₂' k t ω) (fun k t ω j => Z₁' k t ω j - Z₂' k t ω j)
      (fun k t ω e => U₁' k t ω e - U₂' k t ω e)
      = ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => X₁' i t ω - X₂' i t ω)) ∂P
        + (∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun k => Y₁' k t ω - Y₂' k t ω)) ∂P
          + ((∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z₁' k s ω j - Z₂' k s ω j))
            + ∑ k, Poisson.Compensated.markedEnergy P ν T
              (fun ω s e => U₁' k s ω e - U₂' k s ω e))) := by
    unfold supSize
    ring
  refine ⟨?_, ?_, ?_⟩
  -- the squared norm of the difference of the images
  · unfold supSize
    ring
  -- (4.10) and (4.12)
  · rw [hsum]
    refine (add_le_add hX hY).trans_eq ?_
    rw [← add_mul, ← ENNReal.ofReal_add (mul_nonneg hCX (sq_nonneg lam))
      (mul_nonneg hCY (sq_nonneg lam))]
    congr 2
    ring
  -- `C_X + C_Y ≤ C_Φ`
  · gcongr
    exact le_max_right _ _

end MVFBSDEJ.Acceptance
