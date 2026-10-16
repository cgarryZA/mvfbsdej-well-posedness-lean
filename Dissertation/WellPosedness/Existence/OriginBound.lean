/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Existence.WPZero
import Dissertation.WellPosedness.Existence.SizeCompare
import Dissertation.WellPosedness.System.BridgeLip

/-!
# Square integrability of the coefficient processes, (4.2)

Under Assumption 2.2 — the origin values `b(·, 0, δ₀)`, `σ(·, 0, δ₀)`, `h(·, 0, ·, δ₀)`,
`f(·, 0, δ₀)` are square integrable in time over `[0, T]` — and Assumption 2.3, the coefficient
processes along a progressive tuple `Θ` whose `X` and `Y` have finite energy are square
integrable: Assumption 2.3 against the diagonal input `(0, δ₀)`, with `Law 0 = δ₀` and the
coupling bound `W₂(μ_s, δ₀)² ≤ 𝔼‖Θ_s‖²`, gives

`𝔼 ∫_0^T (|b|² + |σ|²_F + ‖h‖²_{L²(ν)} + |f|²)
  ≤ 20 L² 𝔼 ∫_0^T (|X|² + |Y|² + |Z|²_F + ‖U‖²_{L²(ν)}) + 2 ∫_0^T |ψ(s, 0, δ₀)|² ds`,   (4.2)

with `|ψ(s, 0, δ₀)|²` the sum of the four squared origin values. The coefficients are evaluated
along `(Θ_s, Law Θ_s)`, and the jump coefficient through a representative `γ`; the measurability
of the four processes, needed to integrate in time, is that of a cross-evaluation.

## Main definitions

* `CoeffOrigin` — Assumption 2.2 for the coefficients.
* `originSq` — the sum `|b(s, 0, δ₀)|² + |σ(s, 0, δ₀)|²_F + ‖h(s, 0, δ₀)‖² + |f(s, 0, δ₀)|²`.

## Main statements

* `lawP2_const_zero` — the law of the zero random element is `δ₀`.
* `enorm_sq_le_two_mul_sub_add`, `enorm_sq_add_le_of_sub_le` — squaring a Lipschitz bound
  against a base point.
* `lintegral_originSq_lt_top` — under Assumption 2.2 the origin values have finite integral.
* `ProgTuple.coeffEnergy_le` — (4.2).
-/

open MeasureTheory Filter WithLp Dissertation.Law
open scoped NNReal ENNReal

namespace Dissertation.WellPosedness.Existence

open Dissertation.WellPosedness.Stability Dissertation.WellPosedness.System LevyStochCalc

universe u v w

/-! ### Auxiliary facts -/

/-- **The law of the zero random element** is the Dirac mass at the origin. -/
theorem lawP2_const_zero {F : Type*} [NormedAddCommGroup F] [MeasurableSpace F] [BorelSpace F]
    [MeasurableSingletonClass F] {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] : lawP2 P (fun _ : Ω => (0 : F)) = P2.dirac 0 :=
  P2.ext_law (by rw [lawP2_law (memLp_const 0), Measure.map_const, measure_univ, one_smul]; rfl)

section Square

variable {F₁ F₂ F₃ F₄ : Type*} [NormedAddCommGroup F₁] [NormedAddCommGroup F₂]
  [NormedAddCommGroup F₃] [NormedAddCommGroup F₄]

/-- `‖a‖² ≤ 2 ‖a − o‖² + 2 ‖o‖²`, in `ℝ≥0∞`. -/
theorem enorm_sq_le_two_mul_sub_add (a o : F₁) : ‖a‖ₑ ^ 2 ≤ 2 * ‖a - o‖ₑ ^ 2 + 2 * ‖o‖ₑ ^ 2 := by
  have h : ‖a‖ ≤ ‖a - o‖ + ‖o‖ := by simpa using norm_add_le (a - o) o
  have h₁ := norm_nonneg (a - o)
  have h₂ := norm_nonneg o
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_pow h₁, ← ENNReal.ofReal_pow h₂, ← ENNReal.ofReal_ofNat 2,
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (‖a - o‖ - ‖o‖), norm_nonneg a])

/-- **Squaring a Lipschitz bound against a base point**: if
`|a₁ − o₁| + |a₂ − o₂| + |a₃ − o₃| + |a₄ − o₄| ≤ L (x + w)`, then
`|a₁|² + |a₂|² + |a₃|² + |a₄|² ≤ 4L² (x² + w²) + 2 (|o₁|² + |o₂|² + |o₃|² + |o₄|²)`. -/
theorem enorm_sq_add_le_of_sub_le (a₁ o₁ : F₁) (a₂ o₂ : F₂) (a₃ o₃ : F₃) (a₄ o₄ : F₄)
    {L x w : ℝ} (h : ‖a₁ - o₁‖ + ‖a₂ - o₂‖ + ‖a₃ - o₃‖ + ‖a₄ - o₄‖ ≤ L * (x + w)) :
    ‖a₁‖ₑ ^ 2 + ‖a₂‖ₑ ^ 2 + ‖a₃‖ₑ ^ 2 + ‖a₄‖ₑ ^ 2
      ≤ ENNReal.ofReal (4 * L ^ 2) * (ENNReal.ofReal (x ^ 2) + ENNReal.ofReal (w ^ 2))
        + 2 * (‖o₁‖ₑ ^ 2 + ‖o₂‖ₑ ^ 2 + ‖o₃‖ₑ ^ 2 + ‖o₄‖ₑ ^ 2) := by
  have hv := enorm_sq_add_le_of_le_mul_add _ _ _ _ h
  have h4 : ENNReal.ofReal (4 * L ^ 2) = 2 * ENNReal.ofReal (2 * L ^ 2) := by
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
    ring_nf
  calc ‖a₁‖ₑ ^ 2 + ‖a₂‖ₑ ^ 2 + ‖a₃‖ₑ ^ 2 + ‖a₄‖ₑ ^ 2
      ≤ (2 * ‖a₁ - o₁‖ₑ ^ 2 + 2 * ‖o₁‖ₑ ^ 2) + (2 * ‖a₂ - o₂‖ₑ ^ 2 + 2 * ‖o₂‖ₑ ^ 2)
        + (2 * ‖a₃ - o₃‖ₑ ^ 2 + 2 * ‖o₃‖ₑ ^ 2) + (2 * ‖a₄ - o₄‖ₑ ^ 2 + 2 * ‖o₄‖ₑ ^ 2) := by
        gcongr <;> exact enorm_sq_le_two_mul_sub_add _ _
    _ = 2 * (‖a₁ - o₁‖ₑ ^ 2 + ‖a₂ - o₂‖ₑ ^ 2 + ‖a₃ - o₃‖ₑ ^ 2 + ‖a₄ - o₄‖ₑ ^ 2)
        + 2 * (‖o₁‖ₑ ^ 2 + ‖o₂‖ₑ ^ 2 + ‖o₃‖ₑ ^ 2 + ‖o₄‖ₑ ^ 2) := by ring
    _ ≤ _ := by
        rw [h4, mul_assoc]
        gcongr

end Square

/-- The squared `L²` norm of a square-integrable function is finite. -/
theorem lintegral_enorm_sq_lt_top {α F : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup F] {f : α → F} (hf : MemLp f 2 μ) : ∫⁻ a, ‖f a‖ₑ ^ 2 ∂μ < ⊤ := by
  rw [← eLpNorm_two_sq]
  exact ENNReal.pow_lt_top hf.eLpNorm_lt_top

/-! ### Assumption 2.2 -/

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}

/-- **Assumption 2.2 for the coefficients**: the origin values `b(·, 0, δ₀)`, `σ(·, 0, δ₀)`,
`h(·, 0, ·, δ₀)` and `f(·, 0, δ₀)` are square integrable in time over `[0, T]`. -/
def CoeffOrigin (T : ℝ) (C : Coeffs ν n m d) : Prop :=
  OriginIntegrable T (fun t => C.b t 0 (P2.dirac 0)) (fun t => C.σ t 0 (P2.dirac 0))
    (fun t => C.h t 0 (P2.dirac 0)) (fun t => C.f t 0 (P2.dirac 0))

/-- The sum `|b(s, 0, δ₀)|² + |σ(s, 0, δ₀)|²_F + ‖h(s, 0, δ₀)‖²_{L²(ν)} + |f(s, 0, δ₀)|²` of the
squared origin values at time `s`. -/
noncomputable def originSq (C : Coeffs ν n m d) (s : ℝ) : ℝ≥0∞ :=
  ‖C.b s 0 (P2.dirac 0)‖ₑ ^ 2 + ‖C.σ s 0 (P2.dirac 0)‖ₑ ^ 2 + ‖C.h s 0 (P2.dirac 0)‖ₑ ^ 2
    + ‖C.f s 0 (P2.dirac 0)‖ₑ ^ 2

/-- Under Assumption 2.2 the squared origin values have finite integral over `[0, T]`. -/
theorem lintegral_originSq_lt_top {T : ℝ} {C : Coeffs ν n m d} (horig : CoeffOrigin T C) :
    ∫⁻ s in Set.Icc (0 : ℝ) T, originSq C s < ⊤ := by
  have hb : AEMeasurable (fun s => ‖C.b s 0 (P2.dirac 0)‖ₑ ^ 2)
      (volume.restrict (Set.Icc (0 : ℝ) T)) :=
    horig.b_memLp.aestronglyMeasurable.enorm.pow_const 2
  have hσ : AEMeasurable (fun s => ‖C.σ s 0 (P2.dirac 0)‖ₑ ^ 2)
      (volume.restrict (Set.Icc (0 : ℝ) T)) :=
    horig.σ_memLp.aestronglyMeasurable.enorm.pow_const 2
  have hh : AEMeasurable (fun s => ‖C.h s 0 (P2.dirac 0)‖ₑ ^ 2)
      (volume.restrict (Set.Icc (0 : ℝ) T)) :=
    horig.h_memLp.aestronglyMeasurable.enorm.pow_const 2
  have hbσ : AEMeasurable (fun s => ‖C.b s 0 (P2.dirac 0)‖ₑ ^ 2 + ‖C.σ s 0 (P2.dirac 0)‖ₑ ^ 2)
      (volume.restrict (Set.Icc (0 : ℝ) T)) := hb.add hσ
  have hbσh : AEMeasurable (fun s => ‖C.b s 0 (P2.dirac 0)‖ₑ ^ 2
      + ‖C.σ s 0 (P2.dirac 0)‖ₑ ^ 2 + ‖C.h s 0 (P2.dirac 0)‖ₑ ^ 2)
      (volume.restrict (Set.Icc (0 : ℝ) T)) := hbσ.add hh
  unfold originSq
  rw [lintegral_add_left' hbσh, lintegral_add_left' hbσ, lintegral_add_left' hb]
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr
    ⟨lintegral_enorm_sq_lt_top horig.b_memLp, lintegral_enorm_sq_lt_top horig.σ_memLp⟩,
    lintegral_enorm_sq_lt_top horig.h_memLp⟩, lintegral_enorm_sq_lt_top horig.f_memLp⟩

/-! ### The bounds (4.2)–(4.3) -/

variable {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {T L : ℝ} {C : Coeffs ν n m d} {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ}
  {Z : Fin m → ℝ → Ω → Fin d → ℝ} {U : Fin m → ℝ → Ω → E → ℝ} {γ : Fin n → ℝ → Ω → E → ℝ}

/-- **(4.2), the coefficient processes along a progressive tuple are square integrable.** Let
`(X, Y, Z, U)` be a progressive tuple whose `X` and `Y` have finite energy on `[0, T]`, let the
coefficients `C` have the cross-evaluation along it with jump representative `γ`, and satisfy
Assumption 2.3 along the diagonal with constant `L`. Then

`𝔼 ∫_0^T (|b|² + |σ|²_F + ‖γ‖²_{L²(ν)} + |f|²)
  ≤ 20 L² 𝔼 ∫_0^T (|X|² + |Y|² + |Z|²_F + ‖U‖²_{L²(ν)}) + 2 ∫_0^T |ψ(s, 0, δ₀)|² ds`,

the coefficients evaluated along `(Θ_s, Law Θ_s)`. -/
theorem ProgTuple.coeffEnergy_le (hΘ : ProgTuple ℱ P ν T X Y Z U)
    (hXe : ∀ i, Brownian.Ito.energy P T (fun ω s => X i s ω) ≠ ⊤)
    (hYe : ∀ k, Brownian.Ito.energy P T (fun ω s => Y k s ω) ≠ ⊤)
    (hγ : CrossEval ℱ P T C X Y Z U γ) (hL : DiagonalLipschitz ℱ P T L C) :
    ∑ i, Brownian.Ito.energy P T (driftProc P T C X Y Z U i)
        + ∑ i, ∑ j, Brownian.Ito.energy P T (fun ω s => diffusionProc P T C X Y Z U i s ω j)
        + ∑ i, Poisson.Compensated.markedEnergy P ν T (fun ω s e => jumpProc T γ i s ω e)
        + ∑ k, Brownian.Ito.energy P T (driverProc P T C X Y Z U k)
      ≤ ENNReal.ofReal (20 * L ^ 2) * (∑ i, Brownian.Ito.energy P T (fun ω s => X i s ω)
          + (∑ k, Brownian.Ito.energy P T (fun ω s => Y k s ω)
            + ∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z k s ω j)
            + ∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U k s ω e)))
        + 2 * ∫⁻ s in Set.Icc (0 : ℝ) T, originSq C s := by
  have hAm := measurable_sampleEnergy_add (P := P) (ν := ν) (x := driftProc P T C X Y Z U)
    (z := fun i j ω s => diffusionProc P T C X Y Z U i s ω j)
    (u := fun i ω s e => jumpProc T γ i s ω e) hγ.b_meas hγ.σ_meas hγ.h_meas
  have hRm : Measurable fun s => sampleEnergy P (fun i ω s => X i s ω) s
      + (sampleEnergy P (fun k ω s => Y k s ω) s + ∑ k, sampleEnergy P (fun j ω s => Z k s ω j) s
        + markedSampleEnergy P ν (fun k ω s e => U k s ω e) s) :=
    (measurable_sampleEnergy (P := P) (x := fun i ω s => X i s ω) hΘ.measurable_X).add
    (measurable_sampleEnergy_add (P := P) (ν := ν) (x := fun k ω s => Y k s ω)
      (z := fun k j ω s => Z k s ω j) (u := fun k ω s e => U k s ω e) hΘ.measurable_Y hΘ.Z_meas
      hΘ.U_meas)
  -- the bound at almost every time
  have hpt : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      sampleEnergy P (driftProc P T C X Y Z U) s
          + ∑ i, sampleEnergy P (fun j ω s => diffusionProc P T C X Y Z U i s ω j) s
          + markedSampleEnergy P ν (fun i ω s e => jumpProc T γ i s ω e) s
          + sampleEnergy P (driverProc P T C X Y Z U) s
        ≤ ENNReal.ofReal (20 * L ^ 2) * (sampleEnergy P (fun i ω s => X i s ω) s
            + (sampleEnergy P (fun k ω s => Y k s ω) s
              + ∑ k, sampleEnergy P (fun j ω s => Z k s ω j) s
              + markedSampleEnergy P ν (fun k ω s e => U k s ω e) s))
          + 2 * originSq C s := by
    filter_upwards [hL, ae_restrict_mem measurableSet_Icc, hγ.jump_rep,
      hΘ.ae_memLp_tupleAt hXe hYe] with s hLs hs hr hm
    have hb := hLs _ (fun _ => 0) (hΘ.stronglyMeasurable_tupleAt s) stronglyMeasurable_const hm
      (memLp_const 0)
    simp only [lawP2_const_zero, sub_zero] at hb
    have hW : ENNReal.ofReal (w2P (lawP2 P (tupleAt ν X Y Z U s)) (P2.dirac 0) ^ 2)
        ≤ ∫⁻ ω, (∑ i, (‖X i s ω‖₊ : ℝ≥0∞) ^ 2 + ∑ k, (‖Y k s ω‖₊ : ℝ≥0∞) ^ 2
          + ∑ k, ∑ j, (‖Z k s ω j‖₊ : ℝ≥0∞) ^ 2
          + ∑ k, ∫⁻ e, (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ∂P := by
      have h0 := ofReal_w2P_lawP2_sq_le hm (memLp_const (0 : TupleH ν n m d) (μ := P) (p := 2))
      rw [lawP2_const_zero] at h0
      refine h0.trans (lintegral_mono fun ω => ?_)
      rw [sub_zero]
      exact (ENNReal.ofReal_le_ofReal (norm_sq_le_channelSq _)).trans
        (ofReal_channelSq_tupleAt_le s ω)
    have htN : ∀ ω, ENNReal.ofReal (tupleNorm (tupleAt ν X Y Z U s ω) ^ 2)
        ≤ 4 * (∑ i, (‖X i s ω‖₊ : ℝ≥0∞) ^ 2 + ∑ k, (‖Y k s ω‖₊ : ℝ≥0∞) ^ 2
          + ∑ k, ∑ j, (‖Z k s ω j‖₊ : ℝ≥0∞) ^ 2
          + ∑ k, ∫⁻ e, (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν) := fun ω => by
      calc _ ≤ ENNReal.ofReal (4 * channelSq (tupleAt ν X Y Z U s ω)) :=
            ENNReal.ofReal_le_ofReal (tupleNorm_sq_le _)
        _ = 4 * ENNReal.ofReal (channelSq (tupleAt ν X Y Z U s ω)) := by
            rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
        _ ≤ _ := by
            gcongr
            exact ofReal_channelSq_tupleAt_le s ω
    have eb : ∀ ω, C.b s (tupleAt ν X Y Z U s ω) (lawP2 P (tupleAt ν X Y Z U s))
        = toLp 2 fun i => driftProc P T C X Y Z U i ω s := fun ω =>
      (toLp_ofLp 2 _).symm.trans (congrArg (toLp 2) (funext fun i => (driftProc_of_mem hs i).symm))
    have eσ : ∀ ω, C.σ s (tupleAt ν X Y Z U s ω) (lawP2 P (tupleAt ν X Y Z U s))
        = toLp 2 fun p : Fin n × Fin d => diffusionProc P T C X Y Z U p.1 s ω p.2 := fun ω =>
      (toLp_ofLp 2 _).symm.trans (congrArg (toLp 2) (funext fun p =>
        (diffusionProc_of_mem hs p.1 p.2).symm))
    have ef : ∀ ω, C.f s (tupleAt ν X Y Z U s ω) (lawP2 P (tupleAt ν X Y Z U s))
        = toLp 2 fun k => driverProc P T C X Y Z U k ω s := fun ω =>
      (toLp_ofLp 2 _).symm.trans (congrArg (toLp 2) (funext fun k =>
        (driverProc_of_mem hs k).symm))
    calc _ ≤ ∫⁻ ω, esq (fun i => driftProc P T C X Y Z U i ω s) ∂P
            + ∫⁻ ω, ∑ i, esq (fun j => diffusionProc P T C X Y Z U i s ω j) ∂P
            + ∫⁻ ω, ∑ i, ∫⁻ e, (‖jumpProc T γ i s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P
            + ∫⁻ ω, esq (fun k => driverProc P T C X Y Z U k ω s) ∂P := by
          gcongr
          · exact le_lintegral_finsetSum _ _
          · exact (Finset.sum_le_sum fun i _ => le_lintegral_finsetSum _ _).trans
              (le_lintegral_finsetSum _ _)
          · exact le_lintegral_finsetSum _ _
          · exact le_lintegral_finsetSum _ _
      _ ≤ ∫⁻ ω, (esq (fun i => driftProc P T C X Y Z U i ω s)
            + ∑ i, esq (fun j => diffusionProc P T C X Y Z U i s ω j)
            + ∑ i, ∫⁻ e, (‖jumpProc T γ i s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν
            + esq (fun k => driverProc P T C X Y Z U k ω s)) ∂P :=
          (add_le_add (add_le_add (le_lintegral_add _ _) le_rfl) le_rfl).trans
            ((add_le_add (le_lintegral_add _ _) le_rfl).trans (le_lintegral_add _ _))
      _ ≤ ∫⁻ ω, (ENNReal.ofReal (4 * L ^ 2)
            * (ENNReal.ofReal (tupleNorm (tupleAt ν X Y Z U s ω) ^ 2)
              + ENNReal.ofReal (w2P (lawP2 P (tupleAt ν X Y Z U s)) (P2.dirac 0) ^ 2))
            + 2 * originSq C s) ∂P := by
          refine lintegral_mono_ae ?_
          filter_upwards [hb, hr] with ω hω hrω
          refine le_trans ?_ (enorm_sq_add_le_of_sub_le _ _ _ _ _ _ _ _ hω)
          rw [esq_eq_enorm_sq, esq_eq_enorm_sq, sum_esq_eq_enorm_sq, ← eb, ← eσ, ← ef]
          gcongr
          simp only [jumpProc_of_mem hs]
          exact sum_lintegral_le_enorm_sq hrω
      _ = ENNReal.ofReal (4 * L ^ 2)
            * (∫⁻ ω, ENNReal.ofReal (tupleNorm (tupleAt ν X Y Z U s ω) ^ 2) ∂P
              + ENNReal.ofReal (w2P (lawP2 P (tupleAt ν X Y Z U s)) (P2.dirac 0) ^ 2))
            + 2 * originSq C s := by
          rw [lintegral_add_right _ measurable_const,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_right _ measurable_const,
            lintegral_const, lintegral_const, measure_univ, mul_one, mul_one]
      _ ≤ ENNReal.ofReal (4 * L ^ 2)
            * (4 * ∫⁻ ω, (∑ i, (‖X i s ω‖₊ : ℝ≥0∞) ^ 2 + ∑ k, (‖Y k s ω‖₊ : ℝ≥0∞) ^ 2
              + ∑ k, ∑ j, (‖Z k s ω j‖₊ : ℝ≥0∞) ^ 2
              + ∑ k, ∫⁻ e, (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ∂P
            + ∫⁻ ω, (∑ i, (‖X i s ω‖₊ : ℝ≥0∞) ^ 2 + ∑ k, (‖Y k s ω‖₊ : ℝ≥0∞) ^ 2
              + ∑ k, ∑ j, (‖Z k s ω j‖₊ : ℝ≥0∞) ^ 2
              + ∑ k, ∫⁻ e, (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ∂P)
            + 2 * originSq C s := by
          gcongr
          rw [← lintegral_const_mul' _ _ (by norm_num)]
          exact lintegral_mono htN
      _ = _ := by
          have h20 : ENNReal.ofReal (20 * L ^ 2) = ENNReal.ofReal (4 * L ^ 2) * 5 := by
            rw [← ENNReal.ofReal_ofNat 5, ← ENNReal.ofReal_mul (by positivity)]
            ring_nf
          rw [hΘ.lintegral_coords_eq s, h20]
          ring
  -- integration in time
  calc _ = ∫⁻ s in Set.Icc (0 : ℝ) T, (sampleEnergy P (driftProc P T C X Y Z U) s
          + ∑ i, sampleEnergy P (fun j ω s => diffusionProc P T C X Y Z U i s ω j) s
          + markedSampleEnergy P ν (fun i ω s e => jumpProc T γ i s ω e) s
          + sampleEnergy P (driverProc P T C X Y Z U) s) := by
        rw [lintegral_add_left hAm, lintegral_sampleEnergy_add (P := P) (ν := ν)
          (x := driftProc P T C X Y Z U) (z := fun i j ω s => diffusionProc P T C X Y Z U i s ω j)
          (u := fun i ω s e => jumpProc T γ i s ω e) hγ.b_meas hγ.σ_meas hγ.h_meas T,
          lintegral_sampleEnergy hγ.f_meas T]
    _ ≤ ∫⁻ s in Set.Icc (0 : ℝ) T, (ENNReal.ofReal (20 * L ^ 2)
          * (sampleEnergy P (fun i ω s => X i s ω) s
            + (sampleEnergy P (fun k ω s => Y k s ω) s
              + ∑ k, sampleEnergy P (fun j ω s => Z k s ω j) s
              + markedSampleEnergy P ν (fun k ω s e => U k s ω e) s))
          + 2 * originSq C s) := lintegral_mono_ae hpt
    _ = _ := by
        rw [lintegral_add_left (hRm.const_mul _), lintegral_const_mul _ hRm,
          lintegral_const_mul' _ _ (by norm_num), lintegral_add_left
            (measurable_sampleEnergy (P := P) (x := fun i ω s => X i s ω) hΘ.measurable_X),
          lintegral_sampleEnergy hΘ.measurable_X T, lintegral_sampleEnergy_add (P := P) (ν := ν)
            (x := fun k ω s => Y k s ω) (z := fun k j ω s => Z k s ω j)
            (u := fun k ω s e => U k s ω e) hΘ.measurable_Y hΘ.Z_meas hΘ.U_meas T]

end Dissertation.WellPosedness.Existence
