/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Existence.OriginBound

/-!
# The coefficient processes along a solution as a forcing

In the continuation step from `λ₀ = 0`, a solution `Θ` of the `λ₀`-forced system (4.1)
generates the forcing

`Ψ(Θ) = (b(s, Θ_s, μ_s), σ(s, Θ_s, μ_s), h(s, Θ_s, ·, μ_s), f(s, Θ_s, μ_s), g(X_T, Law X_T))`.

A `λ = 0` solution does not see its coefficients, so the regularity of `Ψ(Θ)` has to come from
the coefficients: its measurability from (2.5), the hypothesis `CoeffRegular`, and its square
integrability from Assumptions 2.2–2.3, through (4.2) for the four processes and, for the
terminal value, through the terminal bound (2.6) against `(0, δ₀)`:

`𝔼|g(X_T, Law X_T)|² ≤ 8 L² 𝔼|X_T|² + 2 |g(0, δ₀)|²`.   (4.3)

The terminal value is measurable once `g` is Borel measurable in the state. The conclusion holds
along a solution at every `λ`, over a filtration on which Lemma 4.1 applies, which puts the
coordinates of `X` and `Y` in `S²(0, T)`.

## Main statements

* `lintegral_esq_terminalVal_le` — (4.3).
* `ProgTuple.forcing_coeff` — along a progressive tuple with finite energies and a
  cross-evaluation, the coefficient processes form a forcing.
* `SolvesForced.exists_forcing_coeff` — along a solution, for coefficients with (2.5) and
  Assumptions 2.2–2.3, the coefficient processes form a forcing, with a jointly measurable,
  marked progressively measurable representative of the jump coefficient.
-/

open MeasureTheory Filter WithLp Dissertation.Law
open scoped NNReal ENNReal

namespace Dissertation.WellPosedness.Existence

open Dissertation.WellPosedness.Stability Dissertation.WellPosedness.System LevyStochCalc
  LevyStochCalc.BSDEJ.Solves

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}
  {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {T L : ℝ} {C : Coeffs ν n m d} {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ}
  {Z : Fin m → ℝ → Ω → Fin d → ℝ} {U : Fin m → ℝ → Ω → E → ℝ} {γ : Fin n → ℝ → Ω → E → ℝ}

omit [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
/-- **(4.3), the terminal value is square integrable.** For `X_T` strongly `ℱ_T`-measurable and
square integrable, and `g` satisfying (2.6) along the diagonal with constant `L`,

`𝔼|g(X_T, Law X_T)|² ≤ 8 L² 𝔼|X_T|² + 2 |g(0, δ₀)|²`. -/
theorem lintegral_esq_terminalVal_le (hLT : TerminalLipschitz ℱ P T L C.g)
    (hXm : ∀ i, Measurable[ℱ T] (X i T)) (hX2 : ∀ i, MemLp (X i T) 2 P) :
    ∫⁻ ω, esq (fun k => terminalVal P T C X k ω) ∂P
      ≤ ENNReal.ofReal (8 * L ^ 2) * ∫⁻ ω, esq (fun i => X i T ω) ∂P
        + 2 * ‖C.g 0 (P2.dirac 0)‖ₑ ^ 2 := by
  have hL : MemLp (fun ω => (toLp 2 fun i => X i T ω : EuclideanSpace ℝ (Fin n))) 2 P :=
    memLp_toLp_of_forall (u := fun ω i => X i T ω) hX2
  have hb := hLT _ (fun _ => 0) (measurable_toLp_of_forall (mΩ := ℱ T) hXm).stronglyMeasurable
    stronglyMeasurable_const hL (memLp_const 0)
  simp only [lawP2_const_zero, sub_zero] at hb
  have hx : ∀ ω, ENNReal.ofReal (‖(toLp 2 fun i => X i T ω : EuclideanSpace ℝ (Fin n))‖ ^ 2)
      = esq (fun i => X i T ω) := fun ω => by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, esq_eq_enorm_sq]
  set W := w2P (lawP2 P fun ω => (toLp 2 fun i => X i T ω : EuclideanSpace ℝ (Fin n)))
    (P2.dirac 0)
  have hW : ENNReal.ofReal (W ^ 2) ≤ ∫⁻ ω, esq (fun i => X i T ω) ∂P := by
    have h0 := ofReal_w2P_lawP2_sq_le hL
      (memLp_const (0 : EuclideanSpace ℝ (Fin n)) (μ := P) (p := 2))
    rw [lawP2_const_zero] at h0
    simpa only [sub_zero, hx] using h0
  have h4 : ENNReal.ofReal (4 * L ^ 2) = 2 * ENNReal.ofReal (2 * L ^ 2) := by
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
    ring_nf
  have h8 : ENNReal.ofReal (8 * L ^ 2) = 2 * ENNReal.ofReal (4 * L ^ 2) := by
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
    ring_nf
  calc ∫⁻ ω, esq (fun k => terminalVal P T C X k ω) ∂P
      ≤ ∫⁻ ω, (ENNReal.ofReal (4 * L ^ 2) * (esq (fun i => X i T ω) + ENNReal.ofReal (W ^ 2))
          + 2 * ‖C.g 0 (P2.dirac 0)‖ₑ ^ 2) ∂P := by
        refine lintegral_mono_ae ?_
        filter_upwards [hb] with ω hω
        rw [esq_eq_enorm_sq, ← hx, show (toLp 2 fun k => terminalVal P T C X k ω)
          = C.g (toLp 2 fun i => X i T ω) (lawP2 P fun ω => toLp 2 fun i => X i T ω) from
            toLp_ofLp 2 _]
        calc _ ≤ 2 * ‖C.g (toLp 2 fun i => X i T ω) (lawP2 P fun ω => toLp 2 fun i => X i T ω)
              - C.g 0 (P2.dirac 0)‖ₑ ^ 2 + 2 * ‖C.g 0 (P2.dirac 0)‖ₑ ^ 2 :=
              enorm_sq_le_two_mul_sub_add _ _
          _ ≤ 2 * (ENNReal.ofReal (2 * L ^ 2)
                * (ENNReal.ofReal (‖(toLp 2 fun i => X i T ω : EuclideanSpace ℝ (Fin n))‖ ^ 2)
                  + ENNReal.ofReal (W ^ 2))) + 2 * ‖C.g 0 (P2.dirac 0)‖ₑ ^ 2 := by
              gcongr
              exact enorm_sq_le_of_le_mul_add _ hω
          _ = _ := by
              rw [h4]
              ring
    _ = ENNReal.ofReal (4 * L ^ 2) * (∫⁻ ω, esq (fun i => X i T ω) ∂P + ENNReal.ofReal (W ^ 2))
          + 2 * ‖C.g 0 (P2.dirac 0)‖ₑ ^ 2 := by
        rw [lintegral_add_right _ measurable_const,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_right _ measurable_const,
          lintegral_const, lintegral_const, measure_univ, mul_one, mul_one]
    _ ≤ ENNReal.ofReal (4 * L ^ 2) * (∫⁻ ω, esq (fun i => X i T ω) ∂P
          + ∫⁻ ω, esq (fun i => X i T ω) ∂P) + 2 * ‖C.g 0 (P2.dirac 0)‖ₑ ^ 2 := by
        gcongr
    _ = _ := by
        rw [h8]
        ring

/-- **The coefficient processes along a progressive tuple form a forcing.** Let
`(X, Y, Z, U)` be a progressive tuple whose `X` and `Y` have finite energy on `[0, T]` and whose
`X_T` is square integrable, let the coefficients `C` have the cross-evaluation along it with jump
representative `γ`, satisfy Assumption 2.2 and Assumption 2.3 along the diagonal, and let `g` be
Borel measurable in the state. Then
`(b(s, Θ_s, μ_s), σ(s, Θ_s, μ_s), γ, f(s, Θ_s, μ_s), g(X_T, Law X_T))`, each process extended by
`0` off `[0, T]`, is a forcing. -/
theorem ProgTuple.forcing_coeff (hΘ : ProgTuple ℱ P ν T X Y Z U)
    (hXe : ∀ i, Brownian.Ito.energy P T (fun ω s => X i s ω) ≠ ⊤)
    (hYe : ∀ k, Brownian.Ito.energy P T (fun ω s => Y k s ω) ≠ ⊤)
    (hXT : ∀ i, MemLp (X i T) 2 P) (hγ : CrossEval ℱ P T C X Y Z U γ)
    (horig : CoeffOrigin T C) (hL : DiagonalLipschitz ℱ P T L C)
    (hLT : TerminalLipschitz ℱ P T L C.g) (hg : ∀ ρ, Measurable fun x => C.g x ρ) :
    Forcing ℱ P ν T (driftProc P T C X Y Z U) (diffusionProc P T C X Y Z U) (jumpProc T γ)
      (driverProc P T C X Y Z U) (terminalVal P T C X) := by
  have hfin : ENNReal.ofReal (20 * L ^ 2) * (∑ i, Brownian.Ito.energy P T (fun ω s => X i s ω)
      + (∑ k, Brownian.Ito.energy P T (fun ω s => Y k s ω)
        + ∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z k s ω j)
        + ∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U k s ω e)))
      + 2 * ∫⁻ s in Set.Icc (0 : ℝ) T, originSq C s ≠ ⊤ := by
    refine ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_,
      ENNReal.mul_ne_top (by norm_num) (lintegral_originSq_lt_top horig).ne⟩
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.sum_ne_top.mpr fun i _ => hXe i,
      ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.sum_ne_top.mpr fun k _ => hYe k,
        ENNReal.sum_ne_top.mpr fun k _ => ENNReal.sum_ne_top.mpr fun j _ => hΘ.Z_sq k j⟩,
        ENNReal.sum_ne_top.mpr fun k _ => hΘ.U_sq k⟩⟩
  obtain ⟨hBSH, hF⟩ := ENNReal.add_ne_top.mp
    (ne_top_of_le_ne_top hfin (hΘ.coeffEnergy_le hXe hYe hγ hL))
  obtain ⟨hBS, hH⟩ := ENNReal.add_ne_top.mp hBSH
  obtain ⟨hB, hS⟩ := ENNReal.add_ne_top.mp hBS
  have hG : ∫⁻ ω, esq (fun k => terminalVal P T C X k ω) ∂P ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top (lintegral_esq_lt_top hXT).ne,
        ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top enorm_ne_top)⟩)
      (lintegral_esq_terminalVal_le hLT (fun i => hΘ.X_adapted i T) hXT)
  exact
    { qb_meas := hγ.b_meas
      qb_prog := hγ.b_prog
      qb_vanish := fun i ω s hs => by simp [driftProc, Set.indicator_of_notMem hs]
      qb_sq := fun i => ENNReal.sum_ne_top.mp hB i (Finset.mem_univ i)
      qσ_meas := hγ.σ_meas
      qσ_prog := hγ.σ_prog
      qσ_vanish := fun i ω s hs => by
        funext j
        simp [diffusionProc, Set.indicator_of_notMem hs]
      qσ_sq := fun i j =>
        ENNReal.sum_ne_top.mp (ENNReal.sum_ne_top.mp hS i (Finset.mem_univ i)) j (Finset.mem_univ j)
      qh_meas := hγ.h_meas
      qh_prog := hγ.h_prog
      qh_vanish := fun i ω s e hs => by simp [jumpProc, Set.indicator_of_notMem hs]
      qh_sq := fun i => ENNReal.sum_ne_top.mp hH i (Finset.mem_univ i)
      qf_meas := hγ.f_meas
      qf_prog := hγ.f_prog
      qf_vanish := fun k ω s hs => by simp [driverProc, Set.indicator_of_notMem hs]
      qf_sq := fun k => ENNReal.sum_ne_top.mp hF k (Finset.mem_univ k)
      qg_meas := fun k => stronglyMeasurable_terminalVal hg (fun i => hΘ.X_adapted i T) k
      qg_sq := fun k => Brownian.Ito.memLp_two_of_lintegral_sq_lt_top
        ((stronglyMeasurable_terminalVal hg (fun i => hΘ.X_adapted i T) k).mono
          (ℱ.le T)).aestronglyMeasurable
        ((lintegral_mono fun ω => Finset.single_le_sum
          (f := fun k => (‖terminalVal P T C X k ω‖₊ : ℝ≥0∞) ^ 2) (fun _ _ => zero_le)
          (Finset.mem_univ k)).trans_lt (lt_top_iff_ne_top.mpr hG)) }

variable {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {lam : ℝ} {ξ₀ : Fin n → Ω → ℝ}
  {qb : Fin n → Ω → ℝ → ℝ} {qσ : Fin n → ℝ → Ω → Fin d → ℝ} {qh : Fin n → ℝ → Ω → E → ℝ}
  {qf : Fin m → Ω → ℝ → ℝ} {qg : Fin m → Ω → ℝ}

/-- **The coefficient processes along a solution form a forcing**, for coefficients with (2.5)
along every progressive tuple, Assumption 2.2, and Assumption 2.3 along the diagonal with `g`
Borel measurable in the state: for a solution `(X, Y, Z, U)` of the `λ`-forced system over a
filtration whose null sets lie in its time-`0` field, whose right-continuation is constant
before `0` and which admits a cross witness, there is a jointly measurable, marked
progressively measurable representative `γ'` of the jump coefficient along the solution with
which `(b(s, Θ_s, μ_s), σ(s, Θ_s, μ_s), γ', f(s, Θ_s, μ_s), g(X_T, Law X_T))` is a forcing. -/
theorem _root_.Dissertation.WellPosedness.System.SolvesForced.exists_forcing_coeff
    (h : SolvesForced D ℱ hℱW hℱN T lam C ξ₀ qb qσ qh qf qg X Y Z U γ) (𝒲 : D.CrossWitness ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T)
    (hreg : CoeffRegular ℱ P T C) (horig : CoeffOrigin T C) (hL : DiagonalLipschitz ℱ P T L C)
    (hLT : TerminalLipschitz ℱ P T L C.g) (hg : ∀ ρ, Measurable fun x => C.g x ρ) :
    ∃ γ' : Fin n → ℝ → Ω → E → ℝ, CrossEval ℱ P T C X Y Z U γ'
      ∧ Forcing ℱ P ν T (driftProc P T C X Y Z U) (diffusionProc P T C X Y Z U) (jumpProc T γ')
        (driverProc P T C X Y Z U) (terminalVal P T C X) := by
  obtain ⟨γ', hγ'⟩ := hreg X Y Z U h.progTuple
  refine ⟨γ', hγ', h.progTuple.forcing_coeff (fun i => ?_) (fun k => ?_)
    (fun i => (h.fwd i).memLp_terminal hT.le) hγ' horig hL hLT hg⟩
  · exact (energy_le_of_biSup.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (((h.fwd i).linearBSDEJ hT.le).lintegral_biSup_sq_lt_top 𝒲 hℱ0 hnull hT))).ne
  · exact (energy_le_of_biSup.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      ((h.bwd k).lintegral_biSup_sq_lt_top 𝒲 hℱ0 hnull hT))).ne

end Dissertation.WellPosedness.Existence
