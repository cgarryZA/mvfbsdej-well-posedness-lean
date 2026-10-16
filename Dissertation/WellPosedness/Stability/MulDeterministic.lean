/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Analysis.CellIntegrals
import Dissertation.WellPosedness.Stability.MulDeterministicLegs
/-!
# The product of a solution of the linear forward equation with a deterministic weight

Let `X` solve the linear forward equation

`X_t = ξ₀ + ∫_0^t b_s ds + ∫_0^t σ_s dW_s + ∫_0^t ∫_E γ_s(e) Ñ(ds, de)`,   `t ∈ [0, T]`,

and let `q` be a deterministic real function on `[0, T]` with continuous derivative `q'`. Then
`q X` solves the linear forward equation

`q(t) X_t = q(0) ξ₀ + ∫_0^t (q'(s) X_s + q(s) b_s) ds + ∫_0^t q(s) σ_s dW_s
  + ∫_0^t ∫_E q(s) γ_s(e) Ñ(ds, de)`,

the product rule for a deterministic weight. Off `[0, T]` the weight is read at the time clamped to
`[0, T]`, which keeps the paths of `q X` right-continuous without asking anything of `q` outside
the horizon, and the new drift is cut to `[0, T]`.

The identity is the integration by parts formula `ae_sub_eq_of_increment_le` applied to `V = X`
and to the three legs `M` of the weighted data `(q b, q σ, q γ)`: the increments of `X` are
controlled by the increment density of `(b, σ, γ)`, and `M_t − M_a − c (X_t − X_a)` is the
increment of the three legs of `((q − c) b, (q − c) σ, (q − c) γ)`. The formula then reads
`M_t = q(t) X_t − q(0) X_0 − ∫_0^t q' X ds`, which with `X_0 = ξ₀` is the equation above.

## Main definitions

* `clampTime T t` — the time `t` clamped to `[0, T]`.

## Main statements

* `LinearFSDEJ.mul_deterministic` — the product rule for a deterministic weight.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Dissertation.WellPosedness.Stability

open LevyStochCalc.BSDEJ.Solves LevyStochCalc Dissertation.WellPosedness.BrownianPoisson
  Dissertation.WellPosedness

universe u v w

/-! ### Clamping a time to the horizon -/

/-- The time `t` clamped to the horizon `[0, T]`: `max 0 (min t T)`. -/
def clampTime (T t : ℝ) : ℝ := max 0 (min t T)

/-- A time of the horizon is its own clamp. -/
theorem clampTime_of_mem {T t : ℝ} (ht : t ∈ Set.Icc 0 T) : clampTime T t = t := by
  rw [clampTime, min_eq_left ht.2, max_eq_right ht.1]

/-- The clamped time lies in the horizon. -/
theorem clampTime_mem {T : ℝ} (hT : 0 ≤ T) (t : ℝ) : clampTime T t ∈ Set.Icc 0 T :=
  ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩

/-- Clamping to the horizon is continuous. -/
theorem continuous_clampTime (T : ℝ) : Continuous (clampTime T) :=
  continuous_const.max (continuous_id.min continuous_const)

/-! ### The product rule -/

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ mΩ}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}
  {T : ℝ} {ξ₀ : Ω → ℝ} {b : Ω → ℝ → ℝ} {X : ℝ → Ω → ℝ} {σ : ℝ → Ω → (Fin d → ℝ)}
  {γ : ℝ → Ω → E → ℝ}

namespace LinearFSDEJ

/-- **The product rule for a deterministic weight.** If `X` solves the linear forward equation
with initial value `ξ₀`, drift `b`, diffusion vector `σ` and jump integrand `γ`, and `q` has
continuous derivative `q'` on `[0, T]`, then `q X` solves it with initial value `q(0) ξ₀`, drift
`q' X + q b` on `[0, T]`, diffusion vector `q σ` and jump integrand `q γ`:

`q(t) X_t = q(0) ξ₀ + ∫_0^t (q'(s) X_s + q(s) b_s) ds + ∫_0^t q(s) σ_s dW_s
  + ∫_0^t ∫_E q(s) γ_s(e) Ñ(ds, de)`.

Off `[0, T]` the weight is read at the clamped time. -/
theorem mul_deterministic (h : LinearFSDEJ D ℱ hℱW hℱN T ξ₀ b X σ γ) (hT : 0 ≤ T)
    {q q' : ℝ → ℝ} (hq : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt q (q' t) (Set.Icc 0 T) t)
    (hq' : ContinuousOn q' (Set.Icc 0 T)) :
    LinearFSDEJ D ℱ hℱW hℱN T (fun ω => q 0 * ξ₀ ω)
      (fun ω s => (Set.Icc 0 T).indicator (fun s => q' s * X s ω + q s * b ω s) s)
      (fun t ω => q (clampTime T t) * X t ω)
      (fun s ω j => q (clampTime T s) * σ s ω j) (fun s ω e => q (clampTime T s) * γ s ω e) := by
  -- the clamped weight and its derivative
  have hqc : ContinuousOn q (Set.Icc 0 T) := fun s hs => (hq s hs).continuousWithinAt
  have hQc : Continuous fun s => q (clampTime T s) :=
    hqc.comp_continuous (continuous_clampTime T) (clampTime_mem hT)
  have hQ'c : Continuous fun s => q' (clampTime T s) :=
    hq'.comp_continuous (continuous_clampTime T) (clampTime_mem hT)
  have hQm : Measurable fun s => q (clampTime T s) := hQc.measurable
  have hQ'm : Measurable fun s => q' (clampTime T s) := hQ'c.measurable
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hqc
  have hQB : ∀ s, |q (clampTime T s)| ≤ B := fun s => hB _ (clampTime_mem hT s)
  obtain ⟨B', hB'⟩ := isCompact_Icc.exists_bound_of_continuousOn hq'
  have hQ'B : ∀ s, |q' (clampTime T s)| ≤ B' := fun s => hB' _ (clampTime_mem hT s)
  -- the state
  have hXp := h.progressivelyMeasurable_state
  have hXE := h.energy_state_ne_top hT
  -- the weighted diffusion vector
  have hσm : ∀ j : Fin d,
      Measurable (Function.uncurry fun ω s => q (clampTime T s) * σ s ω j) := fun j =>
    (hQm.comp measurable_snd).mul (h.σ_meas j)
  have hσp : ∀ j : Fin d,
      Probability.ProgressivelyMeasurable ℱ fun ω s => q (clampTime T s) * σ s ω j := fun j =>
    progressivelyMeasurable_weight_mul hQm (h.σ_prog j)
  have hσv : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → (fun j => q (clampTime T s) * σ s ω j) = 0 :=
    fun ω s hs => by
      funext j
      simp [h.σ_vanish ω s hs]
  have hσq : ∀ j : Fin d,
      Brownian.Ito.energy P T (fun ω s => q (clampTime T s) * σ s ω j) ≠ ⊤ := fun j =>
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (h.σ_sq j))
      (energy_weight_mul_le hQB (fun ω s => σ s ω j) T)
  -- the weighted jump integrand
  have hγm : Measurable fun p : Ω × ℝ × E => q (clampTime T p.2.1) * γ p.2.1 p.1 p.2.2 :=
    (hQm.comp measurable_snd.fst).mul h.γ_meas
  have hγp : Probability.MarkedProgressivelyMeasurable ℱ
      fun ω s e => q (clampTime T s) * γ s ω e :=
    markedProgressivelyMeasurable_weight_mul hQm h.γ_prog
  have hγv : ∀ ω s e, s ∉ Set.Icc (0 : ℝ) T → q (clampTime T s) * γ s ω e = 0 :=
    fun ω s e hs => by rw [h.γ_vanish ω s e hs, mul_zero]
  have hγq : Poisson.Compensated.markedEnergy P ν T
      (fun ω s e => q (clampTime T s) * γ s ω e) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top h.γ_sq)
      (markedEnergy_weight_mul_le hQB (fun ω s e => γ s ω e) T)
  -- the new drift, with the weight clamped
  have hbeq : (fun ω s => (Set.Icc 0 T).indicator (fun s => q' s * X s ω + q s * b ω s) s)
      = fun ω s => (Set.Icc (0 : ℝ) T).indicator (fun _ => (1 : ℝ)) s
        * (q' (clampTime T s) * X s ω + q (clampTime T s) * b ω s) := by
    funext ω s
    by_cases hs : s ∈ Set.Icc 0 T
    · simp [Set.indicator_of_mem hs, clampTime_of_mem hs]
    · simp [Set.indicator_of_notMem hs]
  have hIm : Measurable ((Set.Icc (0 : ℝ) T).indicator fun _ => (1 : ℝ)) :=
    measurable_const.indicator measurableSet_Icc
  have hFm : Measurable (Function.uncurry fun ω s =>
      q' (clampTime T s) * X s ω + q (clampTime T s) * b ω s) :=
    ((hQ'm.comp measurable_snd).mul hXp.measurable_uncurry).add
      ((hQm.comp measurable_snd).mul h.b_meas)
  have hFq : Brownian.Ito.energy P T
      (fun ω s => q' (clampTime T s) * X s ω + q (clampTime T s) * b ω s) ≠ ⊤ :=
    Brownian.Ito.energy_add_ne_top ((hQ'm.comp measurable_snd).mul hXp.measurable_uncurry)
      ((hQm.comp measurable_snd).mul h.b_meas)
      (ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hXE)
        (energy_weight_mul_le hQ'B (fun ω s => X s ω) T))
      (ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top h.b_sq)
        (energy_weight_mul_le hQB b T))
  refine
    { σ_meas := hσm
      σ_prog := hσp
      σ_vanish := hσv
      σ_sq := hσq
      γ_meas := hγm
      γ_prog := hγp
      γ_vanish := hγv
      γ_sq := hγq
      b_meas := by
        rw [hbeq]
        exact (hIm.comp measurable_snd).mul hFm
      b_prog := by
        rw [hbeq]
        exact progressivelyMeasurable_weight_mul hIm
          ((progressivelyMeasurable_weight_mul hQ'm hXp).add
            (progressivelyMeasurable_weight_mul hQm h.b_prog))
      b_vanish := fun ω s hs => Set.indicator_of_notMem hs _
      b_sq := by
        rw [hbeq]
        refine ne_top_of_le_ne_top hFq (le_of_eq (lintegral_congr fun ω =>
          setLIntegral_congr_fun measurableSet_Icc fun s hs => ?_))
        beta_reduce
        rw [Set.indicator_of_mem hs, one_mul]
      ξ₀_sq := h.ξ₀_sq.const_mul (q 0)
      X_adapted := fun t => (h.X_adapted t).const_mul _
      X_rightCont := fun ω t =>
        ((hQc.tendsto t).mono_left nhdsWithin_le_nhds).mul (h.X_rightCont ω t)
      eqn := ?_ }
  intro t ht
  have htT : t ≤ T := ht.2
  have hσq' := sq_int_global_of_vanishing hσv hσq
  have hγq' := marked_sq_int_global_of_vanishing hγv hγq
  -- the three legs of the weighted data
  let M : ℝ → Ω → ℝ := fun r ω => (∫ s in Set.Icc 0 r, q (clampTime T s) * b ω s)
    + Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hℱW
      (fun s ω j => q (clampTime T s) * σ s ω j) hσm hσp hσq' r ω
    + Poisson.Compensated.stochasticIntegral D.N ℱ hℱN
      (fun ω s e => q (clampTime T s) * γ s ω e) hγm hγp hγq' r ω
  have hderiv : ∀ s ∈ Set.Icc 0 t, HasDerivWithinAt (fun s => q (clampTime T s))
      (q' (clampTime T s)) (Set.Icc 0 t) s := by
    intro s hs
    have hsT : s ∈ Set.Icc 0 T := ⟨hs.1, hs.2.trans htT⟩
    rw [clampTime_of_mem hsT]
    exact ((hq s hsT).congr (fun x hx => by rw [clampTime_of_mem hx])
      (by rw [clampTime_of_mem hsT])).mono (Set.Icc_subset_Icc le_rfl htT)
  have hXi : ∀ᵐ ω ∂P, IntegrableOn (fun s => X s ω) (Set.Icc 0 T) :=
    ae_mem_integrablePaths hXp.measurable_uncurry hXE
  have hMm : ∀ r, AEMeasurable (M r) P := by
    intro r
    have hA : Measurable fun ω => ∫ s in Set.Icc 0 r, q (clampTime T s) * b ω s :=
      (((hQm.comp measurable_snd).mul h.b_meas).stronglyMeasurable.integral_prod_right'
        (ν := volume.restrict (Set.Icc 0 r))).measurable
    have hW : AEMeasurable (Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ
        hℱW (fun s ω j => q (clampTime T s) * σ s ω j) hσm hσp hσq' r) P :=
      (show MemLp _ 2 P from memLp_finsetSum Finset.univ fun i _ =>
        Brownian.Ito.stochasticIntegralBrownian_memLp (D.W.W i) ℱ (hℱW i)
          (fun ω s => q (clampTime T s) * σ s ω i) (hσm i) (hσp i) (hσq' i)
          r).aestronglyMeasurable.aemeasurable
    have hN := (Poisson.Compensated.stochasticIntegral_memLp D.N ℱ hℱN
      (fun ω s e => q (clampTime T s) * γ s ω e) hγm hγp hγq' r).aestronglyMeasurable.aemeasurable
    exact (hA.aemeasurable.add hW).add hN
  have hcore := ae_sub_eq_of_increment_le (P := P) (V := X) (M := M)
    (q := fun s => q (clampTime T s)) (q' := fun s => q' (clampTime T s))
    (g := forwardIncrementDensity P ν T b σ γ) ht.1 hderiv hQ'c
    (Probability.measurable_uncurry_of_rightContinuous h.X_adapted h.X_rightCont)
    (hXi.mono fun ω hω => IntegrableOn.mono_set hω (Set.Icc_subset_Icc le_rfl htT)) hMm
    (h.setLIntegral_forwardIncrementDensity_ne_top (Set.Icc_subset_Icc le_rfl htT))
    (fun a r ha har hr => h.lintegral_sq_sub_le ha har (hr.trans htT))
    (fun a r c δ ha har hr hδ => h.lintegral_sq_weight_sub_le hQm hQB hσm hσp hσq' hγm hγp
      hγq' ha har (hr.trans htT) hδ)
  have hW0 := Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral_ae_zero_of_nonpos D.W ℱ
    hℱW _ hσm hσp hσq' (le_refl (0 : ℝ))
  have hN0 := Poisson.Compensated.stochasticIntegral_ae_zero_of_nonpos
    (φ := fun ω s e => q (clampTime T s) * γ s ω e) D.N hℱN hγm hγp hγq' (le_refl (0 : ℝ))
  filter_upwards [hcore, h.initial_ae_eq hT, hW0, hN0, hXi,
    ae_mem_integrablePaths h.b_meas h.b_sq] with ω e1 e2 e3 e4 hXω hbω
  simp only [Pi.zero_apply] at e3 e4
  have hXt : IntegrableOn (fun s => X s ω) (Set.Icc 0 t) :=
    IntegrableOn.mono_set hXω (Set.Icc_subset_Icc le_rfl htT)
  have hbt : IntegrableOn (b ω) (Set.Icc 0 t) :=
    IntegrableOn.mono_set hbω (Set.Icc_subset_Icc le_rfl htT)
  have hdrift : ∫ s in Set.Icc 0 t, (Set.Icc 0 T).indicator (fun s => q' s * X s ω + q s * b ω s) s
      = (∫ s in Set.Icc 0 t, q' (clampTime T s) * X s ω)
        + ∫ s in Set.Icc 0 t, q (clampTime T s) * b ω s := by
    rw [← integral_add (IntegrableOn.continuousOn_mul hQ'c.continuousOn hXt isCompact_Icc)
      (IntegrableOn.continuousOn_mul hQc.continuousOn hbt isCompact_Icc)]
    refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
    have hsT : s ∈ Set.Icc 0 T := ⟨hs.1, hs.2.trans htT⟩
    simp only [Set.indicator_of_mem hsT, clampTime_of_mem hsT]
  have hA0 : ∫ s in Set.Icc (0 : ℝ) 0, q (clampTime T s) * b ω s = 0 := by
    rw [Set.Icc_self, Measure.restrict_singleton, measure_singleton, zero_smul,
      integral_zero_measure]
  have hQ0 : q (clampTime T 0) = q 0 := by rw [clampTime_of_mem ⟨le_rfl, hT⟩]
  simp only [M] at e1
  rw [hA0, e3, e4, e2, hQ0] at e1
  rw [hdrift]
  linarith

end LinearFSDEJ

end Dissertation.WellPosedness.Stability
