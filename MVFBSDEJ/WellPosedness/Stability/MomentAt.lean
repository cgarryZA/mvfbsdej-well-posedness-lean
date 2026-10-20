/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Stability.GEnergy
import MVFBSDEJ.WellPosedness.Existence.ZeroEnergy

/-!
# Second moments of the linear equations at every time, and decoupling residuals

For two solutions `X₁, X₂` of the linear forward equation (initial values `ξ₁, ξ₂`, drifts
`b₁, b₂`, diffusion vectors `σ₁, σ₂`, jump integrands `γ₁, γ₂`) over a filtration with a cross
witness, at every `t ∈ [0, T]`,

`𝔼[X₁(t) X₂(t)] = 𝔼[ξ₁ ξ₂] + ∫_0^t (𝔼[X₁ b₂ + X₂ b₁] + ∑_j 𝔼[σ₁ⱼ σ₂ⱼ] + 𝔼 ∫_E γ₁ γ₂ dν) ds`.

For a deterministic weight `p` of class `C¹` on `[0, T]`, the second moment of the residual
`D_t = X₂(t) − p(t) X₁(t)` is then absolutely continuous:

`𝔼[D_t²] = 𝔼[D_0²] + ∫_0^t (2 𝔼[D (b₂ − p' X₁ − p b₁)] + ∑_j 𝔼[(σ₂ⱼ − p σ₁ⱼ)²]
  + 𝔼 ∫_E (γ₂ − p γ₁)² dν) ds`.

The weighting of an absolutely continuous function by a `C¹` weight is isolated first, as a real
identity.

## Main statements

* `mul_eq_add_setIntegral_of_hasDerivAt` — integration by parts against a `C¹` weight.
* `LinearFSDEJ.memLp_apply` — a solution is square integrable at every time of the horizon.
* `LinearFSDEJ.integral_mul_eq_at` — the bilinear identity at every time.
* `LinearFSDEJ.integral_residual_sq_eq` — the second moment of a decoupling residual.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace MVFBSDEJ.WellPosedness.Stability

open LevyStochCalc.BSDEJ.Solves LevyStochCalc MVFBSDEJ.WellPosedness.BrownianPoisson
  MVFBSDEJ.WellPosedness.Existence

universe u v w

/-! ### A `C¹` weight -/

section Weight

/-- The integral of the derivative of a `C¹` weight over `[r, t]`. -/
theorem setIntegral_deriv_eq_sub {w w' : ℝ → ℝ} {T : ℝ} (hwc : ContinuousOn w (Set.Icc (0 : ℝ) T))
    (hw : ∀ x ∈ Set.Ioo (0 : ℝ) T, HasDerivAt w (w' x) x)
    (hw' : ContinuousOn w' (Set.Icc (0 : ℝ) T)) {r t : ℝ} (hr : 0 ≤ r) (hrt : r ≤ t)
    (ht : t ≤ T) :
    ∫ s in Set.Icc r t, w' s = w t - w r := by
  have hsub : Set.Icc r t ⊆ Set.Icc (0 : ℝ) T := Set.Icc_subset_Icc hr ht
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hrt]
  refine intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hrt (hwc.mono hsub)
    (fun x hx => (hw x ⟨hr.trans_lt hx.1, hx.2.trans_le ht⟩).hasDerivWithinAt) ?_
  exact (hw'.mono (by rwa [Set.uIcc_of_le hrt])).intervalIntegrable

/-- **Integration by parts against a `C¹` weight.** If `m(s) = m₀ + ∫_0^s g` on `[0, T]` with `g`
integrable on `[0, T]`, and `w` is continuous on `[0, T]` with a derivative `w'` on `(0, T)`
continuous on `[0, T]`, then for `t ∈ [0, T]`,
`w(t) m(t) = w(0) m₀ + ∫_0^t (w'(s) m(s) + w(s) g(s)) ds`. -/
theorem mul_eq_add_setIntegral_of_hasDerivAt {m g w w' : ℝ → ℝ} {m₀ T : ℝ}
    (hg : IntegrableOn g (Set.Icc (0 : ℝ) T))
    (hm : ∀ s ∈ Set.Icc (0 : ℝ) T, m s = m₀ + ∫ r in Set.Icc (0 : ℝ) s, g r)
    (hwc : ContinuousOn w (Set.Icc (0 : ℝ) T))
    (hw : ∀ x ∈ Set.Ioo (0 : ℝ) T, HasDerivAt w (w' x) x)
    (hw' : ContinuousOn w' (Set.Icc (0 : ℝ) T)) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    w t * m t = w 0 * m₀ + ∫ s in Set.Icc (0 : ℝ) t, (w' s * m s + w s * g s) := by
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T := Set.Icc_subset_Icc le_rfl ht.2
  have hgt : IntegrableOn g (Set.Icc (0 : ℝ) t) := hg.mono_set hsub
  set μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) t) with hμ
  have hw'i : IntegrableOn w' (Set.Icc (0 : ℝ) t) := (hw'.mono hsub).integrableOn_Icc
  have hprod : Integrable (fun p : ℝ × ℝ => g p.1 * w' p.2) (μ.prod μ) := hgt.mul_prod hw'i
  set F : ℝ × ℝ → ℝ := {p : ℝ × ℝ | p.1 ≤ p.2}.indicator fun p => g p.1 * w' p.2 with hF
  have hle : MeasurableSet {p : ℝ × ℝ | p.1 ≤ p.2} :=
    measurableSet_le measurable_fst measurable_snd
  have hFint : Integrable F (μ.prod μ) := hprod.indicator hle
  have hinner : ∀ s ∈ Set.Icc (0 : ℝ) t,
      ∫ r, F (r, s) ∂μ = (∫ r in Set.Icc (0 : ℝ) s, g r) * w' s := by
    intro s hs
    have h1 : (fun r => F (r, s)) = fun r => (Set.Iic s).indicator (fun r => g r * w' s) r := by
      funext r
      simp only [hF, Set.indicator, Set.mem_setOf_eq, Set.mem_Iic]
    have hset : Set.Iic s ∩ Set.Icc (0 : ℝ) t = Set.Icc (0 : ℝ) s := by
      ext r
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
      constructor
      · rintro ⟨h1, h2, _⟩
        exact ⟨h2, h1⟩
      · rintro ⟨h2, h1⟩
        exact ⟨h1, h2, h1.trans hs.2⟩
    rw [h1, integral_indicator measurableSet_Iic, integral_mul_const, hμ,
      Measure.restrict_restrict measurableSet_Iic, hset]
  have hFeq : ∫ p, F p ∂(μ.prod μ)
      = ∫ s in Set.Icc (0 : ℝ) t, (∫ r in Set.Icc (0 : ℝ) s, g r) * w' s := by
    rw [integral_prod_symm F hFint]
    exact setIntegral_congr_fun measurableSet_Icc fun s hs => hinner s hs
  have hinner' : ∀ r ∈ Set.Icc (0 : ℝ) t, ∫ s, F (r, s) ∂μ = g r * (w t - w r) := by
    intro r hr
    have h1 : (fun s => F (r, s)) = fun s => (Set.Ici r).indicator (fun s => g r * w' s) s := by
      funext s
      simp only [hF, Set.indicator, Set.mem_setOf_eq, Set.mem_Ici]
    have hset : Set.Ici r ∩ Set.Icc (0 : ℝ) t = Set.Icc r t := by
      ext s
      simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Icc]
      constructor
      · rintro ⟨h1, _, h3⟩
        exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩
        exact ⟨h1, hr.1.trans h1, h3⟩
    rw [h1, integral_indicator measurableSet_Ici, integral_const_mul, hμ,
      Measure.restrict_restrict measurableSet_Ici, hset,
      setIntegral_deriv_eq_sub hwc hw hw' hr.1 hr.2 ht.2]
  have hFeq' : ∫ p, F p ∂(μ.prod μ) = ∫ r in Set.Icc (0 : ℝ) t, g r * (w t - w r) := by
    rw [integral_prod F hFint]
    exact setIntegral_congr_fun measurableSet_Icc fun r hr => hinner' r hr
  have hgw : IntegrableOn (fun r => g r * w r) (Set.Icc (0 : ℝ) t) :=
    hgt.mul_continuousOn (hwc.mono hsub) isCompact_Icc
  have hG : ContinuousOn (fun s => ∫ r in Set.Icc (0 : ℝ) s, g r) (Set.Icc (0 : ℝ) t) :=
    intervalIntegral.continuousOn_primitive_Icc hgt
  have h1 : IntegrableOn (fun s => w' s * m₀) (Set.Icc (0 : ℝ) t) :=
    hw'i.mul_const _
  have h2 : IntegrableOn (fun s => w' s * ∫ r in Set.Icc (0 : ℝ) s, g r) (Set.Icc (0 : ℝ) t) :=
    ((hw'.mono hsub).mul hG).integrableOn_Icc
  have h3 : IntegrableOn (fun s => w s * g s) (Set.Icc (0 : ℝ) t) :=
    IntegrableOn.continuousOn_mul (hwc.mono hsub) hgt isCompact_Icc
  have hae : ∀ s ∈ Set.Icc (0 : ℝ) t, w' s * m s + w s * g s
      = w' s * m₀ + w' s * (∫ r in Set.Icc (0 : ℝ) s, g r) + w s * g s := by
    intro s hs
    rw [hm s (hsub hs)]
    ring
  have h12 : IntegrableOn (fun s => w' s * m₀ + w' s * ∫ r in Set.Icc (0 : ℝ) s, g r)
      (Set.Icc (0 : ℝ) t) := h1.add h2
  rw [setIntegral_congr_fun measurableSet_Icc hae, integral_add h12 h3,
    integral_add h1 h2, integral_mul_const, setIntegral_deriv_eq_sub hwc hw hw' le_rfl ht.1 ht.2]
  have e2 : ∫ s in Set.Icc (0 : ℝ) t, w' s * ∫ r in Set.Icc (0 : ℝ) s, g r
      = w t * (∫ r in Set.Icc (0 : ℝ) t, g r) - ∫ r in Set.Icc (0 : ℝ) t, w r * g r := by
    have e : (fun r => g r * (w t - w r)) = fun r => w t * g r - g r * w r := by
      funext r
      ring
    calc ∫ s in Set.Icc (0 : ℝ) t, w' s * ∫ r in Set.Icc (0 : ℝ) s, g r
        = ∫ s in Set.Icc (0 : ℝ) t, (∫ r in Set.Icc (0 : ℝ) s, g r) * w' s :=
          setIntegral_congr_fun measurableSet_Icc fun s _ => mul_comm _ _
      _ = ∫ r in Set.Icc (0 : ℝ) t, g r * (w t - w r) := by rw [← hFeq, hFeq']
      _ = _ := by
          rw [e, integral_sub (hgt.const_mul _) hgw, integral_const_mul]
          congr 1
          exact setIntegral_congr_fun measurableSet_Icc fun r _ => mul_comm _ _
  rw [e2, hm t ht]
  ring

end Weight

/-! ### The linear forward equation at every time -/

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {T : ℝ}
  {ξ₁ ξ₂ : Ω → ℝ} {b₁ b₂ : Ω → ℝ → ℝ} {X₁ X₂ : ℝ → Ω → ℝ} {σ₁ σ₂ : ℝ → Ω → (Fin d → ℝ)}
  {γ₁ γ₂ : ℝ → Ω → E → ℝ}

namespace LinearFSDEJ

/-- **A solution of the linear forward equation is square integrable at every time of the
horizon.** -/
theorem memLp_apply (h : LinearFSDEJ D ℱ hℱW hℱN T ξ₁ b₁ X₁ σ₁ γ₁) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) : MemLp (X₁ t) 2 P := by
  have hA : MemLp (fun ω => ∫ s in Set.Icc (0 : ℝ) t, b₁ ω s) 2 P :=
    Ito.SecondMoment.memLp_two_setIntegral h.b_meas ht.1
      ((energy_mono ht.2).trans_lt h.b_sq.lt_top)
  have hB : MemLp (Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hℱW σ₁
      h.σ_meas h.σ_prog (sq_int_global_of_vanishing h.σ_vanish h.σ_sq) t) 2 P :=
    memLp_finsetSum Finset.univ fun i _ =>
      Brownian.Ito.stochasticIntegralBrownian_memLp (D.W.W i) ℱ (hℱW i) (fun ω s => σ₁ s ω i)
        (h.σ_meas i) (h.σ_prog i) (sq_int_global_of_vanishing h.σ_vanish h.σ_sq i) t
  have hN : MemLp (Poisson.Compensated.stochasticIntegral D.N ℱ hℱN
      (fun ω' s e => γ₁ s ω' e) h.γ_meas h.γ_prog
      (marked_sq_int_global_of_vanishing h.γ_vanish h.γ_sq) t) 2 P :=
    Poisson.Compensated.stochasticIntegral_memLp D.N ℱ hℱN _ h.γ_meas h.γ_prog
      (marked_sq_int_global_of_vanishing h.γ_vanish h.γ_sq) t
  refine (((h.ξ₀_sq.add hA).add hB).add hN).ae_eq ?_
  filter_upwards [h.eqn t ht] with ω hω
  rw [hω]
  rfl

/-- **The bilinear identity at every time.** For two solutions of the linear forward equation
over a filtration with a cross witness and `t ∈ [0, T]`,
`𝔼[X₁(t) X₂(t)] = 𝔼[ξ₁ ξ₂] + ∫_0^t (𝔼[X₁ b₂ + X₂ b₁] + ∑_j 𝔼[σ₁ⱼ σ₂ⱼ] + 𝔼 ∫_E γ₁ γ₂ dν) ds`, with
an integrable time integrand. -/
theorem integral_mul_eq_at (h₁ : LinearFSDEJ D ℱ hℱW hℱN T ξ₁ b₁ X₁ σ₁ γ₁)
    (h₂ : LinearFSDEJ D ℱ hℱW hℱN T ξ₂ b₂ X₂ σ₂ γ₂) (𝒲 : D.CrossWitness ℱ) (hT : 0 < T)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∫ ω, X₁ t ω * X₂ t ω ∂P = ∫ ω, ξ₁ ω * ξ₂ ω ∂P
      + ∫ s in Set.Icc (0 : ℝ) t, (∫ ω, (X₁ s ω * b₂ ω s + X₂ s ω * b₁ ω s) ∂P
          + ∑ j, ∫ ω, σ₁ s ω j * σ₂ s ω j ∂P + ∫ ω, ∫ e, γ₁ s ω e * γ₂ s ω e ∂ν ∂P) := by
  have hb₁ := h₁.linearBSDEJ hT.le
  have hb₂ := h₂.linearBSDEJ hT.le
  have hX₁m : Measurable (Function.uncurry fun ω s => X₁ s ω) :=
    hb₁.measurable_uncurry.comp measurable_swap
  have hX₂m : Measurable (Function.uncurry fun ω s => X₂ s ω) :=
    hb₂.measurable_uncurry.comp measurable_swap
  have h0 : ∫ ω, X₁ 0 ω * X₂ 0 ω ∂P = ∫ ω, ξ₁ ω * ξ₂ ω ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [h₁.initial_ae_eq hT.le, h₂.initial_ae_eq hT.le] with ω hω₁ hω₂
    rw [hω₁, hω₂]
  rcases ht.1.eq_or_lt with ht0 | ht0
  · subst ht0
    rw [Set.Icc_self, Measure.restrict_singleton, measure_singleton, zero_smul,
      integral_zero_measure, add_zero, h0]
  have hEt : ∀ (f : Ω → ℝ → ℝ), Brownian.Ito.energy P T f ≠ ⊤ →
      Brownian.Ito.energy P t f < ⊤ := fun f hf => (energy_mono ht.2).trans_lt hf.lt_top
  have hMt : ∀ (φ : Ω → ℝ → E → ℝ), Poisson.Compensated.markedEnergy P ν T φ ≠ ⊤ →
      Poisson.Compensated.markedEnergy P ν t φ < ⊤ :=
    fun φ hφ => (markedEnergy_mono ht.2).trans_lt hφ.lt_top
  have hX₁t : Brownian.Ito.energy P t (fun ω s => X₁ s ω) < ⊤ :=
    (energy_mono ht.2).trans_lt (h₁.energy_lt_top 𝒲 hT)
  have hX₂t : Brownian.Ito.energy P t (fun ω s => X₂ s ω) < ⊤ :=
    (energy_mono ht.2).trans_lt (h₂.energy_lt_top 𝒲 hT)
  have key := Ito.SecondMoment.integral_mul_eq_of_isItoLevyProcess
    (h₁.isItoLevyProcess_clampT hT) (h₂.isItoLevyProcess_clampT hT) 𝒲
    hb₁.stronglyMeasurable_initial (hb₁.memLp_initial hT.le) h₁.b_meas h₁.b_prog
    (fun T' _ => drift_sq_int_global h₁.b_vanish h₁.b_sq T')
    hb₂.stronglyMeasurable_initial (hb₂.memLp_initial hT.le) h₂.b_meas h₂.b_prog
    (fun T' _ => drift_sq_int_global h₂.b_vanish h₂.b_sq T') ht0
  rw [clampT_apply_of_le ht.2 X₁, clampT_apply_of_le ht.2 X₂, h0] at key
  set μ₂ := P.prod (volume.restrict (Set.Icc (0 : ℝ) t)) with hμ₂
  have hσ : ∀ j : Fin d, Integrable (fun p : Ω × ℝ => σ₁ p.2 p.1 j * σ₂ p.2 p.1 j) μ₂ :=
    fun j => integrable_mul_prod (h₁.σ_meas j) (h₂.σ_meas j) (hEt _ (h₁.σ_sq j))
      (hEt _ (h₂.σ_sq j))
  have hγ : Integrable (fun p : Ω × ℝ => ∫ e, γ₁ p.2 p.1 e * γ₂ p.2 p.1 e ∂ν) μ₂ :=
    integrable_integral_mul_marked (φ := fun ω s e => γ₁ s ω e) (ψ := fun ω s e => γ₂ s ω e)
      h₁.γ_meas h₂.γ_meas (hMt _ h₁.γ_sq) (hMt _ h₂.γ_sq)
  have hd : Integrable (fun p : Ω × ℝ => X₁ p.2 p.1 * b₂ p.1 p.2 + X₂ p.2 p.1 * b₁ p.1 p.2) μ₂ :=
    (integrable_mul_prod hX₁m h₂.b_meas hX₁t (hEt _ h₂.b_sq)).add
      (integrable_mul_prod hX₂m h₁.b_meas hX₂t (hEt _ h₁.b_sq))
  have hdrift : ∫ s in Set.Icc (0 : ℝ) t,
      ∫ ω, clampT T X₁ s ω * b₂ ω s + clampT T X₂ s ω * b₁ ω s ∂P
      = ∫ s in Set.Icc (0 : ℝ) t, ∫ ω, (X₁ s ω * b₂ ω s + X₂ s ω * b₁ ω s) ∂P := by
    refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
    simp only [clampT_apply, min_eq_left (hs.2.trans ht.2)]
  have hbrown : ∑ j : Fin d, ∫ ω, ∫ s in Set.Icc (0 : ℝ) t, σ₁ s ω j * σ₂ s ω j ∂volume ∂P
      = ∑ j : Fin d, ∫ s in Set.Icc (0 : ℝ) t, ∫ ω, σ₁ s ω j * σ₂ s ω j ∂P :=
    Finset.sum_congr rfl fun j _ => integral_integral_swap (hσ j)
  have hjump : ∫ ω, ∫ s in Set.Icc (0 : ℝ) t, ∫ e, γ₁ s ω e * γ₂ s ω e ∂ν ∂volume ∂P
      = ∫ s in Set.Icc (0 : ℝ) t, ∫ ω, ∫ e, γ₁ s ω e * γ₂ s ω e ∂ν ∂P :=
    integral_integral_swap hγ
  have hdi : Integrable (fun s => ∫ ω, (X₁ s ω * b₂ ω s + X₂ s ω * b₁ ω s) ∂P)
      (volume.restrict (Set.Icc (0 : ℝ) t)) := hd.integral_prod_right
  have hσi : ∀ j : Fin d, Integrable (fun s => ∫ ω, σ₁ s ω j * σ₂ s ω j ∂P)
      (volume.restrict (Set.Icc (0 : ℝ) t)) := fun j => (hσ j).integral_prod_right
  have hγi : Integrable (fun s => ∫ ω, ∫ e, γ₁ s ω e * γ₂ s ω e ∂ν ∂P)
      (volume.restrict (Set.Icc (0 : ℝ) t)) := hγ.integral_prod_right
  have hS : Integrable (fun s => ∫ ω, (X₁ s ω * b₂ ω s + X₂ s ω * b₁ ω s) ∂P
      + ∑ j, ∫ ω, σ₁ s ω j * σ₂ s ω j ∂P) (volume.restrict (Set.Icc (0 : ℝ) t)) :=
    hdi.add (integrable_finsetSum _ fun j _ => hσi j)
  rw [key, hdrift, hbrown, hjump, integral_add hS hγi, integral_add hdi
    (integrable_finsetSum _ fun j _ => hσi j), integral_finsetSum _ fun j _ => hσi j]
  ring

/-! ### The rate as an integral for `P ⊗ ds` -/

/-- **The product of two solutions is integrable for `P ⊗ ds` on `[0, t]`**, `t ≤ T`. -/
theorem integrable_mul_prod_at (h₁ : LinearFSDEJ D ℱ hℱW hℱN T ξ₁ b₁ X₁ σ₁ γ₁)
    (h₂ : LinearFSDEJ D ℱ hℱW hℱN T ξ₂ b₂ X₂ σ₂ γ₂) (𝒲 : D.CrossWitness ℱ) (hT : 0 < T)
    {t : ℝ} (ht : t ≤ T) :
    Integrable (fun q : Ω × ℝ => X₁ q.2 q.1 * X₂ q.2 q.1)
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) t))) := by
  have hX₁m : Measurable (Function.uncurry fun ω s => X₁ s ω) :=
    (h₁.linearBSDEJ hT.le).measurable_uncurry.comp measurable_swap
  have hX₂m : Measurable (Function.uncurry fun ω s => X₂ s ω) :=
    (h₂.linearBSDEJ hT.le).measurable_uncurry.comp measurable_swap
  exact integrable_mul_prod hX₁m hX₂m ((energy_mono ht).trans_lt (h₁.energy_lt_top 𝒲 hT))
    ((energy_mono ht).trans_lt (h₂.energy_lt_top 𝒲 hT))

/-- **The pairing rate of two solutions is integrable for `P ⊗ ds` on `[0, t]`**, `t ≤ T`:
`X₁ b₂ + X₂ b₁`, each `σ₁ⱼ σ₂ⱼ` and `∫_E γ₁ γ₂ dν`. -/
theorem integrable_rate_prod_at (h₁ : LinearFSDEJ D ℱ hℱW hℱN T ξ₁ b₁ X₁ σ₁ γ₁)
    (h₂ : LinearFSDEJ D ℱ hℱW hℱN T ξ₂ b₂ X₂ σ₂ γ₂) (𝒲 : D.CrossWitness ℱ) (hT : 0 < T)
    {t : ℝ} (ht : t ≤ T) :
    Integrable (fun q : Ω × ℝ => X₁ q.2 q.1 * b₂ q.1 q.2 + X₂ q.2 q.1 * b₁ q.1 q.2)
        (P.prod (volume.restrict (Set.Icc (0 : ℝ) t)))
      ∧ (∀ j : Fin d, Integrable (fun q : Ω × ℝ => σ₁ q.2 q.1 j * σ₂ q.2 q.1 j)
        (P.prod (volume.restrict (Set.Icc (0 : ℝ) t))))
      ∧ Integrable (fun q : Ω × ℝ => ∫ e, γ₁ q.2 q.1 e * γ₂ q.2 q.1 e ∂ν)
        (P.prod (volume.restrict (Set.Icc (0 : ℝ) t))) := by
  have hX₁m : Measurable (Function.uncurry fun ω s => X₁ s ω) :=
    (h₁.linearBSDEJ hT.le).measurable_uncurry.comp measurable_swap
  have hX₂m : Measurable (Function.uncurry fun ω s => X₂ s ω) :=
    (h₂.linearBSDEJ hT.le).measurable_uncurry.comp measurable_swap
  refine ⟨(integrable_mul_prod hX₁m h₂.b_meas ((energy_mono ht).trans_lt (h₁.energy_lt_top 𝒲 hT))
      ((energy_mono ht).trans_lt h₂.b_sq.lt_top)).add
      (integrable_mul_prod hX₂m h₁.b_meas ((energy_mono ht).trans_lt (h₂.energy_lt_top 𝒲 hT))
        ((energy_mono ht).trans_lt h₁.b_sq.lt_top)),
    fun j => integrable_mul_prod (h₁.σ_meas j) (h₂.σ_meas j)
      ((energy_mono ht).trans_lt (h₁.σ_sq j).lt_top)
      ((energy_mono ht).trans_lt (h₂.σ_sq j).lt_top),
    integrable_integral_mul_marked (φ := fun ω s e => γ₁ s ω e) (ψ := fun ω s e => γ₂ s ω e)
      h₁.γ_meas h₂.γ_meas ((markedEnergy_mono ht).trans_lt h₁.γ_sq.lt_top)
      ((markedEnergy_mono ht).trans_lt h₂.γ_sq.lt_top)⟩

omit [IsProbabilityMeasure P] in
/-- For `P ⊗ ds` on `[0, t]`, almost every point has its time in `[0, t]`. -/
theorem ae_snd_mem_Icc [SFinite P] (t : ℝ) :
    ∀ᵐ q ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) t))), q.2 ∈ Set.Icc (0 : ℝ) t :=
  Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Icc)

omit [IsProbabilityMeasure P] in
/-- **A continuous weight of time against a time marginal.** For `f` integrable for `P ⊗ ds` on
`[0, t]` and `c` continuous on `[0, t]`, `c(s) f(ω, s)` is integrable and
`∫_0^t c(s) ∫_Ω f(ω, s) dP ds = ∫ c(s) f(ω, s) d(P ⊗ ds)`. -/
theorem setIntegral_weight_eq [SFinite P] {f : Ω × ℝ → ℝ} {c : ℝ → ℝ} {t : ℝ}
    (hf : Integrable f (P.prod (volume.restrict (Set.Icc (0 : ℝ) t))))
    (hc : ContinuousOn c (Set.Icc (0 : ℝ) t)) :
    Integrable (fun q : Ω × ℝ => c q.2 * f q) (P.prod (volume.restrict (Set.Icc (0 : ℝ) t)))
      ∧ ∫ s in Set.Icc (0 : ℝ) t, c s * ∫ ω, f (ω, s) ∂P
        = ∫ q, c q.2 * f q ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) t))) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  have hcf : Integrable (fun q : Ω × ℝ => c q.2 * f q)
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) t))) :=
    hf.bdd_mul (hc.aestronglyMeasurable measurableSet_Icc).comp_snd
      ((ae_snd_mem_Icc t).mono fun q hq => hC q.2 hq)
  refine ⟨hcf, ?_⟩
  rw [integral_prod_symm _ hcf]
  exact integral_congr_ae (Eventually.of_forall fun s => (integral_const_mul _ _).symm)

/-- **The rate of the bilinear identity against a continuous weight of time.** For two
solutions of the linear forward equation, `t ≤ T` and `c` continuous on `[0, t]`,
`∫_0^t c(s) (𝔼[X₁ b₂ + X₂ b₁] + ∑_j 𝔼[σ₁ⱼ σ₂ⱼ] + 𝔼 ∫_E γ₁ γ₂ dν) ds` is the integral of
`c(s) (X₁ b₂ + X₂ b₁ + ∑_j σ₁ⱼ σ₂ⱼ + ∫_E γ₁ γ₂ dν)` for `P ⊗ ds` on `[0, t]`, which is
integrable. -/
theorem setIntegral_weight_rate_eq (h₁ : LinearFSDEJ D ℱ hℱW hℱN T ξ₁ b₁ X₁ σ₁ γ₁)
    (h₂ : LinearFSDEJ D ℱ hℱW hℱN T ξ₂ b₂ X₂ σ₂ γ₂) (𝒲 : D.CrossWitness ℱ) (hT : 0 < T)
    {t : ℝ} (ht : t ≤ T) {c : ℝ → ℝ} (hc : ContinuousOn c (Set.Icc (0 : ℝ) t)) :
    Integrable (fun q : Ω × ℝ => c q.2 * (X₁ q.2 q.1 * b₂ q.1 q.2 + X₂ q.2 q.1 * b₁ q.1 q.2
        + ∑ j, σ₁ q.2 q.1 j * σ₂ q.2 q.1 j + ∫ e, γ₁ q.2 q.1 e * γ₂ q.2 q.1 e ∂ν))
        (P.prod (volume.restrict (Set.Icc (0 : ℝ) t)))
      ∧ ∫ s in Set.Icc (0 : ℝ) t, c s * (∫ ω, (X₁ s ω * b₂ ω s + X₂ s ω * b₁ ω s) ∂P
          + ∑ j, ∫ ω, σ₁ s ω j * σ₂ s ω j ∂P + ∫ ω, ∫ e, γ₁ s ω e * γ₂ s ω e ∂ν ∂P)
        = ∫ q, c q.2 * (X₁ q.2 q.1 * b₂ q.1 q.2 + X₂ q.2 q.1 * b₁ q.1 q.2
            + ∑ j, σ₁ q.2 q.1 j * σ₂ q.2 q.1 j + ∫ e, γ₁ q.2 q.1 e * γ₂ q.2 q.1 e ∂ν)
          ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) t))) := by
  obtain ⟨hA, hB, hJ⟩ := integrable_rate_prod_at h₁ h₂ 𝒲 hT ht
  have hS : Integrable (fun q : Ω × ℝ => ∑ j, σ₁ q.2 q.1 j * σ₂ q.2 q.1 j)
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) t))) := integrable_finsetSum _ fun j _ => hB j
  have hR : Integrable (fun q : Ω × ℝ => X₁ q.2 q.1 * b₂ q.1 q.2 + X₂ q.2 q.1 * b₁ q.1 q.2
      + ∑ j, σ₁ q.2 q.1 j * σ₂ q.2 q.1 j + ∫ e, γ₁ q.2 q.1 e * γ₂ q.2 q.1 e ∂ν)
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) t))) := (hA.add hS).add hJ
  obtain ⟨hcR, heq⟩ := setIntegral_weight_eq hR hc
  refine ⟨hcR, ?_⟩
  rw [← heq]
  refine integral_congr_ae ?_
  filter_upwards [hA.prod_left_ae, hJ.prod_left_ae,
    ae_all_iff.mpr fun j => (hB j).prod_left_ae] with s hAs hJs hBs
  congr 1
  have hSs : Integrable (fun ω => ∑ j, σ₁ s ω j * σ₂ s ω j) P :=
    integrable_finsetSum _ fun j _ => hBs j
  have h1 : Integrable (fun ω => X₁ s ω * b₂ ω s + X₂ s ω * b₁ ω s
      + ∑ j, σ₁ s ω j * σ₂ s ω j) P := hAs.add hSs
  rw [integral_add h1 hJs, integral_add hAs hSs, integral_finsetSum _ fun j _ => hBs j]

/-- The rate of the bilinear identity is integrable on `[0, T]`. -/
theorem integrableOn_rate (h₁ : LinearFSDEJ D ℱ hℱW hℱN T ξ₁ b₁ X₁ σ₁ γ₁)
    (h₂ : LinearFSDEJ D ℱ hℱW hℱN T ξ₂ b₂ X₂ σ₂ γ₂) (𝒲 : D.CrossWitness ℱ) (hT : 0 < T) :
    IntegrableOn (fun s => ∫ ω, (X₁ s ω * b₂ ω s + X₂ s ω * b₁ ω s) ∂P
      + ∑ j, ∫ ω, σ₁ s ω j * σ₂ s ω j ∂P + ∫ ω, ∫ e, γ₁ s ω e * γ₂ s ω e ∂ν ∂P)
      (Set.Icc (0 : ℝ) T) := by
  obtain ⟨hA, hB, hJ⟩ := integrable_rate_prod_at h₁ h₂ 𝒲 hT le_rfl
  exact (hA.integral_prod_right.add
    (integrable_finsetSum _ fun j _ => (hB j).integral_prod_right)).add hJ.integral_prod_right


/-- `∫_E (a − c b)² dν = ∫_E a² dν − 2 c ∫_E b a dν + c² ∫_E b² dν` for `a², ba, b²` integrable. -/
theorem integral_sub_mul_sq_eq {a b : E → ℝ} (c : ℝ) (haa : Integrable (fun e => a e * a e) ν)
    (hba : Integrable (fun e => b e * a e) ν) (hbb : Integrable (fun e => b e * b e) ν) :
    ∫ e, (a e - c * b e) ^ 2 ∂ν
      = ∫ e, a e * a e ∂ν - 2 * c * ∫ e, b e * a e ∂ν + c * c * ∫ e, b e * b e ∂ν := by
  have h1 : Integrable (fun e => a e * a e - 2 * c * (b e * a e)) ν := haa.sub (hba.const_mul _)
  calc ∫ e, (a e - c * b e) ^ 2 ∂ν
      = ∫ e, (a e * a e - 2 * c * (b e * a e) + c * c * (b e * b e)) ∂ν :=
        integral_congr_ae (Eventually.of_forall fun e => by simp only; ring)
    _ = _ := by
        rw [integral_add h1 (hbb.const_mul _), integral_sub haa (hba.const_mul _),
          integral_const_mul, integral_const_mul]

/-- **The second moment of a decoupling residual.** For two solutions `X₁, X₂` of the linear
forward equation over a filtration with a cross witness, a weight `p` continuous on `[0, T]` with
a derivative `p'` on `(0, T)` continuous on `[0, T]`, and `t ∈ [0, T]`,
`𝔼[(X₂(t) − p(t) X₁(t))²] = 𝔼[(ξ₂ − p(0) ξ₁)²] + ∫ r d(P ⊗ ds)` over `Ω × [0, t]`, with
`r = 2 (X₂ − p X₁)(b₂ − p' X₁ − p b₁) + ∑_j (σ₂ⱼ − p σ₁ⱼ)² + ∫_E (γ₂ − p γ₁)² dν`; `r` is
integrable for `P ⊗ ds` on `[0, t]`. -/
theorem integral_residual_sq_eq (h₁ : LinearFSDEJ D ℱ hℱW hℱN T ξ₁ b₁ X₁ σ₁ γ₁)
    (h₂ : LinearFSDEJ D ℱ hℱW hℱN T ξ₂ b₂ X₂ σ₂ γ₂) (𝒲 : D.CrossWitness ℱ) (hT : 0 < T)
    {p p' : ℝ → ℝ} (hpc : ContinuousOn p (Set.Icc (0 : ℝ) T))
    (hp : ∀ x ∈ Set.Ioo (0 : ℝ) T, HasDerivAt p (p' x) x)
    (hp' : ContinuousOn p' (Set.Icc (0 : ℝ) T)) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    Integrable (fun q : Ω × ℝ => 2 * (X₂ q.2 q.1 - p q.2 * X₁ q.2 q.1)
          * (b₂ q.1 q.2 - p' q.2 * X₁ q.2 q.1 - p q.2 * b₁ q.1 q.2)
        + ∑ j, (σ₂ q.2 q.1 j - p q.2 * σ₁ q.2 q.1 j) ^ 2
        + ∫ e, (γ₂ q.2 q.1 e - p q.2 * γ₁ q.2 q.1 e) ^ 2 ∂ν)
        (P.prod (volume.restrict (Set.Icc (0 : ℝ) t)))
      ∧ ∫ ω, (X₂ t ω - p t * X₁ t ω) ^ 2 ∂P = ∫ ω, (ξ₂ ω - p 0 * ξ₁ ω) ^ 2 ∂P
        + ∫ q, (2 * (X₂ q.2 q.1 - p q.2 * X₁ q.2 q.1)
              * (b₂ q.1 q.2 - p' q.2 * X₁ q.2 q.1 - p q.2 * b₁ q.1 q.2)
            + ∑ j, (σ₂ q.2 q.1 j - p q.2 * σ₁ q.2 q.1 j) ^ 2
            + ∫ e, (γ₂ q.2 q.1 e - p q.2 * γ₁ q.2 q.1 e) ^ 2 ∂ν)
          ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) t))) := by
  set μ₂ := P.prod (volume.restrict (Set.Icc (0 : ℝ) t)) with hμ₂
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T := Set.Icc_subset_Icc le_rfl ht.2
  -- the three second moments and their rates
  have hm₁₂ := fun s (hs : s ∈ Set.Icc (0 : ℝ) T) => integral_mul_eq_at h₁ h₂ 𝒲 hT hs
  have hm₁₁ := fun s (hs : s ∈ Set.Icc (0 : ℝ) T) => integral_mul_eq_at h₁ h₁ 𝒲 hT hs
  have hm₂₂ := fun s (hs : s ∈ Set.Icc (0 : ℝ) T) => integral_mul_eq_at h₂ h₂ 𝒲 hT hs
  have hg₁₂ := integrableOn_rate h₁ h₂ 𝒲 hT
  have hg₁₁ := integrableOn_rate h₁ h₁ 𝒲 hT
  have hg₂₂ := integrableOn_rate h₂ h₂ 𝒲 hT
  -- the weights
  have hpp : ∀ x ∈ Set.Ioo (0 : ℝ) T, HasDerivAt (fun s => p s * p s)
      (p' x * p x + p x * p' x) x := fun x hx => (hp x hx).mul (hp x hx)
  have hppc : ContinuousOn (fun s => p s * p s) (Set.Icc (0 : ℝ) T) := hpc.mul hpc
  have hpp' : ContinuousOn (fun s => p' s * p s + p s * p' s) (Set.Icc (0 : ℝ) T) :=
    (hp'.mul hpc).add (hpc.mul hp')
  have e12 := mul_eq_add_setIntegral_of_hasDerivAt hg₁₂ hm₁₂ hpc hp hp' ht
  have e11 := mul_eq_add_setIntegral_of_hasDerivAt hg₁₁ hm₁₁ hppc hpp hpp' ht
  have e22 := hm₂₂ t ht
  -- the second moments are continuous on `[0, t]`
  have hmc : ∀ {g : ℝ → ℝ} {m : ℝ → ℝ} {m₀ : ℝ}, IntegrableOn g (Set.Icc (0 : ℝ) T) →
      (∀ s ∈ Set.Icc (0 : ℝ) T, m s = m₀ + ∫ r in Set.Icc (0 : ℝ) s, g r) →
      ContinuousOn m (Set.Icc (0 : ℝ) t) := by
    intro g m m₀ hg hm
    refine ((continuousOn_const (c := m₀)).add
      (intervalIntegral.continuousOn_primitive_Icc (hg.mono_set hsub))).congr fun s hs => ?_
    exact hm s (hsub hs)
  have hm₁₂c := hmc hg₁₂ hm₁₂
  have hm₁₁c := hmc hg₁₁ hm₁₁
  -- the pieces as integrals for `P ⊗ ds`
  obtain ⟨hI22, hE22⟩ := setIntegral_weight_rate_eq h₂ h₂ 𝒲 hT ht.2 (c := fun _ => 1)
    continuousOn_const
  obtain ⟨hI12, hE12⟩ := setIntegral_weight_rate_eq h₁ h₂ 𝒲 hT ht.2 (hpc.mono hsub)
  obtain ⟨hI11, hE11⟩ := setIntegral_weight_rate_eq h₁ h₁ 𝒲 hT ht.2 (hppc.mono hsub)
  obtain ⟨hJ12, hF12⟩ := setIntegral_weight_eq (integrable_mul_prod_at h₁ h₂ 𝒲 hT ht.2)
    (hp'.mono hsub)
  obtain ⟨hJ11, hF11⟩ := setIntegral_weight_eq (integrable_mul_prod_at h₁ h₁ 𝒲 hT ht.2)
    (hpp'.mono hsub)
  simp only [one_mul] at hE22 hI22
  have hA12 : IntegrableOn (fun s => p' s * ∫ ω, X₁ s ω * X₂ s ω ∂P) (Set.Icc (0 : ℝ) t) :=
    ((hp'.mono hsub).mul hm₁₂c).integrableOn_Icc
  have hB12 : IntegrableOn (fun s => p s * (∫ ω, (X₁ s ω * b₂ ω s + X₂ s ω * b₁ ω s) ∂P
      + ∑ j, ∫ ω, σ₁ s ω j * σ₂ s ω j ∂P + ∫ ω, ∫ e, γ₁ s ω e * γ₂ s ω e ∂ν ∂P))
      (Set.Icc (0 : ℝ) t) :=
    IntegrableOn.continuousOn_mul (hpc.mono hsub) (hg₁₂.mono_set hsub) isCompact_Icc
  have hA11 : IntegrableOn (fun s => (p' s * p s + p s * p' s) * ∫ ω, X₁ s ω * X₁ s ω ∂P)
      (Set.Icc (0 : ℝ) t) := ((hpp'.mono hsub).mul hm₁₁c).integrableOn_Icc
  have hB11 : IntegrableOn (fun s => p s * p s * (∫ ω, (X₁ s ω * b₁ ω s + X₁ s ω * b₁ ω s) ∂P
      + ∑ j, ∫ ω, σ₁ s ω j * σ₁ s ω j ∂P + ∫ ω, ∫ e, γ₁ s ω e * γ₁ s ω e ∂ν ∂P))
      (Set.Icc (0 : ℝ) t) :=
    IntegrableOn.continuousOn_mul (hppc.mono hsub) (hg₁₁.mono_set hsub) isCompact_Icc
  rw [integral_add hA12 hB12, hF12, hE12] at e12
  rw [integral_add hA11 hB11, hF11, hE11] at e11
  rw [hE22] at e22
  -- the residual at time `t` and at time `0`
  have hX₁ := h₁.memLp_apply ht
  have hX₂ := h₂.memLp_apply ht
  have hres : ∀ {x y : Ω → ℝ} (c : ℝ), MemLp x 2 P → MemLp y 2 P →
      ∫ ω, (y ω - c * x ω) ^ 2 ∂P
        = ∫ ω, y ω * y ω ∂P - 2 * c * ∫ ω, x ω * y ω ∂P + c * c * ∫ ω, x ω * x ω ∂P := by
    intro x y c hx hy
    have hyy : Integrable (fun ω => y ω * y ω) P := hy.integrable_mul hy
    have hxy : Integrable (fun ω => x ω * y ω) P := hx.integrable_mul hy
    have hxx : Integrable (fun ω => x ω * x ω) P := hx.integrable_mul hx
    have h1 : Integrable (fun ω => y ω * y ω - 2 * c * (x ω * y ω)) P :=
      hyy.sub (hxy.const_mul _)
    calc ∫ ω, (y ω - c * x ω) ^ 2 ∂P
        = ∫ ω, (y ω * y ω - 2 * c * (x ω * y ω) + c * c * (x ω * x ω)) ∂P :=
          integral_congr_ae (Eventually.of_forall fun ω => by simp only; ring)
      _ = _ := by
          rw [integral_add h1 (hxx.const_mul _), integral_sub hyy (hxy.const_mul _),
            integral_const_mul, integral_const_mul]
  -- the integrand, as a combination of the pieces
  obtain ⟨-, -, hγ12⟩ := integrable_rate_prod_at h₁ h₂ 𝒲 hT ht.2
  have hγae : ∀ᵐ q ∂μ₂, Integrable (fun e => γ₂ q.2 q.1 e * γ₂ q.2 q.1 e) ν
      ∧ Integrable (fun e => γ₁ q.2 q.1 e * γ₂ q.2 q.1 e) ν
      ∧ Integrable (fun e => γ₁ q.2 q.1 e * γ₁ q.2 q.1 e) ν := by
    have hE₁ := (markedEnergy_mono ht.2).trans_lt h₁.γ_sq.lt_top
    have hE₂ := (markedEnergy_mono ht.2).trans_lt h₂.γ_sq.lt_top
    filter_upwards [ae_integrable_mul_marked (φ := fun ω s e => γ₂ s ω e)
        (ψ := fun ω s e => γ₂ s ω e) h₂.γ_meas h₂.γ_meas hE₂ hE₂,
      ae_integrable_mul_marked (φ := fun ω s e => γ₁ s ω e) (ψ := fun ω s e => γ₂ s ω e)
        h₁.γ_meas h₂.γ_meas hE₁ hE₂,
      ae_integrable_mul_marked (φ := fun ω s e => γ₁ s ω e) (ψ := fun ω s e => γ₁ s ω e)
        h₁.γ_meas h₁.γ_meas hE₁ hE₁] with q h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have hcomb : ∀ᵐ q ∂μ₂,
      (X₂ q.2 q.1 * b₂ q.1 q.2 + X₂ q.2 q.1 * b₂ q.1 q.2
          + ∑ j, σ₂ q.2 q.1 j * σ₂ q.2 q.1 j + ∫ e, γ₂ q.2 q.1 e * γ₂ q.2 q.1 e ∂ν)
        - 2 * (p' q.2 * (X₁ q.2 q.1 * X₂ q.2 q.1) + p q.2 * (X₁ q.2 q.1 * b₂ q.1 q.2
          + X₂ q.2 q.1 * b₁ q.1 q.2 + ∑ j, σ₁ q.2 q.1 j * σ₂ q.2 q.1 j
          + ∫ e, γ₁ q.2 q.1 e * γ₂ q.2 q.1 e ∂ν))
        + ((p' q.2 * p q.2 + p q.2 * p' q.2) * (X₁ q.2 q.1 * X₁ q.2 q.1)
          + p q.2 * p q.2 * (X₁ q.2 q.1 * b₁ q.1 q.2 + X₁ q.2 q.1 * b₁ q.1 q.2
            + ∑ j, σ₁ q.2 q.1 j * σ₁ q.2 q.1 j + ∫ e, γ₁ q.2 q.1 e * γ₁ q.2 q.1 e ∂ν))
      = 2 * (X₂ q.2 q.1 - p q.2 * X₁ q.2 q.1)
          * (b₂ q.1 q.2 - p' q.2 * X₁ q.2 q.1 - p q.2 * b₁ q.1 q.2)
        + ∑ j, (σ₂ q.2 q.1 j - p q.2 * σ₁ q.2 q.1 j) ^ 2
        + ∫ e, (γ₂ q.2 q.1 e - p q.2 * γ₁ q.2 q.1 e) ^ 2 ∂ν := by
    filter_upwards [hγae] with q ⟨h1, h2, h3⟩
    rw [integral_sub_mul_sq_eq (p q.2) h1 h2 h3]
    have hs : ∑ j, (σ₂ q.2 q.1 j - p q.2 * σ₁ q.2 q.1 j) ^ 2
        = ∑ j, σ₂ q.2 q.1 j * σ₂ q.2 q.1 j - 2 * p q.2 * ∑ j, σ₁ q.2 q.1 j * σ₂ q.2 q.1 j
          + p q.2 * p q.2 * ∑ j, σ₁ q.2 q.1 j * σ₁ q.2 q.1 j := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hs]
    ring
  set M12 : Ω × ℝ → ℝ := fun q => X₁ q.2 q.1 * X₂ q.2 q.1 with hM12
  set M11 : Ω × ℝ → ℝ := fun q => X₁ q.2 q.1 * X₁ q.2 q.1 with hM11
  set R22 : Ω × ℝ → ℝ := fun q => X₂ q.2 q.1 * b₂ q.1 q.2 + X₂ q.2 q.1 * b₂ q.1 q.2
    + ∑ j, σ₂ q.2 q.1 j * σ₂ q.2 q.1 j + ∫ e, γ₂ q.2 q.1 e * γ₂ q.2 q.1 e ∂ν with hR22
  set R12 : Ω × ℝ → ℝ := fun q => X₁ q.2 q.1 * b₂ q.1 q.2 + X₂ q.2 q.1 * b₁ q.1 q.2
    + ∑ j, σ₁ q.2 q.1 j * σ₂ q.2 q.1 j + ∫ e, γ₁ q.2 q.1 e * γ₂ q.2 q.1 e ∂ν with hR12
  set R11 : Ω × ℝ → ℝ := fun q => X₁ q.2 q.1 * b₁ q.1 q.2 + X₁ q.2 q.1 * b₁ q.1 q.2
    + ∑ j, σ₁ q.2 q.1 j * σ₁ q.2 q.1 j + ∫ e, γ₁ q.2 q.1 e * γ₁ q.2 q.1 e ∂ν with hR11
  have hP12 : Integrable (fun q : Ω × ℝ => p' q.2 * M12 q + p q.2 * R12 q) μ₂ := hJ12.add hI12
  have hP11 : Integrable (fun q : Ω × ℝ => (p' q.2 * p q.2 + p q.2 * p' q.2) * M11 q
      + p q.2 * p q.2 * R11 q) μ₂ := hJ11.add hI11
  have hL : Integrable (fun q : Ω × ℝ => R22 q - 2 * (p' q.2 * M12 q + p q.2 * R12 q)) μ₂ :=
    hI22.sub (hP12.const_mul 2)
  have hI : Integrable (fun q : Ω × ℝ => R22 q - 2 * (p' q.2 * M12 q + p q.2 * R12 q)
      + ((p' q.2 * p q.2 + p q.2 * p' q.2) * M11 q + p q.2 * p q.2 * R11 q)) μ₂ := hL.add hP11
  refine ⟨hI.congr hcomb, ?_⟩
  rw [← integral_congr_ae hcomb, integral_add hL hP11, integral_sub hI22 (hP12.const_mul 2),
    integral_const_mul, integral_add hJ12 hI12, integral_add hJ11 hI11, hres (p t) hX₁ hX₂,
    hres (p 0) h₁.ξ₀_sq h₂.ξ₀_sq]
  linarith [e12, e11, e22]


omit [IsProbabilityMeasure P] in
/-- For `t ≤ T`, `P ⊗ ds` on `[0, t]` is at most `P ⊗ ds` on `[0, T]`. -/
theorem prod_restrict_Icc_le [SFinite P] {t : ℝ} (ht : t ≤ T) :
    P.prod (volume.restrict (Set.Icc (0 : ℝ) t))
      ≤ P.prod (volume.restrict (Set.Icc (0 : ℝ) T)) := by
  have e : ∀ S : Set ℝ, P.prod (volume.restrict S) = (P.prod volume).restrict (Set.univ ×ˢ S) :=
    fun S => by rw [← Measure.prod_restrict, Measure.restrict_univ]
  rw [e, e]
  exact Measure.restrict_mono (Set.prod_mono le_rfl (Set.Icc_subset_Icc le_rfl ht)) le_rfl

/-- **A decoupling residual with a nonnegative rate and no terminal mass vanishes.** In the
setting of `integral_residual_sq_eq`, if `𝔼[(X₂(T) − p(T) X₁(T))²] = 0` and the rate `r` is
nonnegative for `P ⊗ ds` on `[0, T]`, then `𝔼[(X₂(t) − p(t) X₁(t))²] = 0` at every `t ∈ [0, T]` and
the integral of `r` for `P ⊗ ds` on `[0, T]` is `0`. -/
theorem residual_eq_zero_of_nonneg (h₁ : LinearFSDEJ D ℱ hℱW hℱN T ξ₁ b₁ X₁ σ₁ γ₁)
    (h₂ : LinearFSDEJ D ℱ hℱW hℱN T ξ₂ b₂ X₂ σ₂ γ₂) (𝒲 : D.CrossWitness ℱ) (hT : 0 < T)
    {p p' : ℝ → ℝ} (hpc : ContinuousOn p (Set.Icc (0 : ℝ) T))
    (hp : ∀ x ∈ Set.Ioo (0 : ℝ) T, HasDerivAt p (p' x) x)
    (hp' : ContinuousOn p' (Set.Icc (0 : ℝ) T))
    (hT0 : ∫ ω, (X₂ T ω - p T * X₁ T ω) ^ 2 ∂P = 0)
    (hr : 0 ≤ᵐ[P.prod (volume.restrict (Set.Icc (0 : ℝ) T))] fun q : Ω × ℝ =>
      2 * (X₂ q.2 q.1 - p q.2 * X₁ q.2 q.1)
          * (b₂ q.1 q.2 - p' q.2 * X₁ q.2 q.1 - p q.2 * b₁ q.1 q.2)
        + ∑ j, (σ₂ q.2 q.1 j - p q.2 * σ₁ q.2 q.1 j) ^ 2
        + ∫ e, (γ₂ q.2 q.1 e - p q.2 * γ₁ q.2 q.1 e) ^ 2 ∂ν) :
    (∀ t ∈ Set.Icc (0 : ℝ) T, ∫ ω, (X₂ t ω - p t * X₁ t ω) ^ 2 ∂P = 0)
      ∧ ∫ q, (2 * (X₂ q.2 q.1 - p q.2 * X₁ q.2 q.1)
            * (b₂ q.1 q.2 - p' q.2 * X₁ q.2 q.1 - p q.2 * b₁ q.1 q.2)
          + ∑ j, (σ₂ q.2 q.1 j - p q.2 * σ₁ q.2 q.1 j) ^ 2
          + ∫ e, (γ₂ q.2 q.1 e - p q.2 * γ₁ q.2 q.1 e) ^ 2 ∂ν)
          ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) = 0 := by
  obtain ⟨hrT, eT⟩ := integral_residual_sq_eq h₁ h₂ 𝒲 hT hpc hp hp' ⟨hT.le, le_rfl⟩
  obtain ⟨-, e0⟩ := integral_residual_sq_eq h₁ h₂ 𝒲 hT hpc hp hp' ⟨le_rfl, hT.le⟩
  rw [Set.Icc_self, Measure.restrict_singleton, measure_singleton, zero_smul,
    Measure.prod_zero, integral_zero_measure, add_zero] at e0
  have hF0 : 0 ≤ ∫ ω, (ξ₂ ω - p 0 * ξ₁ ω) ^ 2 ∂P := integral_nonneg fun _ => sq_nonneg _
  have hI0 := integral_nonneg_of_ae hr
  have hF00 : ∫ ω, (ξ₂ ω - p 0 * ξ₁ ω) ^ 2 ∂P = 0 := by linarith
  refine ⟨fun t ht => ?_, by linarith⟩
  obtain ⟨-, et⟩ := integral_residual_sq_eq h₁ h₂ 𝒲 hT hpc hp hp' ht
  have hle := integral_mono_measure (prod_restrict_Icc_le (P := P) ht.2) hr hrT
  have hge : 0 ≤ ∫ ω, (X₂ t ω - p t * X₁ t ω) ^ 2 ∂P := integral_nonneg fun _ => sq_nonneg _
  linarith


/-- **A decoupling residual with a nonnegative rate and no terminal mass vanishes**, the rate
nonnegative at almost every time, almost surely: in the setting of `integral_residual_sq_eq`, if
`𝔼[(X₂(T) − p(T) X₁(T))²] = 0` and at almost every `s ∈ [0, T]` the rate `r(·, s)` is almost
surely nonnegative, then `𝔼[(X₂(t) − p(t) X₁(t))²] = 0` at every `t ∈ [0, T]` and at almost every
`s ∈ [0, T]` the rate `r(·, s)` vanishes almost surely. -/
theorem residual_eq_zero_of_ae_ae_nonneg (h₁ : LinearFSDEJ D ℱ hℱW hℱN T ξ₁ b₁ X₁ σ₁ γ₁)
    (h₂ : LinearFSDEJ D ℱ hℱW hℱN T ξ₂ b₂ X₂ σ₂ γ₂) (𝒲 : D.CrossWitness ℱ) (hT : 0 < T)
    {p p' : ℝ → ℝ} (hpc : ContinuousOn p (Set.Icc (0 : ℝ) T))
    (hp : ∀ x ∈ Set.Ioo (0 : ℝ) T, HasDerivAt p (p' x) x)
    (hp' : ContinuousOn p' (Set.Icc (0 : ℝ) T))
    (hT0 : ∫ ω, (X₂ T ω - p T * X₁ T ω) ^ 2 ∂P = 0)
    (hr : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P,
      0 ≤ 2 * (X₂ s ω - p s * X₁ s ω) * (b₂ ω s - p' s * X₁ s ω - p s * b₁ ω s)
        + ∑ j, (σ₂ s ω j - p s * σ₁ s ω j) ^ 2
        + ∫ e, (γ₂ s ω e - p s * γ₁ s ω e) ^ 2 ∂ν) :
    (∀ t ∈ Set.Icc (0 : ℝ) T, ∫ ω, (X₂ t ω - p t * X₁ t ω) ^ 2 ∂P = 0)
      ∧ ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P,
        2 * (X₂ s ω - p s * X₁ s ω) * (b₂ ω s - p' s * X₁ s ω - p s * b₁ ω s)
          + ∑ j, (σ₂ s ω j - p s * σ₁ s ω j) ^ 2
          + ∫ e, (γ₂ s ω e - p s * γ₁ s ω e) ^ 2 ∂ν = 0 := by
  set r : Ω × ℝ → ℝ := fun q => 2 * (X₂ q.2 q.1 - p q.2 * X₁ q.2 q.1)
      * (b₂ q.1 q.2 - p' q.2 * X₁ q.2 q.1 - p q.2 * b₁ q.1 q.2)
    + ∑ j, (σ₂ q.2 q.1 j - p q.2 * σ₁ q.2 q.1 j) ^ 2
    + ∫ e, (γ₂ q.2 q.1 e - p q.2 * γ₁ q.2 q.1 e) ^ 2 ∂ν with hrdef
  obtain ⟨hrT, eT⟩ := integral_residual_sq_eq h₁ h₂ 𝒲 hT hpc hp hp' ⟨hT.le, le_rfl⟩
  obtain ⟨-, e0⟩ := integral_residual_sq_eq h₁ h₂ 𝒲 hT hpc hp hp' ⟨le_rfl, hT.le⟩
  rw [Set.Icc_self, Measure.restrict_singleton, measure_singleton, zero_smul,
    Measure.prod_zero, integral_zero_measure, add_zero] at e0
  set g : ℝ → ℝ := fun s => ∫ ω, r (ω, s) ∂P with hg
  have hgi : IntegrableOn g (Set.Icc (0 : ℝ) T) := hrT.integral_prod_right
  have hg0 : 0 ≤ᵐ[volume.restrict (Set.Icc (0 : ℝ) T)] g := by
    filter_upwards [hr] with s hs
    exact integral_nonneg_of_ae hs
  have hprod : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫ q, r q ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) t))) = ∫ s in Set.Icc (0 : ℝ) t, g s := by
    intro t ht
    obtain ⟨hrt, -⟩ := integral_residual_sq_eq h₁ h₂ 𝒲 hT hpc hp hp' ht
    exact integral_prod_symm _ hrt
  have hF0 : 0 ≤ ∫ ω, (ξ₂ ω - p 0 * ξ₁ ω) ^ 2 ∂P := integral_nonneg fun _ => sq_nonneg _
  have hIT : 0 ≤ ∫ s in Set.Icc (0 : ℝ) T, g s := integral_nonneg_of_ae hg0
  rw [hprod T ⟨hT.le, le_rfl⟩] at eT
  have hF00 : ∫ ω, (ξ₂ ω - p 0 * ξ₁ ω) ^ 2 ∂P = 0 := by linarith
  have hIT0 : ∫ s in Set.Icc (0 : ℝ) T, g s = 0 := by linarith
  refine ⟨fun t ht => ?_, ?_⟩
  · obtain ⟨-, et⟩ := integral_residual_sq_eq h₁ h₂ 𝒲 hT hpc hp hp' ht
    rw [hprod t ht] at et
    have hle : ∫ s in Set.Icc (0 : ℝ) t, g s ≤ ∫ s in Set.Icc (0 : ℝ) T, g s :=
      setIntegral_mono_set hgi hg0 (Eventually.of_forall (Set.Icc_subset_Icc le_rfl ht.2))
    have hge : 0 ≤ ∫ ω, (X₂ t ω - p t * X₁ t ω) ^ 2 ∂P := integral_nonneg fun _ => sq_nonneg _
    linarith
  · have hgz := (integral_eq_zero_iff_of_nonneg_ae hg0 hgi).mp hIT0
    filter_upwards [hgz, hr, hrT.prod_left_ae] with s hs h1 h2
    exact (integral_eq_zero_iff_of_nonneg_ae h1 h2).mp hs


end LinearFSDEJ

end MVFBSDEJ.WellPosedness.Stability
