/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Stability.SupUpgrade
import LevyStochCalc.Brownian.MultidimItoCongr
import LevyStochCalc.Ito.CompensatedLocalityWindow

/-!
# The forward difference up to an intermediate time

Step 3 of the proof of Lemma 4.3 of the well-posedness paper fixes `t ≤ T` and bounds the running
supremum of the forward difference up to `t`. A solution of the linear forward equation on
`[0, T]` solves, on `[0, t]`, the linear forward equation whose integrands are those of the
original restricted to `[0, t]`, so the `S²` bound on `[0, t]` gives

`𝔼 sup_{s ≤ t} |X_s|² ≤ 3 𝔼|ξ₀|² + 3t 𝔼 ∫_0^t b_s² ds
  + 12 (𝔼 ∫_0^t |σ_s|² ds + 𝔼 ∫_0^t ∫_E γ_s(e)² ν(de) ds)`.

For the difference system, the expected Lipschitz bound (3.2), integrated over `[0, t]`, bounds
the coefficient differences there by the difference itself:

`𝔼 ∫_0^t (|δb|² + |δσ|²_F + ‖δh‖²) ≤ K 𝔼 ∫_0^t (|δX|² + |δY|² + |δZ|²_F + ‖δU‖²)`.

## Main statements

* `markedEnergy_congr_ae_of_le` — the marked energy on `[0, t]`, `t ≤ T`, depends only on the
  class of the integrand on `Ω × [0, T] × E`.
* `LinearFSDEJ.truncate` — the forward equation on `[0, t]` with the restricted integrands.
* `LinearFSDEJ.lintegral_biSup_sq_le_at` — the `S²` bound on `[0, t]`.
* `PairDiff.realisedEnergy_le_at` — the energies of the realised integrands on `[0, t]`.
* `PairDiff.coeffEnergy_le_at` — (3.2) integrated over `[0, t]`.
* `PairDiff.energy_le_lintegral_biSup` — `𝔼 ∫_0^t |δX_s|² ds ≤ ∫_0^t 𝔼 sup_{r ≤ s} |δX_r|² ds`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Dissertation.WellPosedness.Stability

open LevyStochCalc.BSDEJ.Solves LevyStochCalc Dissertation.WellPosedness.BrownianPoisson

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- Restricting the times of a jointly measurable process to a measurable set preserves joint
measurability. -/
theorem measurable_uncurry_indicator_time {S : Set ℝ} (hS : MeasurableSet S)
    {H : Ω → ℝ → ℝ} (hH : Measurable (Function.uncurry H)) :
    Measurable (Function.uncurry fun ω s => S.indicator (fun _ => H ω s) s) := by
  have e : (Function.uncurry fun ω s => S.indicator (fun _ => H ω s) s)
      = (Prod.snd ⁻¹' S).indicator (Function.uncurry H) := by
    funext p
    by_cases hp : p.2 ∈ S
    · simp [Function.uncurry, hp]
    · simp [Function.uncurry, hp, Set.indicator_of_notMem]
  rw [e]
  exact hH.indicator (measurable_snd hS)

omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- Restricting the times of a jointly measurable marked process to a measurable set preserves
joint measurability. -/
theorem measurable_marked_indicator_time {S : Set ℝ} (hS : MeasurableSet S)
    {H : ℝ → Ω → E → ℝ} (hH : Measurable fun p : Ω × ℝ × E => H p.2.1 p.1 p.2.2) :
    Measurable fun p : Ω × ℝ × E => S.indicator (fun _ => H p.2.1 p.1 p.2.2) p.2.1 := by
  have e : (fun p : Ω × ℝ × E => S.indicator (fun _ => H p.2.1 p.1 p.2.2) p.2.1)
      = {p : Ω × ℝ × E | p.2.1 ∈ S}.indicator fun p => H p.2.1 p.1 p.2.2 := by
    funext p
    by_cases hp : p.2.1 ∈ S
    · simp [hp]
    · simp [hp, Set.indicator_of_notMem]
  rw [e]
  exact hH.indicator (measurable_snd.fst hS)

omit [IsProbabilityMeasure P] in
/-- The energy on `[0, t]` of a process restricted to `[0, t]` is that of the process. -/
theorem energy_indicator_Icc (t : ℝ) (H : Ω → ℝ → ℝ) :
    Brownian.Ito.energy P t (fun ω s => (Set.Icc (0 : ℝ) t).indicator (fun _ => H ω s) s)
      = Brownian.Ito.energy P t H :=
  lintegral_congr fun ω => setLIntegral_congr_fun measurableSet_Icc fun s hs => by
    simp only [Set.indicator_of_mem hs]

omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- The marked energy on `[0, t]` of a marked process restricted to `[0, t]` is that of the
process. -/
theorem markedEnergy_indicator_Icc (t : ℝ) (H : Ω → ℝ → E → ℝ) :
    Poisson.Compensated.markedEnergy P ν t
        (fun ω s e => (Set.Icc (0 : ℝ) t).indicator (fun _ => H ω s e) s)
      = Poisson.Compensated.markedEnergy P ν t H :=
  lintegral_congr fun ω => setLIntegral_congr_fun measurableSet_Icc fun s hs => by
    simp only [Set.indicator_of_mem hs]

omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- **The marked energy on an earlier window depends only on the class of the integrand.** Two
integrands agreeing almost everywhere for the marked energy measure on `Ω × [0, T] × E` have the
same marked energy on `[0, t]` for every `t ≤ T`. -/
theorem markedEnergy_congr_ae_of_le [SFinite ν] {t T : ℝ} (htT : t ≤ T)
    {φ₁ φ₂ : Ω → ℝ → E → ℝ}
    (h : ∀ᵐ q ∂(Poisson.Compensated.markedEnergyMeasure P ν T),
      φ₁ q.1 q.2.1 q.2.2 = φ₂ q.1 q.2.1 q.2.2) :
    Poisson.Compensated.markedEnergy P ν t φ₁ = Poisson.Compensated.markedEnergy P ν t φ₂ := by
  rw [Poisson.Compensated.markedEnergyMeasure] at h
  unfold Poisson.Compensated.markedEnergy
  refine lintegral_congr_ae ?_
  filter_upwards [Measure.ae_ae_of_ae_prod h] with ω hω
  have hs := ae_restrict_of_ae_restrict_of_subset (Set.Icc_subset_Icc le_rfl htT)
    (Measure.ae_ae_of_ae_prod hω)
  refine lintegral_congr_ae ?_
  filter_upwards [hs] with s hs
  refine lintegral_congr_ae ?_
  filter_upwards [hs] with e he
  rw [he]

namespace LinearFSDEJ

variable {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}
  {T : ℝ} {ξ₀ : Ω → ℝ} {b : Ω → ℝ → ℝ} {X : ℝ → Ω → ℝ} {σ : ℝ → Ω → (Fin d → ℝ)}
  {γ : ℝ → Ω → E → ℝ}

/-- **The forward equation up to an intermediate time.** A solution of the linear forward
equation on `[0, T]` solves, on `[0, t]` for `t ≤ T`, the linear forward equation whose
integrands are those of the original restricted to `[0, t]`. -/
theorem truncate (h : LinearFSDEJ D ℱ hℱW hℱN T ξ₀ b X σ γ) {t : ℝ} (htT : t ≤ T) :
    LinearFSDEJ D ℱ hℱW hℱN t ξ₀ (fun ω s => (Set.Icc (0 : ℝ) t).indicator (fun _ => b ω s) s) X
      (fun s ω j => (Set.Icc (0 : ℝ) t).indicator (fun _ => σ s ω j) s)
      (fun s ω e => (Set.Icc (0 : ℝ) t).indicator (fun _ => γ s ω e) s) := by
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc 0 T := Set.Icc_subset_Icc le_rfl htT
  have hσm : ∀ j : Fin d, Measurable (Function.uncurry fun ω s =>
      (Set.Icc (0 : ℝ) t).indicator (fun _ => σ s ω j) s) := fun j =>
    measurable_uncurry_indicator_time measurableSet_Icc (h.σ_meas j)
  have hσp : ∀ j : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s =>
      (Set.Icc (0 : ℝ) t).indicator (fun _ => σ s ω j) s := fun j =>
    progressivelyMeasurable_indicator_time (h.σ_prog j) measurableSet_Icc
  have hσv : ∀ ω s, s ∉ Set.Icc (0 : ℝ) t →
      (fun j => (Set.Icc (0 : ℝ) t).indicator (fun _ => σ s ω j) s) = 0 := fun ω s hs => by
    funext j
    simp [Set.indicator_of_notMem hs]
  have hσq : ∀ j : Fin d, Brownian.Ito.energy P t
      (fun ω s => (Set.Icc (0 : ℝ) t).indicator (fun _ => σ s ω j) s) ≠ ⊤ := fun j => by
    rw [energy_indicator_Icc]
    exact ne_top_of_le_ne_top (h.σ_sq j)
      (lintegral_mono fun _ => lintegral_mono_set hsub)
  have hγm : Measurable fun p : Ω × ℝ × E =>
      (Set.Icc (0 : ℝ) t).indicator (fun _ => γ p.2.1 p.1 p.2.2) p.2.1 :=
    measurable_marked_indicator_time measurableSet_Icc h.γ_meas
  have hγp : Probability.MarkedProgressivelyMeasurable ℱ fun ω s e =>
      (Set.Icc (0 : ℝ) t).indicator (fun _ => γ s ω e) s :=
    Probability.MarkedProgressivelyMeasurable.indicator_time h.γ_prog measurableSet_Icc
  have hγv : ∀ ω s e, s ∉ Set.Icc (0 : ℝ) t →
      (Set.Icc (0 : ℝ) t).indicator (fun _ => γ s ω e) s = 0 := fun ω s e hs =>
    Set.indicator_of_notMem hs _
  have hγq : Poisson.Compensated.markedEnergy P ν t
      (fun ω s e => (Set.Icc (0 : ℝ) t).indicator (fun _ => γ s ω e) s) ≠ ⊤ := by
    rw [markedEnergy_indicator_Icc (H := fun ω s e => γ s ω e)]
    exact ne_top_of_le_ne_top h.γ_sq (lintegral_mono fun _ => lintegral_mono_set hsub)
  have hbm : Measurable (Function.uncurry fun ω s =>
      (Set.Icc (0 : ℝ) t).indicator (fun _ => b ω s) s) :=
    measurable_uncurry_indicator_time measurableSet_Icc h.b_meas
  have hbp : Probability.ProgressivelyMeasurable ℱ fun ω s =>
      (Set.Icc (0 : ℝ) t).indicator (fun _ => b ω s) s :=
    progressivelyMeasurable_indicator_time h.b_prog measurableSet_Icc
  have hbv : ∀ ω s, s ∉ Set.Icc (0 : ℝ) t →
      (Set.Icc (0 : ℝ) t).indicator (fun _ => b ω s) s = 0 := fun ω s hs =>
    Set.indicator_of_notMem hs _
  have hbq : Brownian.Ito.energy P t
      (fun ω s => (Set.Icc (0 : ℝ) t).indicator (fun _ => b ω s) s) ≠ ⊤ := by
    rw [energy_indicator_Icc]
    exact ne_top_of_le_ne_top h.b_sq (lintegral_mono fun _ => lintegral_mono_set hsub)
  refine ⟨hσm, hσp, hσv, hσq, hγm, hγp, hγv, hγq, hbm, hbp, hbv, hbq, h.ξ₀_sq, h.X_adapted,
    h.X_rightCont, ?_⟩
  intro s hs
  have hb : ∀ ω, ∫ r in Set.Icc (0 : ℝ) s, (Set.Icc (0 : ℝ) t).indicator (fun _ => b ω r) r
      = ∫ r in Set.Icc (0 : ℝ) s, b ω r := fun ω =>
    setIntegral_congr_fun measurableSet_Icc fun r hr =>
      Set.indicator_of_mem (Set.Icc_subset_Icc le_rfl hs.2 hr) _
  rcases hs.1.eq_or_lt with h0 | hpos
  · subst h0
    filter_upwards [h.eqn 0 (hsub hs),
      Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral_ae_zero_of_nonpos D.W ℱ hℱW σ
        h.σ_meas h.σ_prog (sq_int_global_of_vanishing h.σ_vanish h.σ_sq) le_rfl,
      Poisson.Compensated.stochasticIntegral_ae_zero_of_nonpos (φ := fun ω s e => γ s ω e) D.N
        hℱN h.γ_meas h.γ_prog (marked_sq_int_global_of_vanishing h.γ_vanish h.γ_sq) le_rfl,
      Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral_ae_zero_of_nonpos D.W ℱ hℱW _
        hσm hσp (sq_int_global_of_vanishing hσv hσq) le_rfl,
      Poisson.Compensated.stochasticIntegral_ae_zero_of_nonpos D.N hℱN hγm hγp
        (marked_sq_int_global_of_vanishing hγv hγq) le_rfl]
      with ω e₀ e₁ e₂ e₃ e₄
    simp only [Pi.zero_apply] at e₁ e₂ e₃ e₄
    rw [e₀, e₁, e₂, e₃, e₄, hb]
  · filter_upwards [h.eqn s (hsub hs),
      Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral_congr_ae D.W ℱ hℱW
        hσm hσp (sq_int_global_of_vanishing hσv hσq) h.σ_meas h.σ_prog
        (sq_int_global_of_vanishing h.σ_vanish h.σ_sq) hpos
        (Eventually.of_forall fun ω => (ae_restrict_mem measurableSet_Icc).mono fun r hr => by
          funext j
          exact Set.indicator_of_mem (Set.Icc_subset_Icc le_rfl hs.2 hr) _),
      Poisson.Compensated.stochasticIntegral_congr_of_eqOn_Ioc D.N hℱN hγm hγp
        (marked_sq_int_global_of_vanishing hγv hγq) h.γ_meas h.γ_prog
        (marked_sq_int_global_of_vanishing h.γ_vanish h.γ_sq) hpos
        (fun ω r hr e => Set.indicator_of_mem
          (Set.Icc_subset_Icc le_rfl hs.2 (Set.Ioc_subset_Icc_self hr)) _)]
      with ω e₁ e₂ e₃
    rw [e₁, e₂, e₃, hb]

/-- **The `S²` bound up to an intermediate time.** Over a filtration whose null sets lie in its
time-`0` field, whose right-continuation is constant before `0`, and which admits a cross
witness, a solution of the linear forward equation satisfies, for every `t ∈ [0, T]`,

`𝔼 sup_{s ≤ t} |X_s|² ≤ 3 𝔼|ξ₀|² + 3t 𝔼 ∫_0^t b_s² ds
  + 12 (𝔼 ∫_0^t |σ_s|² ds + 𝔼 ∫_0^t ∫_E γ_s(e)² ν(de) ds)`. -/
theorem lintegral_biSup_sq_le_at (h : LinearFSDEJ D ℱ hℱW hℱN T ξ₀ b X σ γ)
    (𝒲 : D.CrossWitness ℱ) (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∫⁻ ω, (⨆ s ∈ Set.Icc (0 : ℝ) t, (‖X s ω‖₊ : ℝ≥0∞) ^ 2) ∂P
      ≤ 3 * ∫⁻ ω, (‖ξ₀ ω‖₊ : ℝ≥0∞) ^ 2 ∂P
        + 3 * (ENNReal.ofReal t * Brownian.Ito.energy P t b)
        + 12 * ((∑ j : Fin d, Brownian.Ito.energy P t (fun ω s => σ s ω j))
          + Poisson.Compensated.markedEnergy P ν t (fun ω s e => γ s ω e)) := by
  have hX0 : X 0 =ᵐ[P] ξ₀ := h.initial_ae_eq (ht.1.trans ht.2)
  have h0 : ∫⁻ ω, (‖X 0 ω‖₊ : ℝ≥0∞) ^ 2 ∂P = ∫⁻ ω, (‖ξ₀ ω‖₊ : ℝ≥0∞) ^ 2 ∂P :=
    lintegral_congr_ae (hX0.mono fun ω hω => by simp only [hω])
  rcases ht.1.eq_or_lt with ht0 | hpos
  · subst ht0
    have e : ∫⁻ ω, (⨆ s ∈ Set.Icc (0 : ℝ) 0, (‖X s ω‖₊ : ℝ≥0∞) ^ 2) ∂P
        = ∫⁻ ω, (‖X 0 ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
      simp only [Set.Icc_self, iSup_singleton]
    rw [e, h0]
    refine le_trans ?_ (le_self_add.trans le_self_add)
    exact le_mul_of_one_le_left' (by norm_num)
  · have hB := ((h.truncate ht.2).linearBSDEJ hpos.le).lintegral_biSup_sq_le 𝒲 hℱ0 hnull
      hpos
    have eb : Brownian.Ito.energy P t
        (fun ω s => -(Set.Icc (0 : ℝ) t).indicator (fun _ => b ω s) s)
        = Brownian.Ito.energy P t b :=
      lintegral_congr fun ω => setLIntegral_congr_fun measurableSet_Icc fun s hs => by
        simp only [Set.indicator_of_mem hs, nnnorm_neg]
    have eσ : ∀ j : Fin d, Brownian.Ito.energy P t
        (fun ω s => (Set.Icc (0 : ℝ) t).indicator (fun _ => σ s ω j) s)
        = Brownian.Ito.energy P t (fun ω s => σ s ω j) := fun j =>
      energy_indicator_Icc t (fun ω s => σ s ω j)
    have eγ := markedEnergy_indicator_Icc (P := P) (ν := ν) t (fun ω s e => γ s ω e)
    rw [eb, h0] at hB
    simp only [eσ, eγ] at hB
    exact hB

end LinearFSDEJ

namespace PairDiff

variable {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {T lam K KT α β₁ β₂ : ℝ} {n m : ℕ}
  {G : Matrix (Fin m) (Fin n) ℝ} {ξ₀ : Fin n → Ω → ℝ}
  {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ}
  {Z : Fin m → ℝ → Ω → Fin d → ℝ} {U : Fin m → ℝ → Ω → E → ℝ}
  {b : Fin n → Ω → ℝ → ℝ} {σ : Fin n → ℝ → Ω → Fin d → ℝ} {h : Fin n → ℝ → Ω → E → ℝ}
  {f : Fin m → Ω → ℝ → ℝ} {g : Fin m → Ω → ℝ}
  {qb : Fin n → Ω → ℝ → ℝ} {qσ : Fin n → ℝ → Ω → Fin d → ℝ} {qh : Fin n → ℝ → Ω → E → ℝ}
  {qf : Fin m → Ω → ℝ → ℝ} {qg : Fin m → Ω → ℝ}

/-- For `λ ≠ 0` the drift differences of the difference system are jointly measurable. -/
theorem measurable_b (hD : PairDiff D ℱ hℱW hℱN T lam K KT α β₁ β₂ G ξ₀ X Y Z U b σ h f g
    qb qσ qh qf qg) (hlam : lam ≠ 0) (i : Fin n) : Measurable (Function.uncurry (b i)) := by
  have hm := ((hD.fwd i).b_meas.sub (hD.qb_meas i)).const_mul lam⁻¹
  convert hm using 1
  funext p
  simp only [Function.uncurry, Pi.sub_apply]
  field_simp
  ring

/-- For `λ ≠ 0` the diffusion differences of the difference system are jointly measurable. -/
theorem measurable_σ (hD : PairDiff D ℱ hℱW hℱN T lam K KT α β₁ β₂ G ξ₀ X Y Z U b σ h f g
    qb qσ qh qf qg) (hlam : lam ≠ 0) (i : Fin n) (j : Fin d) :
    Measurable (Function.uncurry fun ω s => σ i s ω j) := by
  have hm := (((hD.fwd i).σ_meas j).sub (hD.qσ_meas i j)).const_mul lam⁻¹
  convert hm using 1
  funext p
  simp only [Function.uncurry, Pi.sub_apply]
  field_simp
  ring

/-- For `λ ≠ 0` the jump differences of the difference system are jointly measurable. -/
theorem measurable_h (hD : PairDiff D ℱ hℱW hℱN T lam K KT α β₁ β₂ G ξ₀ X Y Z U b σ h f g
    qb qσ qh qf qg) (hlam : lam ≠ 0) (i : Fin n) :
    Measurable fun p : Ω × ℝ × E => h i p.2.1 p.1 p.2.2 := by
  have hm := ((hD.fwd i).γ_meas.sub (hD.qh_meas i)).const_mul lam⁻¹
  convert hm using 1
  funext p
  simp only [Pi.sub_apply]
  field_simp
  ring

/-- **The energies of the realised integrands on `[0, t]`.** For the difference system with
jointly measurable coefficient differences and `λ² ≤ 1`,

`𝔼 ∫_0^t (|λ δb + q^b|² + |λ δσ + q^σ|²_F + ‖λ δh + q^h‖²)
  ≤ 2 𝔼 ∫_0^t (|δb|² + |δσ|²_F + ‖δh‖²) + 2 𝔼 ∫_0^t (|q^b|² + |q^σ|²_F + ‖q^h‖²)`. -/
theorem realisedEnergy_le_at (hD : PairDiff D ℱ hℱW hℱN T lam K KT α β₁ β₂ G ξ₀ X Y Z U b σ h f g
    qb qσ qh qf qg) (hbm : ∀ i, Measurable (Function.uncurry (b i)))
    (hσm : ∀ i j, Measurable (Function.uncurry fun ω s => σ i s ω j))
    (hhm : ∀ i, Measurable fun p : Ω × ℝ × E => h i p.2.1 p.1 p.2.2) (hl : lam ^ 2 ≤ 1)
    (t : ℝ) :
    ∑ i, Brownian.Ito.energy P t (fun ω s => lam * b i ω s + qb i ω s)
        + ∑ i, ∑ j, Brownian.Ito.energy P t (fun ω s => lam * σ i s ω j + qσ i s ω j)
        + ∑ i, Poisson.Compensated.markedEnergy P ν t
          (fun ω s e => lam * h i s ω e + qh i s ω e)
      ≤ 2 * (∑ i, Brownian.Ito.energy P t (b i)
          + ∑ i, ∑ j, Brownian.Ito.energy P t (fun ω s => σ i s ω j)
          + ∑ i, Poisson.Compensated.markedEnergy P ν t (fun ω s e => h i s ω e))
        + 2 * (∑ i, Brownian.Ito.energy P t (qb i)
          + ∑ i, ∑ j, Brownian.Ito.energy P t (fun ω s => qσ i s ω j)
          + ∑ i, Poisson.Compensated.markedEnergy P ν t (fun ω s e => qh i s ω e)) := by
  have eR := lintegral_sampleEnergy_add (P := P) (ν := ν)
    (x := fun i ω s => lam * b i ω s + qb i ω s)
    (z := fun i j ω s => lam * σ i s ω j + qσ i s ω j)
    (u := fun i ω s e => lam * h i s ω e + qh i s ω e) (fun i => (hD.fwd i).b_meas)
    (fun i j => (hD.fwd i).σ_meas j) (fun i => (hD.fwd i).γ_meas) t
  have eB := lintegral_sampleEnergy_add (P := P) (ν := ν) (x := b)
    (z := fun i j ω s => σ i s ω j) (u := fun i ω s e => h i s ω e) hbm hσm hhm t
  have eQ := lintegral_sampleEnergy_add (P := P) (ν := ν) (x := qb)
    (z := fun i j ω s => qσ i s ω j) (u := fun i ω s e => qh i s ω e) hD.qb_meas
    hD.qσ_meas hD.qh_meas t
  have hBm := measurable_sampleEnergy_add (P := P) (ν := ν) (x := b)
    (z := fun i j ω s => σ i s ω j) (u := fun i ω s e => h i s ω e) hbm hσm hhm
  have hQm := measurable_sampleEnergy_add (P := P) (ν := ν) (x := qb)
    (z := fun i j ω s => qσ i s ω j) (u := fun i ω s e => qh i s ω e) hD.qb_meas
    hD.qσ_meas hD.qh_meas
  have hpt : ∀ s, sampleEnergy P (fun i ω s => lam * b i ω s + qb i ω s) s
        + ∑ i, sampleEnergy P (fun j ω s => lam * σ i s ω j + qσ i s ω j) s
        + markedSampleEnergy P ν (fun i ω s e => lam * h i s ω e + qh i s ω e) s
      ≤ 2 * (sampleEnergy P b s + ∑ i, sampleEnergy P (fun j ω s => σ i s ω j) s
          + markedSampleEnergy P ν (fun i ω s e => h i s ω e) s)
        + 2 * (sampleEnergy P qb s + ∑ i, sampleEnergy P (fun j ω s => qσ i s ω j) s
          + markedSampleEnergy P ν (fun i ω s e => qh i s ω e) s) := fun s => by
    have hb := sampleEnergy_mul_add_le (P := P) hl b qb s fun i =>
      ((hD.qb_meas i).comp (measurable_id.prodMk measurable_const)).aemeasurable
    have hσ := fun i => sampleEnergy_mul_add_le (P := P) hl (fun j ω s => σ i s ω j)
      (fun j ω s => qσ i s ω j) s fun j =>
        ((hD.qσ_meas i j).comp (measurable_id.prodMk measurable_const)).aemeasurable
    have hh := markedSampleEnergy_mul_add_le (P := P) (ν := ν) hl (fun i ω s e => h i s ω e)
      (fun i ω s e => qh i s ω e) s fun i =>
        (hD.qh_meas i).comp (by fun_prop : Measurable fun p : Ω × E => (p.1, s, p.2))
    refine (add_le_add (add_le_add hb (Finset.sum_le_sum fun i _ => hσ i)) hh).trans
      (le_of_eq ?_)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    ring
  calc _ = ∫⁻ s in Set.Icc (0 : ℝ) t,
        (sampleEnergy P (fun i ω s => lam * b i ω s + qb i ω s) s
          + ∑ i, sampleEnergy P (fun j ω s => lam * σ i s ω j + qσ i s ω j) s
          + markedSampleEnergy P ν (fun i ω s e => lam * h i s ω e + qh i s ω e) s) := eR.symm
    _ ≤ ∫⁻ s in Set.Icc (0 : ℝ) t,
        (2 * (sampleEnergy P b s + ∑ i, sampleEnergy P (fun j ω s => σ i s ω j) s
            + markedSampleEnergy P ν (fun i ω s e => h i s ω e) s)
          + 2 * (sampleEnergy P qb s + ∑ i, sampleEnergy P (fun j ω s => qσ i s ω j) s
            + markedSampleEnergy P ν (fun i ω s e => qh i s ω e) s)) := lintegral_mono hpt
    _ = _ := by
        rw [lintegral_add_left (hBm.const_mul 2), lintegral_const_mul _ hBm,
          lintegral_const_mul _ hQm, eB, eQ]

/-- **The expected Lipschitz bound (3.2) on `[0, t]`.** For the difference system with jointly
measurable coefficient differences and `t ∈ [0, T]`,

`𝔼 ∫_0^t (|δb|² + |δσ|²_F + ‖δh‖²) ≤ K 𝔼 ∫_0^t (|δX|² + |δY|² + |δZ|²_F + ‖δU‖²)`. -/
theorem coeffEnergy_le_at (hD : PairDiff D ℱ hℱW hℱN T lam K KT α β₁ β₂ G ξ₀ X Y Z U b σ h f g
    qb qσ qh qf qg) (hbm : ∀ i, Measurable (Function.uncurry (b i)))
    (hσm : ∀ i j, Measurable (Function.uncurry fun ω s => σ i s ω j))
    (hhm : ∀ i, Measurable fun p : Ω × ℝ × E => h i p.2.1 p.1 p.2.2) (hT : 0 ≤ T) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∑ i, Brownian.Ito.energy P t (b i) + ∑ i, ∑ j, Brownian.Ito.energy P t (fun ω s => σ i s ω j)
        + ∑ i, Poisson.Compensated.markedEnergy P ν t (fun ω s e => h i s ω e)
      ≤ ENNReal.ofReal K * (∑ i, Brownian.Ito.energy P t (fun ω s => X i s ω)
          + (∑ k, Brownian.Ito.energy P t (fun ω s => Y k s ω)
            + ∑ k, ∑ j, Brownian.Ito.energy P t (fun ω s => Z k s ω j)
            + ∑ k, Poisson.Compensated.markedEnergy P ν t (fun ω s e => U k s ω e))) := by
  have hXm : ∀ i, Measurable (Function.uncurry fun ω s => X i s ω) := fun i =>
    ((hD.fwd i).linearBSDEJ hT).measurable_uncurry.comp measurable_swap
  have hYm : ∀ k, Measurable (Function.uncurry fun ω s => Y k s ω) := fun k =>
    (hD.bwd k).measurable_uncurry.comp measurable_swap
  have eL := lintegral_sampleEnergy_add (P := P) (ν := ν) (x := b)
    (z := fun i j ω s => σ i s ω j) (u := fun i ω s e => h i s ω e) hbm hσm hhm t
  have eX := lintegral_sampleEnergy (P := P) hXm t
  have eJ := lintegral_sampleEnergy_add (P := P) (ν := ν) (x := fun k ω s => Y k s ω)
    (z := fun k j ω s => Z k s ω j) (u := fun k ω s e => U k s ω e) hYm
    (fun k j => (hD.bwd k).Z_meas j) (fun k => (hD.bwd k).U_meas) t
  set FX : ℝ → ℝ≥0∞ := sampleEnergy P (fun i ω s => X i s ω) with hFX
  set FJ : ℝ → ℝ≥0∞ := fun s => sampleEnergy P (fun k ω s => Y k s ω) s
    + ∑ k, sampleEnergy P (fun j ω s => Z k s ω j) s
    + markedSampleEnergy P ν (fun k ω s e => U k s ω e) s with hFJ
  have hFXm : Measurable FX := measurable_sampleEnergy hXm
  have hFJm : Measurable FJ := measurable_sampleEnergy_add (x := fun k ω s => Y k s ω)
    (z := fun k j ω s => Z k s ω j) (u := fun k ω s e => U k s ω e) hYm
    (fun k j => (hD.bwd k).Z_meas j) fun k => (hD.bwd k).U_meas
  have hrate : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)),
      sampleEnergy P b s + ∑ i, sampleEnergy P (fun j ω s => σ i s ω j) s
          + markedSampleEnergy P ν (fun i ω s e => h i s ω e) s
        ≤ ENNReal.ofReal K * (FX s + FJ s) :=
    (ae_restrict_of_ae_restrict_of_subset (Set.Icc_subset_Icc le_rfl ht.2) hD.ae_lip).mono
      fun s hs => le_self_add.trans hs
  calc _ = ∫⁻ s in Set.Icc (0 : ℝ) t, (sampleEnergy P b s
        + ∑ i, sampleEnergy P (fun j ω s => σ i s ω j) s
        + markedSampleEnergy P ν (fun i ω s e => h i s ω e) s) := eL.symm
    _ ≤ ∫⁻ s in Set.Icc (0 : ℝ) t, ENNReal.ofReal K * (FX s + FJ s) := lintegral_mono_ae hrate
    _ = _ := by
        rw [lintegral_const_mul (ENNReal.ofReal K) (f := fun s => FX s + FJ s)
          (hFXm.add hFJm), lintegral_add_left hFXm, eX, eJ]

/-- **The energy of the forward difference below the integrated running supremum.** For the
difference system, `𝔼 ∫_0^t |δX_s|² ds ≤ ∫_0^t 𝔼 sup_{r ≤ s} |δX_r|² ds`. -/
theorem energy_le_lintegral_biSup (hD : PairDiff D ℱ hℱW hℱN T lam K KT α β₁ β₂ G ξ₀ X Y Z U
    b σ h f g qb qσ qh qf qg) (hT : 0 ≤ T) (t : ℝ) :
    ∑ i, Brownian.Ito.energy P t (fun ω s => X i s ω)
      ≤ ∫⁻ s in Set.Icc (0 : ℝ) t,
        ∫⁻ ω, (⨆ r ∈ Set.Icc (0 : ℝ) s, esq (fun i => X i r ω)) ∂P := by
  have hXm : ∀ i, Measurable (Function.uncurry fun ω s => X i s ω) := fun i =>
    ((hD.fwd i).linearBSDEJ hT).measurable_uncurry.comp measurable_swap
  rw [← lintegral_sampleEnergy (P := P) hXm t]
  refine setLIntegral_mono' measurableSet_Icc fun s hs => ?_
  refine (sum_lintegral_le _ _).trans (lintegral_mono fun ω => ?_)
  exact le_iSup₂ (f := fun r (_ : r ∈ Set.Icc (0 : ℝ) s) => esq (fun i => X i r ω)) s
    ⟨hs.1, le_rfl⟩

end PairDiff

end Dissertation.WellPosedness.Stability
