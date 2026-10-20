/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.Law.P2Measurable
import MVFBSDEJ.WellPosedness.System.HilbertW2Space
import MVFBSDEJ.WellPosedness.System.TupleLaw
import MVFBSDEJ.WellPosedness.System.ULiftMeasurable
import LevyStochCalc.Analysis.CadlagJumps
import LevyStochCalc.Brownian.PredictableIntegrand
import LevyStochCalc.Ito.LeftLimIntegrandRegularity
import LevyStochCalc.Poisson.CompensatedIntegrandComplete
import LevyStochCalc.Probability.MarkedPredictable

/-!
# The law flow of a tuple and its predictable counterpart

For càdlàg adapted `X, Y` and predictable `Z, U` with
`𝔼 ∫_0^T (|X_t|² + |Y_t|² + |Z_t|²_F + ∫_E |U_t(e)|² ν(de)) dt < ∞`, the well-posedness paper's
Lemma A.1 asserts: the maps `t ↦ Law(Θ_t)` and `t ↦ Law(Θ⁻_t)`, `Θ = (X, Y, Z, U)` and
`Θ⁻ = (X₋, Y₋, Z, U)` with `X₋, Y₋` the left limits, defined for almost every `t`, have Borel
representatives `μ, μ⁻ : [0, T] → (P₂(H), W₂)`, unique up to Lebesgue-null sets, with `μ⁻_t = μ_t`
for almost every `t`; and coefficient evaluations along them are invariant, up to `dt ⊗ dP`-null
sets, under the choice of the predictable versions of `(Z, U)` and of the Borel representatives.

The representatives here are `μ_s = lawP2 P Θ_s` and `μ⁻_s = lawP2 P Θ⁻_s` at every time: the law
when the tuple is square integrable, and the Dirac mass at the origin otherwise.

* **Borel flow.** A predictable process is jointly measurable, and so is a càdlàg adapted one and
  its left limits, the limits along the dyadic grid below each time. So `(ω, s) ↦ Θ_s(ω)` and
  `(ω, s) ↦ Θ⁻_s(ω)` are jointly measurable, the law flows are measurable for the evaluation
  σ-algebra on `P₂(H)` (`MVFBSDEJ.Law.measurable_lawP2_flow`), hence Borel for the Hilbert-norm
  `W₂` (`measurable_toP2WH`).
* **Representatives.** By Tonelli's theorem the tuple is square integrable at almost every time of
  `[0, T]`, where `μ_s` is its law.
* **`μ⁻ = μ`.** A càdlàg path meets its left limits off a countable set of times, so for every
  `ω` the tuples `Θ_s(ω)` and `Θ⁻_s(ω)` agree for almost every `s`; by Fubini, for almost every
  `s` they agree almost surely, and so do their laws.
* **Invariance.** Versions `Z = Z'` `dP ⊗ dt`-a.e. and `U = U'` `dP ⊗ dt ⊗ ν`-a.e. give, by
  Fubini, `U_t(ω, ·) = U'_t(ω, ·)` in `L²(ν)` for `dP ⊗ dt`-a.e. `(ω, t)`, so the two tuples agree
  `dP ⊗ dt`-a.e. and, for almost every `t`, almost surely; representatives of their law flows
  then agree for almost every `t`, and every evaluation `ψ(t, Θ_t(ω), μ_t)` agrees
  `dP ⊗ dt`-a.e. This holds for any processes `X, Y`, in particular for the left limits, so it
  covers the evaluations `ψ(t, Θ⁻_t(ω), μ⁻_t)` as well.

## Main definitions

* `leftLimProc` — the left-limit process `s ↦ X_{s−}`.
* `CadlagPredTuple` — the hypotheses of Lemma A.1.

## Main statements

* `measurable_uncurry_leftLimProc`, `measurable_uncurry_tupleAt` — joint measurability.
* `ae_ae_tupleAt_leftLimProc_eq`, `ae_lawP2_tupleAt_leftLimProc_eq` — `Θ⁻ = Θ` and `μ⁻ = μ`
  at almost every time.
* `uLift_congr_ae`, `ae_tupleAt_eq_of_ae_eq`, `ae_eval_eq_of_ae_eq` — invariance under the
  choice of versions of `(Z, U)` and of representatives of the law flow.
* `CadlagPredTuple.measurable_lawFlow`, `CadlagPredTuple.measurable_lawFlow_leftLim` — the Borel
  law flows.
* `CadlagPredTuple.ae_memLp_law_eq`, `CadlagPredTuple.ae_memLp_law_eq_leftLim` — they represent
  `t ↦ Law(Θ_t)` and `t ↦ Law(Θ⁻_t)`.
* `CadlagPredTuple.ae_lawFlow_leftLim_eq` — `μ⁻_t = μ_t` for almost every `t`.
-/

open MeasureTheory Filter Topology MVFBSDEJ.Law
open scoped ENNReal

namespace MVFBSDEJ.WellPosedness.System

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E] {ν : Measure E}
  {n m d : ℕ}

/-! ### Left limits and joint measurability -/

section Measurability

/-- The left-limit process `s ↦ X_{s−}(ω) = lim_{r ↑ s} X_r(ω)` of a family of real processes. -/
noncomputable def leftLimProc {ι : Type*} (X : ι → ℝ → Ω → ℝ) : ι → ℝ → Ω → ℝ :=
  fun i s ω => Function.leftLim (fun r => X i r ω) s

/-- **The left limits of a jointly measurable process with left limits are jointly
measurable.** -/
theorem measurable_uncurry_leftLimProc {X : Fin n → ℝ → Ω → ℝ}
    (hX : ∀ i, Measurable (Function.uncurry fun ω s => X i s ω))
    (hleft : ∀ i ω t, ∃ L : ℝ, Tendsto (fun s => X i s ω) (𝓝[<] t) (𝓝 L)) (i : Fin n) :
    Measurable (Function.uncurry fun ω s => leftLimProc X i s ω) := by
  set Xp : ℝ → Ω → Fin n → ℝ := fun s ω j => X j s ω with hXp_def
  have hXp : Measurable fun q : ℝ × Ω => Xp q.1 q.2 :=
    measurable_pi_lambda _ fun j => (hX j).comp measurable_swap
  have h := LevyStochCalc.Ito.JumpSplitting.measurable_uncurry_leftLimPathAt hXp
    (fun ω t j => hleft j ω t)
  have heq : (fun q : ℝ × Ω => LevyStochCalc.Ito.JumpSplitting.leftLimPathAt Xp q.1 q.2 i)
      = fun q => leftLimProc X i q.1 q.2 := by
    funext q
    choose L hL using fun j => hleft j q.2 q.1
    have hvec : Tendsto (fun r => Xp r q.2) (𝓝[<] q.1) (𝓝 L) := tendsto_pi_nhds.mpr hL
    rw [LevyStochCalc.Ito.JumpSplitting.leftLimPathAt, leftLim_eq_of_tendsto hvec, leftLimProc,
      leftLim_eq_of_tendsto (hL i)]
  have hi : Measurable fun q : ℝ × Ω => leftLimProc X i q.1 q.2 := by
    rw [← heq]
    exact (measurable_pi_apply i).comp h
  exact hi.comp measurable_swap

variable [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]

/-- **The tuple of jointly measurable coordinate processes is jointly measurable** in the sample
point and the time. -/
theorem measurable_uncurry_tupleAt {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ}
    {Z : Fin m → ℝ → Ω → Fin d → ℝ} {U : Fin m → ℝ → Ω → E → ℝ}
    (hX : ∀ i, Measurable (Function.uncurry fun ω s => X i s ω))
    (hY : ∀ k, Measurable (Function.uncurry fun ω s => Y k s ω))
    (hZ : ∀ k j, Measurable (Function.uncurry fun ω s => Z k s ω j))
    (hU : ∀ k, Measurable fun p : Ω × ℝ × E => U k p.2.1 p.1 p.2.2) :
    Measurable (Function.uncurry fun ω s => tupleAt ν X Y Z U s ω) :=
  ((WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.mpr hX)).prodMk
    (((WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.mpr hY)).prodMk
      (((WithLp.measurable_toLp 2 _).comp
        (measurable_pi_iff.mpr fun q : Fin m × Fin d => hZ q.1 q.2)).prodMk
        (measurable_uLift (u := fun p : Ω × ℝ => fun e k => U k p.2 p.1 e)
          (measurable_pi_iff.mpr fun k =>
            (hU k).comp MeasurableEquiv.prodAssoc.measurable))))

end Measurability

/-! ### The left-limit tuple -/

section LeftLimit

variable [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {P : Measure Ω}
  [IsProbabilityMeasure P] {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ}
  {Z : Fin m → ℝ → Ω → Fin d → ℝ} {U : Fin m → ℝ → Ω → E → ℝ}

/-- **The tuple meets its left-limit tuple at almost every time, almost surely**: for jointly
measurable càdlàg `X, Y`, for almost every `s` the tuples `Θ⁻_s = (X_{s−}, Y_{s−}, Z_s, U_s)` and
`Θ_s = (X_s, Y_s, Z_s, U_s)` agree almost surely. -/
theorem ae_ae_tupleAt_leftLimProc_eq
    (hX : ∀ i, Measurable (Function.uncurry fun ω s => X i s ω))
    (hY : ∀ k, Measurable (Function.uncurry fun ω s => Y k s ω))
    (hXr : ∀ i ω t, Tendsto (fun s => X i s ω) (𝓝[>] t) (𝓝 (X i t ω)))
    (hXl : ∀ i ω t, ∃ L : ℝ, Tendsto (fun s => X i s ω) (𝓝[<] t) (𝓝 L))
    (hYr : ∀ k ω t, Tendsto (fun s => Y k s ω) (𝓝[>] t) (𝓝 (Y k t ω)))
    (hYl : ∀ k ω t, ∃ L : ℝ, Tendsto (fun s => Y k s ω) (𝓝[<] t) (𝓝 L)) :
    ∀ᵐ s, tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s =ᵐ[P] tupleAt ν X Y Z U s := by
  set p : Ω → ℝ → Prop := fun ω s =>
    (∀ i, leftLimProc X i s ω = X i s ω) ∧ ∀ k, leftLimProc Y k s ω = Y k s ω with hp_def
  have hpath : ∀ ω, ∀ᵐ s, p ω s := fun ω => by
    have hXa : ∀ i, ∀ᵐ s, X i s ω = leftLimProc X i s ω := fun i =>
      LevyStochCalc.Analysis.ae_eq_leftLim_of_cadlag (hXr i ω) (hXl i ω)
    have hYa : ∀ k, ∀ᵐ s, Y k s ω = leftLimProc Y k s ω := fun k =>
      LevyStochCalc.Analysis.ae_eq_leftLim_of_cadlag (hYr k ω) (hYl k ω)
    filter_upwards [ae_all_iff.mpr hXa, ae_all_iff.mpr hYa] with s hs1 hs2
    exact ⟨fun i => (hs1 i).symm, fun k => (hs2 k).symm⟩
  have hmeas : MeasurableSet {q : Ω × ℝ | p q.1 q.2} := by
    have h1 : MeasurableSet {q : Ω × ℝ | ∀ i, leftLimProc X i q.2 q.1 = X i q.2 q.1} := by
      simp only [Set.setOf_forall]
      exact MeasurableSet.iInter fun i =>
        measurableSet_eq_fun (measurable_uncurry_leftLimProc hX hXl i) (hX i)
    have h2 : MeasurableSet {q : Ω × ℝ | ∀ k, leftLimProc Y k q.2 q.1 = Y k q.2 q.1} := by
      simp only [Set.setOf_forall]
      exact MeasurableSet.iInter fun k =>
        measurableSet_eq_fun (measurable_uncurry_leftLimProc hY hYl k) (hY k)
    exact h1.inter h2
  have hswap := (Measure.ae_ae_comm (μ := P) (ν := (volume : Measure ℝ)) hmeas).mp
    (ae_of_all _ hpath)
  filter_upwards [hswap] with s hs
  filter_upwards [hs] with ω hω
  simp only [tupleAt, hω.1, hω.2]

/-- **`μ⁻ = μ` at almost every time**: for jointly measurable càdlàg `X, Y`, the laws of the
left-limit tuple and of the tuple agree at almost every time. -/
theorem ae_lawP2_tupleAt_leftLimProc_eq
    (hX : ∀ i, Measurable (Function.uncurry fun ω s => X i s ω))
    (hY : ∀ k, Measurable (Function.uncurry fun ω s => Y k s ω))
    (hXr : ∀ i ω t, Tendsto (fun s => X i s ω) (𝓝[>] t) (𝓝 (X i t ω)))
    (hXl : ∀ i ω t, ∃ L : ℝ, Tendsto (fun s => X i s ω) (𝓝[<] t) (𝓝 L))
    (hYr : ∀ k ω t, Tendsto (fun s => Y k s ω) (𝓝[>] t) (𝓝 (Y k t ω)))
    (hYl : ∀ k ω t, ∃ L : ℝ, Tendsto (fun s => Y k s ω) (𝓝[<] t) (𝓝 L)) :
    ∀ᵐ s, lawP2 P (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s)
      = lawP2 P (tupleAt ν X Y Z U s) :=
  (ae_ae_tupleAt_leftLimProc_eq hX hY hXr hXl hYr hYl).mono fun _ hs => lawP2_congr hs

end LeftLimit

/-! ### Invariance under the choice of versions and representatives -/

section Invariance

/-- The `L²(ν)` class of a mark-indexed vector depends only on its `ν`-almost-everywhere class. -/
theorem uLift_congr_ae {ι : Type*} [Fintype ι] {u u' : E → ι → ℝ} (h : u =ᵐ[ν] u') :
    uLift ν u = uLift ν u' := by
  have h' : (fun e => (WithLp.toLp 2 (u e) : EuclideanSpace ℝ ι))
      =ᵐ[ν] fun e => (WithLp.toLp 2 (u' e) : EuclideanSpace ℝ ι) :=
    h.mono fun e he => by simp only [he]
  by_cases hm : MemLp (fun e => (WithLp.toLp 2 (u e) : EuclideanSpace ℝ ι)) 2 ν
  · have hm' := (memLp_congr_ae h').mp hm
    rw [uLift_of_memLp hm, uLift_of_memLp hm']
    exact MemLp.toLp_congr hm hm' h'
  · have hm' : ¬ MemLp (fun e => (WithLp.toLp 2 (u' e) : EuclideanSpace ℝ ι)) 2 ν :=
      fun h'' => hm ((memLp_congr_ae h').mpr h'')
    unfold uLift
    rw [dif_neg hm, dif_neg hm']

omit [MeasurableSpace E] in
/-- A property of the second coordinate holding almost everywhere holds almost everywhere on a
product. -/
theorem ae_prod_of_ae_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    {ν' : Measure β} [SFinite ν'] {q : β → Prop} (h : ∀ᵐ y ∂ν', q y) :
    ∀ᵐ p ∂(μ.prod ν'), q p.2 := by
  rw [ae_iff] at h ⊢
  have hset : {p : α × β | ¬ q p.2} = Set.univ ×ˢ {y | ¬ q y} := by
    ext p
    simp
  rw [hset, Measure.prod_prod, h, mul_zero]

variable [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {P : Measure Ω}
  [IsProbabilityMeasure P] {T : ℝ} {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ}
  {Z Z' : Fin m → ℝ → Ω → Fin d → ℝ} {U U' : Fin m → ℝ → Ω → E → ℝ}

/-- **Two versions of `(Z, U)` give the same tuple `dP ⊗ dt`-almost everywhere**: if `Z = Z'`
`dP ⊗ dt`-a.e. on `Ω × [0, T]` and `U = U'` `dP ⊗ dt ⊗ ν`-a.e. on `Ω × [0, T] × E`, coordinatewise,
then `Θ_t(ω) = Θ'_t(ω)` for `dP ⊗ dt`-a.e. `(ω, t)`, the jump channels agreeing in `L²(ν)`. -/
theorem ae_tupleAt_eq_of_ae_eq
    (hZ : ∀ k j, ∀ᵐ p ∂(LevyStochCalc.Brownian.Ito.energyMeasure P T),
      Z k p.2 p.1 j = Z' k p.2 p.1 j)
    (hU : ∀ k, ∀ᵐ q ∂(LevyStochCalc.Poisson.Compensated.markedEnergyMeasure P ν T),
      U k q.2.1 q.1 q.2.2 = U' k q.2.1 q.1 q.2.2) :
    ∀ᵐ p ∂(LevyStochCalc.Brownian.Ito.energyMeasure P T),
      tupleAt ν X Y Z U p.2 p.1 = tupleAt ν X Y Z' U' p.2 p.1 := by
  have hUae : ∀ k, ∀ᵐ p ∂(LevyStochCalc.Brownian.Ito.energyMeasure P T),
      ∀ᵐ e ∂ν, U k p.2 p.1 e = U' k p.2 p.1 e := by
    intro k
    have h := hU k
    rw [LevyStochCalc.Poisson.Compensated.markedEnergyMeasure, ← Measure.prodAssoc_prod,
      MeasurableEquiv.prodAssoc.measurableEmbedding.ae_map_iff] at h
    exact Measure.ae_ae_of_ae_prod h
  filter_upwards [ae_all_iff.mpr fun k => ae_all_iff.mpr (hZ k), ae_all_iff.mpr hUae]
    with p hpZ hpU
  have hu : (fun e k => U k p.2 p.1 e) =ᵐ[ν] fun e k => U' k p.2 p.1 e := by
    filter_upwards [ae_all_iff.mpr hpU] with e he
    funext k
    exact he k
  simp only [tupleAt, uLift_congr_ae hu, hpZ]

/-- **Two versions of `(Z, U)` give the same tuple, almost surely, at almost every time** of
`[0, T]`. -/
theorem ae_ae_tupleAt_eq_of_ae_eq
    (hZ : ∀ k j, ∀ᵐ p ∂(LevyStochCalc.Brownian.Ito.energyMeasure P T),
      Z k p.2 p.1 j = Z' k p.2 p.1 j)
    (hU : ∀ k, ∀ᵐ q ∂(LevyStochCalc.Poisson.Compensated.markedEnergyMeasure P ν T),
      U k q.2.1 q.1 q.2.2 = U' k q.2.1 q.1 q.2.2) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      tupleAt ν X Y Z U s =ᵐ[P] tupleAt ν X Y Z' U' s := by
  have h := ae_tupleAt_eq_of_ae_eq (X := X) (Y := Y) hZ hU
  rw [LevyStochCalc.Brownian.Ito.energyMeasure, ← Measure.prod_swap] at h
  exact Measure.ae_ae_of_ae_prod
    ((MeasurableEquiv.prodComm (α := ℝ) (β := Ω)).measurableEmbedding.ae_map_iff.mp h)

/-- **Coefficient evaluations are invariant under the choice of versions and representatives.**
Let `Z = Z'` `dP ⊗ dt`-a.e. and `U = U'` `dP ⊗ dt ⊗ ν`-a.e., coordinatewise, and let `ρ, ρ'` be
representatives of the law flows of `Θ = (X, Y, Z, U)` and `Θ' = (X, Y, Z', U')`: maps into
`P₂(H)` whose underlying measures are the laws of `Θ_t` and `Θ'_t` for almost every `t ∈ [0, T]`.
Then for every function `ψ` of the time, the tuple and the law, `ψ(t, Θ_t(ω), ρ_t)` and
`ψ(t, Θ'_t(ω), ρ'_t)` agree for `dP ⊗ dt`-a.e. `(ω, t)`. -/
theorem ae_eval_eq_of_ae_eq {W : Type*} (ψ : ℝ → TupleH ν n m d → P2 (TupleH ν n m d) → W)
    {ρ ρ' : ℝ → P2 (TupleH ν n m d)}
    (hZ : ∀ k j, ∀ᵐ p ∂(LevyStochCalc.Brownian.Ito.energyMeasure P T),
      Z k p.2 p.1 j = Z' k p.2 p.1 j)
    (hU : ∀ k, ∀ᵐ q ∂(LevyStochCalc.Poisson.Compensated.markedEnergyMeasure P ν T),
      U k q.2.1 q.1 q.2.2 = U' k q.2.1 q.1 q.2.2)
    (hρ : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      (ρ s).law = P.map (tupleAt ν X Y Z U s))
    (hρ' : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      (ρ' s).law = P.map (tupleAt ν X Y Z' U' s)) :
    ∀ᵐ p ∂(LevyStochCalc.Brownian.Ito.energyMeasure P T),
      ψ p.2 (tupleAt ν X Y Z U p.2 p.1) (ρ p.2) = ψ p.2 (tupleAt ν X Y Z' U' p.2 p.1) (ρ' p.2) := by
  have hρρ' : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ρ s = ρ' s := by
    filter_upwards [hρ, hρ', ae_ae_tupleAt_eq_of_ae_eq (X := X) (Y := Y) hZ hU] with s h h' hs
    exact P2.ext_law (by rw [h, h', Measure.map_congr hs])
  have hprod : ∀ᵐ p ∂(LevyStochCalc.Brownian.Ito.energyMeasure P T), ρ p.2 = ρ' p.2 := by
    rw [LevyStochCalc.Brownian.Ito.energyMeasure]
    exact ae_prod_of_ae_snd hρρ'
  filter_upwards [ae_tupleAt_eq_of_ae_eq (X := X) (Y := Y) hZ hU, hprod] with p h1 h2
  rw [h1, h2]

end Invariance

/-! ### Lemma A.1 -/

section LemmaA1

/-- The hypotheses of Lemma A.1 of the well-posedness paper: `X, Y` càdlàg and adapted, `Z, U`
predictable, and `𝔼 ∫_0^T (|X_t|² + |Y_t|² + |Z_t|²_F + ∫_E |U_t(e)|² ν(de)) dt < ∞`,
coordinatewise. -/
structure CadlagPredTuple (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (P : Measure Ω)
    (ν : Measure E) (T : ℝ) (X : Fin n → ℝ → Ω → ℝ) (Y : Fin m → ℝ → Ω → ℝ)
    (Z : Fin m → ℝ → Ω → Fin d → ℝ) (U : Fin m → ℝ → Ω → E → ℝ) : Prop where
  /-- Each coordinate of `X` is adapted. -/
  X_adapted : ∀ i, Adapted ℱ (X i)
  /-- Every path of each coordinate of `X` is right-continuous. -/
  X_rightCont : ∀ i ω t, Tendsto (fun s => X i s ω) (𝓝[>] t) (𝓝 (X i t ω))
  /-- Every path of each coordinate of `X` has left limits. -/
  X_leftLim : ∀ i ω t, ∃ L : ℝ, Tendsto (fun s => X i s ω) (𝓝[<] t) (𝓝 L)
  /-- Each coordinate of `Y` is adapted. -/
  Y_adapted : ∀ k, Adapted ℱ (Y k)
  /-- Every path of each coordinate of `Y` is right-continuous. -/
  Y_rightCont : ∀ k ω t, Tendsto (fun s => Y k s ω) (𝓝[>] t) (𝓝 (Y k t ω))
  /-- Every path of each coordinate of `Y` has left limits. -/
  Y_leftLim : ∀ k ω t, ∃ L : ℝ, Tendsto (fun s => Y k s ω) (𝓝[<] t) (𝓝 L)
  /-- Each coordinate of `Z` is predictable. -/
  Z_pred : ∀ k j, LevyStochCalc.Probability.Predictable ℱ fun ω s => Z k s ω j
  /-- Each coordinate of `U` is predictable as a marked process. -/
  U_pred : ∀ k, LevyStochCalc.Probability.MarkedPredictable ℱ ν fun ω s e => U k s ω e
  /-- Each coordinate of `X` has finite energy on the horizon. -/
  X_sq : ∀ i, LevyStochCalc.Brownian.Ito.energy P T (fun ω s => X i s ω) ≠ ⊤
  /-- Each coordinate of `Y` has finite energy on the horizon. -/
  Y_sq : ∀ k, LevyStochCalc.Brownian.Ito.energy P T (fun ω s => Y k s ω) ≠ ⊤
  /-- Each coordinate of `Z` has finite energy on the horizon. -/
  Z_sq : ∀ k j, LevyStochCalc.Brownian.Ito.energy P T (fun ω s => Z k s ω j) ≠ ⊤
  /-- Each coordinate of `U` has finite marked energy on the horizon. -/
  U_sq : ∀ k,
    LevyStochCalc.Poisson.Compensated.markedEnergy P ν T (fun ω s e => U k s ω e) ≠ ⊤

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {P : Measure Ω} {T : ℝ}
  {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ} {Z : Fin m → ℝ → Ω → Fin d → ℝ}
  {U : Fin m → ℝ → Ω → E → ℝ}

namespace CadlagPredTuple

variable (hΘ : CadlagPredTuple ℱ P ν T X Y Z U)
include hΘ

/-- Each coordinate of `X` is jointly measurable. -/
theorem measurable_X (i : Fin n) : Measurable (Function.uncurry fun ω s => X i s ω) :=
  (LevyStochCalc.Probability.measurable_uncurry_of_rightContinuous
    (hΘ.X_adapted i) (hΘ.X_rightCont i)).comp
    measurable_swap

/-- Each coordinate of `Y` is jointly measurable. -/
theorem measurable_Y (k : Fin m) : Measurable (Function.uncurry fun ω s => Y k s ω) :=
  (LevyStochCalc.Probability.measurable_uncurry_of_rightContinuous
    (hΘ.Y_adapted k) (hΘ.Y_rightCont k)).comp
    measurable_swap

/-- Each coordinate of `Z` is jointly measurable. -/
theorem measurable_Z (k : Fin m) (j : Fin d) :
    Measurable (Function.uncurry fun ω s => Z k s ω j) :=
  LevyStochCalc.Brownian.Ito.measurable_uncurry_of_predictable (hΘ.Z_pred k j)

/-- Each coordinate of `U` is jointly measurable in the sample point, the time and the mark. -/
theorem measurable_U (k : Fin m) : Measurable fun p : Ω × ℝ × E => U k p.2.1 p.1 p.2.2 :=
  (hΘ.U_pred k).mono (LevyStochCalc.Probability.markedPredictableSigma_le ℱ ν) le_rfl

variable [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] [IsProbabilityMeasure P]

/-- **The law flow is Borel**: `s ↦ Law(Θ_s)`, the exact law at every time, is Borel measurable
into `P₂(H)` with the 2-Wasserstein distance of the Hilbert norm. -/
theorem measurable_lawFlow : Measurable fun s => (lawP2 P (tupleAt ν X Y Z U s)).toP2WH :=
  (measurable_lawP2_flow (Θ := fun ω s => tupleAt ν X Y Z U s ω)
    (measurable_uncurry_tupleAt hΘ.measurable_X hΘ.measurable_Y hΘ.measurable_Z
      hΘ.measurable_U)).toP2WH

/-- **The predictable law flow is Borel**: `s ↦ Law(Θ⁻_s)`, `Θ⁻_s = (X_{s−}, Y_{s−}, Z_s, U_s)`,
is Borel measurable into `P₂(H)` with the 2-Wasserstein distance of the Hilbert norm. -/
theorem measurable_lawFlow_leftLim :
    Measurable fun s =>
      (lawP2 P (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s)).toP2WH :=
  (measurable_lawP2_flow (Θ := fun ω s => tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s ω)
    (measurable_uncurry_tupleAt (measurable_uncurry_leftLimProc hΘ.measurable_X hΘ.X_leftLim)
      (measurable_uncurry_leftLimProc hΘ.measurable_Y hΘ.Y_leftLim) hΘ.measurable_Z
      hΘ.measurable_U)).toP2WH

/-- **The law flow represents `t ↦ Law(Θ_t)`**: at almost every time of `[0, T]` the tuple is
square integrable and `μ_t = lawP2 P Θ_t` is its law. -/
theorem ae_memLp_law_eq :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), MemLp (tupleAt ν X Y Z U s) 2 P
      ∧ (lawP2 P (tupleAt ν X Y Z U s)).law = P.map (tupleAt ν X Y Z U s) := by
  have hΘm := measurable_uncurry_tupleAt (ν := ν) hΘ.measurable_X hΘ.measurable_Y
    hΘ.measurable_Z hΘ.measurable_U
  have h := ae_memLp_tupleAt (P := P) (T := T)
    (fun s _ => (hΘm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
    hΘ.measurable_X hΘ.measurable_Y hΘ.measurable_Z hΘ.measurable_U hΘ.X_sq hΘ.Y_sq hΘ.Z_sq
    hΘ.U_sq
  exact h.mono fun s hs => ⟨hs, lawP2_law hs⟩

/-- **`μ⁻_t = μ_t` for almost every `t`.** -/
theorem ae_lawFlow_leftLim_eq :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      lawP2 P (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s)
        = lawP2 P (tupleAt ν X Y Z U s) :=
  ae_restrict_of_ae (ae_lawP2_tupleAt_leftLimProc_eq hΘ.measurable_X hΘ.measurable_Y
    hΘ.X_rightCont hΘ.X_leftLim hΘ.Y_rightCont hΘ.Y_leftLim)

/-- **The predictable law flow represents `t ↦ Law(Θ⁻_t)`**: at almost every time of `[0, T]`
the left-limit tuple is square integrable and `μ⁻_t = lawP2 P Θ⁻_t` is its law. -/
theorem ae_memLp_law_eq_leftLim :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      MemLp (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s) 2 P
      ∧ (lawP2 P (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s)).law
        = P.map (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s) := by
  filter_upwards [hΘ.ae_memLp_law_eq, ae_restrict_of_ae (ae_ae_tupleAt_leftLimProc_eq (Z := Z)
    (U := U) (ν := ν) (P := P) hΘ.measurable_X hΘ.measurable_Y hΘ.X_rightCont hΘ.X_leftLim
    hΘ.Y_rightCont hΘ.Y_leftLim)] with s hs heq
  have hm : MemLp (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s) 2 P :=
    (memLp_congr_ae heq).mpr hs.1
  exact ⟨hm, lawP2_law hm⟩

end CadlagPredTuple

end LemmaA1

end MVFBSDEJ.WellPosedness.System
