/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Mathlib.Probability.Kernel.Representation
import MVFBSDEJ.Law.LawP2
import MVFBSDEJ.WellPosedness.System.Tuple
import MVFBSDEJ.WellPosedness.Remarks.UniformVariable

/-!
# Couplings realised by measurable pairs

Remark 2.9 of the well-posedness paper: for `t > 0` every coupling of two laws in `P₂(H)` is the
joint law of a pair of `ℱ_t`-measurable inputs. A complete separable normed group `F` with its
Borel σ-algebra is a standard Borel space, and so is `F × F`; by the kernel representation lemma
(`MeasureTheory.Measure.exists_measurable_map_eq`, Kallenberg's Lemma 4.22) every probability
measure `γ` on `F × F` is the image of the Lebesgue measure on `[0, 1]` under a measurable
`f : [0, 1] → F × F`. Composing `f` with a uniform variable `V` measurable for a sub-σ-algebra
`m₀` gives the pair `(Θ, Θ') = f ∘ V`, `m₀`-measurable with joint law `γ`. When `γ` couples two
laws `μ, μ'` of finite second moment, `Θ` and `Θ'` have the laws `μ, μ'` and are square
integrable.

The tuple space `H = ℝⁿ × ℝᵐ × ℝ^{m×d} × L²(ν; ℝᵐ)` is a separable Banach space when `ν` is
σ-finite on a countably generated mark space, the standing assumption that makes `L²(ν; ℝᵐ)`
separable; the realisation applies to it, and to `ℝⁿ` for the terminal conditions.

## Main statements

* `MVFBSDEJ.Law.memLp_id_of_secondMoment_ne_top` — the identity is square integrable against
  a law of finite second moment.
* `MVFBSDEJ.Law.exists_pair_map_eq_of_uniform` — a uniform variable measurable for `m₀`
  realises every coupling of two laws of finite second moment by an `m₀`-measurable
  square-integrable pair.
* `SupportsUniform.exists_pair_map_eq` — for `t > 0`, over a filtration supporting a uniform
  variable at positive times.
* `exists_pair_of_coupling` — every coupling of two laws in `P₂(H)` is the joint law of a pair of
  strongly `ℱ_t`-measurable square-integrable tuples, `t > 0`, over a filtration to which a
  Brownian motion is adapted.
-/

open MeasureTheory ProbabilityTheory unitInterval
open scoped ENNReal

namespace MVFBSDEJ.Law

variable {F : Type*} [NormedAddCommGroup F] [MeasurableSpace F] [BorelSpace F]
  [SecondCountableTopology F]

/-- **The identity is square integrable against a law of finite second moment.** -/
theorem memLp_id_of_secondMoment_ne_top {μ : Measure F} (h : secondMoment μ ≠ ⊤) :
    MemLp id 2 μ := by
  refine (memLp_two_iff_integrable_sq_norm aestronglyMeasurable_id).mpr ⟨by fun_prop, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => by positivity)]
  exact lt_of_le_of_ne le_top h

variable [CompleteSpace F] {Ω : Type*} {m₀ mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- **A uniform variable realises every coupling by a measurable square-integrable pair**: if `V`
is measurable for a sub-σ-algebra `m₀` and uniform on `[0, 1]`, then every coupling `γ` of two
laws `μ, μ'` of finite second moment on a complete separable normed group `F` with its Borel
σ-algebra is the joint law of a pair `(Θ, Θ')` of strongly `m₀`-measurable square-integrable
random elements of `F` with laws `μ` and `μ'`. -/
theorem exists_pair_map_eq_of_uniform (hm : m₀ ≤ mΩ) {V : Ω → I} (hV : Measurable[m₀] V)
    (hVP : P.map V = volume) {μ μ' : P2 F} {γ : Measure (F × F)}
    (hγ : IsCoupling μ.law μ'.law γ) :
    ∃ Θ Θ' : Ω → F, StronglyMeasurable[m₀] Θ ∧ StronglyMeasurable[m₀] Θ' ∧ MemLp Θ 2 P ∧
      MemLp Θ' 2 P ∧ P.map (fun ω => (Θ ω, Θ' ω)) = γ ∧ lawP2 P Θ = μ ∧ lawP2 P Θ' = μ' := by
  haveI : IsProbabilityMeasure γ := ⟨by rw [← Measure.fst_univ, hγ.1, measure_univ]⟩
  haveI : StandardBorelSpace F := inferInstance
  obtain ⟨f, hf, hfγ⟩ := Measure.exists_measurable_map_eq γ
  have hV' : Measurable V := hV.mono hm le_rfl
  have hmap : P.map (f ∘ V) = γ := by rw [← Measure.map_map hf hV', hVP, hfγ]
  have hΘ : Measurable[m₀] fun ω => (f (V ω)).1 := (measurable_fst.comp hf).comp hV
  have hΘ' : Measurable[m₀] fun ω => (f (V ω)).2 := (measurable_snd.comp hf).comp hV
  have hpair : (fun ω => ((f (V ω)).1, (f (V ω)).2)) = f ∘ V := rfl
  have hlaw : P.map (fun ω => (f (V ω)).1) = μ.law := by
    rw [← hγ.1, ← hmap, ← hpair, Measure.fst_map_prodMk (hΘ'.mono hm le_rfl)]
  have hlaw' : P.map (fun ω => (f (V ω)).2) = μ'.law := by
    rw [← hγ.2, ← hmap, ← hpair, Measure.snd_map_prodMk (hΘ.mono hm le_rfl)]
  have hL2 : MemLp (fun ω => (f (V ω)).1) 2 P := by
    have h := memLp_id_of_secondMoment_ne_top μ.secondMoment_ne_top
    rw [← hlaw] at h
    exact (memLp_map_measure_iff aestronglyMeasurable_id (hΘ.mono hm le_rfl).aemeasurable).mp h
  have hL2' : MemLp (fun ω => (f (V ω)).2) 2 P := by
    have h := memLp_id_of_secondMoment_ne_top μ'.secondMoment_ne_top
    rw [← hlaw'] at h
    exact (memLp_map_measure_iff aestronglyMeasurable_id (hΘ'.mono hm le_rfl).aemeasurable).mp h
  exact ⟨_, _, hΘ.stronglyMeasurable, hΘ'.stronglyMeasurable, hL2, hL2', by rw [hpair, hmap],
    P2.ext_law (by rw [lawP2_law hL2, hlaw]), P2.ext_law (by rw [lawP2_law hL2', hlaw'])⟩

end MVFBSDEJ.Law

namespace MVFBSDEJ.WellPosedness.System

open MVFBSDEJ.Law

section Generic

variable {F : Type*} [NormedAddCommGroup F] [MeasurableSpace F] [BorelSpace F]
  [SecondCountableTopology F] [CompleteSpace F] {Ω : Type*} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

/-- **Couplings realised at a positive time**: over a filtration supporting a uniform variable at
every positive time, for `t > 0` every coupling `γ` of two laws `μ, μ'` of finite second moment
on a complete separable normed group `F` is the joint law of a pair of strongly
`ℱ_t`-measurable square-integrable random elements of `F` with laws `μ` and `μ'`. -/
theorem SupportsUniform.exists_pair_map_eq (hU : SupportsUniform ℱ P) {t : ℝ} (ht : 0 < t)
    {μ μ' : P2 F} {γ : Measure (F × F)} (hγ : IsCoupling μ.law μ'.law γ) :
    ∃ Θ Θ' : Ω → F, StronglyMeasurable[ℱ t] Θ ∧ StronglyMeasurable[ℱ t] Θ' ∧ MemLp Θ 2 P ∧
      MemLp Θ' 2 P ∧ P.map (fun ω => (Θ ω, Θ' ω)) = γ ∧ lawP2 P Θ = μ ∧ lawP2 P Θ' = μ' :=
  let ⟨_, hV, hVP⟩ := hU t ht
  exists_pair_map_eq_of_uniform (ℱ.le t) hV hVP hγ

end Generic

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} {n m d : ℕ} [SigmaFinite ν]
  [MeasurableSpace.CountablyGenerated E] {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- **Every coupling of two laws in `P₂(H)` is the law of a pair of `ℱ_t`-measurable inputs**
(Remark 2.9): over a filtration `ℱ` to which a Brownian motion is adapted, for `t > 0` every
coupling `γ` of two laws `μ, μ'` of finite second moment on the tuple space is the joint law of a
pair `(Θ, Θ')` of strongly `ℱ_t`-measurable square-integrable tuples with `Law(Θ) = μ` and
`Law(Θ') = μ'`. -/
theorem exists_pair_of_coupling (W : LevyStochCalc.Brownian.BrownianMotion P)
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hW : ∀ s, Measurable[ℱ s] (W.W s)) {t : ℝ}
    (ht : 0 < t) {μ μ' : P2 (TupleH ν n m d)} {γ : Measure (TupleH ν n m d × TupleH ν n m d)}
    (hγ : IsCoupling μ.law μ'.law γ) :
    ∃ Θ Θ' : Ω → TupleH ν n m d, StronglyMeasurable[ℱ t] Θ ∧ StronglyMeasurable[ℱ t] Θ' ∧
      MemLp Θ 2 P ∧ MemLp Θ' 2 P ∧ P.map (fun ω => (Θ ω, Θ' ω)) = γ ∧ lawP2 P Θ = μ ∧
      lawP2 P Θ' = μ' :=
  (supportsUniform_of_brownian W hW).exists_pair_map_eq ht hγ

end MVFBSDEJ.WellPosedness.System
