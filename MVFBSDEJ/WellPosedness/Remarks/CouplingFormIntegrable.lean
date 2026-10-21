/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Remarks.CouplingForm
import MVFBSDEJ.WellPosedness.Spec.Bridge25
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

/-!
# Assumption 2.5 as printed, in coupling form

Remark 2.9 of the well-posedness paper: Assumption 2.5 is a property of the coefficients, not of
the standing basis. As printed, its interior inequality (2.7) and its terminal inequality require
the expectations of their pairings to exist. For two diagonal inputs `(Θ, μ), (Θ', μ') ∈ 𝒟_t`
the pairing of (2.7) is `F(Θ, Θ')` for a function `F` on `H × H` which is measurable under the
joint measurability (2.3), so its integrability, like its expectation, is a property of the joint
law `γ` of `(Θ, Θ')`: `F(Θ, Θ')` is `P`-integrable exactly when `F` is `γ`-integrable. The same
holds for the terminal pairing when `x ↦ g(x, ρ)` is measurable. Since every coupling of two laws
of finite second moment is the joint law of two diagonal inputs at every positive time, each
condition of Assumption 2.5, the existence of its expectations included, is equivalent to the
same condition over all couplings of all pairs of laws, a statement about the coefficients
alone, and Assumption 2.3 plays no role.

## Main definitions

* `CouplingMono27` — (2.7) over couplings, the pairing being integrable for the coupling.
* `CouplingTerminalMono25` — the terminal inequality of Assumption 2.5 over couplings, the
  pairing being integrable for the coupling.

## Main statements

* `mono27_pair_iff`, `terminal25_pair_iff` — along two inputs, each condition of Assumption 2.5
  is the same condition against their joint law.
* `ae_mono27At_iff_coupling`, `terminal25_iff_coupling`, `assumption25_iff_coupling` — each
  condition of Assumption 2.5, and Assumption 2.5 itself, is equivalent to its coupling form.
* `assumption25_congr_basis` — Assumption 2.5 holds on one basis if and only if it holds on
  another.
-/

open MeasureTheory Filter MVFBSDEJ.Law
open scoped Matrix

namespace MVFBSDEJ.WellPosedness.Spec

open MVFBSDEJ.WellPosedness.System MVFBSDEJ.WellPosedness.Existence

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} {n m d : ℕ} [SigmaFinite ν]
  [MeasurableSpace.CountablyGenerated E]

/-! ### The coupling forms -/

/-- **(2.7) over couplings, with the expectation of the pairing existing**: for almost every
`t ∈ [0, T]`, every two laws `μ, μ'` of finite second moment on `H` and every coupling `γ` of
them, `(θ, θ') ↦ ⟨δb, Gᵀ δy⟩ + ⟨δσ, Gᵀ δz⟩_F − ⟨δf, G δx⟩ + ⟨δh, Gᵀ δu⟩_{L²(ν)}` is
`γ`-integrable and its integral against `γ` is at most that of
`−β₁ (|Gᵀ δy|² + |Gᵀ δz|²_F + ‖Gᵀ δu‖²_{L²(ν)}) − β₂ |G δx|²`, with
`δψ = ψ(t, θ, μ) − ψ(t, θ', μ')`. -/
def CouplingMono27 (T : ℝ) (G : Matrix (Fin m) (Fin n) ℝ) (β₁ β₂ : ℝ) (C : Coeffs ν n m d) :
    Prop :=
  ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ (μ μ' : P2 (TupleH ν n m d))
    (γ : Measure (TupleH ν n m d × TupleH ν n m d)), IsCoupling μ.law μ'.law γ →
    Integrable (fun p => interiorPairing (GX G) (GZ G) (GU G ν) (diagDiff C t p.1 p.2 μ μ')) γ
      ∧ ∫ p, interiorPairing (GX G) (GZ G) (GU G ν) (diagDiff C t p.1 p.2 μ μ') ∂γ
        ≤ ∫ p, dissipation (GX G) (GZ G) (GU G ν) β₁ β₂ (diagDiff C t p.1 p.2 μ μ') ∂γ

/-- **The terminal inequality of Assumption 2.5 over couplings, with the expectation of the
pairing existing**: for every two laws `ρ, ρ'` of finite second moment on `ℝⁿ` and every
coupling `γ` of them, `(x, x') ↦ ⟨g(x, ρ) − g(x', ρ'), G (x − x')⟩` is `γ`-integrable and
`α ∫ |G (x − x')|² dγ ≤ ∫ ⟨g(x, ρ) − g(x', ρ'), G (x − x')⟩ dγ`. -/
def CouplingTerminalMono25 (G : Matrix (Fin m) (Fin n) ℝ) (α : ℝ)
    (g : EuclideanSpace ℝ (Fin n) → P2 (EuclideanSpace ℝ (Fin n)) → EuclideanSpace ℝ (Fin m)) :
    Prop :=
  ∀ (ρ ρ' : P2 (EuclideanSpace ℝ (Fin n)))
    (γ : Measure (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))),
    IsCoupling ρ.law ρ'.law γ →
    Integrable (fun p => inner ℝ (g p.1 ρ - g p.2 ρ') (GX G (p.1 - p.2))) γ
      ∧ α * ∫ p, ‖GX G (p.1 - p.2)‖ ^ 2 ∂γ
        ≤ ∫ p, inner ℝ (g p.1 ρ - g p.2 ρ') (GX G (p.1 - p.2)) ∂γ

/-! ### The interior inequality (2.7) -/

section Interior

variable {Ω : Type*} [MeasurableSpace Ω] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {P : Measure Ω} [IsProbabilityMeasure P] {T β₁ β₂ : ℝ} {G : Matrix (Fin m) (Fin n) ℝ}
  {C : Coeffs ν n m d} {t : ℝ}

/-- **(2.7) along two diagonal inputs is (2.7) against their joint law**: under the joint
measurability (2.3), for `t ∈ [0, T]` and `(Θ, μ), (Θ', μ') ∈ 𝒟_t` with joint law `γ`, the
pairing of (2.7) is `P`-integrable with expectation at most that of the right-hand side if and
only if its integrand on `H × H` is `γ`-integrable with integral at most that of the right-hand
side. -/
theorem mono27_pair_iff (hC : CoeffBorel T C) (ht : t ∈ Set.Icc (0 : ℝ) T)
    {p p' : (Ω → TupleH ν n m d) × P2 (TupleH ν n m d)}
    (hp : p ∈ diagonalInputs ν n m d ℱ P t) (hp' : p' ∈ diagonalInputs ν n m d ℱ P t) :
    (Integrable (fun ω => pairing27 G C t (p.1 ω) (p'.1 ω) p.2 p'.2) P
      ∧ ∫ ω, pairing27 G C t (p.1 ω) (p'.1 ω) p.2 p'.2 ∂P
        ≤ -β₁ * ∫ ω, (‖GX Gᵀ ((p.1 ω).2.1 - (p'.1 ω).2.1)‖ ^ 2
            + ‖GZ Gᵀ ((p.1 ω).2.2.1 - (p'.1 ω).2.2.1)‖ ^ 2
            + ‖GU Gᵀ ν ((p.1 ω).2.2.2 - (p'.1 ω).2.2.2)‖ ^ 2) ∂P
          - β₂ * ∫ ω, ‖GX G ((p.1 ω).1 - (p'.1 ω).1)‖ ^ 2 ∂P)
      ↔ Integrable (fun q => interiorPairing (GX G) (GZ G) (GU G ν)
            (diagDiff C t q.1 q.2 p.2 p'.2)) (P.map fun ω => (p.1 ω, p'.1 ω))
        ∧ ∫ q, interiorPairing (GX G) (GZ G) (GU G ν) (diagDiff C t q.1 q.2 p.2 p'.2)
            ∂(P.map fun ω => (p.1 ω, p'.1 ω))
          ≤ ∫ q, dissipation (GX G) (GZ G) (GU G ν) β₁ β₂ (diagDiff C t q.1 q.2 p.2 p'.2)
            ∂(P.map fun ω => (p.1 ω, p'.1 ω)) := by
  have hae : AEMeasurable (fun ω => (p.1 ω, p'.1 ω)) P :=
    hp.2.1.aestronglyMeasurable.aemeasurable.prodMk hp'.2.1.aestronglyMeasurable.aemeasurable
  have hF := aestronglyMeasurable_interiorPairing_of_coeffBorel hC ht G p.2 p'.2
    (P.map fun ω => (p.1 ω, p'.1 ω))
  rw [integrable_map_measure hF hae, integral_map hae hF,
    integral_map hae (aestronglyMeasurable_dissipation_diagDiff G β₁ β₂ C t _ _ _),
    ← integral_dissipation_eq hp.2.1 hp'.2.1 G β₁ β₂ C t p.2 p'.2]
  simp only [Function.comp_def, pairing27_eq]

/-- **(2.7), with the expectation of the pairing existing, in coupling form**: under the joint
measurability (2.3), over a filtration supporting a uniform variable at every positive time,
(2.7) as printed holds for almost every `t ∈ [0, T]` if and only if it holds, the pairing being
integrable, over every coupling of every two laws in `P₂(H)` for almost every `t ∈ [0, T]`. -/
theorem ae_mono27At_iff_coupling (hC : CoeffBorel T C) (hU : SupportsUniform ℱ P) :
    (∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), Mono27At ℱ P t G β₁ β₂ C)
      ↔ CouplingMono27 T G β₁ β₂ C := by
  constructor
  · intro h
    filter_upwards [h, ae_restrict_mem measurableSet_Icc, ae_restrict_Icc_pos T]
      with t ht htI htpos μ μ' γ hγ
    obtain ⟨p, hp, p', hp', rfl, rfl, rfl⟩ := hU.exists_mem_diagonalInputs htpos hγ
    exact (mono27_pair_iff hC htI hp hp').mp (ht p hp p' hp')
  · intro h
    filter_upwards [h, ae_restrict_mem measurableSet_Icc] with t ht htI p hp p' hp'
    exact (mono27_pair_iff hC htI hp hp').mpr
      (ht p.2 p'.2 _ (isCoupling_of_mem_diagonalInputs hp hp'))

end Interior

/-! ### The terminal inequality -/

section Terminal

variable {Ω : Type*} [MeasurableSpace Ω] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {P : Measure Ω} [IsProbabilityMeasure P] {T α : ℝ} {G : Matrix (Fin m) (Fin n) ℝ}
  {g : EuclideanSpace ℝ (Fin n) → P2 (EuclideanSpace ℝ (Fin n)) → EuclideanSpace ℝ (Fin m)}

/-- **The terminal inequality along two variables is the inequality against their joint law**:
if `x ↦ g(x, ρ)` is measurable for every law `ρ`, then for square-integrable `X_T, X'_T` with
laws `ρ, ρ'` and joint law `γ`, `⟨g(X_T, ρ) − g(X'_T, ρ'), G (X_T − X'_T)⟩` is `P`-integrable
with `𝔼⟨δg_T, G δX_T⟩ ≥ α 𝔼|G δX_T|²` if and only if
`(x, x') ↦ ⟨g(x, ρ) − g(x', ρ'), G (x − x')⟩` is `γ`-integrable with
`α ∫ |G (x − x')|² dγ ≤ ∫ ⟨g(x, ρ) − g(x', ρ'), G (x − x')⟩ dγ`. -/
theorem terminal25_pair_iff (hg : ∀ ρ, Measurable fun x => g x ρ)
    {ξ ξ' : Ω → EuclideanSpace ℝ (Fin n)} (hξ : MemLp ξ 2 P) (hξ' : MemLp ξ' 2 P) :
    (Integrable (fun ω => inner ℝ (g (ξ ω) (lawP2 P ξ) - g (ξ' ω) (lawP2 P ξ'))
        (GX G (ξ ω - ξ' ω))) P
      ∧ ∫ ω, inner ℝ (g (ξ ω) (lawP2 P ξ) - g (ξ' ω) (lawP2 P ξ')) (GX G (ξ ω - ξ' ω)) ∂P
        ≥ α * ∫ ω, ‖GX G (ξ ω - ξ' ω)‖ ^ 2 ∂P)
      ↔ Integrable (fun q => inner ℝ (g q.1 (lawP2 P ξ) - g q.2 (lawP2 P ξ'))
            (GX G (q.1 - q.2))) (P.map fun ω => (ξ ω, ξ' ω))
        ∧ α * ∫ q, ‖GX G (q.1 - q.2)‖ ^ 2 ∂(P.map fun ω => (ξ ω, ξ' ω))
          ≤ ∫ q, inner ℝ (g q.1 (lawP2 P ξ) - g q.2 (lawP2 P ξ')) (GX G (q.1 - q.2))
            ∂(P.map fun ω => (ξ ω, ξ' ω)) := by
  have hae : AEMeasurable (fun ω => (ξ ω, ξ' ω)) P :=
    hξ.aestronglyMeasurable.aemeasurable.prodMk hξ'.aestronglyMeasurable.aemeasurable
  have hsq : Continuous fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      ‖GX G (q.1 - q.2)‖ ^ 2 := by fun_prop
  have hin : Measurable fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      inner ℝ (g q.1 (lawP2 P ξ) - g q.2 (lawP2 P ξ')) (GX G (q.1 - q.2)) :=
    (((hg _).comp measurable_fst).sub ((hg _).comp measurable_snd)).inner
      ((GX G).continuous.measurable.comp (measurable_fst.sub measurable_snd))
  rw [integrable_map_measure hin.aestronglyMeasurable hae,
    integral_map hae hin.aestronglyMeasurable, integral_map hae hsq.aestronglyMeasurable]
  exact Iff.rfl

/-- **The terminal inequality of Assumption 2.5, with the expectation of the pairing existing,
in coupling form**: if `x ↦ g(x, ρ)` is measurable for every law `ρ` and `ℱ_T`, `T > 0`, carries
a uniform variable, then `𝔼⟨δg_T, G δX_T⟩ ≥ α 𝔼|G δX_T|²`, the pairing being integrable, holds
for all `X_T, X'_T ∈ L²(Ω, ℱ_T; ℝⁿ)` if and only if it holds, the pairing being integrable, over
every coupling of every two laws in `P₂(ℝⁿ)`. -/
theorem terminal25_iff_coupling (hg : ∀ ρ, Measurable fun x => g x ρ)
    (hU : SupportsUniform ℱ P) (hT : 0 < T) :
    (∀ XT XT' : Ω → EuclideanSpace ℝ (Fin n), StronglyMeasurable[ℱ T] XT →
      StronglyMeasurable[ℱ T] XT' → MemLp XT 2 P → MemLp XT' 2 P →
      Integrable (fun ω => inner ℝ (g (XT ω) (lawP2 P XT) - g (XT' ω) (lawP2 P XT'))
          (GX G (XT ω - XT' ω))) P
        ∧ ∫ ω, inner ℝ (g (XT ω) (lawP2 P XT) - g (XT' ω) (lawP2 P XT'))
            (GX G (XT ω - XT' ω)) ∂P
          ≥ α * ∫ ω, ‖GX G (XT ω - XT' ω)‖ ^ 2 ∂P)
      ↔ CouplingTerminalMono25 G α g := by
  constructor
  · intro h ρ ρ' γ hγ
    obtain ⟨ξ, ξ', hξ, hξ', hL, hL', rfl, rfl, rfl⟩ := hU.exists_pair_map_eq hT hγ
    exact (terminal25_pair_iff hg hL hL').mp (h ξ ξ' hξ hξ' hL hL')
  · intro h ξ ξ' _ _ hL hL'
    exact (terminal25_pair_iff hg hL hL').mpr (h _ _ _ (isCoupling_lawP2_map hL hL'))

end Terminal

/-! ### Assumption 2.5 -/

section Basis

variable {Ω : Type*} [MeasurableSpace Ω] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {P : Measure Ω} [IsProbabilityMeasure P] {Ω' : Type*} [MeasurableSpace Ω']
  {ℱ' : Filtration ℝ ‹MeasurableSpace Ω'›} {P' : Measure Ω'} [IsProbabilityMeasure P']
  {T α β₁ β₂ : ℝ} {G : Matrix (Fin m) (Fin n) ℝ} {C : Coeffs ν n m d}

/-- **Assumption 2.5 in coupling form**: under the joint measurability (2.3), for `T > 0` and a
filtration supporting a uniform variable at every positive time, Assumption 2.5 holds if and
only if its terminal inequality and (2.7) hold, the pairings being integrable, over every
coupling of every two laws, and the constants are admissible. -/
theorem assumption25_iff_coupling (hJ : JointBorel T C) (hU : SupportsUniform ℱ P)
    (hT : 0 < T) :
    Assumption25 ℱ P T G α β₁ β₂ C
      ↔ CouplingTerminalMono25 G α C.g ∧ CouplingMono27 T G β₁ β₂ C
        ∧ Constants n m α β₁ β₂ := by
  have hT25 := terminal25_iff_coupling (G := G) (α := α) hJ.measurable_g_section hU hT
  have hM27 := ae_mono27At_iff_coupling (G := G) (β₁ := β₁) (β₂ := β₂)
    (jointBorel_iff.mp hJ).1.toCoeffBorel hU
  exact ⟨fun h => ⟨hT25.mp h.terminal, hM27.mp h.interior, h.constants⟩,
    fun h => ⟨hT25.mpr h.1, hM27.mpr h.2.1, h.2.2⟩⟩

/-- **Assumption 2.5 does not depend on the basis**: under the joint measurability (2.3) and for
`T > 0`, Assumption 2.5 holds on one filtered probability space supporting a uniform variable at
every positive time if and only if it holds on another. -/
theorem assumption25_congr_basis (hJ : JointBorel T C) (hU : SupportsUniform ℱ P)
    (hU' : SupportsUniform ℱ' P') (hT : 0 < T) :
    Assumption25 ℱ P T G α β₁ β₂ C ↔ Assumption25 ℱ' P' T G α β₁ β₂ C :=
  (assumption25_iff_coupling hJ hU hT).trans (assumption25_iff_coupling hJ hU' hT).symm

end Basis

end MVFBSDEJ.WellPosedness.Spec
