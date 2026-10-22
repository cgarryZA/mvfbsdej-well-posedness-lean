/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Remarks.CouplingRealisation
import MVFBSDEJ.WellPosedness.Remarks.Pointwise
import MVFBSDEJ.WellPosedness.System.DiagonalInputs

/-!
# The diagonal assumptions in coupling form

Remark 2.9 of the well-posedness paper: the diagonal hypotheses, Assumptions 2.3 and 2.5, are
properties of the coefficients, not of the standing basis. Two diagonal inputs
`(Θ, μ), (Θ', μ') ∈ 𝒟_t` enter the conditions only through the joint law `γ` of `(Θ, Θ')`, a
coupling of `μ` and `μ'`: an expectation along the pair is the integral against `γ`, and an
almost sure bound along the pair is a `γ`-almost everywhere bound. Conversely, when `ℱ_t`
carries a uniform variable, every coupling `γ` of two laws of finite second moment is the joint
law of two diagonal inputs at time `t`. So each diagonal condition of Assumption 2.3 at time `t`
is equivalent to the same condition over all couplings of all pairs of laws in `P₂(H)`, a
statement about the coefficients alone:

* `CouplingLipschitzH` — for almost every `t ∈ [0, T]`, every pair of laws `μ, μ'` and every
  coupling `γ`, for `γ`-almost every `(θ, θ')`,
  `|δb| + |δσ|_F + ‖δh‖_{L²(ν)} + |δf| ≤ L (|δx| + |δy| + |δz|_F + ‖δu‖_{L²(ν)} + W₂(μ, μ'))`;
* `CouplingTerminalLipschitz` — the terminal condition over the couplings of pairs of laws in
  `P₂(ℝⁿ)`.

The transfer between the two forms needs the integrands to be measurable on `H × H`, which the joint
measurability (2.3) of the coefficients provides
(`MVFBSDEJ.WellPosedness.Existence.CoeffBorel`), and the Borel measurability of `x ↦ g(x, ρ)`
for the terminal conditions; both are standing in the paper. Without them an integrand on `H × H`
need not be measurable for `γ`; its integral against `γ` is then `0` by the Bochner convention and
need not equal the expectation along the pair.

The uniform variable is needed only in the direction from the diagonal form to the coupling form,
and only at the times where the condition is imposed. The interior conditions are imposed for
almost every `t ∈ [0, T]`, so the time `t = 0`, where `ℱ_0` may carry no uniform variable, is a
null set and plays no role; the terminal conditions are imposed at `T > 0`. Hence the hypothesis
`SupportsUniform ℱ P`, a uniform variable on every `ℱ_t` with `t > 0`, which every filtration
carrying a Brownian motion satisfies, and no condition on `ℱ_0`.

## Main definitions

* `CouplingLipschitzH` — the interior condition of Assumption 2.3 over couplings.
* `CouplingTerminalLipschitz` — the terminal condition of Assumption 2.3 over couplings.

## Main statements

* `isCoupling_of_mem_diagonalInputs`, `SupportsUniform.exists_mem_diagonalInputs` — the joint law
  of two diagonal inputs couples their laws, and for `t > 0` every coupling arises so.
* `lipschitzAlong_iff_coupling`, `diagonalLipschitzH_iff_coupling`,
  `terminalLipschitz_iff_coupling` — each diagonal condition is equivalent to its coupling form.
* `diagonalLipschitzH_congr_basis`, `terminalLipschitz_congr_basis` — each holds on one basis if
  and only if it holds on another.
-/

open MeasureTheory Filter MVFBSDEJ.Law
open scoped ENNReal

namespace MVFBSDEJ.WellPosedness.System

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} {n m d : ℕ} [SigmaFinite ν]
  [MeasurableSpace.CountablyGenerated E]

/-! ### The coupling forms -/

section Defs

/-- **Assumption 2.3, interior, over couplings, with the Hilbert-norm `W₂`**: for almost every
`t ∈ [0, T]`, every two laws `μ, μ'` of finite second moment on `H` and every coupling `γ` of
them, for `γ`-almost every `(θ, θ')`,
`|δb| + |δσ|_F + ‖δh‖_{L²(ν)} + |δf| ≤ L (|δx| + |δy| + |δz|_F + ‖δu‖_{L²(ν)} + W₂(μ, μ'))`,
with `W₂` for the Hilbert norm of `H`. -/
def CouplingLipschitzH (T L : ℝ) (C : Coeffs ν n m d) : Prop :=
  ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ (μ μ' : P2 (TupleH ν n m d))
    (γ : Measure (TupleH ν n m d × TupleH ν n m d)), IsCoupling μ.law μ'.law γ →
    ∀ᵐ p ∂γ, ‖C.b t p.1 μ - C.b t p.2 μ'‖ + ‖C.σ t p.1 μ - C.σ t p.2 μ'‖
        + ‖C.h t p.1 μ - C.h t p.2 μ'‖ + ‖C.f t p.1 μ - C.f t p.2 μ'‖
      ≤ L * (tupleNorm (p.1 - p.2) + w2H μ μ')

end Defs

/-- **Assumption 2.3, terminal (2.6), over couplings**: for every two laws `ρ, ρ'` of finite
second moment on `ℝⁿ` and every coupling `γ` of them, for `γ`-almost every `(x, x')`,
`|g(x, ρ) − g(x', ρ')| ≤ L (|x − x'| + W₂(ρ, ρ'))`. -/
def CouplingTerminalLipschitz (L : ℝ)
    (g : EuclideanSpace ℝ (Fin n) → P2 (EuclideanSpace ℝ (Fin n)) → EuclideanSpace ℝ (Fin m)) :
    Prop :=
  ∀ (ρ ρ' : P2 (EuclideanSpace ℝ (Fin n)))
    (γ : Measure (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))),
    IsCoupling ρ.law ρ'.law γ →
    ∀ᵐ p ∂γ, ‖g p.1 ρ - g p.2 ρ'‖ ≤ L * (‖p.1 - p.2‖ + w2P ρ ρ')

/-! ### Joint laws of diagonal inputs -/

section Joint

variable {F : Type*} [NormedAddCommGroup F] [MeasurableSpace F] [BorelSpace F]
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
/-- **The joint law of two square-integrable random elements couples their laws.** -/
theorem isCoupling_lawP2_map {Θ Θ' : Ω → F} (hΘ : MemLp Θ 2 P) (hΘ' : MemLp Θ' 2 P) :
    IsCoupling (lawP2 P Θ).law (lawP2 P Θ').law (P.map fun ω => (Θ ω, Θ' ω)) := by
  rw [lawP2_law hΘ, lawP2_law hΘ']
  exact ⟨Measure.fst_map_prodMk₀ hΘ'.aestronglyMeasurable.aemeasurable,
    Measure.snd_map_prodMk₀ hΘ.aestronglyMeasurable.aemeasurable⟩

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {t : ℝ}

/-- **The joint law of two diagonal inputs couples their laws**: for `(Θ, μ), (Θ', μ') ∈ 𝒟_t`,
the joint law of `(Θ, Θ')` is a coupling of `μ` and `μ'`. -/
theorem isCoupling_of_mem_diagonalInputs {p p' : (Ω → TupleH ν n m d) × P2 (TupleH ν n m d)}
    (hp : p ∈ diagonalInputs ν n m d ℱ P t) (hp' : p' ∈ diagonalInputs ν n m d ℱ P t) :
    IsCoupling p.2.law p'.2.law (P.map fun ω => (p.1 ω, p'.1 ω)) := by
  rw [hp.2.2, hp'.2.2]
  exact isCoupling_lawP2_map hp.2.1 hp'.2.1

/-- **Every coupling is the joint law of two diagonal inputs** (Remark 2.9): over a filtration
supporting a uniform variable at every positive time, for `t > 0` and every coupling `γ` of two
laws `μ, μ'` of finite second moment on `H`, there are `(Θ, μ), (Θ', μ') ∈ 𝒟_t` with the joint
law of `(Θ, Θ')` equal to `γ`. -/
theorem SupportsUniform.exists_mem_diagonalInputs (hU : SupportsUniform ℱ P) (ht : 0 < t)
    {μ μ' : P2 (TupleH ν n m d)} {γ : Measure (TupleH ν n m d × TupleH ν n m d)}
    (hγ : IsCoupling μ.law μ'.law γ) :
    ∃ p ∈ diagonalInputs ν n m d ℱ P t, ∃ p' ∈ diagonalInputs ν n m d ℱ P t,
      p.2 = μ ∧ p'.2 = μ' ∧ P.map (fun ω => (p.1 ω, p'.1 ω)) = γ := by
  obtain ⟨Θ, Θ', hΘ, hΘ', hL, hL', hmap, hlaw, hlaw'⟩ := hU.exists_pair_map_eq ht hγ
  exact ⟨(Θ, μ), ⟨hΘ, hL, hlaw.symm⟩, (Θ', μ'), ⟨hΘ', hL', hlaw'.symm⟩, rfl, rfl, hmap⟩

end Joint

/-! ### Measurability of the integrands on `H × H` -/

section Measurability

variable {T : ℝ} {C : Coeffs ν n m d} {t : ℝ}

/-- **The coefficient differences on `H × H`**: under the joint measurability (2.3), for
`t ∈ [0, T]` and laws `μ, μ'`, `(θ, θ') ↦ |δb| + |δσ|_F + ‖δh‖_{L²(ν)} + |δf|` is measurable. -/
theorem measurable_coeffDiff_of_coeffBorel (hC : Existence.CoeffBorel T C)
    (ht : t ∈ Set.Icc (0 : ℝ) T) (μ μ' : P2 (TupleH ν n m d)) :
    Measurable fun p : TupleH ν n m d × TupleH ν n m d =>
      ‖C.b t p.1 μ - C.b t p.2 μ'‖ + ‖C.σ t p.1 μ - C.σ t p.2 μ'‖
        + ‖C.h t p.1 μ - C.h t p.2 μ'‖ + ‖C.f t p.1 μ - C.f t p.2 μ'‖ := by
  have hb := measurable_section_of_cutoff hC.b_meas ht
  have hσ := measurable_section_of_cutoff hC.σ_meas ht
  have hh := measurable_section_of_cutoff hC.h_meas ht
  have hf := measurable_section_of_cutoff hC.f_meas ht
  exact (((((hb μ).comp measurable_fst).sub ((hb μ').comp measurable_snd)).norm.add
    (((hσ μ).comp measurable_fst).sub ((hσ μ').comp measurable_snd)).norm).add
    (((hh μ).comp measurable_fst).sub ((hh μ').comp measurable_snd)).norm).add
    (((hf μ).comp measurable_fst).sub ((hf μ').comp measurable_snd)).norm

omit [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
/-- The sum of the channel norms of a difference is continuous on `H × H`. -/
theorem continuous_tupleNorm_sub :
    Continuous fun p : TupleH ν n m d × TupleH ν n m d => tupleNorm (p.1 - p.2) := by
  unfold tupleNorm
  fun_prop

/-- The sum of the channel norms of a difference is measurable on `H × H`. -/
theorem measurable_tupleNorm_sub :
    Measurable fun p : TupleH ν n m d × TupleH ν n m d => tupleNorm (p.1 - p.2) := by
  haveI : OpensMeasurableSpace (TupleH ν n m d × TupleH ν n m d) := Prod.opensMeasurableSpace
  exact continuous_tupleNorm_sub.measurable

/-- **The interior pairing on `H × H`**: under the joint measurability (2.3), for `t ∈ [0, T]`
and laws `μ, μ'`, `(θ, θ') ↦ ⟨δb, Gᵀ δy⟩ + ⟨δσ, Gᵀ δz⟩_F − ⟨δf, G δx⟩ + ⟨δh, Gᵀ δu⟩_{L²(ν)}` is
almost everywhere strongly measurable for every measure on `H × H`. -/
theorem aestronglyMeasurable_interiorPairing_of_coeffBorel (hC : Existence.CoeffBorel T C)
    (ht : t ∈ Set.Icc (0 : ℝ) T) (G : Matrix (Fin m) (Fin n) ℝ) (μ μ' : P2 (TupleH ν n m d))
    (γ : Measure (TupleH ν n m d × TupleH ν n m d)) :
    AEStronglyMeasurable (fun p : TupleH ν n m d × TupleH ν n m d =>
      interiorPairing (GX G) (GZ G) (GU G ν) (diagDiff C t p.1 p.2 μ μ')) γ :=
  aestronglyMeasurable_interiorPairing_diagDiff G C t μ μ' measurable_fst.aestronglyMeasurable
    measurable_snd.aestronglyMeasurable
    (aestronglyMeasurable_sub_of_cutoff hC.b_meas ht measurable_fst.aemeasurable
      measurable_snd.aemeasurable μ μ')
    (aestronglyMeasurable_sub_of_cutoff hC.σ_meas ht measurable_fst.aemeasurable
      measurable_snd.aemeasurable μ μ')
    (aestronglyMeasurable_sub_of_cutoff hC.h_meas ht measurable_fst.aemeasurable
      measurable_snd.aemeasurable μ μ')
    (aestronglyMeasurable_sub_of_cutoff hC.f_meas ht measurable_fst.aemeasurable
      measurable_snd.aemeasurable μ μ')

omit [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
/-- **The right-hand side of (2.7) is continuous on `H × H`**: for every time and laws `μ, μ'`,
`(θ, θ') ↦ −β₁ (|Gᵀ δy|² + |Gᵀ δz|²_F + ‖Gᵀ δu‖²_{L²(ν)}) − β₂ |G δx|²` is continuous. -/
theorem continuous_dissipation_diagDiff (G : Matrix (Fin m) (Fin n) ℝ) (β₁ β₂ : ℝ)
    (C : Coeffs ν n m d) (t : ℝ) (μ μ' : P2 (TupleH ν n m d)) :
    Continuous fun p : TupleH ν n m d × TupleH ν n m d =>
      dissipation (GX G) (GZ G) (GU G ν) β₁ β₂ (diagDiff C t p.1 p.2 μ μ') := by
  unfold dissipation diagDiff
  fun_prop

/-- The right-hand side of (2.7) is almost everywhere strongly measurable for every measure on
`H × H`. -/
theorem aestronglyMeasurable_dissipation_diagDiff (G : Matrix (Fin m) (Fin n) ℝ) (β₁ β₂ : ℝ)
    (C : Coeffs ν n m d) (t : ℝ) (μ μ' : P2 (TupleH ν n m d))
    (γ : Measure (TupleH ν n m d × TupleH ν n m d)) :
    AEStronglyMeasurable (fun p : TupleH ν n m d × TupleH ν n m d =>
      dissipation (GX G) (GZ G) (GU G ν) β₁ β₂ (diagDiff C t p.1 p.2 μ μ')) γ := by
  haveI : OpensMeasurableSpace (TupleH ν n m d × TupleH ν n m d) := Prod.opensMeasurableSpace
  exact (continuous_dissipation_diagDiff G β₁ β₂ C t μ μ').aestronglyMeasurable

end Measurability

/-! ### The interior conditions -/

section Interior

variable {Ω : Type*} [MeasurableSpace Ω] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {P : Measure Ω} [IsProbabilityMeasure P] {T L β₁ β₂ : ℝ} {G : Matrix (Fin m) (Fin n) ℝ}
  {C : Coeffs ν n m d}

omit [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
/-- Almost every time of `[0, T]` is positive. -/
theorem ae_restrict_Icc_pos (T : ℝ) : ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), 0 < t := by
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    ae_restrict_of_ae (Measure.ae_ne volume (0 : ℝ))] with t ht ht0
  exact lt_of_le_of_ne ht.1 (Ne.symm ht0)

/-- **The diagonal Lipschitz bound in coupling form, for a distance on the laws**: for any real
function `δ` of two laws in `P₂(H)`, the bound
`|δb| + |δσ|_F + ‖δh‖_{L²(ν)} + |δf| ≤ L (|δx| + |δy| + |δz|_F + ‖δu‖_{L²(ν)} + δ(μ, μ'))` holds
almost surely along every two diagonal inputs, for almost every `t ∈ [0, T]`, if and only if it
holds `γ`-almost everywhere for every coupling `γ` of every two laws, for almost every
`t ∈ [0, T]`. -/
theorem lipschitzAlong_iff_coupling (hC : Existence.CoeffBorel T C) (hU : SupportsUniform ℱ P)
    (δ : P2 (TupleH ν n m d) → P2 (TupleH ν n m d) → ℝ) :
    (∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ Θ Θ' : Ω → TupleH ν n m d,
      StronglyMeasurable[ℱ t] Θ → StronglyMeasurable[ℱ t] Θ' → MemLp Θ 2 P → MemLp Θ' 2 P →
      ∀ᵐ ω ∂P, ‖C.b t (Θ ω) (lawP2 P Θ) - C.b t (Θ' ω) (lawP2 P Θ')‖
          + ‖C.σ t (Θ ω) (lawP2 P Θ) - C.σ t (Θ' ω) (lawP2 P Θ')‖
          + ‖C.h t (Θ ω) (lawP2 P Θ) - C.h t (Θ' ω) (lawP2 P Θ')‖
          + ‖C.f t (Θ ω) (lawP2 P Θ) - C.f t (Θ' ω) (lawP2 P Θ')‖
        ≤ L * (tupleNorm (Θ ω - Θ' ω) + δ (lawP2 P Θ) (lawP2 P Θ')))
      ↔ ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ (μ μ' : P2 (TupleH ν n m d))
        (γ : Measure (TupleH ν n m d × TupleH ν n m d)), IsCoupling μ.law μ'.law γ →
        ∀ᵐ p ∂γ, ‖C.b t p.1 μ - C.b t p.2 μ'‖ + ‖C.σ t p.1 μ - C.σ t p.2 μ'‖
            + ‖C.h t p.1 μ - C.h t p.2 μ'‖ + ‖C.f t p.1 μ - C.f t p.2 μ'‖
          ≤ L * (tupleNorm (p.1 - p.2) + δ μ μ') := by
  constructor
  · intro h
    filter_upwards [h, ae_restrict_mem measurableSet_Icc, ae_restrict_Icc_pos T]
      with t ht htI htpos μ μ' γ hγ
    obtain ⟨Θ, Θ', hΘ, hΘ', hL, hL', hmap, hlaw, hlaw'⟩ := hU.exists_pair_map_eq htpos hγ
    have key := ht Θ Θ' hΘ hΘ' hL hL'
    rw [hlaw, hlaw'] at key
    subst hmap
    exact (ae_map_iff (hL.aestronglyMeasurable.aemeasurable.prodMk
      hL'.aestronglyMeasurable.aemeasurable)
      (measurableSet_le (measurable_coeffDiff_of_coeffBorel hC htI μ μ')
        (measurable_const.mul (measurable_tupleNorm_sub.add measurable_const)))).mpr
      key
  · intro h
    filter_upwards [h] with t ht Θ Θ' _ _ hL hL'
    exact ae_of_ae_map (hL.aestronglyMeasurable.aemeasurable.prodMk
      hL'.aestronglyMeasurable.aemeasurable)
      (ht _ _ _ (isCoupling_lawP2_map hL hL'))

/-- **Assumption 2.3, interior, with the Hilbert-norm `W₂`, is intrinsic** (Remark 2.9): for
jointly measurable coefficients (2.3) and a filtration supporting a uniform variable at every
positive time, the diagonal Lipschitz bound holds if and only if it holds over every coupling of
every two laws in `P₂(H)`. -/
theorem diagonalLipschitzH_iff_coupling (hC : Existence.CoeffBorel T C)
    (hU : SupportsUniform ℱ P) : DiagonalLipschitzH ℱ P T L C ↔ CouplingLipschitzH T L C :=
  lipschitzAlong_iff_coupling hC hU w2H

end Interior

/-! ### The terminal conditions -/

section Terminal

variable {Ω : Type*} [MeasurableSpace Ω] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {P : Measure Ω} [IsProbabilityMeasure P] {T L α : ℝ} {G : Matrix (Fin m) (Fin n) ℝ}
  {g : EuclideanSpace ℝ (Fin n) → P2 (EuclideanSpace ℝ (Fin n)) → EuclideanSpace ℝ (Fin m)}

/-- **Assumption 2.3, terminal, is intrinsic** (Remark 2.9): if `x ↦ g(x, ρ)` is measurable for
every law `ρ` and `ℱ_T`, `T > 0`, carries a uniform variable, then (2.6) holds along the
diagonal if and only if it holds over every coupling of every two laws in `P₂(ℝⁿ)`. -/
theorem terminalLipschitz_iff_coupling (hg : ∀ ρ, Measurable fun x => g x ρ)
    (hU : SupportsUniform ℱ P) (hT : 0 < T) :
    TerminalLipschitz ℱ P T L g ↔ CouplingTerminalLipschitz L g := by
  constructor
  · intro h ρ ρ' γ hγ
    obtain ⟨ξ, ξ', hξ, hξ', hL, hL', hmap, hlaw, hlaw'⟩ := hU.exists_pair_map_eq hT hγ
    have key := h ξ ξ' hξ hξ' hL hL'
    rw [hlaw, hlaw'] at key
    subst hmap
    exact (ae_map_iff (hL.aestronglyMeasurable.aemeasurable.prodMk
      hL'.aestronglyMeasurable.aemeasurable)
      (measurableSet_le (((hg ρ).comp measurable_fst).sub ((hg ρ').comp measurable_snd)).norm
        (measurable_const.mul ((measurable_fst.sub measurable_snd).norm.add
          measurable_const)))).mpr key
  · intro h ξ ξ' _ _ hL hL'
    exact ae_of_ae_map (hL.aestronglyMeasurable.aemeasurable.prodMk
      hL'.aestronglyMeasurable.aemeasurable) (h _ _ _ (isCoupling_lawP2_map hL hL'))

end Terminal

/-! ### Independence of the basis -/

section Basis

variable {Ω : Type*} [MeasurableSpace Ω] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {P : Measure Ω} [IsProbabilityMeasure P] {Ω' : Type*} [MeasurableSpace Ω']
  {ℱ' : Filtration ℝ ‹MeasurableSpace Ω'›} {P' : Measure Ω'} [IsProbabilityMeasure P']
  {T L α β₁ β₂ : ℝ} {G : Matrix (Fin m) (Fin n) ℝ} {C : Coeffs ν n m d}

/-- **Assumption 2.3, interior, with the Hilbert-norm `W₂`, does not depend on the basis**: for
jointly measurable coefficients (2.3), it holds on one filtered probability space supporting a
uniform variable at every positive time if and only if it holds on another. -/
theorem diagonalLipschitzH_congr_basis (hC : Existence.CoeffBorel T C)
    (hU : SupportsUniform ℱ P) (hU' : SupportsUniform ℱ' P') :
    DiagonalLipschitzH ℱ P T L C ↔ DiagonalLipschitzH ℱ' P' T L C :=
  (diagonalLipschitzH_iff_coupling hC hU).trans (diagonalLipschitzH_iff_coupling hC hU').symm

/-- **Assumption 2.3, terminal, does not depend on the basis**: if `x ↦ g(x, ρ)` is measurable
for every law `ρ` and `T > 0`, (2.6) holds on one filtered probability space supporting a uniform
variable at every positive time if and only if it holds on another. -/
theorem terminalLipschitz_congr_basis
    {g : EuclideanSpace ℝ (Fin n) → P2 (EuclideanSpace ℝ (Fin n)) → EuclideanSpace ℝ (Fin m)}
    (hg : ∀ ρ, Measurable fun x => g x ρ) (hU : SupportsUniform ℱ P)
    (hU' : SupportsUniform ℱ' P') (hT : 0 < T) :
    TerminalLipschitz ℱ P T L g ↔ TerminalLipschitz ℱ' P' T L g :=
  (terminalLipschitz_iff_coupling hg hU hT).trans (terminalLipschitz_iff_coupling hg hU' hT).symm

end Basis

end MVFBSDEJ.WellPosedness.System
