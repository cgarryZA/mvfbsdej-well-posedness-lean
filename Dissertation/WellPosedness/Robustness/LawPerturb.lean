/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Robustness.Perturb
import Dissertation.WellPosedness.Robustness.Margin
import Dissertation.WellPosedness.Robustness.CouplingNorm
import Dissertation.WellPosedness.System.DiagonalLipschitzH

/-!
# Law-Lipschitz perturbations and the pairing bound (3.4)

The second half of Corollary 3.6 of the well-posedness paper takes perturbations independent of
the tuple and Lipschitz in the law, (3.5): for almost every `t ∈ [0, T]` and any two diagonal
inputs `(Θ, μ)`, `(Θ', μ')`,

`|δp_b| + |δp_σ|_F + ‖δp_h‖_{L²(ν)} + |δp_f| ≤ L_p W₂(μ, μ')`,

with `W₂` the 2-Wasserstein distance of the Hilbert norm of the tuple space, `w2H`, and
`L_p ≥ 0`. Then (3.4) holds with `c_pert = ‖G‖ L_p`, `‖G‖` the operator norm of `GX G`. Write
`R = (|δX|² + |δY|² + |δZ|²_F + ‖δU‖²_{L²(ν)})^{1/2}`, which bounds each channel difference, and
`D² = 𝔼 R²`. By Cauchy–Schwarz in each pairing, the bounds of `G` and `Gᵀ` on the three channels
by `‖G‖`, (3.5), and `2 W R ≤ W² + R²`, the pairing of the perturbation is at most

`‖G‖ (|δp_b| + |δp_σ|_F + ‖δp_h‖ + |δp_f|) R ≤ ‖G‖ L_p W₂(μ, μ') R`
`  ≤ ‖G‖ L_p (W₂(μ, μ')² + R²) / 2`

almost surely, and its expectation at most `‖G‖ L_p (W₂(μ, μ')² + D²) / 2 ≤ ‖G‖ L_p D²` by the
coupling bound (2.8). The same bound on the absolute value of the pairing makes it integrable:
independence of the tuple makes the coefficient differences deterministic, so the pairing is a
continuous function of the two inputs, hence measurable.

A perturbation with (3.5) and `L_p ≥ 0` satisfies Assumption 2.3 along the diagonal with the
constant `L_p`.

## Main definitions

* `DiagonalLawLipschitzH` — (3.5) along the diagonal, with the Hilbert-norm `W₂`.

## Main statements

* `Coeffs.TupleIndep.diagDiff_eq` — the differences of a perturbation independent of the tuple.
* `DiagonalLawLipschitzH.diagonalLipschitzH` — (3.5) gives Assumption 2.3 at the same constant.
* `DiagonalLawLipschitzH.diagonalPairingBound` — (3.5) gives (3.4) with `c_pert = ‖G‖ L_p`.
-/

open MeasureTheory Filter Dissertation.Law
open scoped ENNReal

namespace Dissertation.WellPosedness.System

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} {n m d : ℕ}

/-- **The differences of a perturbation independent of the tuple** are the tuple differences
together with the deterministic differences `p_ψ(t, 0, μ) − p_ψ(t, 0, μ')`. -/
theorem Coeffs.TupleIndep.diagDiff_eq {p : Coeffs ν n m d} (hp : p.TupleIndep) (t : ℝ)
    (θ θ' : TupleH ν n m d) (μ μ' : P2 (TupleH ν n m d)) :
    diagDiff p t θ θ' μ μ' =
      { δX := θ.1 - θ'.1
        δY := θ.2.1 - θ'.2.1
        δZ := θ.2.2.1 - θ'.2.2.1
        δU := θ.2.2.2 - θ'.2.2.2
        δb := p.b t 0 μ - p.b t 0 μ'
        δσ := p.σ t 0 μ - p.σ t 0 μ'
        δh := p.h t 0 μ - p.h t 0 μ'
        δf := p.f t 0 μ - p.f t 0 μ' } := by
  unfold diagDiff
  rw [hp.b t θ 0, hp.b t θ' 0, hp.σ t θ 0, hp.σ t θ' 0, hp.h t θ 0, hp.h t θ' 0, hp.f t θ 0,
    hp.f t θ' 0]

/-- Each channel of a tuple has norm at most the Hilbert norm `R` of the tuple:
`‖x‖, ‖y‖, ‖z‖, ‖u‖ ≤ (‖x‖² + ‖y‖² + ‖z‖² + ‖u‖²)^{1/2}`. -/
theorem norm_channels_le_norm_toL2 (θ : TupleH ν n m d) :
    ‖θ.1‖ ≤ ‖toL2 θ‖ ∧ ‖θ.2.1‖ ≤ ‖toL2 θ‖ ∧ ‖θ.2.2.1‖ ≤ ‖toL2 θ‖ ∧ ‖θ.2.2.2‖ ≤ ‖toL2 θ‖ := by
  have h := norm_toL2_sq θ
  unfold channelSq at h
  have h1 := sq_nonneg ‖θ.1‖
  have h2 := sq_nonneg ‖θ.2.1‖
  have h3 := sq_nonneg ‖θ.2.2.1‖
  have h4 := sq_nonneg ‖θ.2.2.2‖
  have key : ∀ a : ℝ, 0 ≤ a → a ^ 2 ≤ ‖toL2 θ‖ ^ 2 → a ≤ ‖toL2 θ‖ := fun a ha hle =>
    (pow_le_pow_iff_left₀ ha (norm_nonneg _) two_ne_zero).mp hle
  exact ⟨key _ (norm_nonneg _) (by linarith), key _ (norm_nonneg _) (by linarith),
    key _ (norm_nonneg _) (by linarith), key _ (norm_nonneg _) (by linarith)⟩

/-- **The pointwise bound behind (3.4)**: if the four coefficient differences sum to at most
`L_p W` with `L_p ≥ 0`, the interior pairing is at most `‖G‖ L_p (W² + R²) / 2` in absolute
value, with `R² = |δX|² + |δY|² + |δZ|²_F + ‖δU‖²_{L²(ν)}`. -/
theorem abs_interiorPairing_diagDiff_le (G : Matrix (Fin m) (Fin n) ℝ) (C : Coeffs ν n m d)
    (t : ℝ) (θ θ' : TupleH ν n m d) (μ μ' : P2 (TupleH ν n m d)) {Lₚ W : ℝ} (hLp : 0 ≤ Lₚ)
    (h : ‖C.b t θ μ - C.b t θ' μ'‖ + ‖C.σ t θ μ - C.σ t θ' μ'‖ + ‖C.h t θ μ - C.h t θ' μ'‖
      + ‖C.f t θ μ - C.f t θ' μ'‖ ≤ Lₚ * W) :
    |interiorPairing (GX G) (GZ G) (GU G ν) (diagDiff C t θ θ' μ μ')|
      ≤ ‖GX G‖ * Lₚ * (W ^ 2 + channelSq (θ - θ')) / 2 := by
  have hCS := abs_interiorPairing_le G ν (diagDiff C t θ θ' μ μ')
  obtain ⟨hX, hY, hZ, hU⟩ := norm_channels_le_norm_toL2 (θ - θ')
  set R := ‖toL2 (θ - θ')‖ with hR
  have hRsq : R ^ 2 = channelSq (θ - θ') := norm_toL2_sq _
  simp only [diagDiff] at hCS
  have hR0 : 0 ≤ R := norm_nonneg _
  have hsum : ‖C.b t θ μ - C.b t θ' μ'‖ * ‖θ.2.1 - θ'.2.1‖
        + ‖C.σ t θ μ - C.σ t θ' μ'‖ * ‖θ.2.2.1 - θ'.2.2.1‖
        + ‖C.f t θ μ - C.f t θ' μ'‖ * ‖θ.1 - θ'.1‖
        + ‖C.h t θ μ - C.h t θ' μ'‖ * ‖θ.2.2.2 - θ'.2.2.2‖
      ≤ Lₚ * W * R := by
    calc _ ≤ ‖C.b t θ μ - C.b t θ' μ'‖ * R + ‖C.σ t θ μ - C.σ t θ' μ'‖ * R
          + ‖C.f t θ μ - C.f t θ' μ'‖ * R + ‖C.h t θ μ - C.h t θ' μ'‖ * R := by
          gcongr
          exacts [hY, hZ, hX, hU]
      _ = (‖C.b t θ μ - C.b t θ' μ'‖ + ‖C.σ t θ μ - C.σ t θ' μ'‖
          + ‖C.h t θ μ - C.h t θ' μ'‖ + ‖C.f t θ μ - C.f t θ' μ'‖) * R := by ring
      _ ≤ Lₚ * W * R := mul_le_mul_of_nonneg_right h hR0
  have hWR : W * R ≤ (W ^ 2 + R ^ 2) / 2 := by nlinarith [sq_nonneg (W - R)]
  have hG := norm_nonneg (GX G)
  calc _ ≤ ‖GX G‖ * (Lₚ * W * R) := hCS.trans (mul_le_mul_of_nonneg_left hsum hG)
    _ = ‖GX G‖ * Lₚ * (W * R) := by ring
    _ ≤ ‖GX G‖ * Lₚ * ((W ^ 2 + R ^ 2) / 2) :=
        mul_le_mul_of_nonneg_left hWR (mul_nonneg hG hLp)
    _ = _ := by rw [hRsq]; ring

variable {Ω : Type*} [MeasurableSpace Ω] [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]

/-- **(3.5), the law-Lipschitz bound of a perturbation, along the diagonal**: for almost every
`t ∈ [0, T]` and any two strongly `ℱ_t`-measurable square-integrable tuples `Θ, Θ'` with laws
`μ, μ'`, almost surely
`|δp_b| + |δp_σ|_F + ‖δp_h‖_{L²(ν)} + |δp_f| ≤ L_p W₂(μ, μ')`,
with `W₂` the 2-Wasserstein distance on `P₂(H)` for the Hilbert norm of `H`. -/
def DiagonalLawLipschitzH (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (P : Measure Ω)
    [IsProbabilityMeasure P] (T Lₚ : ℝ) (p : Coeffs ν n m d) : Prop :=
  ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ Θ Θ' : Ω → TupleH ν n m d,
    StronglyMeasurable[ℱ t] Θ → StronglyMeasurable[ℱ t] Θ' → MemLp Θ 2 P → MemLp Θ' 2 P →
    ∀ᵐ ω ∂P, ‖p.b t (Θ ω) (lawP2 P Θ) - p.b t (Θ' ω) (lawP2 P Θ')‖
        + ‖p.σ t (Θ ω) (lawP2 P Θ) - p.σ t (Θ' ω) (lawP2 P Θ')‖
        + ‖p.h t (Θ ω) (lawP2 P Θ) - p.h t (Θ' ω) (lawP2 P Θ')‖
        + ‖p.f t (Θ ω) (lawP2 P Θ) - p.f t (Θ' ω) (lawP2 P Θ')‖
      ≤ Lₚ * w2H (lawP2 P Θ) (lawP2 P Θ')

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {P : Measure Ω} [IsProbabilityMeasure P]
  {T Lₚ : ℝ} {p : Coeffs ν n m d}

/-- **(3.5) gives Assumption 2.3** along the diagonal with the constant `L_p ≥ 0`. -/
theorem DiagonalLawLipschitzH.diagonalLipschitzH (h : DiagonalLawLipschitzH ℱ P T Lₚ p)
    (hLp : 0 ≤ Lₚ) : DiagonalLipschitzH ℱ P T Lₚ p := by
  filter_upwards [h] with t ht Θ Θ' hΘ hΘ' hΘ2 hΘ2'
  filter_upwards [ht Θ Θ' hΘ hΘ' hΘ2 hΘ2'] with ω hω
  have h0 : 0 ≤ tupleNorm (Θ ω - Θ' ω) := by unfold tupleNorm; positivity
  nlinarith

/-- **(3.5) gives (3.4) with `c_pert = ‖G‖ L_p`** (Corollary 3.6): for a perturbation independent
of the tuple satisfying (3.5) with constant `L_p ≥ 0`, along the diagonal the pairing of the
perturbation is integrable and
`𝔼[⟨δp_b, Gᵀ δY⟩ + ⟨δp_σ, Gᵀ δZ⟩_F − ⟨δp_f, G δX⟩ + ∫_E ⟨δp_h(e), Gᵀ δU(e)⟩ ν(de)]
  ≤ ‖G‖ L_p 𝔼[|δX|² + |δY|² + |δZ|²_F + ‖δU‖²_{L²(ν)}]`,
with `‖G‖` the operator norm of `GX G`. -/
theorem DiagonalLawLipschitzH.diagonalPairingBound (h : DiagonalLawLipschitzH ℱ P T Lₚ p)
    (hind : p.TupleIndep) (hLp : 0 ≤ Lₚ) (G : Matrix (Fin m) (Fin n) ℝ) :
    DiagonalPairingBound ℱ P T G (‖GX G‖ * Lₚ) p := by
  filter_upwards [h] with t ht Θ Θ' hΘ hΘ' hΘ2 hΘ2'
  set μ := lawP2 P Θ
  set μ' := lawP2 P Θ'
  set W := w2H μ μ' with hWdef
  have hW0 : 0 ≤ W := w2H_nonneg _ _
  have hW2 : W ^ 2 ≤ ∫ ω, channelSq (Θ ω - Θ' ω) ∂P := w2H_lawP2_sq_le hΘ2 hΘ2'
  have hQi := integrable_channelSq_sub hΘ2 hΘ2'
  have hbound : ∀ᵐ ω ∂P, |interiorPairing (GX G) (GZ G) (GU G ν)
      (diagDiff p t (Θ ω) (Θ' ω) μ μ')|
        ≤ ‖GX G‖ * Lₚ * (W ^ 2 + channelSq (Θ ω - Θ' ω)) / 2 := by
    filter_upwards [ht Θ Θ' hΘ hΘ' hΘ2 hΘ2'] with ω hω
    exact abs_interiorPairing_diagDiff_le G p t _ _ _ _ hLp hω
  have hcont : Continuous fun q : TupleH ν n m d × TupleH ν n m d =>
      interiorPairing (GX G) (GZ G) (GU G ν)
        ({ δX := q.1.1 - q.2.1
           δY := q.1.2.1 - q.2.2.1
           δZ := q.1.2.2.1 - q.2.2.2.1
           δU := q.1.2.2.2 - q.2.2.2.2
           δb := p.b t 0 μ - p.b t 0 μ'
           δσ := p.σ t 0 μ - p.σ t 0 μ'
           δh := p.h t 0 μ - p.h t 0 μ'
           δf := p.f t 0 μ - p.f t 0 μ' } : ChannelDiff _ _ _ _ _ _) := by
    unfold interiorPairing
    fun_prop
  have hmeas : AEStronglyMeasurable (fun ω => interiorPairing (GX G) (GZ G) (GU G ν)
      (diagDiff p t (Θ ω) (Θ' ω) μ μ')) P := by
    refine (hcont.comp_aestronglyMeasurable
      (hΘ2.aestronglyMeasurable.prodMk hΘ2'.aestronglyMeasurable)).congr
      (ae_of_all _ fun ω => ?_)
    simp only [hind.diagDiff_eq]
  have hgi : Integrable (fun ω => ‖GX G‖ * Lₚ * (W ^ 2 + channelSq (Θ ω - Θ' ω)) / 2) P :=
    (((integrable_const (W ^ 2)).add hQi).const_mul (‖GX G‖ * Lₚ)).div_const 2
  have hpi : Integrable (fun ω => interiorPairing (GX G) (GZ G) (GU G ν)
      (diagDiff p t (Θ ω) (Θ' ω) μ μ')) P :=
    hgi.mono' hmeas (hbound.mono fun ω hω => by rwa [Real.norm_eq_abs])
  refine ⟨hpi, ?_⟩
  calc ∫ ω, interiorPairing (GX G) (GZ G) (GU G ν) (diagDiff p t (Θ ω) (Θ' ω) μ μ') ∂P
      ≤ ∫ ω, ‖GX G‖ * Lₚ * (W ^ 2 + channelSq (Θ ω - Θ' ω)) / 2 ∂P :=
        integral_mono_ae hpi hgi (hbound.mono fun ω hω => (le_abs_self _).trans hω)
    _ = ‖GX G‖ * Lₚ * (W ^ 2 + ∫ ω, channelSq (Θ ω - Θ' ω) ∂P) / 2 := by
        rw [integral_div, integral_const_mul, integral_add (integrable_const _) hQi,
          integral_const, probReal_univ, one_smul]
    _ ≤ ‖GX G‖ * Lₚ * ∫ ω, channelSq (Θ ω - Θ' ω) ∂P := by
        have hK : 0 ≤ ‖GX G‖ * Lₚ := mul_nonneg (norm_nonneg _) hLp
        nlinarith

end Dissertation.WellPosedness.System
