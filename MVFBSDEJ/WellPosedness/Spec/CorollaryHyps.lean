/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Spec.Bridge25
import MVFBSDEJ.WellPosedness.Robustness.Regular

/-!
# The hypotheses of Corollary 3.6, as printed

Corollary 3.6 of the paper assumes, besides Assumptions 2.2–2.5 for the baseline `C`, the
interior inequality with a margin `c_diss > 0` in the unweighted form (2.13),

`𝔼[⟨δb, Gᵀ δY⟩ + ⟨δσ, Gᵀ δZ⟩_F + ⟨−δf, G δX⟩ + ∫_E ⟨δh(e), Gᵀ δU(e)⟩ ν(de)]
  ≤ −β₁ 𝔼[|Gᵀ δY|² + |Gᵀ δZ|²_F + ‖Gᵀ δU‖²_{L²(ν)}] − β₂ 𝔼|G δX|²
    − c 𝔼[|δY|² + |δZ|²_F + ‖δU‖²_{L²(ν)} + |δX|²]`,

and, for the perturbation `p`, the pairing bound (3.4),

`𝔼[⟨δp_b, Gᵀ δY⟩ + ⟨δp_σ, Gᵀ δZ⟩_F + ⟨−δp_f, G δX⟩ + ∫_E ⟨δp_h(e), Gᵀ δU(e)⟩ ν(de)]
  ≤ c_pert 𝔼[|δX|² + |δY|² + |δZ|²_F + ‖δU‖²_{L²(ν)}]`,

each for almost every `t ∈ [0, T]` and all `(Θ, μ), (Θ', μ') ∈ 𝒟_t`. As in Assumption 2.5, the
expectations of the pairings are required to exist.

## Main definitions

* `Margin213` — (2.13).
* `PairingBound34` — (3.4).

## Main statements

* `Margin213.diagonalMonotoneMargin`, `margin213_iff` — (2.13) as printed gives
  `MVFBSDEJ.WellPosedness.System.DiagonalMonotoneMargin` with the same constants, and for
  `c > 0`, `β₁, β₂ ≥ 0` the two are equivalent.
* `pairingBound34_iff`, `PairingBound34.diagonalPairingBound` — (3.4) as printed is
  `MVFBSDEJ.WellPosedness.System.DiagonalPairingBound`.
-/

open MeasureTheory Filter MVFBSDEJ.Law Matrix

namespace MVFBSDEJ.WellPosedness.Spec

open MVFBSDEJ.WellPosedness.System MVFBSDEJ.WellPosedness.Existence

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}

/-- **(2.13)**, the interior inequality with the margin `c` in the unweighted form: for almost
every `t ∈ [0, T]` and all `(Θ, μ), (Θ', μ') ∈ 𝒟_t`, the expectation of the pairing exists and
is at most `−β₁ 𝔼[|Gᵀ δY|² + |Gᵀ δZ|²_F + ‖Gᵀ δU‖²_{L²(ν)}] − β₂ 𝔼|G δX|²
− c 𝔼[|δY|² + |δZ|²_F + ‖δU‖²_{L²(ν)} + |δX|²]`. -/
def Margin213 (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (P : Measure Ω) [IsProbabilityMeasure P]
    (T : ℝ) (G : Matrix (Fin m) (Fin n) ℝ) (β₁ β₂ c : ℝ) (C : Coeffs ν n m d) : Prop :=
  ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
    ∀ p ∈ diagonalInputs ν n m d ℱ P t, ∀ p' ∈ diagonalInputs ν n m d ℱ P t,
      Integrable (fun ω => pairing27 G C t (p.1 ω) (p'.1 ω) p.2 p'.2) P
        ∧ ∫ ω, pairing27 G C t (p.1 ω) (p'.1 ω) p.2 p'.2 ∂P
          ≤ -β₁ * ∫ ω, (‖GX Gᵀ ((p.1 ω).2.1 - (p'.1 ω).2.1)‖ ^ 2
              + ‖GZ Gᵀ ((p.1 ω).2.2.1 - (p'.1 ω).2.2.1)‖ ^ 2
              + ‖GU Gᵀ ν ((p.1 ω).2.2.2 - (p'.1 ω).2.2.2)‖ ^ 2) ∂P
            - β₂ * ∫ ω, ‖GX G ((p.1 ω).1 - (p'.1 ω).1)‖ ^ 2 ∂P
            - c * ∫ ω, (‖(p.1 ω).2.1 - (p'.1 ω).2.1‖ ^ 2 + ‖(p.1 ω).2.2.1 - (p'.1 ω).2.2.1‖ ^ 2
              + ‖(p.1 ω).2.2.2 - (p'.1 ω).2.2.2‖ ^ 2 + ‖(p.1 ω).1 - (p'.1 ω).1‖ ^ 2) ∂P

/-- **(3.4)**, the pairing bound of the perturbation `p` with the constant `c`: for almost every
`t ∈ [0, T]` and all `(Θ, μ), (Θ', μ') ∈ 𝒟_t`, the expectation of the pairing of the
perturbation differences exists and is at most
`c 𝔼[|δX|² + |δY|² + |δZ|²_F + ‖δU‖²_{L²(ν)}]`. -/
def PairingBound34 (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (P : Measure Ω)
    [IsProbabilityMeasure P] (T : ℝ) (G : Matrix (Fin m) (Fin n) ℝ) (c : ℝ)
    (p : Coeffs ν n m d) : Prop :=
  ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
    ∀ q ∈ diagonalInputs ν n m d ℱ P t, ∀ q' ∈ diagonalInputs ν n m d ℱ P t,
      Integrable (fun ω => pairing27 G p t (q.1 ω) (q'.1 ω) q.2 q'.2) P
        ∧ ∫ ω, pairing27 G p t (q.1 ω) (q'.1 ω) q.2 q'.2 ∂P
          ≤ c * ∫ ω, (‖(q.1 ω).1 - (q'.1 ω).1‖ ^ 2 + ‖(q.1 ω).2.1 - (q'.1 ω).2.1‖ ^ 2
              + ‖(q.1 ω).2.2.1 - (q'.1 ω).2.2.1‖ ^ 2 + ‖(q.1 ω).2.2.2 - (q'.1 ω).2.2.2‖ ^ 2) ∂P

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {P : Measure Ω} [IsProbabilityMeasure P]
  {T β₁ β₂ c : ℝ} {G : Matrix (Fin m) (Fin n) ℝ} {C p : Coeffs ν n m d}

omit [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] [IsProbabilityMeasure P] in
/-- The unweighted quantity of (2.13), in the printed order, is `channelSq` of the difference. -/
theorem integral_margin_eq (Θ Θ' : Ω → TupleH ν n m d) :
    ∫ ω, (‖(Θ ω).2.1 - (Θ' ω).2.1‖ ^ 2 + ‖(Θ ω).2.2.1 - (Θ' ω).2.2.1‖ ^ 2
        + ‖(Θ ω).2.2.2 - (Θ' ω).2.2.2‖ ^ 2 + ‖(Θ ω).1 - (Θ' ω).1‖ ^ 2) ∂P
      = ∫ ω, channelSq (Θ ω - Θ' ω) ∂P := by
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  simp only [channelSq, Prod.fst_sub, Prod.snd_sub]
  ring

/-- **(2.13) as printed gives `DiagonalMonotoneMargin`** with the same constants. -/
theorem Margin213.diagonalMonotoneMargin (h : Margin213 ℱ P T G β₁ β₂ c C) :
    DiagonalMonotoneMargin ℱ P T G β₁ β₂ c C := by
  filter_upwards [h] with t ht Θ Θ' hΘ hΘ' hΘ2 hΘ2'
  have key := (ht (Θ, lawP2 P Θ) (mk_mem_diagonalInputs hΘ hΘ2) (Θ', lawP2 P Θ')
    (mk_mem_diagonalInputs hΘ' hΘ2')).2
  rw [integral_dissipation_eq hΘ2 hΘ2', ← integral_margin_eq]
  simpa only [pairing27_eq] using key

/-- **For a positive margin, (2.13) as printed is `DiagonalMonotoneMargin`**, with the same
constants, `β₁, β₂ ≥ 0`: the margin forces the pairing to be integrable. -/
theorem margin213_iff (hc : 0 < c) (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂) :
    Margin213 ℱ P T G β₁ β₂ c C ↔ DiagonalMonotoneMargin ℱ P T G β₁ β₂ c C := by
  refine ⟨Margin213.diagonalMonotoneMargin, fun h => ?_⟩
  filter_upwards [h, h.integrable hc hβ₁ hβ₂] with t ht hi p hp p' hp'
  obtain ⟨hs, h2, he⟩ := hp
  obtain ⟨hs', h2', he'⟩ := hp'
  rw [he, he']
  refine ⟨by simpa only [pairing27_eq] using hi p.1 p'.1 hs hs' h2 h2', ?_⟩
  rw [integral_margin_eq, ← integral_dissipation_eq h2 h2']
  simpa only [pairing27_eq] using ht p.1 p'.1 hs hs' h2 h2'

/-- **(3.4) as printed is `DiagonalPairingBound`**, with the same constant. -/
theorem pairingBound34_iff : PairingBound34 ℱ P T G c p ↔ DiagonalPairingBound ℱ P T G c p := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · filter_upwards [h] with t ht Θ Θ' hΘ hΘ' hΘ2 hΘ2'
    simpa only [pairing27_eq, channelSq, Prod.fst_sub, Prod.snd_sub] using
      ht (Θ, lawP2 P Θ) (mk_mem_diagonalInputs hΘ hΘ2) (Θ', lawP2 P Θ')
        (mk_mem_diagonalInputs hΘ' hΘ2')
  · filter_upwards [h] with t ht q hq q' hq'
    obtain ⟨hs, h2, he⟩ := hq
    obtain ⟨hs', h2', he'⟩ := hq'
    rw [he, he']
    simpa only [pairing27_eq, channelSq, Prod.fst_sub, Prod.snd_sub] using
      ht q.1 q'.1 hs hs' h2 h2'

/-- **(3.4) as printed gives `DiagonalPairingBound`**, with the same constant. -/
theorem PairingBound34.diagonalPairingBound (h : PairingBound34 ℱ P T G c p) :
    DiagonalPairingBound ℱ P T G c p :=
  pairingBound34_iff.mp h

end MVFBSDEJ.WellPosedness.Spec
