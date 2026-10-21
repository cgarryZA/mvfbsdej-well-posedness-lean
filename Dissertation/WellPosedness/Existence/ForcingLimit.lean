/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Existence.ForcingAlgebra

/-!
# The limit of a Cauchy sequence of forcings

The continuation argument of the existence proof takes its fixed point on the space of forcings
`q = (q^b, q^σ, q^h, q^f, q^g_T)` of the `λ`-system (4.1), measured by the data size of (4.14)
with zero initial datum,

`‖q‖² = 𝔼|q^g_T|² + 𝔼 ∫_0^T (|q^b|² + |q^σ|²_F + ‖q^h‖²_{L²(ν)} + |q^f|²)`.

That space is complete: a sequence of forcings that is Cauchy for this size has a limit which is
again a forcing. Each process component is Cauchy for its energy, so it has a limit that is
jointly and progressively measurable (marked progressively measurable for `q^h`) and vanishes
off `[0, T]`, the pointwise `limsup` of an almost everywhere convergent subsequence. The terminal
component is Cauchy in `L²(P)`; the `limsup` of an almost surely convergent subsequence of
strongly `ℱ_T`-measurable random variables is again strongly `ℱ_T`-measurable, and it
represents the `L²(P)` limit.

## Main statements

* `exists_stronglyMeasurable_sq_limit` — a Cauchy sequence in `L²(P)` of strongly
  `m`-measurable random variables has a strongly `m`-measurable limit.
* `le_dataSize` — each component of the data size is at most the data size.
* `dataSize_initial_sub_self` — the data size of a difference with equal initial data.
* `exists_forcing_limit` — a data-size Cauchy sequence of forcings has a forcing as limit.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace Dissertation.WellPosedness.Existence

open Dissertation.WellPosedness.Stability Dissertation.WellPosedness.System LevyStochCalc

universe u v

/-! ### The terminal component -/

section Terminal

variable {Ω : Type u} {m : MeasurableSpace Ω} [MeasurableSpace Ω] {P : Measure Ω}

/-- **A Cauchy sequence in `L²(P)` of strongly `m`-measurable random variables has a strongly
`m`-measurable limit**: if `𝔼|g_a − g_b|² → 0` as `a, b → ∞` for square-integrable, strongly
`m`-measurable `g_a`, there is a square-integrable, strongly `m`-measurable `g` with
`𝔼|g_a − g|² → 0`. -/
theorem exists_stronglyMeasurable_sq_limit {g : ℕ → Ω → ℝ}
    (hs : ∀ a, StronglyMeasurable[m] (g a)) (hL : ∀ a, MemLp (g a) 2 P)
    (hcau : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ a, N ≤ a → ∀ b, N ≤ b →
      ∫⁻ ω, (‖g a ω - g b ω‖₊ : ℝ≥0∞) ^ 2 ∂P < ε) :
    ∃ g' : Ω → ℝ, StronglyMeasurable[m] g' ∧ MemLp g' 2 P
      ∧ Tendsto (fun a => ∫⁻ ω, (‖g a ω - g' ω‖₊ : ℝ≥0∞) ^ 2 ∂P) atTop (𝓝 0) := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  have hcs : CauchySeq fun a => (hL a).toLp (g a) := by
    rw [EMetric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hcau (ε ^ 2) (by positivity)
    refine ⟨N, fun a ha b hb => ?_⟩
    rw [Lp.edist_def]
    have hcongr : eLpNorm (((hL a).toLp (g a) : Ω → ℝ) - ((hL b).toLp (g b) : Ω → ℝ)) 2 P
        = eLpNorm (fun ω => g a ω - g b ω) 2 P := by
      refine eLpNorm_congr_ae ?_
      filter_upwards [(hL a).coeFn_toLp, (hL b).coeFn_toLp] with ω h1 h2
      simp only [Pi.sub_apply]
      rw [h1, h2]
    rw [hcongr]
    by_contra hge
    have hsq : ε ^ 2 ≤ eLpNorm (fun ω => g a ω - g b ω) 2 P ^ 2 :=
      pow_le_pow_left' (not_lt.mp hge) 2
    have hlt := hN a ha b hb
    rw [← Brownian.Ito.eLpNorm_sq_eq_lintegral] at hlt
    exact absurd hlt (not_lt.mpr hsq)
  obtain ⟨G, hG⟩ := cauchySeq_tendsto_of_complete hcs
  have hlim : Tendsto (fun a => eLpNorm (g a - ⇑G) 2 P) atTop (𝓝 0) := by
    refine ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ G).mp hG).congr fun a => ?_
    refine eLpNorm_congr_ae ?_
    filter_upwards [(hL a).coeFn_toLp] with ω h1
    simp only [Pi.sub_apply]
    rw [h1]
  obtain ⟨ns, -, hae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num)
    (fun a => (hL a).aestronglyMeasurable) (Lp.memLp G).aestronglyMeasurable
    hlim).exists_seq_tendsto_ae
  have hg'm : StronglyMeasurable[m] fun ω => limsup (fun i => g (ns i) ω) atTop := by
    letI := m
    exact (Measurable.limsup fun i => (hs (ns i)).measurable).stronglyMeasurable
  have hg'G : (fun ω => limsup (fun i => g (ns i) ω) atTop) =ᵐ[P] G := by
    filter_upwards [hae] with ω hω
    exact hω.limsup_eq
  refine ⟨fun ω => limsup (fun i => g (ns i) ω) atTop, hg'm, (Lp.memLp G).ae_eq hg'G.symm, ?_⟩
  have hEq : ∀ a, ∫⁻ ω, (‖g a ω - limsup (fun i => g (ns i) ω) atTop‖₊ : ℝ≥0∞) ^ 2 ∂P
      = eLpNorm (g a - ⇑G) 2 P ^ 2 := by
    intro a
    rw [Brownian.Ito.eLpNorm_sq_eq_lintegral]
    refine lintegral_congr_ae ?_
    filter_upwards [hg'G] with ω hω
    simp only [Pi.sub_apply, hω]
  simp only [hEq]
  have hcont : Continuous fun x : ℝ≥0∞ => x ^ 2 := ENNReal.continuous_pow 2
  simpa [Function.comp_def] using (hcont.tendsto 0).comp hlim

end Terminal

/-! ### The components of the data size -/

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {P : Measure Ω}
  {ν : Measure E} {T : ℝ} {n m d : ℕ}

/-- **Each component of the data size is at most the data size**: the terminal second moment,
and the energy of each coordinate of `q^b`, `q^σ`, `q^h` and `q^f`. -/
theorem le_dataSize (ξ₀ : Fin n → Ω → ℝ) (qb : Fin n → Ω → ℝ → ℝ)
    (qσ : Fin n → ℝ → Ω → Fin d → ℝ) (qh : Fin n → ℝ → Ω → E → ℝ) (qf : Fin m → Ω → ℝ → ℝ)
    (qg : Fin m → Ω → ℝ) :
    (∀ k, ∫⁻ ω, (‖qg k ω‖₊ : ℝ≥0∞) ^ 2 ∂P ≤ dataSize P ν T ξ₀ qb qσ qh qf qg)
      ∧ (∀ i, Brownian.Ito.energy P T (qb i) ≤ dataSize P ν T ξ₀ qb qσ qh qf qg)
      ∧ (∀ i j, Brownian.Ito.energy P T (fun ω s => qσ i s ω j)
        ≤ dataSize P ν T ξ₀ qb qσ qh qf qg)
      ∧ (∀ i, Poisson.Compensated.markedEnergy P ν T (fun ω s e => qh i s ω e)
        ≤ dataSize P ν T ξ₀ qb qσ qh qf qg)
      ∧ (∀ k, Brownian.Ito.energy P T (qf k) ≤ dataSize P ν T ξ₀ qb qσ qh qf qg) := by
  unfold dataSize
  refine ⟨fun k => ?_, fun i => ?_, fun i j => ?_, fun i => ?_, fun k => ?_⟩
  · refine le_trans ?_ (le_add_self.trans (le_self_add.trans
      (le_self_add.trans (le_self_add.trans le_self_add))))
    exact lintegral_mono fun ω => Finset.single_le_sum (f := fun k => (‖qg k ω‖₊ : ℝ≥0∞) ^ 2)
      (fun _ _ => zero_le) (Finset.mem_univ k)
  · exact (Finset.single_le_sum (f := fun i => Brownian.Ito.energy P T (qb i))
      (fun _ _ => zero_le) (Finset.mem_univ i)).trans
      (le_add_self.trans (le_self_add.trans (le_self_add.trans le_self_add)))
  · exact ((Finset.single_le_sum (f := fun j => Brownian.Ito.energy P T (fun ω s => qσ i s ω j))
      (fun _ _ => zero_le) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, Brownian.Ito.energy P T (fun ω s => qσ i s ω j))
        (fun _ _ => zero_le) (Finset.mem_univ i))).trans
      (le_add_self.trans (le_self_add.trans le_self_add))
  · exact (Finset.single_le_sum
      (f := fun i => Poisson.Compensated.markedEnergy P ν T (fun ω s e => qh i s ω e))
      (fun _ _ => zero_le) (Finset.mem_univ i)).trans (le_add_self.trans le_self_add)
  · exact (Finset.single_le_sum (f := fun k => Brownian.Ito.energy P T (qf k))
      (fun _ _ => zero_le) (Finset.mem_univ k)).trans le_add_self

/-- **Equal initial data contribute nothing to the data size**: the data size of a difference
with initial datum `ξ₀ − ξ₀` is that with the zero initial datum. -/
theorem dataSize_initial_sub_self (ξ₀ : Fin n → Ω → ℝ) (qb : Fin n → Ω → ℝ → ℝ)
    (qσ : Fin n → ℝ → Ω → Fin d → ℝ) (qh : Fin n → ℝ → Ω → E → ℝ) (qf : Fin m → Ω → ℝ → ℝ)
    (qg : Fin m → Ω → ℝ) :
    dataSize P ν T (fun i ω => ξ₀ i ω - ξ₀ i ω) qb qσ qh qf qg
      = dataSize P ν T 0 qb qσ qh qf qg := by
  simp only [sub_self]
  rfl

/-! ### The limit forcing -/

variable [SigmaFinite ν] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

/-- **A data-size Cauchy sequence of forcings has a forcing as limit.** Let `qᵃ`, `a ∈ ℕ`, be
forcings over `ℱ` such that the data size of `qᵃ − qᵇ` with zero initial datum tends to `0` as
`a, b → ∞`. Then there is a forcing `q` such that the data size of `qᵃ − q` with zero initial
datum tends to `0`. -/
theorem exists_forcing_limit {qb : ℕ → Fin n → Ω → ℝ → ℝ} {qσ : ℕ → Fin n → ℝ → Ω → Fin d → ℝ}
    {qh : ℕ → Fin n → ℝ → Ω → E → ℝ} {qf : ℕ → Fin m → Ω → ℝ → ℝ} {qg : ℕ → Fin m → Ω → ℝ}
    (hF : ∀ a, Forcing ℱ P ν T (qb a) (qσ a) (qh a) (qf a) (qg a))
    (hcau : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ a, N ≤ a → ∀ b, N ≤ b →
      dataSize P ν T 0 (fun i ω s => qb a i ω s - qb b i ω s)
        (fun i s ω j => qσ a i s ω j - qσ b i s ω j)
        (fun i s ω e => qh a i s ω e - qh b i s ω e) (fun k ω s => qf a k ω s - qf b k ω s)
        (fun k ω => qg a k ω - qg b k ω) < ε) :
    ∃ (qb' : Fin n → Ω → ℝ → ℝ) (qσ' : Fin n → ℝ → Ω → Fin d → ℝ)
      (qh' : Fin n → ℝ → Ω → E → ℝ) (qf' : Fin m → Ω → ℝ → ℝ) (qg' : Fin m → Ω → ℝ),
      Forcing ℱ P ν T qb' qσ' qh' qf' qg'
        ∧ Tendsto (fun a => dataSize P ν T 0 (fun i ω s => qb a i ω s - qb' i ω s)
            (fun i s ω j => qσ a i s ω j - qσ' i s ω j)
            (fun i s ω e => qh a i s ω e - qh' i s ω e) (fun k ω s => qf a k ω s - qf' k ω s)
            (fun k ω => qg a k ω - qg' k ω)) atTop (𝓝 0) := by
  -- each component is Cauchy
  have hc : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ a, N ≤ a → ∀ b, N ≤ b →
      (∀ k, ∫⁻ ω, (‖qg a k ω - qg b k ω‖₊ : ℝ≥0∞) ^ 2 ∂P < ε)
      ∧ (∀ i, Brownian.Ito.energy P T (fun ω s => qb a i ω s - qb b i ω s) < ε)
      ∧ (∀ i j, Brownian.Ito.energy P T (fun ω s => qσ a i s ω j - qσ b i s ω j) < ε)
      ∧ (∀ i, Poisson.Compensated.markedEnergy P ν T
        (fun ω s e => qh a i s ω e - qh b i s ω e) < ε)
      ∧ (∀ k, Brownian.Ito.energy P T (fun ω s => qf a k ω s - qf b k ω s) < ε) := by
    intro ε hε
    obtain ⟨N, hN⟩ := hcau ε hε
    refine ⟨N, fun a ha b hb => ?_⟩
    obtain ⟨h1, h2, h3, h4, h5⟩ := le_dataSize (P := P) (ν := ν) (T := T) 0
      (fun i ω s => qb a i ω s - qb b i ω s) (fun i s ω j => qσ a i s ω j - qσ b i s ω j)
      (fun i s ω e => qh a i s ω e - qh b i s ω e) (fun k ω s => qf a k ω s - qf b k ω s)
      (fun k ω => qg a k ω - qg b k ω)
    have hlt := hN a ha b hb
    exact ⟨fun k => (h1 k).trans_lt hlt, fun i => (h2 i).trans_lt hlt,
      fun i j => (h3 i j).trans_lt hlt, fun i => (h4 i).trans_lt hlt,
      fun k => (h5 k).trans_lt hlt⟩
  -- the limits of the components
  choose Kb hKbm hKbp hKbz hKbf hKbt using fun i =>
    Brownian.Ito.exists_progressive_energy_limit ℱ (P := P) (T := T) (H := fun a => qb a i)
      (fun a => (hF a).qb_meas i) (fun a => (hF a).qb_prog i) (fun a => (hF a).qb_vanish i)
      (fun a => (hF a).qb_sq i) fun ε hε =>
        let ⟨N, hN⟩ := hc ε hε
        ⟨N, fun a ha b hb => (hN a ha b hb).2.1 i⟩
  choose Kσ hKσm hKσp hKσz hKσf hKσt using fun i j =>
    Brownian.Ito.exists_progressive_energy_limit ℱ (P := P) (T := T)
      (H := fun a ω s => qσ a i s ω j) (fun a => (hF a).qσ_meas i j)
      (fun a => (hF a).qσ_prog i j)
      (fun a ω s hs => by simp only [(hF a).qσ_vanish i ω s hs, Pi.zero_apply])
      (fun a => (hF a).qσ_sq i j) fun ε hε =>
        let ⟨N, hN⟩ := hc ε hε
        ⟨N, fun a ha b hb => (hN a ha b hb).2.2.1 i j⟩
  choose Kh hKhm hKhp hKhz hKhf hKht using fun i =>
    Poisson.Compensated.exists_marked_progressive_energy_limit ℱ (P := P) (ν := ν) (T := T)
      (φ := fun a ω s e => qh a i s ω e) (fun a => (hF a).qh_meas i)
      (fun a => (hF a).qh_prog i) (fun a ω s e hs => (hF a).qh_vanish i ω s e hs)
      (fun a => (hF a).qh_sq i) fun ε hε =>
        let ⟨N, hN⟩ := hc ε hε
        ⟨N, fun a ha b hb => (hN a ha b hb).2.2.2.1 i⟩
  choose Kf hKfm hKfp hKfz hKff hKft using fun k =>
    Brownian.Ito.exists_progressive_energy_limit ℱ (P := P) (T := T) (H := fun a => qf a k)
      (fun a => (hF a).qf_meas k) (fun a => (hF a).qf_prog k) (fun a => (hF a).qf_vanish k)
      (fun a => (hF a).qf_sq k) fun ε hε =>
        let ⟨N, hN⟩ := hc ε hε
        ⟨N, fun a ha b hb => (hN a ha b hb).2.2.2.2 k⟩
  choose Kg hKgm hKgL hKgt using fun k =>
    exists_stronglyMeasurable_sq_limit (m := ℱ T) (P := P) (g := fun a => qg a k)
      (fun a => (hF a).qg_meas k) (fun a => (hF a).qg_sq k) fun ε hε =>
        let ⟨N, hN⟩ := hc ε hε
        ⟨N, fun a ha b hb => (hN a ha b hb).1 k⟩
  refine ⟨Kb, fun i s ω j => Kσ i j ω s, fun i s ω e => Kh i ω s e, Kf, Kg, ?_, ?_⟩
  · exact
      { qb_meas := hKbm
        qb_prog := hKbp
        qb_vanish := hKbz
        qb_sq := hKbf
        qσ_meas := hKσm
        qσ_prog := hKσp
        qσ_vanish := fun i ω s hs => funext fun j => hKσz i j ω s hs
        qσ_sq := hKσf
        qh_meas := hKhm
        qh_prog := hKhp
        qh_vanish := fun i ω s e hs => hKhz i ω s e hs
        qh_sq := hKhf
        qf_meas := hKfm
        qf_prog := hKfp
        qf_vanish := hKfz
        qf_sq := hKff
        qg_meas := hKgm
        qg_sq := hKgL }
  · have h0 : Tendsto (fun _ : ℕ => ∫⁻ ω, esq (fun i => (0 : Fin n → Ω → ℝ) i ω) ∂P) atTop
        (𝓝 0) := by
      simp [esq]
    have hg : Tendsto (fun a => ∫⁻ ω, esq (fun k => qg a k ω - Kg k ω) ∂P) atTop (𝓝 0) := by
      have e : ∀ a, ∫⁻ ω, esq (fun k => qg a k ω - Kg k ω) ∂P
          = ∑ k, ∫⁻ ω, (‖qg a k ω - Kg k ω‖₊ : ℝ≥0∞) ^ 2 ∂P := fun a => by
        unfold esq
        exact lintegral_finsetSum' _ fun k _ =>
          (((hF a).qg_sq k).sub (hKgL k)).aestronglyMeasurable.aemeasurable.nnnorm
            |>.coe_nnreal_ennreal.pow_const 2
      simp only [e]
      simpa using tendsto_finsetSum Finset.univ fun k _ => hKgt k
    have hb : Tendsto (fun a => ∑ i, Brownian.Ito.energy P T
        (fun ω s => qb a i ω s - Kb i ω s)) atTop (𝓝 0) := by
      simpa using tendsto_finsetSum Finset.univ fun i _ => hKbt i
    have hσ : Tendsto (fun a => ∑ i, ∑ j, Brownian.Ito.energy P T
        (fun ω s => qσ a i s ω j - Kσ i j ω s)) atTop (𝓝 0) := by
      simpa using tendsto_finsetSum Finset.univ fun i _ =>
        (tendsto_finsetSum Finset.univ fun j _ => hKσt i j)
    have hh : Tendsto (fun a => ∑ i, Poisson.Compensated.markedEnergy P ν T
        (fun ω s e => qh a i s ω e - Kh i ω s e)) atTop (𝓝 0) := by
      simpa using tendsto_finsetSum Finset.univ fun i _ => hKht i
    have hf : Tendsto (fun a => ∑ k, Brownian.Ito.energy P T
        (fun ω s => qf a k ω s - Kf k ω s)) atTop (𝓝 0) := by
      simpa using tendsto_finsetSum Finset.univ fun k _ => hKft k
    have key := ((((h0.add hg).add hb).add hσ).add hh).add hf
    simp only [add_zero] at key
    exact key

end Dissertation.WellPosedness.Existence
