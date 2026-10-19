/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.PaperSpec.A.Sec5DealerActive
import Dissertation.Acceptance.A.Sec5Dealer
import Dissertation.WellPosedness.Examples.Dealer.Riccati
import Dissertation.WellPosedness.Examples.Dealer.Depends
import Dissertation.WellPosedness.Examples.Dealer.MarkSizes

/-!
# Example 5.5 of the well-posedness paper: the interaction is active, proofs

## Main statements

* `Dissertation.Acceptance.A.ex_dealer_riccati` — the Riccati function.
* `Dissertation.Acceptance.A.ex_dealer_inert` — without the exposure term the interaction is
  inert.
* `Dissertation.Acceptance.A.ex_dealer_spec_marks` — the marks of the specialisation.
* `Dissertation.Acceptance.A.ex_dealer_zero` — the linear equation, `Θ⁰` and its moments.
* `Dissertation.Acceptance.A.ex_dealer_symm` — the symmetrised crowding pairing.
* `Dissertation.Acceptance.A.ex_dealer_active` — the interaction is active.
* `Dissertation.Acceptance.A.ex_dealer_depends` — the solution depends on `ε`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal RealInnerProductSpace

namespace Dissertation.Acceptance.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence
  Dissertation.WellPosedness.Enlarged Dissertation.WellPosedness.Spec Dissertation.Law
  Dissertation.WellPosedness.Stability

universe u v w

/-- Example 5.5, the Riccati function. -/
theorem ex_dealer_riccati : PaperSpec.A.ex_dealer_riccati := by
  intro β₁ β₂ T hβ₁ hβ₂ _
  exact ⟨exists_pos_riccati hβ₁ hβ₂, fun p q hp hpT hq hqT =>
    riccati_unique hβ₁.le hp hq (hpT.trans hqT.symm)⟩

/-- Example 5.5, without the exposure term the interaction is inert. -/
theorem ex_dealer_inert : PaperSpec.A.ex_dealer_inert.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ ν _ _ P _ D h𝒢₀ hind₀ T hT β₁ β₂ hβ₁ hβ₂ σc hc ε hε ξ₀ hξm hξ p hp hpT
    hp0
  refine ⟨(ex_dealer_wp 𝒢₀ ν P D h𝒢₀ hind₀ T hT β₁ β₂ hβ₁ hβ₂ σc hc 0 ε hε ξ₀ hξm hξ).1,
    fun X Y Z U hsol => ?_⟩
  obtain ⟨⟨γ, hPS⟩, hXl, hYl⟩ := hsol
  rw [ex55Coeffs_eq] at hPS
  obtain ⟨h1, h2, h3, h4, h5⟩ := PaperSolution.dealer_inert hPS (crossWitnessEnl D h𝒢₀ hind₀)
    (hF0_enlJoint D h𝒢₀) (fun _ hs h0 => measurableSet_enlJoint_of_null D h𝒢₀ hs h0) hT hβ₁ hε
    hp hpT hp0 (hXl 0) (hYl 0)
  refine ⟨h1, h2, h3, h4, fun ε' _ => ⟨⟨γ, ?_⟩, hXl, hYl⟩⟩
  rw [ex55Coeffs_eq]
  exact h5 ε'

/-- The signed size `ς q` of the mark of the specialisation. -/
private theorem signedSize_eq (e : DealerMark) :
    signedSize e = (if e.1 then 1 else -1) * (e.2 : ℝ) := rfl

/-- The constants of the specialisation: `c_{±1} = (2 − ϱ)/2` gives
`(c_{+1} + c_{−1}) / (2 − ϱ) = 1` and `c_{+1} − c_{−1} = 0`. -/
private theorem spec_moments {ϱ : ℝ} (hϱ0 : 0 < ϱ) (hϱ2 : ϱ < 2) :
    ∫ e, ((if e.1 then 1 else -1) * (e.2 : ℝ)) ^ 2 ∂PaperSpec.A.ex55Marks ϱ = 1
      ∧ ∫ e, (e.2 : ℝ) ^ 2 ∂PaperSpec.A.ex55Marks ϱ = 1
      ∧ ∫ e, (if e.1 then 1 else -1) * (e.2 : ℝ) * e.2 ∂PaperSpec.A.ex55Marks ϱ = 0 := by
  have hc : ∀ b : Bool, 0 ≤ (fun _ : Bool => (2 - ϱ) / 2) b := fun _ => by
    change 0 ≤ (2 - ϱ) / 2
    linarith
  have h1 := integral_signedSize_sq hc hϱ2
  have h2 := integral_markSize_sq hc hϱ2
  have h3 := integral_signedSize_mul_markSize hc hϱ2
  rw [rate_sum_div_eq_one hϱ2 (fun _ => rfl)] at h1 h2
  simp only [sub_self, zero_div] at h3
  exact ⟨h1, h2, h3⟩

/-- Example 5.5, the marks of the specialisation. -/
theorem ex_dealer_spec_marks : PaperSpec.A.ex_dealer_spec_marks := by
  intro ϱ hϱ0 hϱ2
  obtain ⟨h1, h2, h3⟩ := spec_moments hϱ0 hϱ2
  exact ⟨memLp_signedSize _ hϱ2, memLp_markSize _ hϱ2, h1, h2, h3⟩

/-- The data of the specialisation: the representatives of `h_c, h_x` are measurable and square
integrable with `∫ η_c² = ∫ η_x² = 1`, `∫ η_c η_x = 0`, and `‖h_x‖ = 1`, `⟨h_x, h_c⟩ = 0`. -/
private theorem spec_data {ϱ : ℝ} (hϱ0 : 0 < ϱ) (hϱ2 : ϱ < 2)
    {hc hx : Lp (EuclideanSpace ℝ (Fin 1)) 2 (PaperSpec.A.ex55Marks ϱ)}
    (hcr : ∀ᵐ e ∂PaperSpec.A.ex55Marks ϱ,
      hc e = EuclideanSpace.single 0 ((if e.1 then 1 else -1) * (e.2 : ℝ)))
    (hxr : ∀ᵐ e ∂PaperSpec.A.ex55Marks ϱ, hx e = EuclideanSpace.single 0 (e.2 : ℝ)) :
    Measurable (fun e : DealerMark => (if e.1 then 1 else -1) * (e.2 : ℝ))
      ∧ Measurable (fun e : DealerMark => (e.2 : ℝ))
      ∧ MemLp (fun e : DealerMark => (if e.1 then 1 else -1) * (e.2 : ℝ)) 2
        (PaperSpec.A.ex55Marks ϱ)
      ∧ MemLp (fun e : DealerMark => (e.2 : ℝ)) 2 (PaperSpec.A.ex55Marks ϱ)
      ∧ ‖hx‖ = 1 ∧ ⟪hx, hc⟫ = 0 := by
  obtain ⟨h1, h2, h3⟩ := spec_moments hϱ0 hϱ2
  have hq : Measurable fun e : DealerMark => (e.2 : ℝ) := measurable_subtype_coe.comp measurable_snd
  have hhx : ‖hx‖ = 1 := by
    have h := inner_eq_integral_of_rep hxr hxr
    rw [real_inner_self_eq_norm_sq] at h
    rw [show (fun e : DealerMark => (e.2 : ℝ) * e.2) = fun e => (e.2 : ℝ) ^ 2 from
      funext fun e => (sq _).symm, h2] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h
  have hxc : ⟪hx, hc⟫ = 0 := by
    rw [inner_eq_integral_of_rep hxr hcr]
    rw [show (fun e : DealerMark => (e.2 : ℝ) * ((if e.1 then 1 else -1) * (e.2 : ℝ)))
      = fun e => (if e.1 then 1 else -1) * (e.2 : ℝ) * e.2 from funext fun e => by ring, h3]
  exact ⟨((measurable_of_countable markSide).comp measurable_fst).mul hq, hq,
    memLp_signedSize _ hϱ2, memLp_markSize _ hϱ2, hhx, hxc⟩

/-- `σ_c = 1` in the coordinates of `ℝ^{1 × 1}`. -/
private theorem single_one_apply :
    (EuclideanSpace.single (0, 0) (1 : ℝ) : EuclideanSpace ℝ (Fin 1 × Fin 1)) (0, 0) = 1 := by
  simp [PiLp.single_apply]

/-- Example 5.5, the linear equation, the solution at `ε = 0` and its moments. -/
theorem ex_dealer_zero : PaperSpec.A.ex_dealer_zero.{u, w} := by
  intro Ω 𝒢₀ mΩ ϱ hϱ0 hϱ2 P _ D h𝒢₀ hind₀ T hT hc hx hcr hxr
  obtain ⟨hηcm, hηxm, hcm, hxm, hhx, hxc⟩ := spec_data hϱ0 hϱ2 hcr hxr
  obtain ⟨hηc, hηx, hηcx⟩ := spec_moments hϱ0 hϱ2
  have hηcx' : ∫ e, (if e.1 then 1 else -1) * (e.2 : ℝ) * (e.2 : ℝ) ∂PaperSpec.A.ex55Marks ϱ = 0 :=
    hηcx
  set 𝒲 := crossWitnessEnl D h𝒢₀ hind₀
  have hℱ0 := hF0_enlJoint D h𝒢₀
  have hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[enlJoint 𝒢₀ D h𝒢₀ 0] s :=
    fun _ hs h0 => measurableSet_enlJoint_of_null D h𝒢₀ hs h0
  refine ⟨?_, fun X₁ X₂ h₁ h₂ => DealerLinear.unique (ηc := fun e : DealerMark =>
    (if e.1 then 1 else -1) * (e.2 : ℝ)) (ηx := fun e : DealerMark => (e.2 : ℝ)) h₁ h₂ 𝒲 hT hηx,
    fun X0 hlin0 hXl => ?_⟩
  · -- existence, from the well-posedness of the system at `ε = 0`
    obtain ⟨X, Y, Z, U, ⟨γ, hPS⟩, hXl, -⟩ := (ex_dealer_wp 𝒢₀ (PaperSpec.A.ex55Marks ϱ) P D h𝒢₀
      hind₀ T hT 1 (1 / 2) one_pos one_half_pos (EuclideanSpace.single (0, 0) 1) hc hx 0
      le_rfl 0 stronglyMeasurable_const (memLp_const _)).1
    rw [ex55Coeffs_eq] at hPS
    obtain ⟨X', Y', hXX, -, hS⟩ := hPS.exists_solves hT.le
    have hX'l : ∀ ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ,
        Tendsto (fun s => X' 0 s ω) (𝓝[<] t) (𝓝 l) := by
      intro ω t ht
      obtain ⟨l, hl⟩ := hXl 0 ω t ht
      refine ⟨l, hl.congr' ?_⟩
      filter_upwards [Ioo_mem_nhdsLT ht.1] with r hr
      exact (congrFun (hXX 0 r ⟨hr.1.le, hr.2.le.trans ht.2⟩) ω).symm
    have hlin := Solves.dealerLinear hS 𝒲 hT single_one_apply hhx hxc hηcm hηxm hcm hxm hcr hxr
      hX'l
    refine ⟨X' 0, hlin, ?_, hX'l⟩
    have h := (hlin.linearBSDEJ hT.le).lintegral_biSup_sq_lt_top 𝒲 hℱ0 hnull hT
    refine lt_of_eq_of_lt (lintegral_congr fun ω => ?_) h
    refine iSup_congr fun t => iSup_congr fun _ => ?_
    rw [sq_nnnorm_eq_ofReal, sq]
  · -- `Θ⁰` and its moments
    have hlin : DealerLinear D (enlJoint 𝒢₀ D h𝒢₀) (isBrownianFiltration_enlJoint D h𝒢₀ hind₀)
        (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) T
        (fun e : DealerMark => (if e.1 then 1 else -1) * (e.2 : ℝ)) (fun e => (e.2 : ℝ)) X0 :=
      hlin0
    have hPS := DealerLinear.paperSolution hlin 𝒲 hℱ0 hnull hT single_one_apply hhx hxc hηcm hηxm
      hcm hxm hcr hxr hXl
    refine ⟨⟨⟨dealerZeroU T (fun e : DealerMark => (if e.1 then 1 else -1) * (e.2 : ℝ))
      (fun e => (e.2 : ℝ)) X0, ?_⟩, fun _ => hXl, fun _ => hXl⟩, hlin.expectation_eq_zero 𝒲 hT,
      hlin.integral_sq_eq 𝒲 hT hcm hxm hηc hηx hηcx',
      fun t ht => hlin.hasDerivAt_integral_sq 𝒲 hT hcm hxm hηc hηx hηcx' ht, fun t ht => ?_⟩
    · rw [ex55Coeffs_eq]
      exact hPS
    · obtain ⟨-, -, hvar, hD⟩ :=
        hlin.dealerU0_moments (hc := hc) 𝒲 hℱ0 hnull hT hcm hxm hηc hηx hηcx' hhx hXl ht
      have hv := hlin.integral_sq_eq 𝒲 hT hcm hxm hηc hηx hηcx' t (Set.Ioc_subset_Icc_self ht)
      refine ⟨hvar, ?_, hD⟩
      change (∫ ω, X0 t ω ^ 2 ∂P) / 4 = _
      rw [hv]
      ring

/-- Example 5.5, the symmetrised crowding pairing. -/
theorem ex_dealer_symm : PaperSpec.A.ex_dealer_symm.{v} := by
  intro E _ ν _ _ Λ
  have hΛ := integrable_norm_of_secondMoment_ne_top Λ.secondMoment_ne_top
  exact ⟨integral_inner_crowdOp_self Λ.law hΛ, crowdPairing_pos Λ.law hΛ⟩

/-- Example 5.5, the interaction is active. -/
theorem ex_dealer_active : PaperSpec.A.ex_dealer_active.{u, w} := by
  intro Ω 𝒢₀ mΩ ϱ hϱ0 hϱ2 P _ D h𝒢₀ hind₀ T hT hc hx hcr hxr
  obtain ⟨hηcm, hηxm, hcm, hxm, hhx, hxc⟩ := spec_data hϱ0 hϱ2 hcr hxr
  obtain ⟨hηc, hηx, hηcx⟩ := spec_moments hϱ0 hϱ2
  have hηcx' : ∫ e, (if e.1 then 1 else -1) * (e.2 : ℝ) * (e.2 : ℝ) ∂PaperSpec.A.ex55Marks ϱ = 0 :=
    hηcx
  set 𝒲 := crossWitnessEnl D h𝒢₀ hind₀
  have hℱ0 := hF0_enlJoint D h𝒢₀
  have hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[enlJoint 𝒢₀ D h𝒢₀ 0] s :=
    fun _ hs h0 => measurableSet_enlJoint_of_null D h𝒢₀ hs h0
  refine ⟨fun X0 hlin hXl t ht =>
    DealerLinear.crowd_ne_zero (ηc := fun e : DealerMark => (if e.1 then 1 else -1) * (e.2 : ℝ))
      (ηx := fun e : DealerMark => (e.2 : ℝ)) (hc := hc) hlin 𝒲 hℱ0 hnull hT hcm hxm hηc hηx
      hηcx' hhx hXl ht,
    fun ε hε X Y Z U hsol => ?_⟩
  obtain ⟨⟨γ, hPS⟩, hXl, hYl⟩ := hsol
  rw [ex55Coeffs_eq] at hPS
  exact PaperSolution.dealer_active hPS 𝒲 hℱ0 hnull hT single_one_apply hhx hxc hηcm hηxm hcm
    hxm hcr hxr hηc hηx hηcx' hε.ne' hXl hYl

/-- Example 5.5, a tuple solving the system at two strengths has vanishing crowding
correction. -/
theorem ex_dealer_depends_crowd {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    {E : Type v} [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν]
    [MeasurableSpace.CountablyGenerated E] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P 1 ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P) (T : ℝ) (hT : 0 < T) (β₁ β₂ : ℝ)
    (σc : EuclideanSpace ℝ (Fin 1 × Fin 1)) (hc hx : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν)
    (ε ε' : ℝ) (hεε : ε ≠ ε') (ξ₀ : Ω → EuclideanSpace ℝ (Fin 1)) (X : Fin 1 → ℝ → Ω → ℝ)
    (Y : Fin 1 → ℝ → Ω → ℝ) (Z : Fin 1 → ℝ → Ω → Fin 1 → ℝ) (U : Fin 1 → ℝ → Ω → E → ℝ)
    (h₁ : PaperSpec.A.Solution D h𝒢₀ hind₀ T (PaperSpec.A.ex55Coeffs ν β₁ β₂ σc hc hx ε) ξ₀
      X Y Z U)
    (h₂ : PaperSpec.A.Solution D h𝒢₀ hind₀ T (PaperSpec.A.ex55Coeffs ν β₁ β₂ σc hc hx ε') ξ₀
      X Y Z U) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P,
      PaperSpec.A.ex55Crowd
          (lawP2 P (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s)).margU.law
        (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s ω).2.2.2 = 0 := by
  obtain ⟨⟨γ₁, hPS₁⟩, -, -⟩ := h₁
  obtain ⟨⟨γ₂, hPS₂⟩, -, -⟩ := h₂
  rw [ex55Coeffs_eq] at hPS₁ hPS₂
  exact PaperSolution.dealer_crowd_eq_zero_of_two hPS₁ hPS₂ (crossWitnessEnl D h𝒢₀ hind₀) hT hεε

/-- Example 5.5, the solution depends on `ε`. -/
theorem ex_dealer_depends : PaperSpec.A.ex_dealer_depends.{u, v, w} := by
  refine ⟨?_, ?_⟩
  · intro Ω 𝒢₀ mΩ E _ ν _ _ P _ D h𝒢₀ hind₀ T hT β₁ β₂ σc hc hx ε ε' hεε ξ₀ X Y Z U h₁ h₂
    exact ex_dealer_depends_crowd 𝒢₀ ν P D h𝒢₀ hind₀ T hT β₁ β₂ σc hc hx ε ε' hεε ξ₀ X Y Z U h₁ h₂
  intro Ω 𝒢₀ mΩ ϱ hϱ0 hϱ2 P _ D h𝒢₀ hind₀ T hT hc hx hcr hxr ε ε' hε hε' hεε
  rintro ⟨X, Y, Z, U, h₁, h₂⟩
  have hA := ex_dealer_depends_crowd 𝒢₀ (PaperSpec.A.ex55Marks ϱ) P D h𝒢₀ hind₀ T hT 1 (1 / 2)
    _ hc hx ε ε' hεε 0 X Y Z U h₁ h₂
  -- one of the two strengths is positive
  obtain ⟨ε₀, hε₀, hsol⟩ : ∃ ε₀ : ℝ, 0 < ε₀ ∧ PaperSpec.A.Solution D h𝒢₀ hind₀ T
      (PaperSpec.A.ex55Coeffs (PaperSpec.A.ex55Marks ϱ) 1 (1 / 2)
        (EuclideanSpace.single (0, 0) 1) hc hx ε₀) 0 X Y Z U := by
    rcases hε.lt_or_eq with h | h
    · exact ⟨ε, h, h₁⟩
    · exact ⟨ε', lt_of_le_of_ne hε' (fun h' => hεε (h.symm.trans h')), h₂⟩
  have hpos := (ex_dealer_active 𝒢₀ ϱ hϱ0 hϱ2 P D h𝒢₀ hind₀ T hT hc hx hcr hxr).2 ε₀ hε₀ X Y Z U
    hsol
  obtain ⟨⟨γ, hPS⟩, hXl, hYl⟩ := hsol
  rw [ex55Coeffs_eq] at hPS
  have hΛ := PaperSolution.ae_margU_law_eq_map hPS (crossWitnessEnl D h𝒢₀ hind₀)
    (hF0_enlJoint D h𝒢₀) (fun _ hs h0 => measurableSet_enlJoint_of_null D h𝒢₀ hs h0) hT hXl hYl
  have h0 := (lintegral_crowd_eq_zero_iff (P := P) (T := T)
    (PaperSolution.measurable_uncurry_uLift hPS) hΛ ε₀).mpr (by
      filter_upwards [hA] with s hs
      filter_upwards [hs] with ω hω
      change ε₀ • crowdOp _ (tupleAt (PaperSpec.A.ex55Marks ϱ) (leftLimProc X) (leftLimProc Y)
        Z U s ω).2.2.2 = 0
      rw [← ex55Crowd_eq, hω, smul_zero])
  exact hpos.ne' h0

/-! ### The hypotheses hold -/

/-- **The hypotheses of the inert case of Example 5.5 hold.** With `c_{±1} = 1/2` and `ϱ = 1`,
the mark measure is σ-finite on a countably generated space with `ν(E) = ∞`; a probability space
carries a Lévy driver with `d = 1` and mark measure `ν`, with `𝒢₀ = ⊥` independent of it, the
initial datum `0` strongly measurable for the time-`0` field of `enlJoint ⊥ D` and square
integrable; `T = β₁ = β₂ = 1` and `ε = 0`; and for these constants a Riccati function `p` with
`p' = p² − 1` on `[0, 1]`, `p(1) = 1` and `p > 0` on `[0, 1]` exists. -/
theorem ex_dealer_inert_hypotheses :
    (SigmaFinite (dealerMarks (fun _ => 1 / 2) 1) ∧ MeasurableSpace.CountablyGenerated DealerMark
      ∧ dealerMarks (fun _ => 1 / 2) 1 Set.univ = ⊤
      ∧ ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
        (D : LevyStochCalc.Driver.LevyDriver P 1 (dealerMarks (fun _ => 1 / 2) 1)),
        Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P
        ∧ StronglyMeasurable[enlJoint ⊥ D bot_le 0] (fun _ : Ω => (0 : EuclideanSpace ℝ (Fin 1)))
        ∧ MemLp (fun _ : Ω => (0 : EuclideanSpace ℝ (Fin 1))) 2 P
        ∧ (0 : ℝ) < 1 ∧ (0 : ℝ) ≤ 1)
    ∧ ∃ p : ℝ → ℝ, (∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt p (1 * p t ^ 2 - 1) t) ∧ p 1 = 1
      ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < p t :=
  ⟨ex_dealer_hypotheses, exists_pos_riccati one_pos one_pos⟩

/-- **The hypotheses of the specialisation of Example 5.5 hold.** For `ϱ = 1`, `0 < ϱ < 2`; the
mark measure `ex55Marks 1` is σ-finite on a countably generated space; the classes `h_c, h_x` of
`ς q` and `q` exist with these representatives; and a probability space carries a Lévy driver
with `d = 1` and mark measure `ex55Marks 1`, with `𝒢₀ = ⊥` independent of it. -/
theorem ex_dealer_spec_hypotheses :
    (0 : ℝ) < 1 ∧ (1 : ℝ) < 2 ∧ SigmaFinite (PaperSpec.A.ex55Marks 1)
      ∧ MeasurableSpace.CountablyGenerated DealerMark
      ∧ (∃ hc hx : Lp (EuclideanSpace ℝ (Fin 1)) 2 (PaperSpec.A.ex55Marks 1),
        (∀ᵐ e ∂PaperSpec.A.ex55Marks 1,
          hc e = EuclideanSpace.single 0 ((if e.1 then 1 else -1) * (e.2 : ℝ)))
        ∧ ∀ᵐ e ∂PaperSpec.A.ex55Marks 1, hx e = EuclideanSpace.single 0 (e.2 : ℝ))
      ∧ ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
        (D : LevyStochCalc.Driver.LevyDriver P 1 (PaperSpec.A.ex55Marks 1)),
        Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P := by
  have hϱ : (1 : ℝ) < 2 := by norm_num
  have hxm : MemLp (fun e : DealerMark =>
      (PiLp.single 2 (0 : Fin 1) (e.2 : ℝ) : EuclideanSpace ℝ (Fin 1))) 2
      (PaperSpec.A.ex55Marks 1) :=
    (memLp_markSize _ hϱ).congr_norm
      (continuous_euclideanSingle_zero.comp_aestronglyMeasurable (memLp_markSize _ hϱ).1)
      (Eventually.of_forall fun _ => (PiLp.norm_single 2 (fun _ : Fin 1 => ℝ) 0 _).symm)
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ :=
    LevyStochCalc.Driver.LevyDriver.exists 1 DealerMark (PaperSpec.A.ex55Marks 1)
  exact ⟨one_pos, hϱ, inferInstance, inferInstance,
    ⟨dealerJump (fun _ => (2 - 1) / 2) hϱ, hxm.toLp _, coeFn_dealerJump hϱ, hxm.coeFn_toLp⟩,
    Ω, inferInstance, P, inferInstance, D, indep_bot_left _⟩

end Dissertation.Acceptance.A
