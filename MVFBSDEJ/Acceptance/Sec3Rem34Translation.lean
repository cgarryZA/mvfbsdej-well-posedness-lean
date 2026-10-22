/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.PaperSpec.Sec3Rem34
import MVFBSDEJ.Acceptance.Sec3
import MVFBSDEJ.WellPosedness.Spec.NotAssumption22

/-!
# Remark 3.4 of the well-posedness paper: the translation of the singular drift

Statement numbers refer to the well-posedness paper at `1f67672`, in the standing setting of §2. Let
the system `C` with initial datum `ξ₀` satisfy (2.3) and Assumptions 2.2–2.5, and let `e ∈ ℝⁿ` be
nonzero. Adding the deterministic drift `t^{-1/2} e` to `b` gives the system `C⁺ = C.addDrift c`,
`c_t = t^{-1/2} e`, whose coefficient differences are those of `C`; its drift has the origin value
`t^{-1/2} e + b(t, 0, δ₀)`, which is not square integrable on `(0, T)`. With `r_t = 2√t e`, the
system `C̃ = translatedCoeffs C r T` evaluates `C` at the translated tuple `θ + (r_t, 0)` and the
translated law `μ ∘ (· + (r_t, 0))⁻¹`: along `(X, Y, Z, U)` it is `C⁺` along `(X + r, Y, Z, U)`
without the drift `c`.

* **Translated laws.** For a square-integrable `Θ`, `Law(Θ + a) = Law(Θ) ∘ (· + a)⁻¹`.
  Translation is an isometry, so it does not increase the 2-Wasserstein distances, and
  `W₂(μ ∘ (· + a)⁻¹, μ ∘ (· + a')⁻¹) ≤ |a − a'|` by the synchronous coupling. Hence
  `(t, θ, μ) ↦ (t, θ + (r_t, 0), μ ∘ (· + (r_t, 0))⁻¹)` is continuous for a continuous `r`, and
  `C̃` inherits (2.3) from `C`.
* **The assumptions of `C̃`.** A diagonal input `(Θ, μ)` at time `t` translated,
  `(Θ + (r_t, 0), μ ∘ (· + (r_t, 0))⁻¹)`, is again a diagonal input with the same channel
  differences, so Assumptions 2.3 and 2.5 hold for `C̃` with the constants of `C`. Assumption 2.3
  at the deterministic inputs `(r_t, 0)` and `0` bounds the difference of the origin values of
  `C̃` and `C` by `2L |r_t|`, and `r` is bounded on `[0, T]`, so Assumption 2.2 holds for `C̃`.
* **The solution.** For a solution `Θ = (X, Y, Z, U)` of (1.1) for `C̃` in `𝕊`, the tuple `Θ_s`
  is square integrable at almost every time; there the coefficient processes of `C⁺` along
  `Θ⁺ = (X + r, Y, Z, U)` are those of `C̃` along `Θ`, the drift with `c_s` added. The left
  limits of `X + r` are those of `X` shifted by the continuous `r`, `g̃(X_T, Law X_T)` is
  `g(X_T + r_T, Law(X_T + r_T))`, and `∫_0^t c_s ds = r_t`. So `Θ⁺` satisfies (1.1) for `C⁺` in
  `ℍ²`, the drift integral read pathwise, and keeps the `S²` bounds of `Θ`.

## Main statements

* `lawP2_add_const`, `lawP2_translateTuple` — the law of a translated random element.
* `w2P_lawP2_add_const_le`, `w2H_translateTuple_le`, `w2H_translateTuple_le_norm` — translation
  and the 2-Wasserstein distances.
* `jointBorel_translatedCoeffs`, `jointBorel_addDrift` — (2.3) for `C̃` and `C⁺`.
* `assumption23_addDrift`, `assumption25_addDrift`, `not_assumption22_addDrift_inv_sqrt` —
  Assumptions 2.3 and 2.5 for `C⁺`, and the failure of Assumption 2.2.
* `assumption23_translatedCoeffs`, `assumption25_translatedCoeffs`,
  `originValues_translatedCoeffs` — Assumptions 2.2, 2.3 and 2.5 for `C̃`.
* `paperWeakSolutionInt_addDrift_of_translated` — the translated solution `Θ⁺` of `C⁺`.
* `MVFBSDEJ.Acceptance.rem_uniq_translation` — Remark 3.4, the singular drift for a general
  system.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MVFBSDEJ.Acceptance

open MVFBSDEJ.WellPosedness.System MVFBSDEJ.WellPosedness.Existence
  MVFBSDEJ.WellPosedness.Enlarged MVFBSDEJ.WellPosedness.Stability
  MVFBSDEJ.WellPosedness.Spec MVFBSDEJ.Law MVFBSDEJ.PaperSpec
  LevyStochCalc LevyStochCalc.BSDEJ.Solves

universe u v w

/-! ### Translated laws -/

section Laws

variable {F : Type*} [NormedAddCommGroup F] [MeasurableSpace F] [BorelSpace F]
  [SecondCountableTopology F]

/-- The identity is square integrable against a law of finite second moment. -/
theorem memLp_id_law (μ : P2 F) : MemLp id 2 μ.law := by
  refine (memLp_two_iff_integrable_sq_norm aestronglyMeasurable_id).mpr ⟨by fun_prop, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => by positivity)]
  exact lt_of_le_of_ne le_top μ.secondMoment_ne_top

/-- A translation is square integrable against a law of finite second moment. -/
theorem memLp_add_const_law (μ : P2 F) (a : F) : MemLp (fun x => x + a) 2 μ.law :=
  (memLp_id_law μ).add (memLp_const a)

/-- **The law of a translated random element**: for square-integrable `Θ`,
`Law(Θ + a) = Law(Θ) ∘ (· + a)⁻¹`. -/
theorem lawP2_add_const {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Θ : Ω → F} (hΘ : MemLp Θ 2 P) (a : F) :
    lawP2 P (fun ω => Θ ω + a) = lawP2 (lawP2 P Θ).law (fun x => x + a) := by
  have h1 : MemLp (fun ω => Θ ω + a) 2 P := hΘ.add (memLp_const a)
  refine P2.ext_law ?_
  rw [lawP2_law h1, lawP2_law (memLp_add_const_law _ a), lawP2_law hΘ,
    AEMeasurable.map_map_of_aemeasurable (by fun_prop) hΘ.aestronglyMeasurable.aemeasurable]
  rfl

/-- **Translation does not increase the 2-Wasserstein distance**:
`W₂(ρ ∘ (· + a)⁻¹, ρ' ∘ (· + a)⁻¹) ≤ W₂(ρ, ρ')`. -/
theorem w2P_lawP2_add_const_le (ρ ρ' : P2 F) (a : F) :
    w2P (lawP2 ρ.law fun x => x + a) (lawP2 ρ'.law fun x => x + a) ≤ w2P ρ ρ' := by
  rw [w2P, lawP2_law (memLp_add_const_law ρ a), lawP2_law (memLp_add_const_law ρ' a)]
  exact w2_map_le_of_norm_sub_le (by fun_prop) (fun x y => by rw [add_sub_add_right_eq_sub])
    ρ.law ρ'.law (w2sq_ne_top ρ ρ')

end Laws

section Tuple

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]
  [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}

/-- The translation of the forward coordinate is the translation by `(r, 0)` in `H`. -/
theorem translateTuple_eq_add (r : EuclideanSpace ℝ (Fin n)) :
    translateTuple (ν := ν) (m := m) (d := d) r = fun θ => θ + (r, 0) := by
  funext θ
  exact Prod.ext rfl (add_zero θ.2).symm

/-- The translation of the forward coordinate is continuous. -/
theorem continuous_translateTuple (r : EuclideanSpace ℝ (Fin n)) :
    Continuous (translateTuple (ν := ν) (m := m) (d := d) r) := by
  rw [translateTuple_eq_add]
  fun_prop

/-- The translation of the forward coordinate leaves differences unchanged. -/
theorem translateTuple_sub (r : EuclideanSpace ℝ (Fin n)) (θ θ' : TupleH ν n m d) :
    translateTuple r θ - translateTuple r θ' = θ - θ' := by
  rw [translateTuple_eq_add, add_sub_add_right_eq_sub]

/-- The translation of the forward coordinate is square integrable against a law of finite
second moment on `H`. -/
theorem memLp_translateTuple_law (μ : P2 (TupleH ν n m d)) (r : EuclideanSpace ℝ (Fin n)) :
    MemLp (translateTuple r) 2 μ.law := by
  rw [translateTuple_eq_add]
  exact memLp_add_const_law μ _

/-- **The law of a tuple with translated forward coordinate**: for square-integrable `Θ`,
`Law(Θ + (r, 0)) = Law(Θ) ∘ (· + (r, 0))⁻¹`. -/
theorem lawP2_translateTuple {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Θ : Ω → TupleH ν n m d} (hΘ : MemLp Θ 2 P)
    (r : EuclideanSpace ℝ (Fin n)) :
    lawP2 P (fun ω => translateTuple r (Θ ω)) = lawP2 (lawP2 P Θ).law (translateTuple r) := by
  rw [translateTuple_eq_add]
  exact lawP2_add_const hΘ _

/-- **The translation of the forward coordinate does not increase the Hilbert-norm
2-Wasserstein distance**: `W₂(μ ∘ (· + (r, 0))⁻¹, μ' ∘ (· + (r, 0))⁻¹) ≤ W₂(μ, μ')`. -/
theorem w2H_translateTuple_le (μ μ' : P2 (TupleH ν n m d)) (r : EuclideanSpace ℝ (Fin n)) :
    w2H (lawP2 μ.law (translateTuple r)) (lawP2 μ'.law (translateTuple r)) ≤ w2H μ μ' := by
  set S : TupleL2 (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m))
      (EuclideanSpace ℝ (Fin m × Fin d)) (Lp (EuclideanSpace ℝ (Fin m)) 2 ν) → _ :=
    fun w => toL2 (translateTuple r (ofL2 w)) with hS
  have hSm : Measurable S :=
    measurable_toL2.comp ((continuous_translateTuple r).measurable.comp measurable_ofL2)
  have hT := (continuous_translateTuple (ν := ν) (m := m) (d := d) r).measurable
  have hmap : ∀ μ₀ : P2 (TupleH ν n m d),
      (lawP2 μ₀.law (translateTuple r)).law.map toL2 = (μ₀.law.map toL2).map S := by
    intro μ₀
    rw [lawP2_law (memLp_translateTuple_law μ₀ r), Measure.map_map measurable_toL2 hT,
      Measure.map_map hSm measurable_toL2]
    rfl
  rw [w2H, w2H, hmap, hmap]
  refine w2_map_le_of_norm_sub_le hSm (fun w w' => le_of_eq ?_) _ _ (w2sq_map_toL2_ne_top μ μ')
  rw [hS]
  dsimp only
  rw [← toL2_sub, translateTuple_sub]
  rfl

/-- **Translations of one law by two vectors are at Hilbert-norm 2-Wasserstein distance at most
the distance of the vectors**: `W₂(μ ∘ (· + (r, 0))⁻¹, μ ∘ (· + (r', 0))⁻¹) ≤ |r − r'|`. -/
theorem w2H_translateTuple_le_norm (μ : P2 (TupleH ν n m d)) (r r' : EuclideanSpace ℝ (Fin n)) :
    w2H (lawP2 μ.law (translateTuple r)) (lawP2 μ.law (translateTuple r')) ≤ ‖r - r'‖ := by
  have h := w2H_lawP2_sq_le (memLp_translateTuple_law μ r) (memLp_translateTuple_law μ r')
  have e : ∀ θ : TupleH ν n m d,
      channelSq (translateTuple r θ - translateTuple r' θ) = ‖r - r'‖ ^ 2 := by
    intro θ
    simp [channelSq, translateTuple]
  simp only [e, integral_const, probReal_univ, one_smul] at h
  exact (pow_le_pow_iff_left₀ (w2H_nonneg _ _) (norm_nonneg _) two_ne_zero).mp h

end Tuple

/-! ### The joint Borel measurability (2.3) -/

section Borel

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]
  [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}

/-- **The translated law is Lipschitz in the translation and the law**:
`(r, μ) ↦ μ ∘ (· + (r, 0))⁻¹` is `2`-Lipschitz into `P₂(H)` with the Hilbert-norm `W₂`. -/
theorem lipschitzWith_translateTuple_law :
    LipschitzWith 2 fun p : EuclideanSpace ℝ (Fin n) × TupleP2WH ν n m d =>
      (lawP2 p.2.toP2.law (translateTuple p.1)).toP2WH := by
  refine LipschitzWith.of_dist_le_mul fun p q => ?_
  have h1 := w2H_translateTuple_le p.2.toP2 q.2.toP2 p.1
  have h2 := w2H_translateTuple_le_norm q.2.toP2 p.1 q.1
  have hd2 : dist p.2 q.2 = w2H p.2.toP2 q.2.toP2 := P2WH.dist_toP2WH p.2.toP2 q.2.toP2
  have hd1 : dist p.1 q.1 = ‖p.1 - q.1‖ := dist_eq_norm _ _
  have hp := le_max_left (dist p.1 q.1) (dist p.2 q.2)
  have hq := le_max_right (dist p.1 q.1) (dist p.2 q.2)
  rw [← Prod.dist_eq] at hp hq
  calc dist (lawP2 p.2.toP2.law (translateTuple p.1)).toP2WH
        (lawP2 q.2.toP2.law (translateTuple q.1)).toP2WH
      ≤ dist (lawP2 p.2.toP2.law (translateTuple p.1)).toP2WH
          (lawP2 q.2.toP2.law (translateTuple p.1)).toP2WH
        + dist (lawP2 q.2.toP2.law (translateTuple p.1)).toP2WH
          (lawP2 q.2.toP2.law (translateTuple q.1)).toP2WH := dist_triangle _ _ _
    _ ≤ w2H p.2.toP2 q.2.toP2 + ‖p.1 - q.1‖ := add_le_add h1 h2
    _ ≤ ((2 : ℝ≥0) : ℝ) * dist p q := by
        rw [NNReal.coe_ofNat]
        linarith

/-- The translated law `ρ ↦ ρ ∘ (· + a)⁻¹` is `1`-Lipschitz on `P₂(ℝⁿ)`. -/
theorem lipschitzWith_add_const_law (a : EuclideanSpace ℝ (Fin n)) :
    LipschitzWith 1 fun ρ : P2W (EuclideanSpace ℝ (Fin n)) =>
      (lawP2 ρ.toP2.law fun x => x + a).toP2W := by
  refine LipschitzWith.of_dist_le_mul fun ρ ρ' => ?_
  rw [NNReal.coe_one, one_mul]
  exact w2P_lawP2_add_const_le ρ.toP2 ρ'.toP2 a

/-- **(2.3) for the translated coefficients**: if `C` satisfies (2.3) and `r` is continuous,
then `translatedCoeffs C r T` satisfies (2.3). -/
theorem jointBorel_translatedCoeffs {T : ℝ} {C : Coeffs ν n m d} (hJ : JointBorel T C)
    {r : ℝ → EuclideanSpace ℝ (Fin n)} (hr : Continuous r) :
    JointBorel T (translatedCoeffs C r T) := by
  have hr' : Continuous fun p : Set.Icc (0 : ℝ) T × TupleH ν n m d × TupleP2WH ν n m d =>
      r p.1 := hr.comp (continuous_subtype_val.comp continuous_fst)
  have hΨ : Continuous fun p : Set.Icc (0 : ℝ) T × TupleH ν n m d × TupleP2WH ν n m d =>
      (p.1, translateTuple (r p.1) p.2.1,
        (lawP2 p.2.2.toP2.law (translateTuple (r p.1))).toP2WH) := by
    refine continuous_fst.prodMk (Continuous.prodMk ?_ ?_)
    · simp only [translateTuple_eq_add]
      exact continuous_snd.fst.add (hr'.prodMk continuous_const)
    · exact lipschitzWith_translateTuple_law.continuous.comp (hr'.prodMk continuous_snd.snd)
  have hΨg : Continuous fun p : EuclideanSpace ℝ (Fin n) × P2W (EuclideanSpace ℝ (Fin n)) =>
      (p.1 + r T, (lawP2 p.2.toP2.law fun x => x + r T).toP2W) :=
    (continuous_fst.add continuous_const).prodMk
      ((lipschitzWith_add_const_law (r T)).continuous.comp continuous_snd)
  have hm := hΨ.borel_measurable
  exact ⟨hJ.b_meas.comp hm, hJ.σ_meas.comp hm, hJ.h_meas.comp hm, hJ.f_meas.comp hm,
    hJ.g_meas.comp hΨg.borel_measurable⟩

/-- **(2.3) for the coefficients with a measurable deterministic drift added.** -/
theorem jointBorel_addDrift {T : ℝ} {C : Coeffs ν n m d} (hJ : JointBorel T C)
    {c : ℝ → EuclideanSpace ℝ (Fin n)} (hc : Measurable c) : JointBorel T (C.addDrift c) :=
  jointBorel_iff.mpr ⟨coeffBorelW2_addDrift (jointBorel_iff.mp hJ).1 hc,
    (jointBorel_iff.mp hJ).2⟩

end Borel

/-! ### Assumptions 2.2, 2.3 and 2.5 -/

section Assumptions

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {P : Measure Ω} [IsProbabilityMeasure P]
  {T L α β₁ β₂ : ℝ} {G : Matrix (Fin m) (Fin n) ℝ} {C : Coeffs ν n m d}

/-- **A deterministic drift leaves Assumption 2.3 unchanged.** -/
theorem assumption23_addDrift (h : Assumption23 ℱ P T L C) (c : ℝ → EuclideanSpace ℝ (Fin n)) :
    Assumption23 ℱ P T L (C.addDrift c) :=
  ⟨h.nonneg, h.interior.mono fun t ht p hp p' hp' => by
    simpa only [Coeffs.addDrift, add_sub_add_left_eq_sub] using ht p hp p' hp', h.terminal⟩

omit [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
/-- A deterministic drift cancels in the integrand of the left-hand side of (2.7). -/
theorem pairing27_addDrift (c : ℝ → EuclideanSpace ℝ (Fin n)) (t : ℝ) (θ θ' : TupleH ν n m d)
    (μ μ' : P2 (TupleH ν n m d)) :
    pairing27 G (C.addDrift c) t θ θ' μ μ' = pairing27 G C t θ θ' μ μ' := by
  simp only [pairing27, Coeffs.addDrift, add_sub_add_left_eq_sub]

/-- **A deterministic drift leaves Assumption 2.5 unchanged.** -/
theorem assumption25_addDrift (h : Assumption25 ℱ P T G α β₁ β₂ C)
    (c : ℝ → EuclideanSpace ℝ (Fin n)) : Assumption25 ℱ P T G α β₁ β₂ (C.addDrift c) where
  terminal := h.terminal
  interior := h.interior.mono fun t ht p hp p' hp' => by
    simpa only [pairing27_addDrift] using ht p hp p' hp'
  constants := h.constants

omit [IsProbabilityMeasure P] in
/-- **The drift `t^{-1/2} e` breaks Assumption 2.2**: for `T > 0` and `e ≠ 0`, if the origin
values of `C` lie in `L²(0, T)`, then `C` with the drift `t^{-1/2} e` added violates Assumption 2.2
for every initial datum, since `t^{-1/2}` is not square integrable on `(0, T)`. -/
theorem not_assumption22_addDrift_inv_sqrt (hT : 0 < T) {e : EuclideanSpace ℝ (Fin n)}
    (he : e ≠ 0) (hC : OriginValues T C) (ξ : Ω → EuclideanSpace ℝ (Fin n)) :
    ¬ Assumption22 ℱ P T (C.addDrift fun t => (Real.sqrt t)⁻¹ • e) ξ := by
  intro h
  have hc : MemLp (fun t : ℝ => (Real.sqrt t)⁻¹ • e) 2 (volume.restrict (Set.Ioo 0 T)) :=
    (h.origin.b_memLp.sub hC.b_memLp).ae_eq (ae_of_all _ fun t => by
      simp [Coeffs.addDrift])
  have hlt := lintegral_enorm_sq_lt_top hc
  have e1 : ∀ t : ℝ, ‖(Real.sqrt t)⁻¹ • e‖ₑ ^ 2
      = (‖(Real.sqrt t)⁻¹ - (fun _ => (0 : ℝ)) t‖₊ : ℝ≥0∞) ^ 2 * ‖e‖ₑ ^ 2 := by
    intro t
    rw [enorm_smul, mul_pow, sub_zero, enorm_eq_nnnorm]
  simp_rw [e1] at hlt
  rw [lintegral_mul_const' _ _ (by simp), Measure.restrict_congr_set Ioo_ae_eq_Icc,
    lintegral_sq_inv_sqrt_sub_eq_top tendsto_const_nhds hT,
    ENNReal.top_mul (pow_ne_zero 2 (enorm_ne_zero.mpr he))] at hlt
  exact lt_irrefl _ hlt

/-- The integrand of the left-hand side of (2.7) for the translated coefficients is that of `C`
at the translated tuples and laws. -/
theorem pairing27_translatedCoeffs (r : ℝ → EuclideanSpace ℝ (Fin n)) (t : ℝ)
    (θ θ' : TupleH ν n m d)
    (μ μ' : P2 (TupleH ν n m d)) :
    pairing27 G (translatedCoeffs C r T) t θ θ' μ μ'
      = pairing27 G C t (translateTuple (r t) θ) (translateTuple (r t) θ')
          (lawP2 μ.law (translateTuple (r t))) (lawP2 μ'.law (translateTuple (r t))) := by
  simp only [pairing27, translatedCoeffs, translateTuple, add_sub_add_right_eq_sub]

/-- **A translated diagonal input is a diagonal input**: for `(Θ, μ) ∈ 𝒟_t`,
`(Θ + (a, 0), μ ∘ (· + (a, 0))⁻¹) ∈ 𝒟_t`. -/
theorem translate_mem_diagonalInputs {t : ℝ} {p : (Ω → TupleH ν n m d) × P2 (TupleH ν n m d)}
    (hp : p ∈ diagonalInputs ν n m d ℱ P t) (a : EuclideanSpace ℝ (Fin n)) :
    ((fun ω => translateTuple a (p.1 ω)), lawP2 p.2.law (translateTuple a))
      ∈ diagonalInputs ν n m d ℱ P t := by
  obtain ⟨hs, hL, he⟩ := hp
  refine ⟨(continuous_translateTuple a).comp_stronglyMeasurable hs, ?_, ?_⟩
  · rw [translateTuple_eq_add]
    exact hL.add (memLp_const _)
  · rw [he]
    exact (lawP2_translateTuple hL a).symm

/-- **Assumption 2.3 for the translated coefficients**, with the constant of `C`. -/
theorem assumption23_translatedCoeffs (h : Assumption23 ℱ P T L C)
    (r : ℝ → EuclideanSpace ℝ (Fin n)) : Assumption23 ℱ P T L (translatedCoeffs C r T) := by
  refine ⟨h.nonneg, h.interior.mono fun t ht p hp p' hp' => ?_,
    fun XT XT' hs hs' hL hL' => ?_⟩
  · have key := ht _ (translate_mem_diagonalInputs hp (r t)) _
      (translate_mem_diagonalInputs hp' (r t))
    have hw := w2H_translateTuple_le p.2 p'.2 (r t)
    filter_upwards [key] with ω hω
    refine hω.trans (mul_le_mul_of_nonneg_left ?_ h.nonneg)
    simp only [translateTuple, add_sub_add_right_eq_sub]
    linarith
  · have k := h.terminal (fun ω => XT ω + r T) (fun ω => XT' ω + r T)
      (hs.add stronglyMeasurable_const) (hs'.add stronglyMeasurable_const)
      (hL.add (memLp_const _)) (hL'.add (memLp_const _))
    filter_upwards [k] with ω hω
    rw [lawP2_add_const hL, lawP2_add_const hL', add_sub_add_right_eq_sub] at hω
    exact hω.trans (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (w2P_lawP2_add_const_le _ _ _)) h.nonneg)

/-- **Assumption 2.5 for the translated coefficients**, with the coupling matrix and the
constants of `C`. -/
theorem assumption25_translatedCoeffs (h : Assumption25 ℱ P T G α β₁ β₂ C)
    (r : ℝ → EuclideanSpace ℝ (Fin n)) :
    Assumption25 ℱ P T G α β₁ β₂ (translatedCoeffs C r T) where
  terminal XT XT' hs hs' hL hL' := by
    have k := h.terminal (fun ω => XT ω + r T) (fun ω => XT' ω + r T)
      (hs.add stronglyMeasurable_const) (hs'.add stronglyMeasurable_const)
      (hL.add (memLp_const _)) (hL'.add (memLp_const _))
    simp only [lawP2_add_const hL, lawP2_add_const hL', add_sub_add_right_eq_sub] at k
    exact k
  interior := h.interior.mono fun t ht p hp p' hp' => by
    have k := ht _ (translate_mem_diagonalInputs hp (r t)) _
      (translate_mem_diagonalInputs hp' (r t))
    simp only [pairing27_translatedCoeffs]
    simpa only [translateTuple, add_sub_add_right_eq_sub] using k
  constants := h.constants

/-- The Dirac mass at the origin of `H`, translated by `(a, 0)`, is the Dirac mass at `(a, 0)`. -/
theorem lawP2_dirac_translateTuple (a : EuclideanSpace ℝ (Fin n)) :
    lawP2 (P2.dirac (0 : TupleH ν n m d)).law (translateTuple a)
      = P2.dirac (translateTuple a 0) :=
  P2.ext_law (by
    rw [lawP2_law (memLp_translateTuple_law _ a)]
    exact Measure.map_dirac' (continuous_translateTuple a).measurable 0)

/-- A coefficient Borel measurable on `[0, T] × H × P₂(H)` has an almost everywhere strongly
measurable origin value `t ↦ ψ(t, 0, δ₀)` on `(0, T)`. -/
theorem aestronglyMeasurable_origin {W : Type*} [NormedAddCommGroup W] [MeasurableSpace W]
    [BorelSpace W] [SecondCountableTopology W] (hT : 0 ≤ T)
    {ψ : ℝ → TupleH ν n m d → P2 (TupleH ν n m d) → W}
    (hψ : Measurable[borel (Set.Icc (0 : ℝ) T × TupleH ν n m d × TupleP2WH ν n m d), borel W]
      fun p => ψ p.1 p.2.1 p.2.2.toP2) :
    AEStronglyMeasurable (fun t => ψ t 0 (P2.dirac 0)) (volume.restrict (Set.Ioo 0 T)) := by
  have hΨ : Continuous fun t : ℝ => ((Set.projIcc 0 T hT t : Set.Icc (0 : ℝ) T),
      (0 : TupleH ν n m d), (P2.dirac (0 : TupleH ν n m d)).toP2WH) :=
    continuous_projIcc.prodMk continuous_const
  have hm := hψ.comp hΨ.borel_measurable
  rw [← BorelSpace.measurable_eq (α := ℝ), ← BorelSpace.measurable_eq (α := W)] at hm
  refine hm.aestronglyMeasurable.congr ?_
  refine (ae_restrict_mem measurableSet_Ioo).mono fun t ht => ?_
  simp only [Function.comp_apply, Set.projIcc_of_mem hT ⟨ht.1.le, ht.2.le⟩]
  rfl

/-- **The origin values of the translated coefficients**: under Assumption 2.3 for `C`, for
almost every `t ∈ [0, T]` the origin values of `translatedCoeffs C r T` and of `C` differ by at
most `2L |r_t|` in total, the bound of Assumption 2.3 at the deterministic inputs `(r_t, 0)` and
`0`. -/
theorem translatedCoeffs_origin_le (h23 : Assumption23 ℱ P T L C)
    (r : ℝ → EuclideanSpace ℝ (Fin n)) :
    ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      ‖(translatedCoeffs C r T).b t 0 (P2.dirac 0) - C.b t 0 (P2.dirac 0)‖
        + ‖(translatedCoeffs C r T).σ t 0 (P2.dirac 0) - C.σ t 0 (P2.dirac 0)‖
        + ‖(translatedCoeffs C r T).h t 0 (P2.dirac 0) - C.h t 0 (P2.dirac 0)‖
        + ‖(translatedCoeffs C r T).f t 0 (P2.dirac 0) - C.f t 0 (P2.dirac 0)‖
      ≤ L * (2 * ‖r t‖) := by
  filter_upwards [h23.interior] with t ht
  set a : TupleH ν n m d := translateTuple (r t) 0 with ha
  have hp : ((fun _ : Ω => a), lawP2 P (fun _ : Ω => a)) ∈ diagonalInputs ν n m d ℱ P t :=
    mk_mem_diagonalInputs stronglyMeasurable_const (memLp_const a)
  have hp0 : ((fun _ : Ω => (0 : TupleH ν n m d)), lawP2 P (fun _ : Ω => (0 : TupleH ν n m d)))
      ∈ diagonalInputs ν n m d ℱ P t :=
    mk_mem_diagonalInputs stronglyMeasurable_const (memLp_const 0)
  obtain ⟨ω, hω⟩ := (ht _ hp _ hp0).exists
  have hw := w2H_lawP2_sq_le (P := P) (memLp_const a) (memLp_const (0 : TupleH ν n m d))
  rw [lawP2_const, lawP2_const] at hω hw
  have ha1 : a.1 = r t := by simp [ha, translateTuple]
  have ha2 : a.2 = 0 := by simp [ha, translateTuple]
  have hcs : channelSq (a - 0) = ‖r t‖ ^ 2 := by
    simp [channelSq, ha1, ha2]
  simp only [hcs, integral_const, probReal_univ, one_smul] at hw
  have hw' := (pow_le_pow_iff_left₀ (w2H_nonneg _ _) (norm_nonneg _) two_ne_zero).mp hw
  simp only [translatedCoeffs, lawP2_dirac_translateTuple, ← ha]
  refine hω.trans (mul_le_mul_of_nonneg_left ?_ h23.nonneg)
  simp only [ha1, ha2, Prod.fst_zero, Prod.snd_zero, sub_zero, norm_zero, add_zero]
  linarith

/-- An origin value within a bounded distance of a square-integrable one, almost everywhere on
`[0, T]`, is square integrable on `(0, T)` when its coefficient is Borel measurable on
`[0, T] × H × P₂(H)`. -/
theorem memLp_origin_of_le {W : Type*} [NormedAddCommGroup W] [MeasurableSpace W]
    [BorelSpace W] [SecondCountableTopology W] (hT : 0 ≤ T)
    {ψ ψ' : ℝ → TupleH ν n m d → P2 (TupleH ν n m d) → W}
    (hψ' : Measurable[borel (Set.Icc (0 : ℝ) T × TupleH ν n m d × TupleP2WH ν n m d), borel W]
      fun p => ψ' p.1 p.2.1 p.2.2.toP2)
    (hψ : MemLp (fun t => ψ t 0 (P2.dirac 0)) 2 (volume.restrict (Set.Ioo 0 T))) {M : ℝ}
    (hle : ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      ‖ψ' t 0 (P2.dirac 0) - ψ t 0 (P2.dirac 0)‖ ≤ M) :
    MemLp (fun t => ψ' t 0 (P2.dirac 0)) 2 (volume.restrict (Set.Ioo 0 T)) := by
  refine (hψ.norm.add (memLp_const M)).of_le (aestronglyMeasurable_origin hT hψ') ?_
  filter_upwards [ae_restrict_of_ae_restrict_of_subset Set.Ioo_subset_Icc_self hle] with t ht
  have h1 := norm_le_norm_add_norm_sub' (ψ' t 0 (P2.dirac 0)) (ψ t 0 (P2.dirac 0))
  exact h1.trans ((add_le_add le_rfl ht).trans (le_abs_self _))

/-- **The origin values of Assumption 2.2 for the translated coefficients**: if `C` has origin
values in `L²(0, T)` and satisfies Assumption 2.3, `r` is bounded on `[0, T]` and
`translatedCoeffs C r T` satisfies (2.3), then its origin values lie in `L²(0, T)`. -/
theorem originValues_translatedCoeffs (hT : 0 ≤ T) {r : ℝ → EuclideanSpace ℝ (Fin n)}
    (hJ : JointBorel T (translatedCoeffs C r T)) (h22 : OriginValues T C)
    (h23 : Assumption23 ℱ P T L C) {K : ℝ} (hK : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖r t‖ ≤ K) :
    OriginValues T (translatedCoeffs C r T) := by
  have hle : ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      ‖(translatedCoeffs C r T).b t 0 (P2.dirac 0) - C.b t 0 (P2.dirac 0)‖
        + ‖(translatedCoeffs C r T).σ t 0 (P2.dirac 0) - C.σ t 0 (P2.dirac 0)‖
        + ‖(translatedCoeffs C r T).h t 0 (P2.dirac 0) - C.h t 0 (P2.dirac 0)‖
        + ‖(translatedCoeffs C r T).f t 0 (P2.dirac 0) - C.f t 0 (P2.dirac 0)‖
      ≤ L * (2 * K) := by
    filter_upwards [translatedCoeffs_origin_le h23 r, ae_restrict_mem measurableSet_Icc]
      with t ht htI
    exact ht.trans (mul_le_mul_of_nonneg_left (by linarith [hK t htI]) h23.nonneg)
  refine ⟨memLp_origin_of_le (M := L * (2 * K)) hT hJ.b_meas h22.b_memLp
      (hle.mono fun t ht => ?_),
    memLp_origin_of_le (M := L * (2 * K)) hT hJ.σ_meas h22.σ_memLp (hle.mono fun t ht => ?_),
    memLp_origin_of_le (M := L * (2 * K)) hT hJ.h_meas h22.h_memLp (hle.mono fun t ht => ?_),
    memLp_origin_of_le (M := L * (2 * K)) hT hJ.f_meas h22.f_memLp
      (hle.mono fun t ht => ?_)⟩ <;>
  linarith [norm_nonneg ((translatedCoeffs C r T).b t 0 (P2.dirac 0) - C.b t 0 (P2.dirac 0)),
    norm_nonneg ((translatedCoeffs C r T).σ t 0 (P2.dirac 0) - C.σ t 0 (P2.dirac 0)),
    norm_nonneg ((translatedCoeffs C r T).h t 0 (P2.dirac 0) - C.h t 0 (P2.dirac 0)),
    norm_nonneg ((translatedCoeffs C r T).f t 0 (P2.dirac 0) - C.f t 0 (P2.dirac 0))]

end Assumptions

/-! ### The translated solution -/

section Solution

/-- **The left limit of a sum with a function continuous at the point**:
`(f + g)(a−) = f(a−) + g(a)`, where `f(a−)` is `Function.leftLim f a`. -/
theorem leftLim_add_of_continuousAt {f g : ℝ → ℝ} {a : ℝ} (hg : ContinuousAt g a) :
    Function.leftLim (fun s => f s + g s) a = Function.leftLim f a + g a := by
  have hg' : Tendsto g (𝓝[<] a) (𝓝 (g a)) := hg.tendsto.mono_left nhdsWithin_le_nhds
  by_cases h : ∃ y, Tendsto f (𝓝[<] a) (𝓝 y)
  · obtain ⟨y, hy⟩ := h
    rw [leftLim_eq_of_tendsto hy, leftLim_eq_of_tendsto (hy.add hg')]
  · have h' : ¬ ∃ y, Tendsto (fun s => f s + g s) (𝓝[<] a) (𝓝 y) := by
      rintro ⟨y, hy⟩
      exact h ⟨y - g a, by simpa using hy.sub hg'⟩
    rw [leftLim_eq_of_not_tendsto _ h, leftLim_eq_of_not_tendsto _ h']

/-- A coordinate vector with a vector added coordinatewise is the sum of the vectors. -/
theorem toLp_add_ofLp {n : ℕ} (x : Fin n → ℝ) (r : EuclideanSpace ℝ (Fin n)) :
    (WithLp.toLp 2 fun i => x i + r i : EuclideanSpace ℝ (Fin n)) = WithLp.toLp 2 x + r := by
  ext i
  simp

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}
  {P : Measure Ω} [IsProbabilityMeasure P] {T : ℝ} {r : ℝ → EuclideanSpace ℝ (Fin n)}

omit [MeasurableSpace Ω] in
/-- The tuple of `(X + r, Y, Z, U)` is the tuple of `(X, Y, Z, U)` with its forward coordinate
translated by `r`. -/
theorem tupleAt_add_translate {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ}
    {Z : Fin m → ℝ → Ω → Fin d → ℝ} {U : Fin m → ℝ → Ω → E → ℝ} (s : ℝ) (ω : Ω) :
    tupleAt ν (fun i t ω => X i t ω + r t i) Y Z U s ω
      = translateTuple (r s) (tupleAt ν X Y Z U s ω) := by
  refine Prod.ext ?_ rfl
  ext i
  simp [tupleAt, translateTuple]

omit [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
/-- **A continuous translation keeps the `S²` bound**: if `𝔼 sup_{t ≤ T} |x_t|² < ∞` and `r` is
continuous, then `𝔼 sup_{t ≤ T} |x_t + r_t|² < ∞`. -/
theorem lintegral_biSup_esq_add_lt_top {x : Fin n → ℝ → Ω → ℝ}
    (hx : ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => x i t ω)) ∂P < ⊤)
    (hr : Continuous r) :
    ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => x i t ω + r t i)) ∂P < ⊤ := by
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    hr.continuousOn
  have hrK : ∀ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => r t i) ≤ ENNReal.ofReal (K ^ 2) := by
    intro t ht
    rw [esq_eq_enorm_sq, WithLp.toLp_ofLp, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (hK t ht) 2)
  have hle : ∀ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => x i t ω + r t i))
      ≤ 2 * (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => x i t ω)) + 2 * ENNReal.ofReal (K ^ 2) := by
    intro ω
    refine iSup₂_le fun t ht => ?_
    have h1 := esq_mul_add_le (l := 1) (by norm_num) (fun i => x i t ω) (fun i => r t i)
    simp only [one_mul] at h1
    refine h1.trans ?_
    gcongr
    · exact le_iSup₂ (f := fun t (_ : t ∈ Set.Icc (0 : ℝ) T) => esq fun i => x i t ω) t ht
    · exact hrK t ht
  refine (lintegral_mono hle).trans_lt ?_
  rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ (by norm_num),
    lintegral_const, measure_univ, mul_one]
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top (by norm_num) hx,
    ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top⟩

variable {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {C : Coeffs ν n m d}
  {ξ₀ : Fin n → Ω → ℝ} {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ}
  {Z : Fin m → ℝ → Ω → Fin d → ℝ} {U : Fin m → ℝ → Ω → E → ℝ} {γ : Fin n → ℝ → Ω → E → ℝ}
  {c : ℝ → EuclideanSpace ℝ (Fin n)}

/-- **The translated solution.** For `T ≥ 0`, let `c` be integrable on `[0, T]` coordinatewise
with `∫_0^t c_s ds = r_t` for `t ∈ [0, T]`, `r` continuous, and let `C` with the drift `c` added
satisfy (2.3) with the evaluation σ-algebra on `P₂(H)`. If `(X, Y, Z, U)` solves (1.1) for
`translatedCoeffs C r T` in the sense of the paper, with jump representative `γ`, then
`(X + r, Y, Z, U)` solves (1.1) for `C` with the drift `c` added in `ℍ²`, with pathwise drift
and driver integrals and the same `γ`. -/
theorem paperWeakSolutionInt_addDrift_of_translated (hT : 0 ≤ T) (hr : Continuous r)
    (hc : ∀ i, IntegrableOn (fun s => c s i) (Set.Icc (0 : ℝ) T))
    (hcr : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ s in Set.Icc (0 : ℝ) t, c s i = r t i)
    (hB : CoeffBorel T (C.addDrift c))
    (h : PaperSolution D ℱ hℱW hℱN T (translatedCoeffs C r T) ξ₀ X Y Z U γ) :
    PaperWeakSolutionInt D ℱ hℱW hℱN T (C.addDrift c) ξ₀ (fun i t ω => X i t ω + r t i)
      Y Z U γ := by
  have hri : ∀ i, Continuous fun t => r t i := fun i =>
    (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).continuous.comp hr
  have hsup' := lintegral_biSup_esq_add_lt_top h.X_sup hr
  -- extensions of `X` and `Y` off the horizon, and the progressive tuples
  obtain ⟨X₁, hX₁e, hX₁a, hX₁r⟩ := exists_adapted_rightCont_extension hT h.X_adapted
    h.X_rightCont
  obtain ⟨Y₁, hY₁e, hY₁a, hY₁r⟩ := exists_adapted_rightCont_extension hT h.Y_adapted
    h.Y_rightCont
  have hΘ₁ : ProgTuple ℱ P ν T X₁ Y₁ Z U :=
    { X_adapted := hX₁a
      X_rightCont := hX₁r
      Y_adapted := hY₁a
      Y_rightCont := hY₁r
      Z_meas := fun k j => Brownian.Ito.measurable_uncurry_of_predictable (h.Z_pred k j)
      Z_prog := fun k j =>
        progressivelyMeasurable_of_predictable_of_vanish (h.Z_pred k) (h.Z_vanish k) j
      Z_sq := h.Z_sq
      U_meas := fun k => (h.U_pred k).mono (Probability.markedPredictableSigma_le ℱ ν) le_rfl
      U_prog := fun k => (h.U_pred k).markedProgressivelyMeasurable
      U_sq := h.U_sq }
  have hΘ₁' : ProgTuple ℱ P ν T (fun i t ω => X₁ i t ω + r t i) Y₁ Z U :=
    { hΘ₁ with
      X_adapted := fun i t => (hX₁a i t).add_const _
      X_rightCont := fun i ω t =>
        (hX₁r i ω t).add (((hri i).tendsto t).mono_left nhdsWithin_le_nhds) }
  have hCE := (hB.crossEval hΘ₁').of_eqOn (X' := fun i t ω => X i t ω + r t i) (Y' := Y)
    (fun i t ht => by simp only [hX₁e i t ht]) (fun k t ht => (hY₁e k t ht).symm)
  -- the tuples are square integrable at almost every time
  have hX₁E : ∀ i, Brownian.Ito.energy P T (fun ω s => X₁ i s ω) ≠ ⊤ := fun i => by
    rw [energy_eq_of_eqOn (hX₁e i)]
    exact energy_ne_top_of_lintegral_biSup_esq_lt_top h.X_sup i
  have hY₁E : ∀ k, Brownian.Ito.energy P T (fun ω s => Y₁ k s ω) ≠ ⊤ := fun k => by
    rw [energy_eq_of_eqOn (hY₁e k)]
    exact energy_ne_top_of_lintegral_biSup_esq_lt_top h.Y_sup k
  have hG1 : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), MemLp (tupleAt ν X Y Z U s) 2 P := by
    filter_upwards [hΘ₁.ae_memLp_tupleAt hX₁E hY₁E, ae_restrict_mem measurableSet_Icc]
      with s hs hsI
    rwa [tupleAt_eq_of_eqOn hX₁e hY₁e hsI] at hs
  have hG2 : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      MemLp (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s) 2 P := by
    filter_upwards [hG1, h.toWeak.toPaperWeakTuple.ae_ae_tupleAt_leftLimProc_eq hT]
      with s hs heq
    exact (memLp_congr_ae heq).mpr hs
  -- the tuples, the laws and the coefficient processes
  have hleft : leftLimProc (fun i t ω => X i t ω + r t i)
      = fun i t ω => leftLimProc X i t ω + r t i := by
    funext i t ω
    exact leftLim_add_of_continuousAt (hri i).continuousAt
  have hlaw : ∀ s, MemLp (tupleAt ν X Y Z U s) 2 P →
      lawP2 P (tupleAt ν (fun i t ω => X i t ω + r t i) Y Z U s)
        = lawP2 (lawP2 P (tupleAt ν X Y Z U s)).law (translateTuple (r s)) := by
    intro s hs
    rw [← lawP2_translateTuple hs]
    exact congrArg _ (funext fun ω => tupleAt_add_translate s ω)
  have hlawL : ∀ s, MemLp (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s) 2 P →
      lawP2 P (tupleAt ν (leftLimProc fun i t ω => X i t ω + r t i) (leftLimProc Y) Z U s)
        = lawP2 (lawP2 P (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s)).law
          (translateTuple (r s)) := by
    intro s hs
    rw [← lawP2_translateTuple hs, hleft]
    exact congrArg _ (funext fun ω => tupleAt_add_translate s ω)
  have hb : ∀ i ω s, MemLp (tupleAt ν X Y Z U s) 2 P →
      driftProc P T (C.addDrift c) (fun i t ω => X i t ω + r t i) Y Z U i ω s
        = (Set.Icc (0 : ℝ) T).indicator (fun s => c s i) s
          + driftProc P T (translatedCoeffs C r T) X Y Z U i ω s := by
    intro i ω s hs
    by_cases hsI : s ∈ Set.Icc (0 : ℝ) T
    · simp only [driftProc, Set.indicator_of_mem hsI, hlaw s hs, tupleAt_add_translate,
        Coeffs.addDrift, translatedCoeffs, PiLp.add_apply]
    · simp only [driftProc, Set.indicator_of_notMem hsI, add_zero]
  have hσ : ∀ i s ω j, MemLp (tupleAt ν X Y Z U s) 2 P →
      diffusionProc P T (C.addDrift c) (fun i t ω => X i t ω + r t i) Y Z U i s ω j
        = diffusionProc P T (translatedCoeffs C r T) X Y Z U i s ω j := by
    intro i s ω j hs
    by_cases hsI : s ∈ Set.Icc (0 : ℝ) T
    · simp only [diffusionProc, Set.indicator_of_mem hsI, hlaw s hs, tupleAt_add_translate,
        Coeffs.addDrift, translatedCoeffs]
    · simp only [diffusionProc, Set.indicator_of_notMem hsI]
  have hf : ∀ k ω s, MemLp (tupleAt ν X Y Z U s) 2 P →
      driverProc P T (C.addDrift c) (fun i t ω => X i t ω + r t i) Y Z U k ω s
        = driverProc P T (translatedCoeffs C r T) X Y Z U k ω s := by
    intro k ω s hs
    by_cases hsI : s ∈ Set.Icc (0 : ℝ) T
    · simp only [driverProc, Set.indicator_of_mem hsI, hlaw s hs, tupleAt_add_translate,
        Coeffs.addDrift, translatedCoeffs]
    · simp only [driverProc, Set.indicator_of_notMem hsI]
  have hXT : MemLp (fun ω => (WithLp.toLp 2 fun i => X i T ω : EuclideanSpace ℝ (Fin n))) 2 P :=
    memLp_toLp_of_forall fun i => memLp_of_lintegral_biSup_esq_lt_top h.X_sup ⟨hT, le_rfl⟩ i
      ((h.X_adapted i T ⟨hT, le_rfl⟩).mono (ℱ.le T) le_rfl).aestronglyMeasurable
  have hg : ∀ k ω, terminalVal P T (C.addDrift c) (fun i t ω => X i t ω + r t i) k ω
      = terminalVal P T (translatedCoeffs C r T) X k ω := by
    intro k ω
    have e1 : (fun ω' => (WithLp.toLp 2 fun i => X i T ω' + r T i : EuclideanSpace ℝ (Fin n)))
        = fun ω' => WithLp.toLp 2 (fun i => X i T ω') + r T :=
      funext fun ω' => toLp_add_ofLp _ _
    simp only [terminalVal, Coeffs.addDrift, translatedCoeffs]
    rw [e1, lawP2_add_const hXT, toLp_add_ofLp]
  -- the diffusion processes agree in energy
  have hσin : ∀ i j ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖diffusionProc P T (translatedCoeffs C r T) X Y Z U i s ω j
        - diffusionProc P T (C.addDrift c) (fun i t ω => X i t ω + r t i) Y Z U i s ω j‖₊
          : ℝ≥0∞) ^ 2 = 0 := fun i j ω => by
    rw [← lintegral_zero (μ := volume.restrict (Set.Icc (0 : ℝ) T))]
    exact lintegral_congr_ae (hG1.mono fun s hs => by simp [hσ i s ω j hs])
  have hσ0 : ∀ i j, Brownian.Ito.energy P T (fun ω s =>
      diffusionProc P T (translatedCoeffs C r T) X Y Z U i s ω j
        - diffusionProc P T (C.addDrift c) (fun i t ω => X i t ω + r t i) Y Z U i s ω j) = 0 :=
    fun i j => by simp only [Brownian.Ito.energy, hσin i j, lintegral_zero]
  have hσE : ∀ i j, Brownian.Ito.energy P T (fun ω s =>
      diffusionProc P T (C.addDrift c) (fun i t ω => X i t ω + r t i) Y Z U i s ω j)
        = Brownian.Ito.energy P T (fun ω s =>
          diffusionProc P T (translatedCoeffs C r T) X Y Z U i s ω j) := fun i j =>
    lintegral_congr fun ω => lintegral_congr_ae (hG1.mono fun s hs => by
      simp only [hσ i s ω j hs])
  refine
    { X_adapted := fun i t ht => (h.X_adapted i t ht).add_const _
      X_rightCont := fun i ω t ht =>
        (h.X_rightCont i ω t ht).add (((hri i).tendsto t).mono_left nhdsWithin_le_nhds)
      X_leftLim := fun i => (h.X_leftLim i).mono fun ω hω t ht =>
        let ⟨L, hL⟩ := hω t ht
        ⟨L + r t i, hL.add (((hri i).tendsto t).mono_left nhdsWithin_le_nhds)⟩
      X_sq := fun i => energy_ne_top_of_lintegral_biSup_esq_lt_top hsup' i
      Y_adapted := h.Y_adapted
      Y_rightCont := h.Y_rightCont
      Y_leftLim := h.Y_leftLim
      Y_sq := fun k => energy_ne_top_of_lintegral_biSup_esq_lt_top h.Y_sup k
      Z_pred := h.Z_pred
      Z_vanish := h.Z_vanish
      Z_sq := h.Z_sq
      U_pred := h.U_pred
      U_vanish := h.U_vanish
      U_sq := h.U_sq
      b_meas := hCE.b_meas
      b_prog := hCE.b_prog
      b_int := fun i => ?_
      σ_meas := hCE.σ_meas
      σ_prog := hCE.σ_prog
      σ_sq := fun i j => by rw [hσE i j]; exact h.σ_sq i j
      γ_meas := h.γ_meas
      γ_prog := h.γ_prog
      γ_sq := h.γ_sq
      f_meas := hCE.f_meas
      f_prog := hCE.f_prog
      f_int := fun k => ?_
      jump_rep := ?_
      XT_sq := fun i => (memLp_of_lintegral_biSup_esq_lt_top h.X_sup ⟨hT, le_rfl⟩ i
        ((h.X_adapted i T ⟨hT, le_rfl⟩).mono (ℱ.le T) le_rfl).aestronglyMeasurable).add
        (memLp_const _)
      fwd := fun i => ?_
      bwd := fun k => ?_ }
  · -- the drift process: the drift `c` plus that of the translated system, at almost every time
    filter_upwards [ae_mem_integrablePaths (h.b_meas i) (h.b_sq i)] with ω hω
    refine ((hc i).add hω).congr_fun_ae ?_
    filter_upwards [hG1, ae_restrict_mem measurableSet_Icc] with s hs hsI
    simp only [Pi.add_apply, hb i ω s hs, Set.indicator_of_mem hsI]
  · filter_upwards [ae_mem_integrablePaths (h.f_meas k) (h.f_sq k)] with ω hω
    refine (show IntegrableOn _ _ _ from hω).congr_fun_ae ?_
    filter_upwards [hG1] with s hs
    exact (hf k ω s hs).symm
  · -- the jump coefficient at the translated predictable tuple
    filter_upwards [h.jump_rep, hG2] with s hs hM
    rw [hlawL s hM]
    filter_upwards [hs] with ω hω
    rw [hleft, tupleAt_add_translate]
    exact hω
  · -- the forward identity: `∫_0^t c_s ds = r_t`
    obtain ⟨M, hM, hMc, hid⟩ := h.fwd i
    refine ⟨M, fun t ht => (hM t ht).trans (multidimStochasticIntegral_congr_of_energy D.W hℱW
      _ _ _ _ _ _ (hσ0 i) ht.2), hMc, ?_⟩
    filter_upwards [hid, ae_mem_integrablePaths (h.b_meas i) (h.b_sq i)] with ω hω hint t ht
    have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T := Set.Icc_subset_Icc le_rfl ht.2
    have hI : ∫ s in Set.Icc (0 : ℝ) t,
        driftProc P T (C.addDrift c) (fun i t ω => X i t ω + r t i) Y Z U i ω s
          = r t i
            + ∫ s in Set.Icc (0 : ℝ) t, driftProc P T (translatedCoeffs C r T) X Y Z U i ω s := by
      rw [← hcr i t ht, ← integral_add ((hc i).mono_set hsub)
        ((show IntegrableOn _ _ _ from hint).mono_set hsub)]
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hG1,
        ae_restrict_mem measurableSet_Icc] with s hs hsI
      rw [hb i ω s hs, Set.indicator_of_mem (hsub hsI)]
    rw [hI, hω t ht]
    ring
  · -- the backward identity
    obtain ⟨M, hM, hMc, hid⟩ := h.bwd k
    refine ⟨M, hM, hMc, ?_⟩
    filter_upwards [hid] with ω hω t ht
    have hI : ∫ s in Set.Icc t T,
        driverProc P T (C.addDrift c) (fun i t ω => X i t ω + r t i) Y Z U k ω s
          = ∫ s in Set.Icc t T, driverProc P T (translatedCoeffs C r T) X Y Z U k ω s := by
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_of_ae_restrict_of_subset (Set.Icc_subset_Icc ht.1 le_rfl) hG1]
        with s hs
      exact hf k ω s hs
    rw [hI, hg k ω]
    exact hω t ht

end Solution

/-! ### Remark 3.4 -/

/-- Remark 3.4, the singular drift for a general system. -/
theorem rem_uniq_translation : PaperSpec.rem_uniq_translation.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ hind₀ hn hm hd T hT L α β₁ β₂ G C ξ₀ e he hJ h22 h23
    hG h25
  set c : ℝ → EuclideanSpace ℝ (Fin n) := fun t => (Real.sqrt t)⁻¹ • e with hc_def
  set r : ℝ → EuclideanSpace ℝ (Fin n) := fun t => (2 * Real.sqrt t) • e with hr_def
  have hcm : Measurable c := Real.continuous_sqrt.measurable.inv.smul_const e
  have hrc : Continuous r := (continuous_const.mul Real.continuous_sqrt).smul continuous_const
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    hrc.continuousOn
  have hJ' := jointBorel_addDrift hJ hcm
  have hJt := jointBorel_translatedCoeffs hJ hrc
  have h22t : Assumption22 (enlJoint 𝒢₀ D h𝒢₀) P T (translatedCoeffs C r T) ξ₀ :=
    ⟨h22.initial_meas, h22.initial_memLp, originValues_translatedCoeffs hT.le hJt h22.origin h23 hK⟩
  have h23t := assumption23_translatedCoeffs h23 r
  have h25t := assumption25_translatedCoeffs h25 r
  obtain ⟨X, Y, Z, U, hS⟩ :=
    (thm_cwp 𝒢₀ ν n m d P D h𝒢₀ hind₀ hn hm hd T hT L α β₁ β₂ G (translatedCoeffs C r T) ξ₀ hJt
      h22t h23t hG h25t).1
  obtain ⟨⟨γ, hγ⟩, hXl, hYl⟩ := Solution.paperSolutionEnl hT.le hJt h22t.origin h23t hS
  have hci : ∀ i, IntegrableOn (fun s => c s i) (Set.Icc (0 : ℝ) T) := fun i =>
    IntegrableOn.congr_fun ((integrableOn_inv_sqrt T).mul_const (e i))
      (fun s _ => by simp [hc_def]) measurableSet_Icc
  have hcr : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ s in Set.Icc (0 : ℝ) t, c s i = r t i := by
    intro i t ht
    simp only [hc_def, hr_def, PiLp.smul_apply, smul_eq_mul]
    rw [integral_mul_const, integral_inv_sqrt ht.1]
  have hW := paperWeakSolutionInt_addDrift_of_translated hT.le hrc hci hcr
    (jointBorel_iff.mp hJ').1.toCoeffBorel hγ
  have hX' : (fun i t ω => X i t ω + 2 * Real.sqrt t * e i) = fun i t ω => X i t ω + r t i := by
    funext i t ω
    simp [hr_def]
  refine ⟨hJ', assumption23_addDrift h23 c, assumption25_addDrift h25 c,
    fun ξ => not_assumption22_addDrift_inv_sqrt hT he h22.origin ξ, hJt, h22t, h23t, h25t,
    X, Y, Z, U, hS, ⟨?_, ?_, hγ.Y_sup⟩⟩
  · rw [hX']
    refine ⟨⟨γ, hW⟩, fun i ω t ht => ?_, hYl⟩
    obtain ⟨l, hl⟩ := hXl i ω t ht
    have hrt : Continuous fun t => r t i :=
      (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).continuous.comp hrc
    exact ⟨l + r t i, hl.add ((hrt.tendsto t).mono_left nhdsWithin_le_nhds)⟩
  · simpa [hr_def] using lintegral_biSup_esq_add_lt_top hγ.X_sup hrc

end MVFBSDEJ.Acceptance
