/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.PaperSpec.A.AsPrinted
import Dissertation.PaperSpec.A.Sec5Regimes
import Dissertation.Acceptance.A.Sec2Remarks
import Dissertation.Acceptance.A.Sec3Margin
import Dissertation.Acceptance.A.Sec3Rem34
import Dissertation.Acceptance.A.Dealer
import LevyStochCalc.Driver.Existence

/-!
# Claims of the well-posedness paper read as printed: refutations

## Main statements

* `Dissertation.Acceptance.A.rem_beta1_dich_printed_false` — at `ν = 0` the system of
  Example 5.1(i) has an additive jump coefficient and satisfies Assumption 2.5 with `β₁ = 1`.
* `Dissertation.Acceptance.A.cor_margin_additive_printed_false` — at `ν = 0` every jump
  coefficient is additive and Example 5.1(i) satisfies (2.13) with a margin.
* `Dissertation.Acceptance.A.cor_margin_finite_printed_false` — at `ν = δ₀` one functional
  determines `u` and Example 5.1(i) satisfies (2.13) with a margin.
* `Dissertation.Acceptance.A.ex_fulllaw_beyond_Q_printed_false` — with the features `φ ≡ 0` the
  cylindrical term of `Q(s) = min{1, |s|}` is constant.
* `Dissertation.Acceptance.A.rem_freelaw_printed_false` — at `ν = 0` the jump coefficient takes
  values in `L²(ν) = {0}`.
* `Dissertation.Acceptance.A.rem_regimes_law_nonlinear_false` — the crowding correction is affine
  in the law.
* `Dissertation.Acceptance.A.rem_regimes_corr` — the corrected reading of Remark 5.7.
-/

open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal Matrix

namespace Dissertation.Acceptance.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence
  Dissertation.WellPosedness.Enlarged Dissertation.WellPosedness.Stability
  Dissertation.WellPosedness.Spec Dissertation.Law

universe v

/-- With the zero intensity, `L²(ν)` has one element. -/
theorem subsingleton_Lp_zero (m : ℕ) :
    Subsingleton (Lp (EuclideanSpace ℝ (Fin m)) 2 (0 : Measure PUnit.{1})) :=
  ⟨fun _ _ => Lp.ext (by simp [Filter.EventuallyEq])⟩

/-- **Remark 2.10, the `β₁` dichotomy, is false as printed at `ν = 0`.** Over a Lévy driver with
`ν = 0` on a point, the coefficients of Example 5.1(i) with `β₁ = β₂ = 1`, `n = m = d = 1` have a
jump coefficient depending on `t` and `x` only and satisfy Assumption 2.5 with `G = 1`, `α = 1`,
`β₁ = 1`, so additivity does not force `β₁ = 0`. -/
theorem rem_beta1_dich_printed_false : ¬ PaperSpec.A.rem_beta1_dich_printed.{0, 0, 0} := by
  intro h
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ :=
    LevyStochCalc.Driver.LevyDriver.exists 1 PUnit.{1} (0 : Measure PUnit.{1})
  have hind : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P := indep_bot_left _
  obtain ⟨hadd, h25⟩ :=
    rem_beta1_zero ⊥ 1 1 P D bot_le hind one_pos 1 one_pos 1 1 one_pos one_pos 0 0
  have h1 := (h ⊥ (0 : Measure PUnit.{1}) 1 1 1 P D bot_le hind one_pos one_pos 1 one_pos 1
    (by simp) 1 1 1 _ h25).2.1 hadd
  exact one_ne_zero h1.1

/-- **The paragraph after Corollary 3.6, the additive jump coefficient, is false as printed at
`ν = 0`.** Over a Lévy driver with `ν = 0` on a point, `L²(ν) = {0}`, so every jump coefficient
depends on `t` and `x` only, and the coefficients of Example 5.1(i) with `β₁ = β₂ = 1` satisfy
(2.13) at `G = 1` with the constants `0, 0` and the margin `1`. -/
theorem cor_margin_additive_printed_false :
    ¬ PaperSpec.A.cor_margin_additive_printed.{0, 0, 0} := by
  intro h
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ :=
    LevyStochCalc.Driver.LevyDriver.exists 1 PUnit.{1} (0 : Measure PUnit.{1})
  have hind : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P := indep_bot_left _
  haveI := subsingleton_Lp_zero 1
  obtain ⟨k, ℓ, -, -, hM⟩ := cor_margin_findim ⊥ (0 : Measure PUnit.{1}) 1 1 P D bot_le hind
    one_pos 1 one_pos inferInstance 0 0 1 le_rfl le_rfl one_pos 0 0
  exact h ⊥ (0 : Measure PUnit.{1}) 1 1 1 P D bot_le hind one_pos 1 one_pos 0 0 1 1 _ le_rfl
    one_pos (fun _ _ _ _ _ _ => Subsingleton.elim _ _) hM

/-- **The paragraph after Corollary 3.6, finitely many functionals, is false as printed when
`L²(ν)` is finite dimensional.** Over a Lévy driver with `d = 1` and `ν = δ₀` on `ℝ`, one linear
functional of `u` determines `u`, and the coefficients of Example 5.1(i) with `β₁ = β₂ = 1`,
whose jump coefficient depends on `u` only through it, satisfy (2.13) at `G = 1` with the
constants `0, 0` and the margin `1`. -/
theorem cor_margin_finite_printed_false :
    ¬ PaperSpec.A.cor_margin_finite_printed.{0, 0, 0} := by
  intro h
  obtain ⟨Ω, _, P, _, D, hind, hfin⟩ := cor_margin_findim_hypotheses
  obtain ⟨k, ℓ, -, hdep, hM⟩ := cor_margin_findim ⊥ (Measure.dirac (0 : ℝ)) 1 1 P D bot_le hind
    one_pos 1 one_pos hfin 0 0 1 le_rfl le_rfl one_pos 0 0
  exact h ⊥ (Measure.dirac (0 : ℝ)) 1 1 1 P D bot_le hind 1 one_pos 0 0 1 1 _ k ℓ le_rfl one_pos
    (fun t x y z u u' hu => hdep t (x, y, z, u) (x, y, z, u') _ _ hu) hM

/-- **Example 5.4, the cylindrical term as no expectation functional, is false as printed.** For
`ν = δ₀` on `ℝ`, `n = m = d = J = 1`, the bounded Lipschitz feature `φ ≡ 0` and the bounded
Lipschitz `Q(s) = min{1, |s₁|}`, which is not affine, the cylindrical term is `Q(0) = 0` at every
law, the expectation functional of `0`. -/
theorem ex_fulllaw_beyond_Q_printed_false : ¬ PaperSpec.A.ex_fulllaw_beyond_Q_printed.{0} := by
  intro h
  let Q : EuclideanSpace ℝ (Fin 1) → ℝ := fun s => min 1 |s 0|
  have hlip : ∀ v v', |Q v - Q v'| ≤ 1 * ‖v - v'‖ := by
    intro v v'
    rw [one_mul]
    calc |Q v - Q v'| ≤ max |(1 : ℝ) - 1| |(|v 0| - |v' 0|)| := abs_min_sub_min_le_max _ _ _ _
      _ = |(|v 0| - |v' 0|)| := by simp
      _ ≤ |v 0 - v' 0| := abs_abs_sub_abs_le_abs_sub _ _
      _ = ‖(v - v') 0‖ := by simp [Real.norm_eq_abs]
      _ ≤ ‖v - v'‖ := PiLp.norm_apply_le _ _
  have hbd : ∀ v, |Q v| ≤ 1 := fun v => by
    rw [abs_of_nonneg (le_min zero_le_one (abs_nonneg _))]
    exact min_le_left _ _
  have hnaff : ¬ ∃ (a : ℝ) (c : Fin 1 → ℝ),
      ∀ s : EuclideanSpace ℝ (Fin 1), Q s = a + ∑ j, c j * s j := by
    rintro ⟨a, c, hc⟩
    have h0 := hc 0
    have h1 := hc (EuclideanSpace.single 0 1)
    have h2 := hc (EuclideanSpace.single 0 (-1))
    simp [Q] at h0 h1 h2
    linarith
  obtain ⟨μ, hμ⟩ := h (Measure.dirac (0 : ℝ)) 1 1 1 1 Q (fun _ _ => 0) 1 1 0 (fun _ => 0) hlip hbd
    (by simp) (by simp) hnaff (fun _ => 0) (fun _ => integrable_zero _ _ _)
  apply hμ
  have e : (WithLp.toLp 2 fun _ : Fin 1 => ∫ _, (0 : ℝ) ∂μ.margU.law :
      EuclideanSpace ℝ (Fin 1)) = 0 := by
    ext j
    simp
  rw [e]
  simp [Q]

/-- **Remark 5.6, the measure argument, is false as printed at `ν = 0`.** Over a Lévy driver with
`ν = 0` on a point, the coefficients of Example 5.1(i) with `β₁ = β₂ = 1`, `n = m = d = 1` satisfy
Assumption 2.5 with `G = 1`, `α = 1`, `β₁ = 1`, and the jump coefficient takes values in
`L²(ν) = {0}`, so it never differs at two inputs. -/
theorem rem_freelaw_printed_false : ¬ PaperSpec.A.rem_freelaw_printed.{0, 0, 0} := by
  intro h
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ :=
    LevyStochCalc.Driver.LevyDriver.exists 1 PUnit.{1} (0 : Measure PUnit.{1})
  have hind : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P := indep_bot_left _
  haveI := subsingleton_Lp_zero 1
  obtain ⟨-, h25⟩ :=
    rem_beta1_zero ⊥ 1 1 P D bot_le hind one_pos 1 one_pos 1 1 one_pos one_pos 0 0
  have hae := h ⊥ (0 : Measure PUnit.{1}) 1 1 1 P D bot_le hind one_pos one_pos one_pos 1 one_pos
    1 (by simp) 1 1 1 _ h25 one_pos
  have hfalse : ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), False :=
    hae.mono fun t ⟨p, _, p', _, _, _, hne⟩ =>
      hne (Filter.Eventually.of_forall fun _ => Subsingleton.elim _ _)
  have h0 : volume.restrict (Set.Icc (0 : ℝ) 1) = 0 := by
    rwa [Filter.eventually_false_iff_eq_bot, ae_eq_bot] at hfalse
  have h1 := congrArg (fun μ : Measure ℝ => μ Set.univ) h0
  simp at h1

/-- **Remark 5.7, the dealer interaction as a nonlinear `U`-law interaction, is false as
printed.** For `ν = δ₀` on `ℝ`, the crowding correction of Example 5.5 is affine in the law. -/
theorem rem_regimes_law_nonlinear_false : ¬ PaperSpec.A.rem_regimes_law_nonlinear.{0} := by
  intro h
  obtain ⟨Λ₁, Λ₂, s, hs, u, hne⟩ := h (Measure.dirac (0 : ℝ))
  exact hne ((ex_dealer_affine (Measure.dirac (0 : ℝ))).1 Λ₁ Λ₂ s hs u)

/-- **Remark 5.7, the dealer interaction, corrected.** With `L²(ν)` not reduced to `0`, the
crowding correction of Example 5.5 is affine in the law, no function of its mean, and nonlinear
in the valuation curve. -/
theorem rem_regimes_corr : PaperSpec.A.rem_regimes_corr.{v} := by
  intro E _ ν _ _ hne
  obtain ⟨h1, h2⟩ := ex_dealer_not_mean_corr ν hne
  exact ⟨(ex_dealer_affine ν).1, h1, h2⟩

end Dissertation.Acceptance.A
