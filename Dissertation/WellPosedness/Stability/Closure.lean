/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The rank-case closure and absorption step of Lemma 4.3

Step 5 of the proof of Lemma 4.3 of the paper is real algebra on the expected sizes of the
difference `(δX, δY, δZ, δU)` of two solutions:

* `A = 𝔼|δX_T|²`, `Y₀ = 𝔼|δY_0|²`, `I_X = 𝔼 ∫_0^T |δX|²` and
  `J = 𝔼 ∫_0^T (|δY|² + |δZ|²_F + ‖δU‖²_{L²(ν)})`, with `N' = A + Y₀ + I_X + J`;
* the data size `P`;
* the coercive blocks `𝔼|GδX_T|²`, `𝔼 ∫_0^T |GδX|²` and
  `𝔼 ∫_0^T (|GᵀδY|² + |GᵀδZ|²_F + ‖GᵀδU‖²)`.

Its inputs are the forward estimate `A + I_X ≤ k_F (J + P)`, the backward estimate
`Y₀ + J ≤ k_B (A + I_X + P)`, the coercivity bound (4.22) with `K = η N' + (‖G‖²/4η) P` for
every `η > 0`, and the rank case of Assumption 2.4. In Case A (`β₁ > 0`, `Gᵀ` coercive) the
`β₁`-block bounds `λ̲ β₁ J / c_G`; in Case B (`α, β₂ > 0`, `G` coercive) the `α`- and
`β₂`-blocks bound `λ̲ min(α, β₂) (A + I_X) / c_G`. Either way `N' ≤ M (x + P)` with
`x ≤ a (η N' + (‖G‖²/4η) P)` for every `η > 0`, and the choice `η = 1/(2Ma + 1)` absorbs the
`N'`-term:

`N' ≤ (M a ‖G‖² (2 M a + 1)/2 + 2 M) P`.

Since `a = c_G/(λ̲ β₁)` or `a = c_G/(λ̲ min(α, β₂))` and `a` enters quadratically, the constant
is of order `λ̲⁻²` in the lower bound `λ̲` of the homotopy parameter: coercivity of size `λ̲` is
paired against the data linearly.

## Main definitions

* `absorbConst` — the constant `M a g² (2 M a + 1)/2 + 2 M` of the absorption.
* `closureConst` — the sum of the Case A and Case B constants.

## Main statements

* `le_absorbConst_mul` — the absorption of a free multiple of `N'`.
* `closure_le` — Step 5: `N' ≤ closureConst · P`.
-/

namespace Dissertation.WellPosedness.Stability

/-- The constant `M a g² (2 M a + 1)/2 + 2 M` produced by absorbing a free multiple of `N'` when
`N' ≤ M (x + P)` and `x ≤ a (η N' + (g²/4η) P)` for every `η > 0`. -/
noncomputable def absorbConst (M a g : ℝ) : ℝ := M * a * g ^ 2 * (2 * M * a + 1) / 2 + 2 * M

/-- The closure constant of Lemma 4.3: the Case A constant, with `M = k_F (1 + k_B) + k_B` and
`a = c_G/(λ̲ β₁)`, plus the Case B constant, with `M = 1 + k_B` and `a = c_G/(λ̲ min(α, β₂))`. -/
noncomputable def closureConst (kF kB gG cG α β₁ β₂ lamLow : ℝ) : ℝ :=
  absorbConst (kF * (1 + kB) + kB) (cG / (lamLow * β₁)) gG
    + absorbConst (1 + kB) (cG / (lamLow * min α β₂)) gG

/-- The absorption constant is nonnegative for nonnegative `M` and `a`. -/
theorem absorbConst_nonneg {M a : ℝ} (hM : 0 ≤ M) (ha : 0 ≤ a) (g : ℝ) :
    0 ≤ absorbConst M a g := by
  unfold absorbConst
  positivity

/-- **The absorption.** If `N ≤ M (x + P)` and `x ≤ a (η N + (g²/4η) P)` for every `η > 0`,
then `N ≤ (M a g² (2 M a + 1)/2 + 2 M) P`. -/
theorem le_absorbConst_mul {N x P M a g : ℝ} (hN : 0 ≤ N) (hM : 0 ≤ M) (ha : 0 ≤ a)
    (hNx : N ≤ M * (x + P)) (hx : ∀ η : ℝ, 0 < η → x ≤ a * (η * N + g ^ 2 / (4 * η) * P)) :
    N ≤ absorbConst M a g * P := by
  set k : ℝ := 2 * M * a + 1 with hk
  have hMa : 0 ≤ M * a := mul_nonneg hM ha
  have hkpos : 0 < k := by rw [hk]; linarith
  have hx' := hx (1 / k) (by positivity)
  have e : g ^ 2 / (4 * (1 / k)) = g ^ 2 * k / 4 := by field_simp
  rw [e] at hx'
  have h1 : M * x ≤ M * (a * (1 / k * N + g ^ 2 * k / 4 * P)) :=
    mul_le_mul_of_nonneg_left hx' hM
  have h2 : M * a / k ≤ 1 / 2 := by
    rw [div_le_iff₀ hkpos, hk]
    linarith
  have h3 : M * a / k * N ≤ 1 / 2 * N := mul_le_mul_of_nonneg_right h2 hN
  have h4 : M * (a * (1 / k * N + g ^ 2 * k / 4 * P))
      = M * a / k * N + M * a * g ^ 2 * k / 4 * P := by
    field_simp
  unfold absorbConst
  rw [← hk]
  nlinarith

variable {A Y₀ IX J P GXT GIX GIY kF kB gG cG α β₁ β₂ lam lamLow : ℝ}

/-- **Case A of the closure.** With `β₁ > 0` and
`J ≤ c_G · 𝔼 ∫ (|GᵀδY|² + |GᵀδZ|²_F + ‖GᵀδU‖²)`, the `β₁`-block of (4.22) controls `J`, the
forward estimate then controls `A + I_X` and the backward estimate `Y₀`, and absorption gives
`N' ≤ C_A P`. -/
theorem closure_caseA (hA : 0 ≤ A) (hY₀ : 0 ≤ Y₀) (hIX : 0 ≤ IX) (hJ : 0 ≤ J) (hP : 0 ≤ P)
    (hGXT : 0 ≤ GXT) (hGIX : 0 ≤ GIX) (hGIY : 0 ≤ GIY) (hkF : 0 ≤ kF) (hkB : 0 ≤ kB)
    (hcG : 0 ≤ cG) (hα : 0 ≤ α) (hβ₂ : 0 ≤ β₂) (hlow : 0 < lamLow) (hlam : lamLow ≤ lam)
    (hF : A + IX ≤ kF * (J + P)) (hB : Y₀ + J ≤ kB * (A + IX + P))
    (hco : ∀ η : ℝ, 0 < η → lam * (α * GXT + β₂ * GIX + β₁ * GIY)
      ≤ η * (A + Y₀ + IX + J) + gG ^ 2 / (4 * η) * P)
    (hβ₁ : 0 < β₁) (hJc : J ≤ cG * GIY) :
    A + Y₀ + IX + J ≤ absorbConst (kF * (1 + kB) + kB) (cG / (lamLow * β₁)) gG * P := by
  have hM : 0 ≤ kF * (1 + kB) + kB := by positivity
  have hlb : 0 < lamLow * β₁ := mul_pos hlow hβ₁
  refine le_absorbConst_mul (x := J) (by linarith) hM (div_nonneg hcG hlb.le) ?_ ?_
  · nlinarith [mul_le_mul_of_nonneg_left hF hkB]
  · intro η hη
    have hblock : lamLow * β₁ * GIY ≤ η * (A + Y₀ + IX + J) + gG ^ 2 / (4 * η) * P := by
      have h1 : lamLow * β₁ * GIY ≤ lam * (β₁ * GIY) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right hlam (mul_nonneg hβ₁.le hGIY)
      have h2 : lam * (β₁ * GIY) ≤ lam * (α * GXT + β₂ * GIX + β₁ * GIY) :=
        mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg hα hGXT, mul_nonneg hβ₂ hGIX])
          (hlow.le.trans hlam)
      exact h1.trans (h2.trans (hco η hη))
    calc J ≤ cG * GIY := hJc
      _ = cG / (lamLow * β₁) * (lamLow * β₁ * GIY) := by field_simp
      _ ≤ cG / (lamLow * β₁) * (η * (A + Y₀ + IX + J) + gG ^ 2 / (4 * η) * P) :=
          mul_le_mul_of_nonneg_left hblock (div_nonneg hcG hlb.le)

/-- **Case B of the closure.** With `α, β₂ > 0`, `A ≤ c_G 𝔼|GδX_T|²` and
`I_X ≤ c_G 𝔼 ∫ |GδX|²`, the `α`- and `β₂`-blocks of (4.22) control `A + I_X`, the backward
estimate then controls `Y₀ + J`, and absorption gives `N' ≤ C_B P`. -/
theorem closure_caseB (hA : 0 ≤ A) (hY₀ : 0 ≤ Y₀) (hIX : 0 ≤ IX) (hJ : 0 ≤ J) (hP : 0 ≤ P)
    (hGXT : 0 ≤ GXT) (hGIX : 0 ≤ GIX) (hGIY : 0 ≤ GIY) (hkB : 0 ≤ kB)
    (hcG : 0 ≤ cG) (hβ₁ : 0 ≤ β₁) (hlow : 0 < lamLow) (hlam : lamLow ≤ lam)
    (hB : Y₀ + J ≤ kB * (A + IX + P))
    (hco : ∀ η : ℝ, 0 < η → lam * (α * GXT + β₂ * GIX + β₁ * GIY)
      ≤ η * (A + Y₀ + IX + J) + gG ^ 2 / (4 * η) * P)
    (hα : 0 < α) (hβ₂ : 0 < β₂) (hAc : A ≤ cG * GXT) (hIXc : IX ≤ cG * GIX) :
    A + Y₀ + IX + J ≤ absorbConst (1 + kB) (cG / (lamLow * min α β₂)) gG * P := by
  have hM : 0 ≤ 1 + kB := by positivity
  have hμ : 0 < min α β₂ := lt_min hα hβ₂
  have hlb : 0 < lamLow * min α β₂ := mul_pos hlow hμ
  refine le_absorbConst_mul (x := A + IX) (by linarith) hM (div_nonneg hcG hlb.le) ?_ ?_
  · nlinarith
  · intro η hη
    have hblock : lamLow * min α β₂ * (GXT + GIX)
        ≤ η * (A + Y₀ + IX + J) + gG ^ 2 / (4 * η) * P := by
      have h1 : lamLow * min α β₂ * (GXT + GIX) ≤ lam * (α * GXT + β₂ * GIX) := by
        have e1 : min α β₂ * GXT ≤ α * GXT := mul_le_mul_of_nonneg_right (min_le_left _ _) hGXT
        have e2 : min α β₂ * GIX ≤ β₂ * GIX := mul_le_mul_of_nonneg_right (min_le_right _ _) hGIX
        have e3 : lamLow * (α * GXT + β₂ * GIX) ≤ lam * (α * GXT + β₂ * GIX) :=
          mul_le_mul_of_nonneg_right hlam (by positivity)
        nlinarith
      have h2 : lam * (α * GXT + β₂ * GIX) ≤ lam * (α * GXT + β₂ * GIX + β₁ * GIY) :=
        mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg hβ₁ hGIY]) (hlow.le.trans hlam)
      exact h1.trans (h2.trans (hco η hη))
    calc A + IX ≤ cG * (GXT + GIX) := by linarith
      _ = cG / (lamLow * min α β₂) * (lamLow * min α β₂ * (GXT + GIX)) := by field_simp
      _ ≤ cG / (lamLow * min α β₂) * (η * (A + Y₀ + IX + J) + gG ^ 2 / (4 * η) * P) :=
          mul_le_mul_of_nonneg_left hblock (div_nonneg hcG hlb.le)

/-- **Step 5 of Lemma 4.3: the rank-case closure and absorption.** Given the forward and
backward estimates, the coercivity bound (4.22) for every `η > 0`, and Case A or Case B,

`𝔼|δX_T|² + 𝔼|δY_0|² + 𝔼 ∫_0^T (|δX|² + |δY|² + |δZ|²_F + ‖δU‖²) ≤ closureConst · P`. -/
theorem closure_le (hA : 0 ≤ A) (hY₀ : 0 ≤ Y₀) (hIX : 0 ≤ IX) (hJ : 0 ≤ J) (hP : 0 ≤ P)
    (hGXT : 0 ≤ GXT) (hGIX : 0 ≤ GIX) (hGIY : 0 ≤ GIY) (hkF : 0 ≤ kF) (hkB : 0 ≤ kB)
    (hcG : 0 ≤ cG) (hα : 0 ≤ α) (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂) (hlow : 0 < lamLow)
    (hlam : lamLow ≤ lam) (hF : A + IX ≤ kF * (J + P)) (hB : Y₀ + J ≤ kB * (A + IX + P))
    (hco : ∀ η : ℝ, 0 < η → lam * (α * GXT + β₂ * GIX + β₁ * GIY)
      ≤ η * (A + Y₀ + IX + J) + gG ^ 2 / (4 * η) * P)
    (hcase : (0 < β₁ ∧ J ≤ cG * GIY) ∨ (0 < α ∧ 0 < β₂ ∧ A ≤ cG * GXT ∧ IX ≤ cG * GIX)) :
    A + Y₀ + IX + J ≤ closureConst kF kB gG cG α β₁ β₂ lamLow * P := by
  have hCA : 0 ≤ absorbConst (kF * (1 + kB) + kB) (cG / (lamLow * β₁)) gG :=
    absorbConst_nonneg (by positivity) (div_nonneg hcG (mul_nonneg hlow.le hβ₁)) gG
  have hCB : 0 ≤ absorbConst (1 + kB) (cG / (lamLow * min α β₂)) gG :=
    absorbConst_nonneg (by positivity) (div_nonneg hcG (mul_nonneg hlow.le (le_min hα hβ₂))) gG
  unfold closureConst
  rcases hcase with ⟨hβ₁', hJc⟩ | ⟨hα', hβ₂', hAc, hIXc⟩
  · have h := closure_caseA hA hY₀ hIX hJ hP hGXT hGIX hGIY hkF hkB hcG hα hβ₂ hlow hlam hF hB
      hco hβ₁' hJc
    nlinarith [mul_nonneg hCB hP]
  · have h := closure_caseB hA hY₀ hIX hJ hP hGXT hGIX hGIY hkB hcG hβ₁ hlow hlam hB hco hα'
      hβ₂' hAc hIXc
    nlinarith [mul_nonneg hCA hP]

end Dissertation.WellPosedness.Stability
