/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.PaperSpec.Sec2
import MVFBSDEJ.Acceptance.Sec3Space
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Topology.UniformSpace.Uniformizable

/-!
# Instances of the hypotheses of the setting statements of the well-posedness paper

For a statement of §2, §3 or Example 5.1 with hypotheses, an instance the manuscript intends at
which the hypotheses hold. The intensity is `ν = δ₀` on `ℝ` (Lebesgue measure on `ℝ` for the
separability of `L²(ν; ℝʲ)`), `n = m = d = 1`, and the random elements live on `Ω = Bool` with the
uniform law; `θ₁ ∈ H` is the point all of whose channels are `1`, its `U`-channel the constant
`1 ∈ L²(δ₀)`.

## Main statements

* `MVFBSDEJ.Acceptance.sec2_separable_hypotheses` — the hypotheses of the separability of
  `L²(ν; ℝʲ)`, at Lebesgue measure on `ℝ` and `j = 1`.
* `MVFBSDEJ.Acceptance.eq_fubiniiso_hypotheses` — the hypotheses of (2.4), at
  `μ = dP ⊗ dt` on `Bool × [0, 1]` and `ν = δ₀`.
* `MVFBSDEJ.Acceptance.eq_coupling_hypotheses` — the hypotheses of (2.8), at the random
  tuples `1_{true} θ₁` and `1_{false} θ₁`.
* `MVFBSDEJ.Acceptance.eq_couplingT_hypotheses` — the hypotheses of (2.9), at the random
  vectors `1_{true} e₁` and `1_{false} e₁`.
* `MVFBSDEJ.Acceptance.eq_margproj_hypotheses` — the hypotheses of (2.11), at the Dirac
  masses at `0` and `θ₁`.
* `MVFBSDEJ.Acceptance.sec3_HH_inclusion_hypotheses` — the hypotheses of `𝕊 ⊂ ℍ²`, at
  the forward component of the solution of Example 5.1(i) from `ξ₀ ≡ e₁`.
* `MVFBSDEJ.Acceptance.ex_concrete_i_ham_hypotheses` — the hypotheses of the Hamiltonian
  claim of Example 5.1(i), at `ν = δ₀` and `β₁ = 1`.
* `MVFBSDEJ.Acceptance.ex_concrete_ii_mean_hypotheses` — the hypotheses of the mean and
  barycentre claim of Example 5.1(ii), at `ν = δ₀`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MVFBSDEJ.Acceptance

open MVFBSDEJ.WellPosedness.System MVFBSDEJ.WellPosedness.Existence
  MVFBSDEJ.WellPosedness.Enlarged MVFBSDEJ.WellPosedness.Stability
  MVFBSDEJ.WellPosedness.Spec MVFBSDEJ.Law MVFBSDEJ.PaperSpec

/-- The point `θ₁ = (1, 1, 1, 1)` of `H = ℝ × ℝ × ℝ^{1×1} × L²(δ₀; ℝ)`. -/
local notation "θ₁" => ((EuclideanSpace.single 0 1, EuclideanSpace.single 0 1,
  EuclideanSpace.single (0, 0) 1, Lp.const 2 (Measure.dirac (0 : ℝ)) (EuclideanSpace.single 0 1))
  : TupleH (Measure.dirac (0 : ℝ)) 1 1 1)

/-- The uniform law on `Bool`. -/
local notation "P𝔹" => PMF.toMeasure (PMF.uniformOfFintype Bool)

/-- The uniform law on `Bool` charges `{true}`. -/
private theorem uniformBool_true_ne_zero : P𝔹 {true} ≠ 0 := by
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), PMF.uniformOfFintype_apply]
  simp

/-- The constant `e₁ ∈ L²(δ₀; ℝ¹)` is not zero. -/
private theorem lpConst_ne_zero :
    Lp.const 2 (Measure.dirac (0 : ℝ)) (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) ≠ 0 := by
  intro h
  have h1 := congrArg (fun u : Lp (EuclideanSpace ℝ (Fin 1)) 2 (Measure.dirac (0 : ℝ)) => ‖u‖) h
  simp only [norm_zero] at h1
  rw [Lp.norm_const' _ _ _ two_ne_zero ENNReal.ofNat_ne_top] at h1
  simp at h1

/-- The point `θ₁` of `H` is not the origin. -/
private theorem theta_one_ne_zero : θ₁ ≠ 0 := by
  intro h
  have h1 := congrArg (fun θ : TupleH (Measure.dirac (0 : ℝ)) 1 1 1 => θ.1 0) h
  simp at h1

/-! ### §2 -/

/-- **The hypotheses of the separability claim of §2 hold** at Lebesgue measure on `ℝ`, which is
σ-finite of infinite mass on a countably generated space, and `j = 1`. -/
theorem sec2_separable_hypotheses :
    SigmaFinite (volume : Measure ℝ) ∧ MeasurableSpace.CountablyGenerated ℝ
      ∧ (volume : Measure ℝ) Set.univ = ⊤ ∧ 1 ≤ 1 :=
  ⟨inferInstance, inferInstance, Real.volume_univ, le_rfl⟩

/-- **The hypotheses of (2.4) hold** at `μ = dP ⊗ dt` on `Bool × ℝ`, with `P` the uniform law and
`dt` Lebesgue measure on `[0, 1]`, of total mass `1`, and at `ν = δ₀` on `ℝ` and `j = 1`. -/
theorem eq_fubiniiso_hypotheses :
    SigmaFinite (Measure.prod P𝔹 (volume.restrict (Set.Icc (0 : ℝ) 1)))
      ∧ Measure.prod P𝔹 (volume.restrict (Set.Icc (0 : ℝ) 1)) Set.univ = 1
      ∧ SigmaFinite (Measure.dirac (0 : ℝ)) ∧ Measure.dirac (0 : ℝ) ≠ 0
      ∧ MeasurableSpace.CountablyGenerated ℝ := by
  refine ⟨inferInstance, ?_, inferInstance, Measure.dirac_ne_zero, inferInstance⟩
  rw [← Set.univ_prod_univ, Measure.prod_prod, measure_univ, Measure.restrict_apply_univ,
    Real.volume_Icc]
  simp

/-- **The hypotheses of (2.8) hold at two random tuples that are not almost surely equal.** At
`ν = δ₀` on `ℝ` and `n = m = d = 1`, the random tuples `1_{true} θ₁` and `1_{false} θ₁` on `Bool`
with the uniform law are square integrable and differ on `{true}`. -/
theorem eq_coupling_hypotheses :
    IsProbabilityMeasure P𝔹 ∧ SigmaFinite (Measure.dirac (0 : ℝ)) ∧ Measure.dirac (0 : ℝ) ≠ 0
      ∧ MeasurableSpace.CountablyGenerated ℝ
      ∧ MemLp (fun b : Bool => if b then θ₁ else 0) 2 P𝔹
      ∧ MemLp (fun b : Bool => if b then 0 else θ₁) 2 P𝔹
      ∧ ¬ (fun b : Bool => if b then θ₁ else 0) =ᵐ[P𝔹] fun b : Bool => if b then 0 else θ₁ := by
  refine ⟨inferInstance, inferInstance, Measure.dirac_ne_zero, inferInstance, MemLp.of_discrete,
    MemLp.of_discrete, fun h => ?_⟩
  rw [Filter.EventuallyEq, ae_iff_of_countable] at h
  exact theta_one_ne_zero (by simpa using h true uniformBool_true_ne_zero)

/-- **The hypotheses of (2.9) hold at two random vectors that are not almost surely equal**: the
random vectors `1_{true} e₁` and `1_{false} e₁` of `ℝ¹` on `Bool` with the uniform law are square
integrable and differ on `{true}`. -/
theorem eq_couplingT_hypotheses :
    IsProbabilityMeasure P𝔹
      ∧ MemLp (fun b : Bool => if b then EuclideanSpace.single (0 : Fin 1) (1 : ℝ) else 0) 2 P𝔹
      ∧ MemLp (fun b : Bool => if b then 0 else EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) 2 P𝔹
      ∧ ¬ (fun b : Bool => if b then EuclideanSpace.single (0 : Fin 1) (1 : ℝ) else 0)
          =ᵐ[P𝔹] fun b : Bool => if b then 0 else EuclideanSpace.single (0 : Fin 1) (1 : ℝ) := by
  refine ⟨inferInstance, MemLp.of_discrete, MemLp.of_discrete, fun h => ?_⟩
  rw [Filter.EventuallyEq, ae_iff_of_countable] at h
  have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin 1) => v 0) (h true uniformBool_true_ne_zero)
  simp at h1

/-- **The hypotheses of (2.11) hold at two laws with distinct `U`-marginals.** At `ν = δ₀` on `ℝ`
and `n = m = d = 1`, `ν` is σ-finite and nonzero on a countably generated space, and the Dirac
masses at `0` and at `θ₁` are laws of `P₂(H)` whose `U`-marginals differ. -/
theorem eq_margproj_hypotheses :
    SigmaFinite (Measure.dirac (0 : ℝ)) ∧ Measure.dirac (0 : ℝ) ≠ 0
      ∧ MeasurableSpace.CountablyGenerated ℝ
      ∧ (P2.dirac (0 : TupleH (Measure.dirac (0 : ℝ)) 1 1 1)).margU ≠ (P2.dirac θ₁).margU := by
  refine ⟨inferInstance, Measure.dirac_ne_zero, inferInstance, fun h => ?_⟩
  rw [margU_dirac, margU_dirac] at h
  have h1 := congrArg (fun μ => w2P (P2.dirac (0 : Lp (EuclideanSpace ℝ (Fin 1)) 2
    (Measure.dirac (0 : ℝ)))) μ) h
  simp only [w2P, P2.dirac, w2_dirac_dirac, Prod.snd_zero, sub_zero, zero_sub, norm_neg,
    norm_zero] at h1
  exact lpConst_ne_zero (norm_eq_zero.mp h1.symm)

/-! ### §3 -/

/-- **The hypotheses of the inclusion `𝕊 ⊂ ℍ²` hold at a nonzero process of `𝕊`.** Over a
probability space carrying a Lévy driver with `d = 1` and `ν = δ₀` on `ℝ`, with `𝒢₀ = ⊥`,
`n = m = 1` and `T = 1 ≥ 0`, the forward component `X` of the solution of Example 5.1(i)
(`β₁ = β₂ = 1`, `σ_c = h_c = 0`) from `ξ₀ ≡ e₁` has `𝔼 sup_{t ≤ 1} |X_t|² < ∞` and `X_0 = 1`
almost surely. -/
theorem sec3_HH_inclusion_hypotheses :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyStochCalc.Driver.LevyDriver P 1 (Measure.dirac (0 : ℝ)))
      (hind₀ : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P)
      (X : Fin 1 → ℝ → Ω → ℝ) (Y : Fin 1 → ℝ → Ω → ℝ) (Z : Fin 1 → ℝ → Ω → Fin 1 → ℝ)
      (U : Fin 1 → ℝ → Ω → ℝ → ℝ),
      Solution D bot_le hind₀ 1
          (affineCoeffs (ν := Measure.dirac (0 : ℝ)) (n := 1) (d := 1) 1 1 0 0)
          (fun _ => EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) X Y Z U
      ∧ (0 : ℝ) ≤ 1
      ∧ ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) 1, esq (fun i => X i t ω)) ∂P < ⊤
      ∧ ∀ᵐ ω ∂P, X 0 0 ω = 1 := by
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ := LevyStochCalc.Driver.LevyDriver.exists 1 ℝ (Measure.dirac (0 : ℝ))
  have hind₀ : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P := indep_bot_left _
  obtain ⟨hJ, h22, h23, hG, h25⟩ :=
    affine_assumptions (ν := Measure.dirac (0 : ℝ)) (ℱ := enlJoint ⊥ D bot_le) (P := P) (T := 1)
      (σc := 0) (hc := 0) one_pos one_pos (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))
  have e₁ : max (max (1 : ℝ) 1) 1 = 1 := by norm_num
  rw [e₁] at h23
  obtain ⟨X, Y, Z, U, hS⟩ := (thm_cwp ⊥ _ 1 1 1 P D bot_le hind₀ one_pos one_pos one_pos 1
    one_pos 1 1 1 1 1 _ _ hJ h22 h23 hG h25).1
  refine ⟨Ω, inferInstance, P, inferInstance, D, hind₀, X, Y, Z, U, hS, zero_le_one, hS.2.1, ?_⟩
  filter_upwards [Solution.X_zero_ae zero_le_one hS 0] with ω hω
  rw [hω]
  simp

/-! ### Example 5.1 -/

/-- **The hypotheses of the Hamiltonian claim of Example 5.1(i) hold** at `ν = δ₀` on `ℝ` and
`β₁ = 1`: `ν` is nonzero and `β₁ > 0`. -/
theorem ex_concrete_i_ham_hypotheses : Measure.dirac (0 : ℝ) ≠ 0 ∧ (0 : ℝ) < 1 :=
  ⟨Measure.dirac_ne_zero, one_pos⟩

/-- **The hypotheses of the mean and barycentre claim of Example 5.1(ii) hold** at `ν = δ₀` on
`ℝ`, σ-finite and nonzero on a countably generated space; the Dirac masses at `0` and `θ₁` on `H`
have distinct means, and the Dirac masses at `0` and `e₁` on `ℝ¹` distinct barycentres. -/
theorem ex_concrete_ii_mean_hypotheses :
    SigmaFinite (Measure.dirac (0 : ℝ)) ∧ Measure.dirac (0 : ℝ) ≠ 0
      ∧ MeasurableSpace.CountablyGenerated ℝ
      ∧ tupleMean (P2.dirac (0 : TupleH (Measure.dirac (0 : ℝ)) 1 1 1)) ≠ tupleMean (P2.dirac θ₁)
      ∧ barycentre (P2.dirac (0 : EuclideanSpace ℝ (Fin 1)))
          ≠ barycentre (P2.dirac (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))) := by
  refine ⟨inferInstance, Measure.dirac_ne_zero, inferInstance, ?_, ?_⟩
  · rw [tupleMean_dirac, tupleMean_dirac]
    exact theta_one_ne_zero.symm
  · intro h
    have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin 1) => v 0) h
    simp [barycentre, P2.dirac] at h1

end MVFBSDEJ.Acceptance
