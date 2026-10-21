/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Dissertation.Law.P2Separation

/-!
# Completeness of the 2-Wasserstein space

On a separable Banach space `E` the laws of finite second moment with the 2-Wasserstein distance
form a complete space. For a sequence `μ_k` with `W₂(μ_k, μ_{k+1}) < 2^{-k}`, choose couplings
`γ_k` of `(μ_k, μ_{k+1})` of quadratic cost below `4^{-k}`. Disintegrating each `γ_k` along its
first marginal gives Markov kernels, and the Ionescu-Tulcea theorem chains them into one law on
`E^ℕ` under which consecutive coordinates `(ξ_k, ξ_{k+1})` have the joint law `γ_k`. The
coordinates then form a Cauchy sequence in `L²(E^ℕ; E)`, whose limit `ξ` has a law of finite
second moment, and the coupling bound gives `W₂(μ_k, Law ξ) ≤ ‖ξ_k − ξ‖_{L²} → 0`.

## Main definitions

* `Dissertation.Law.chainKernel` — the transition kernels of the chain of a sequence of couplings.
* `Dissertation.Law.chainLaw` — the law of that chain on `E^ℕ`.

## Main statements

* `Dissertation.Law.chainLaw_map` — under the chain law the coordinate `ξ_n` has law `μ_n` and
  the pair `(ξ_n, ξ_{n+1})` has law `γ_n`.
* `Dissertation.Law.P2W.instCompleteSpace` — the 2-Wasserstein space of a separable Banach space
  is complete.
-/

namespace Dissertation.Law

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal

/-! ### The chain of a sequence of couplings -/

section Chain

/-- Composing a measure with a kernel pulled back along `f` and pushing the first coordinate
forward along `f` composes the image measure with the kernel. -/
theorem map_prodMap_compProd_comap {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (ρ : Measure α) [SFinite ρ] (κ : Kernel β γ) [IsSFiniteKernel κ]
    {f : α → β} (hf : Measurable f) :
    (ρ ⊗ₘ κ.comap f hf).map (Prod.map f id) = ρ.map f ⊗ₘ κ := by
  ext s hs
  rw [Measure.map_apply (hf.prodMap measurable_id) hs,
    Measure.compProd_apply ((hf.prodMap measurable_id) hs), Measure.compProd_apply hs,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hf]
  rfl

variable {E : Type*} [MeasurableSpace E] [StandardBorelSpace E] [Nonempty E]

/-- The transition kernels of the chain of a sequence of couplings `γ n` on `E × E`: from the
trajectory up to time `n`, the next point is drawn from the disintegration of `γ n` along its
first coordinate, at the current point. -/
noncomputable def chainKernel (γ : ℕ → Measure (E × E)) [∀ n, IsFiniteMeasure (γ n)] (n : ℕ) :
    Kernel (Π _ : Iic n, E) E :=
  (γ n).condKernel.comap (fun x => x ⟨n, mem_Iic.2 le_rfl⟩) (measurable_pi_apply _)

instance (γ : ℕ → Measure (E × E)) [∀ n, IsFiniteMeasure (γ n)] (n : ℕ) :
    IsMarkovKernel (chainKernel γ n) := by
  unfold chainKernel
  infer_instance

/-- The law on `E^ℕ` of the chain of a sequence of couplings `γ n`, started at `μ₀`. -/
noncomputable def chainLaw (μ₀ : Measure E) (γ : ℕ → Measure (E × E))
    [∀ n, IsFiniteMeasure (γ n)] : Measure (ℕ → E) :=
  Kernel.trajMeasure (X := fun _ => E) μ₀ (chainKernel γ)

instance (μ₀ : Measure E) [IsProbabilityMeasure μ₀] (γ : ℕ → Measure (E × E))
    [∀ n, IsFiniteMeasure (γ n)] : IsProbabilityMeasure (chainLaw μ₀ γ) := by
  unfold chainLaw
  infer_instance

/-- Under the chain law the initial coordinate has the initial law. -/
theorem chainLaw_map_zero (μ₀ : Measure E) [IsProbabilityMeasure μ₀]
    (γ : ℕ → Measure (E × E)) [∀ n, IsFiniteMeasure (γ n)] :
    (chainLaw μ₀ γ).map (fun x => x 0) = μ₀ := by
  have h0 : (fun x : ℕ → E => x 0)
      = (fun y : Π _ : Iic 0, E => y ⟨0, mem_Iic.2 le_rfl⟩) ∘ Preorder.frestrictLe 0 := rfl
  have hm : Measurable fun y : Π _ : Iic 0, E => y ⟨0, mem_Iic.2 le_rfl⟩ :=
    measurable_pi_apply _
  rw [h0, ← Measure.map_map hm (Preorder.measurable_frestrictLe 0), chainLaw,
    Kernel.trajMeasure, Measure.map_comp _ _ (Preorder.measurable_frestrictLe 0),
    Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, Measure.id_comp,
    Measure.map_map hm (MeasurableEquiv.measurable _)]
  convert Measure.map_id (μ := μ₀)
  funext y
  rfl

/-- **The marginals of the chain law.** For couplings `γ n` of `(μ n, μ (n + 1))`, under the
chain law started at `μ 0` the coordinate `ξ_n` has law `μ n` and the pair `(ξ_n, ξ_{n+1})` has
law `γ n`. -/
theorem chainLaw_map (μ : ℕ → Measure E) [∀ n, IsProbabilityMeasure (μ n)]
    (γ : ℕ → Measure (E × E)) [∀ n, IsFiniteMeasure (γ n)]
    (hγ : ∀ n, IsCoupling (μ n) (μ (n + 1)) (γ n)) (n : ℕ) :
    (chainLaw (μ 0) γ).map (fun x => x n) = μ n
      ∧ (chainLaw (μ 0) γ).map (fun x => (x n, x (n + 1))) = γ n := by
  have pair : ∀ n, (chainLaw (μ 0) γ).map (fun x => x n) = μ n →
      (chainLaw (μ 0) γ).map (fun x => (x n, x (n + 1))) = γ n := by
    intro n hn
    have hg : Measurable fun y : Π _ : Iic n, E => y ⟨n, mem_Iic.2 le_rfl⟩ :=
      measurable_pi_apply _
    have key := congrArg (fun ρ => ρ.map (Prod.map (fun y : Π _ : Iic n, E =>
      y ⟨n, mem_Iic.2 le_rfl⟩) id))
      (Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure (X := fun _ => E)
        (κ := chainKernel γ) (μ₀ := μ 0) (a := n))
    rw [chainKernel, map_prodMap_compProd_comap _ _ hg,
      Measure.map_map hg (Preorder.measurable_frestrictLe n),
      Measure.map_map (hg.prodMap measurable_id) (by fun_prop)] at key
    have e1 : (fun y : Π _ : Iic n, E => y ⟨n, mem_Iic.2 le_rfl⟩) ∘ Preorder.frestrictLe n
        = fun x : ℕ → E => x n := rfl
    have e2 : (Prod.map (fun y : Π _ : Iic n, E => y ⟨n, mem_Iic.2 le_rfl⟩) id ∘
        fun x : ℕ → E => (Preorder.frestrictLe n x, x (n + 1))) = fun x => (x n, x (n + 1)) :=
      rfl
    rw [e1, e2] at key
    change (chainLaw (μ 0) γ).map (fun x => x n) ⊗ₘ (γ n).condKernel
      = (chainLaw (μ 0) γ).map (fun x => (x n, x (n + 1))) at key
    rw [← key, hn, ← (hγ n).1, Measure.disintegrate]
  induction n with
  | zero => exact ⟨chainLaw_map_zero (μ 0) γ, pair 0 (chainLaw_map_zero (μ 0) γ)⟩
  | succ n ih =>
    have hs : (chainLaw (μ 0) γ).map (fun x => x (n + 1)) = μ (n + 1) := by
      rw [← (hγ n).2, ← ih.2, Measure.snd, Measure.map_map measurable_snd (by fun_prop)]
      rfl
    exact ⟨hs, pair (n + 1) hs⟩

end Chain

/-! ### Completeness -/

section Complete

/-- The square of the `L²` seminorm is the lower integral of the squared norm. -/
theorem eLpNorm_two_sq_eq_lintegral {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F]
    (μ : Measure α) (f : α → F) : eLpNorm f 2 μ ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := μ) (p := 2) two_ne_zero
  simpa only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_two] using h

/-- An extended real whose square is below `a²` has real part at most `a`. -/
theorem toReal_le_of_sq_lt_ofReal_sq {e : ℝ≥0∞} {a : ℝ} (ha : 0 ≤ a)
    (h : e ^ 2 < ENNReal.ofReal (a ^ 2)) : e.toReal ≤ a := by
  refine ENNReal.toReal_le_of_le_ofReal ha (le_of_lt ?_)
  by_contra hc
  rw [not_lt] at hc
  have h2 : ENNReal.ofReal a ^ 2 ≤ e ^ 2 := pow_le_pow_left₀ bot_le hc 2
  rw [← ENNReal.ofReal_pow ha] at h2
  exact absurd h (not_lt.mpr h2)

variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

omit [CompleteSpace E] in
/-- A random element whose law is a law of finite second moment is square integrable. -/
theorem memLp_two_of_map_eq {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} {ξ : Ω → E}
    (hξ : Measurable ξ) (μ : P2 E) (h : Q.map ξ = μ.law) : MemLp ξ 2 Q := by
  have hid : MemLp (id : E → E) 2 μ.law := by
    refine (memLp_two_iff_integrable_sq_norm aestronglyMeasurable_id).mpr
      ⟨by fun_prop, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => by positivity)]
    exact lt_of_le_of_ne le_top μ.secondMoment_ne_top
  rw [← h] at hid
  exact (memLp_map_measure_iff aestronglyMeasurable_id hξ.aemeasurable).mp hid

/-- **The 2-Wasserstein space of a separable Banach space is complete.** -/
instance P2W.instCompleteSpace : CompleteSpace (P2W E) := by
  refine Metric.complete_of_convergent_controlled_sequences (fun n => (1 / 2 : ℝ) ^ n)
    (fun n => by positivity) fun u hu => ?_
  set μ : ℕ → Measure E := fun n => (u n).toP2.law with hμ
  have hcons : ∀ n, w2sq (μ n) (μ (n + 1)) < ENNReal.ofReal (((1 / 2 : ℝ) ^ n) ^ 2) := by
    intro n
    have hd : w2P (u n).toP2 (u (n + 1)).toP2 < (1 / 2 : ℝ) ^ n :=
      hu n n (n + 1) le_rfl (Nat.le_succ n)
    have hfin := w2sq_ne_top (u n).toP2 (u (n + 1)).toP2
    rw [w2P, w2] at hd
    rw [← ENNReal.ofReal_toReal hfin]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr ((Real.sqrt_lt' (by positivity)).mp hd)
  choose γ hγc hγcost using fun n => exists_isCoupling_transportCostSq_lt (hcons n)
  haveI : ∀ n, IsProbabilityMeasure (μ n) := fun n => (u n).toP2.isProbabilityMeasure
  haveI : ∀ n, IsProbabilityMeasure (γ n) := fun n => isProbabilityMeasure_of_isCoupling (hγc n)
  set Q := chainLaw (μ 0) γ with hQ
  have hmarg := chainLaw_map μ γ hγc
  have hmem : ∀ n, MemLp (fun x : ℕ → E => x n) 2 Q := fun n =>
    memLp_two_of_map_eq (measurable_pi_apply n) (u n).toP2 (hmarg n).1
  set F : ℕ → Lp E 2 Q := fun n => (hmem n).toLp _ with hF
  have hdist : ∀ n, dist (F n) (F (n + 1)) ≤ 2 / 2 / 2 ^ n := by
    intro n
    have hcost : eLpNorm ((fun x : ℕ → E => x n) - fun x => x (n + 1)) 2 Q ^ 2
        = transportCostSq (γ n) := by
      rw [eLpNorm_two_sq_eq_lintegral, ← (hmarg n).2,
        transportCostSq_map Q (measurable_pi_apply n) (measurable_pi_apply (n + 1))]
      refine lintegral_congr fun x => ?_
      rw [Pi.sub_apply, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    have hlt : eLpNorm ((fun x : ℕ → E => x n) - fun x => x (n + 1)) 2 Q ^ 2
        < ENNReal.ofReal (((1 / 2 : ℝ) ^ n) ^ 2) := by
      rw [hcost]
      exact hγcost n
    rw [dist_eq_norm, hF, ← MemLp.toLp_sub, Lp.norm_toLp]
    refine (toReal_le_of_sq_lt_ofReal_sq (by positivity) hlt).trans_eq ?_
    rw [div_self two_ne_zero, one_div_pow]
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric_two hdist)
  refine ⟨(lawP2 Q (L : (ℕ → E) → E)).toP2W, ?_⟩
  have hle : ∀ n, dist (u n) (lawP2 Q (L : (ℕ → E) → E)).toP2W ≤ dist (F n) L := by
    intro n
    have hlaw : (u n).toP2 = lawP2 Q (F n : (ℕ → E) → E) := by
      rw [lawP2_congr (hmem n).coeFn_toLp]
      exact P2.ext_law (by rw [lawP2_law (hmem n), (hmarg n).1])
    have hw := ofReal_w2P_lawP2_sq_le (Lp.memLp (F n)) (Lp.memLp L)
    have hnorm : ∫⁻ x, ENNReal.ofReal (‖(F n : (ℕ → E) → E) x - (L : (ℕ → E) → E) x‖ ^ 2) ∂Q
        = ENNReal.ofReal (dist (F n) L ^ 2) := by
      rw [dist_eq_norm, Lp.norm_def, ENNReal.ofReal_pow ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal (by finiteness), eLpNorm_two_sq_eq_lintegral]
      refine lintegral_congr_ae ?_
      filter_upwards [Lp.coeFn_sub (F n) L] with x hx
      rw [hx, Pi.sub_apply, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    rw [hnorm, ENNReal.ofReal_le_ofReal_iff (by positivity)] at hw
    change w2P (u n).toP2 (lawP2 Q (L : (ℕ → E) → E)) ≤ dist (F n) L
    rw [hlaw]
    exact (pow_le_pow_iff_left₀ (w2P_nonneg _ _) dist_nonneg two_ne_zero).mp hw
  rw [tendsto_iff_dist_tendsto_zero]
  exact squeeze_zero (fun n => dist_nonneg) hle (tendsto_iff_dist_tendsto_zero.mp hL)

end Complete

end Dissertation.Law
