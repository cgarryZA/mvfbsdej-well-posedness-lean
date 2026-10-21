/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.BrownianPoisson.Decomposition
import Dissertation.WellPosedness.System.Solves

/-!
# The equations of a solution on one set of full measure

The solution predicate `SolvesForced` of the `λ`-forced system (4.1) asks each of its linear
forward and backward equations to hold almost surely at each time of `[0, T]`, the exceptional
set depending on the time. The well-posedness paper takes one exceptional set for all times,
since both sides of each identity are càdlàg in `t`. This file gives that form of the two linear
equations, and with it the left limits of a solution on `(0, T]`.

The three terms of the right-hand sides behave as follows.

* The drift integral `t ↦ ∫_{[0, t]} b_s ds` is continuous along every path on which the drift is
  integrable over `[0, T]`, hence along almost every path (`LevyStochCalc.BSDEJ.Solves.driftLeg`).
* The compensated Poisson integral is a càdlàg modification, so its paths are càdlàg almost
  surely.
* The multidimensional Brownian integral is defined separately at each time, as a representative
  of an `L²` limit, and has no path regularity of its own. The identities hold with any version
  `M` of it whose paths are right-continuous almost surely, and such a version with càdlàg paths
  almost surely exists: the sum of càdlàg adapted modifications of the coordinate integrals.

Two processes with almost surely right-continuous paths that agree almost surely at each time of
`[0, T]` agree at all those times on one set of full measure: they agree on the countably many
clamped rationals, which approach every time of `[0, T)` from the right.

Left limits are obtained on `(0, T]` only. Off `[0, T]` the equations say nothing, and a solution
there is any adapted process with right-continuous paths, which need not have left limits.

## Main statements

* `ae_forall_Icc_eq_of_ae_rightContinuous` — processes with almost surely right-continuous paths
  agreeing almost surely at each time of `[0, T]` agree at all those times on one set of full
  measure.
* `exists_ae_cadlag_brownianIntegral` — the multidimensional Brownian integral has an adapted
  version with almost surely càdlàg paths.
* `LinearFSDEJ.ae_forall_eq`, `LinearBSDEJ.ae_forall_eq` — the forward and backward identities
  at all times of `[0, T]` on one set of full measure.
* `LinearFSDEJ.ae_leftLim`, `LinearBSDEJ.ae_leftLim` — a solution has left limits at every time
  of `(0, T]`, almost surely.
* `SolvesForced.ae_leftLim` — every coordinate of `X` and `Y` of a solution of (4.1) has left
  limits at every time of `(0, T]`, almost surely.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace Dissertation.WellPosedness.System

open Dissertation.WellPosedness.BrownianPoisson Dissertation.WellPosedness.Stability
  LevyStochCalc.BSDEJ.Solves LevyStochCalc

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]

/-! ### Indistinguishability from agreement at each time -/

/-- **Right-continuous processes agreeing at each time are indistinguishable on `[0, T]`**: two
processes whose paths are almost surely right-continuous and which agree almost surely at each
time of `[0, T]` agree at every time of `[0, T]` on a single set of full measure. -/
theorem ae_forall_Icc_eq_of_ae_rightContinuous {P : Measure Ω} {T : ℝ} {A B : ℝ → Ω → ℝ}
    (hT : 0 ≤ T) (h : ∀ t ∈ Set.Icc (0 : ℝ) T, A t =ᵐ[P] B t)
    (hA : ∀ᵐ ω ∂P, ∀ t : ℝ, Tendsto (fun s => A s ω) (𝓝[>] t) (𝓝 (A t ω)))
    (hB : ∀ᵐ ω ∂P, ∀ t : ℝ, Tendsto (fun s => B s ω) (𝓝[>] t) (𝓝 (B t ω))) :
    ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, A t ω = B t ω := by
  set G : Set Ω := {ω | (∀ t : ℝ, Tendsto (fun s => A s ω) (𝓝[>] t) (𝓝 (A t ω)))
    ∧ ∀ t : ℝ, Tendsto (fun s => B s ω) (𝓝[>] t) (𝓝 (B t ω))} with hG
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := hA.and hB
  have hrc : ∀ C : ℝ → Ω → ℝ,
      (∀ ω ∈ G, ∀ t : ℝ, Tendsto (fun s => C s ω) (𝓝[>] t) (𝓝 (C t ω))) →
      ∀ (ω : Ω) (t : ℝ),
        Tendsto (fun s => G.indicator (C s) ω) (𝓝[>] t) (𝓝 (G.indicator (C t) ω)) := by
    intro C hC ω t
    by_cases hω : ω ∈ G
    · simp only [Set.indicator_of_mem hω]
      exact hC ω hω t
    · simp only [Set.indicator_of_notMem hω]
      exact tendsto_const_nhds
  have hkey := ae_forall_Icc_eq_of_rightContinuous (P := P)
    (Y := fun t => G.indicator (A t)) (R := fun t => G.indicator (B t)) hT
    (fun t ht => by
      filter_upwards [h t ht, hGae] with ω hω hωG
      simp only [Set.indicator_of_mem hωG, hω])
    (hrc A fun _ hω => hω.1) (hrc B fun _ hω => hω.2)
  filter_upwards [hkey, hGae] with ω hω hωG t ht
  simpa only [Set.indicator_of_mem hωG] using hω t ht

/-! ### A càdlàg version of the Brownian integral -/

variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

/-- **The multidimensional Brownian integral has a càdlàg version**: `∫_0^t Z_s · dW_s` has a
version adapted to the right-continuous filtration whose paths are almost surely right-continuous
with left limits. -/
theorem exists_ae_cadlag_brownianIntegral (W : Brownian.Multidim.MultidimBrownianMotion P d)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, Brownian.IsBrownianFiltration (W.W j) ℱ) (Z : ℝ → Ω → (Fin d → ℝ))
    (hm : ∀ j : Fin d, Measurable (Function.uncurry fun ω s => Z s ω j))
    (hp : ∀ j : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s => Z s ω j)
    (hq : ∀ (j : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∃ M : ℝ → Ω → ℝ, Adapted ℱ.rightCont M ∧
      (∀ t : ℝ, M t =ᵐ[P]
        Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W ℱ hℱW Z hm hp hq t) ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ, Tendsto (fun s => M s ω) (𝓝[>] t) (𝓝 (M t ω)) ∧
        ∃ L : ℝ, Tendsto (fun s => M s ω) (𝓝[<] t) (𝓝 L) := by
  choose Y hYadapt hYae hYcad using fun j : Fin d =>
    Ito.Picard.exists_cadlag_modification_itoIntegral (W.W j) ℱ (hℱW j)
      (fun ω s => Z s ω j) (hm j) (hp j) (hq j)
  refine ⟨fun t ω => ∑ j : Fin d, Y j t ω, fun t => ?_, fun t => ?_, ?_⟩
  · exact Finset.measurable_sum _ fun j _ => hYadapt j t
  · filter_upwards [ae_all_iff.mpr fun j : Fin d => hYae j t] with ω hω
    exact Finset.sum_congr rfl fun j _ => hω j
  · filter_upwards [ae_all_iff.mpr hYcad] with ω hω t
    refine ⟨tendsto_finsetSum _ fun j _ => (hω j t).1, ?_⟩
    choose L hL using fun j : Fin d => (hω j t).2
    exact ⟨∑ j : Fin d, L j, tendsto_finsetSum _ fun j _ => hL j⟩

/-! ### The linear equations on one set of full measure -/

variable {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {T : ℝ}

omit [MeasurableSpace Ω] in
/-- The integral of an integrable drift path over `[t, T]` is the difference of its primitives
at `T` and at `t`. -/
theorem setIntegral_Icc_eq_driftLeg_sub {b : Ω → ℝ → ℝ} {ω : Ω}
    (hω : ω ∈ integrablePaths b T) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∫ s in Set.Icc t T, b ω s = driftLeg b T T ω - driftLeg b T t ω := by
  have hI : IntegrableOn (b ω) (Set.Icc (0 : ℝ) T) volume := hω
  have h1 : IntegrableOn (b ω) (Set.Icc (0 : ℝ) t) volume :=
    hI.mono_set (Set.Icc_subset_Icc le_rfl ht.2)
  have h2 : IntegrableOn (b ω) (Set.Ioc t T) volume :=
    hI.mono_set fun s hs => ⟨ht.1.trans hs.1.le, hs.2⟩
  have hdisj : Disjoint (Set.Icc (0 : ℝ) t) (Set.Ioc t T) :=
    (Set.Iic_disjoint_Ioi le_rfl).mono Set.Icc_subset_Iic_self Set.Ioc_subset_Ioi_self
  rw [driftLeg_of_mem hω T, driftLeg_of_mem hω t, integral_Icc_eq_integral_Ioc,
    ← Set.Icc_union_Ioc_eq_Icc ht.1 ht.2, setIntegral_union hdisj measurableSet_Ioc h1 h2]
  ring

section Forward

variable {ξ₀ : Ω → ℝ} {b : Ω → ℝ → ℝ} {X : ℝ → Ω → ℝ} {σ : ℝ → Ω → (Fin d → ℝ)}
  {γ : ℝ → Ω → E → ℝ}

/-- **The forward identity on one set of full measure.** For a solution of the linear forward
equation and a version `M` of its Brownian integral with almost surely right-continuous paths,
on a single set of full measure

`X_t = ξ₀ + ∫_{[0, t]} b_s ds + M_t + ∫_0^t ∫_E γ_s(e) Ñ(ds, de)`

at every `t ∈ [0, T]`. -/
theorem _root_.Dissertation.WellPosedness.Stability.LinearFSDEJ.ae_forall_eq
    (h : LinearFSDEJ D ℱ hℱW hℱN T ξ₀ b X σ γ) (hT : 0 ≤ T) {M : ℝ → Ω → ℝ}
    (hMae : ∀ t ∈ Set.Icc (0 : ℝ) T, M t =ᵐ[P]
      Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hℱW σ h.σ_meas h.σ_prog
        (sq_int_global_of_vanishing h.σ_vanish h.σ_sq) t)
    (hMrc : ∀ᵐ ω ∂P, ∀ t : ℝ, Tendsto (fun s => M s ω) (𝓝[>] t) (𝓝 (M t ω))) :
    ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T,
      X t ω = ξ₀ ω + (∫ s in Set.Icc (0 : ℝ) t, b ω s) + M t ω
        + Poisson.Compensated.stochasticIntegral D.N ℱ hℱN (fun ω' s e => γ s ω' e) h.γ_meas
          h.γ_prog (marked_sq_int_global_of_vanishing h.γ_vanish h.γ_sq) t ω := by
  set N := Poisson.Compensated.stochasticIntegral D.N ℱ hℱN (fun ω' s e => γ s ω' e) h.γ_meas
    h.γ_prog (marked_sq_int_global_of_vanishing h.γ_vanish h.γ_sq) with hN
  have hBrc : ∀ᵐ ω ∂P, ∀ t : ℝ,
      Tendsto (fun s => ξ₀ ω + driftLeg b T s ω + M s ω + N s ω) (𝓝[>] t)
        (𝓝 (ξ₀ ω + driftLeg b T t ω + M t ω + N t ω)) := by
    filter_upwards [hMrc, Poisson.Compensated.stochasticIntegral_cadlag D.N ℱ hℱN _ h.γ_meas
      h.γ_prog (marked_sq_int_global_of_vanishing h.γ_vanish h.γ_sq)] with ω hM hNc t
    exact ((tendsto_const_nhds.add (((continuous_driftLeg h.b_vanish ω).tendsto t).mono_left
      nhdsWithin_le_nhds)).add (hM t)).add (hNc t).1
  have hkey := ae_forall_Icc_eq_of_ae_rightContinuous (A := X)
    (B := fun t ω => ξ₀ ω + driftLeg b T t ω + M t ω + N t ω) hT
    (fun t ht => by
      filter_upwards [h.eqn t ht, driftLeg_ae_eq h.b_meas h.b_sq t, hMae t ht] with ω h1 h2 h3
      rw [h1, h2, h3])
    (ae_of_all _ h.X_rightCont) hBrc
  filter_upwards [hkey, ae_mem_integrablePaths h.b_meas h.b_sq] with ω hω hωb t ht
  rw [hω t ht, driftLeg_of_mem hωb t]

/-- **A solution of the linear forward equation has left limits on `(0, T]`**, almost surely:
along almost every path, `s ↦ X_s` has a left limit at every `t ∈ (0, T]`. -/
theorem _root_.Dissertation.WellPosedness.Stability.LinearFSDEJ.ae_leftLim
    (h : LinearFSDEJ D ℱ hℱW hℱN T ξ₀ b X σ γ) (hT : 0 ≤ T) :
    ∀ᵐ ω ∂P, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ L : ℝ, Tendsto (fun s => X s ω) (𝓝[<] t) (𝓝 L) := by
  obtain ⟨M, -, hMae, hMcad⟩ := exists_ae_cadlag_brownianIntegral D.W ℱ hℱW σ h.σ_meas h.σ_prog
    (sq_int_global_of_vanishing h.σ_vanish h.σ_sq)
  have hid := h.ae_forall_eq hT (fun t _ => hMae t) (hMcad.mono fun _ hω t => (hω t).1)
  filter_upwards [hid, hMcad, Poisson.Compensated.stochasticIntegral_cadlag D.N ℱ hℱN _ h.γ_meas
    h.γ_prog (marked_sq_int_global_of_vanishing h.γ_vanish h.γ_sq),
    ae_mem_integrablePaths h.b_meas h.b_sq] with ω hω hM hNc hωb t ht
  obtain ⟨LM, hLM⟩ := (hM t).2
  obtain ⟨LN, hLN⟩ := (hNc t).2
  refine ⟨ξ₀ ω + driftLeg b T t ω + LM + LN, ?_⟩
  refine (((tendsto_const_nhds.add (((continuous_driftLeg h.b_vanish ω).tendsto t).mono_left
    nhdsWithin_le_nhds)).add hLM).add hLN).congr' ?_
  filter_upwards [Ioo_mem_nhdsLT ht.1] with s hs
  rw [hω s ⟨hs.1.le, hs.2.le.trans ht.2⟩, driftLeg_of_mem hωb s]

end Forward

section Backward

variable {ξ : Ω → ℝ} {φ : Ω → ℝ → ℝ} {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)}
  {U : ℝ → Ω → E → ℝ}

/-- **The backward identity on one set of full measure.** For a solution of the linear backward
equation and a version `M` of its Brownian integral with almost surely right-continuous paths,
on a single set of full measure

`Y_t = ξ + ∫_{[t, T]} φ_s ds − (M_T − M_t) − ∫_t^T ∫_E U_s(e) Ñ(ds, de)`

at every `t ∈ [0, T]`. -/
theorem _root_.Dissertation.WellPosedness.BrownianPoisson.LinearBSDEJ.ae_forall_eq
    (h : LinearBSDEJ D ℱ hℱW hℱN T ξ φ Y Z U) (hT : 0 ≤ T) {M : ℝ → Ω → ℝ}
    (hMae : ∀ t ∈ Set.Icc (0 : ℝ) T, M t =ᵐ[P]
      Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hℱW Z h.Z_meas h.Z_prog
        (sq_int_global_of_vanishing h.Z_vanish h.Z_sq) t)
    (hMrc : ∀ᵐ ω ∂P, ∀ t : ℝ, Tendsto (fun s => M s ω) (𝓝[>] t) (𝓝 (M t ω))) :
    ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Y t ω = ξ ω + (∫ s in Set.Icc t T, φ ω s) - (M T ω - M t ω)
        - (Poisson.Compensated.stochasticIntegral D.N ℱ hℱN (fun ω' s e => U s ω' e) h.U_meas
            h.U_prog (marked_sq_int_global_of_vanishing h.U_vanish h.U_sq) T ω
          - Poisson.Compensated.stochasticIntegral D.N ℱ hℱN (fun ω' s e => U s ω' e) h.U_meas
            h.U_prog (marked_sq_int_global_of_vanishing h.U_vanish h.U_sq) t ω) := by
  set N := Poisson.Compensated.stochasticIntegral D.N ℱ hℱN (fun ω' s e => U s ω' e) h.U_meas
    h.U_prog (marked_sq_int_global_of_vanishing h.U_vanish h.U_sq) with hN
  have hBrc : ∀ᵐ ω ∂P, ∀ t : ℝ,
      Tendsto (fun s => ξ ω + (driftLeg φ T T ω - driftLeg φ T s ω) - (M T ω - M s ω)
          - (N T ω - N s ω)) (𝓝[>] t)
        (𝓝 (ξ ω + (driftLeg φ T T ω - driftLeg φ T t ω) - (M T ω - M t ω)
          - (N T ω - N t ω))) := by
    filter_upwards [hMrc, Poisson.Compensated.stochasticIntegral_cadlag D.N ℱ hℱN _ h.U_meas
      h.U_prog (marked_sq_int_global_of_vanishing h.U_vanish h.U_sq)] with ω hM hNc t
    exact ((tendsto_const_nhds.add (tendsto_const_nhds.sub
      (((continuous_driftLeg h.φ_vanish ω).tendsto t).mono_left nhdsWithin_le_nhds))).sub
      (tendsto_const_nhds.sub (hM t))).sub (tendsto_const_nhds.sub (hNc t).1)
  have hkey := ae_forall_Icc_eq_of_ae_rightContinuous (A := Y)
    (B := fun t ω => ξ ω + (driftLeg φ T T ω - driftLeg φ T t ω) - (M T ω - M t ω)
      - (N T ω - N t ω)) hT
    (fun t ht => by
      filter_upwards [h.eqn t ht, hMae t ht, hMae T ⟨hT, le_rfl⟩,
        ae_mem_integrablePaths h.φ_meas h.φ_sq] with ω h1 h2 h3 h4
      rw [h1, h2, h3, setIntegral_Icc_eq_driftLeg_sub h4 ht])
    (ae_of_all _ h.Y_rightCont) hBrc
  filter_upwards [hkey, ae_mem_integrablePaths h.φ_meas h.φ_sq] with ω hω hωφ t ht
  rw [hω t ht, setIntegral_Icc_eq_driftLeg_sub hωφ ht]

/-- **A solution of the linear backward equation has left limits on `(0, T]`**, almost surely:
along almost every path, `s ↦ Y_s` has a left limit at every `t ∈ (0, T]`. -/
theorem _root_.Dissertation.WellPosedness.BrownianPoisson.LinearBSDEJ.ae_leftLim
    (h : LinearBSDEJ D ℱ hℱW hℱN T ξ φ Y Z U) (hT : 0 ≤ T) :
    ∀ᵐ ω ∂P, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ L : ℝ, Tendsto (fun s => Y s ω) (𝓝[<] t) (𝓝 L) :=
  (h.linearFSDEJ (EventuallyEq.refl _ _) hT).ae_leftLim hT

end Backward

/-! ### Left limits of a solution -/

variable [MeasurableSpace.CountablyGenerated E] {n m : ℕ} {lam : ℝ} {C : Coeffs ν n m d}
  {ξ₀ : Fin n → Ω → ℝ} {qb : Fin n → Ω → ℝ → ℝ} {qσ : Fin n → ℝ → Ω → Fin d → ℝ}
  {qh : Fin n → ℝ → Ω → E → ℝ} {qf : Fin m → Ω → ℝ → ℝ} {qg : Fin m → Ω → ℝ}
  {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ} {Z : Fin m → ℝ → Ω → Fin d → ℝ}
  {U : Fin m → ℝ → Ω → E → ℝ} {γ : Fin n → ℝ → Ω → E → ℝ}

/-- **A solution has left limits on `(0, T]`**: for a solution of the `λ`-forced system (4.1),
along almost every path every coordinate of `X` and of `Y` has a left limit at every
`t ∈ (0, T]`. -/
theorem SolvesForced.ae_leftLim
    (h : SolvesForced D ℱ hℱW hℱN T lam C ξ₀ qb qσ qh qf qg X Y Z U γ) (hT : 0 ≤ T) :
    ∀ᵐ ω ∂P, ∀ t ∈ Set.Ioc (0 : ℝ) T,
      (∀ i, ∃ L : ℝ, Tendsto (fun s => X i s ω) (𝓝[<] t) (𝓝 L))
        ∧ ∀ k, ∃ L : ℝ, Tendsto (fun s => Y k s ω) (𝓝[<] t) (𝓝 L) := by
  filter_upwards [ae_all_iff.mpr fun i => (h.fwd i).ae_leftLim hT,
    ae_all_iff.mpr fun k => (h.bwd k).ae_leftLim hT] with ω hX hY t ht
  exact ⟨fun i => hX i t ht, fun k => hY k t ht⟩

end Dissertation.WellPosedness.System
