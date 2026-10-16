/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.Law.LpRepresentative
import Dissertation.WellPosedness.System.ProgressiveComp
import Dissertation.WellPosedness.Existence.TupleMeasurable

/-!
# Joint measurability of the coefficients

The paper asks the coefficients `b, σ, f` on `[0, T] × H × P₂(H)` to be jointly Borel
measurable, and the jump coefficient `h` to be Borel measurable as a map
`[0, T] × H × P₂(H) → L²(ν; ℝⁿ)`, its (2.3). `CoeffBorel T C` states this for the coefficients
cut off to `[0, T]`, as maps on `ℝ × H × P₂(H)`, with the Borel σ-algebras on `ℝ`, `H` and
`L²(ν; ℝⁿ)` and the evaluation σ-algebra on `P₂(H)` (`Dissertation.Law.P2.instMeasurableSpace`).
The paper reads `P₂(H)` as the metric space `(P₂(H), W₂)` with its Borel σ-algebra, and
`[0, T] × H × P₂(H)` with the Borel σ-algebra of the product topology; since `ℝ` and `H` are
second countable, the latter is the product of the Borel σ-algebras of the factors. Every
`W₂`-Borel set of `P₂(H)` lies in the evaluation σ-algebra
(`Dissertation.WellPosedness.System.measurable_toP2WH`), so `CoeffBorel` follows from the paper's
hypothesis (`CoeffBorelW2.toCoeffBorel`). For the Polish `H` the two σ-algebras on `P₂(H)`
coincide, classically; only the inclusion is used. The terminal function `g` enters only through
the Borel measurability of `x ↦ g(x, ρ)` for each law `ρ`, a hypothesis of its own that the
paper's joint measurability of `g` implies.

Joint measurability gives the paper's (2.5) along every progressive tuple, at every time and for
the exact law `μ_s = Law(Θ_s)`, with no Borel representative of the law flow. The tuple
`Θ_s(ω)` is jointly and progressively measurable and `s ↦ μ_s` is measurable
(`ProgTuple.measurable_tupleAt`, `ProgTuple.progressivelyMeasurable_tupleAt`,
`ProgTuple.measurable_lawP2_tupleAt`), so `(s, θ) ↦ 1_{[0, T]}(s) ψ(s, θ, μ_s)` is jointly
measurable and the coefficient processes `1_{[0, T]}(s) ψ(s, Θ_s(ω), μ_s)` are jointly and
progressively measurable. The jump coefficient is represented through the jointly measurable
representative `Φ = lpRep` of the elements of `L²(ν; ℝⁿ)`: `coeffJump` is
`(i, s, ω, e) ↦ Φ(1_{[0, T]}(s) h(s, Θ_s(ω), μ_s), e)_i`, which represents
`h(s, Θ_s(ω), ·, μ_s)` at every `s ∈ [0, T]` and every `ω`, and vanishes off `[0, T]` since
`Φ(0, ·) = 0`.

## Main definitions

* `CoeffBorel` — the joint measurability (2.3) of the coefficients cut off to `[0, T]`.
* `coeffJump` — the canonical representative of the jump coefficient along a tuple.

## Main statements

* `measurable_cutoff_along` — a cut-off coefficient jointly measurable on `ℝ × H × P₂(H)` is
  jointly measurable along a measurable law flow.
* `coeffJump_ae_eq` — `coeffJump` represents the jump coefficient at every time of `[0, T]`.
* `CoeffBorel.crossEval` — (2.5) along a progressive tuple, with `coeffJump`.
* `CoeffBorel.coeffRegular` — (2.5) along every progressive tuple, for every filtration.
-/

open MeasureTheory Filter Dissertation.Law

namespace Dissertation.WellPosedness.Existence

open Dissertation.WellPosedness.System

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} {n m d : ℕ}

/-- **The joint measurability (2.3) of the coefficients**, cut off to the horizon: each of
`(t, θ, μ) ↦ 1_{[0, T]}(t) ψ(t, θ, μ)`, `ψ ∈ {b, σ, h, f}`, is measurable on `ℝ × H × P₂(H)`, with
the Borel σ-algebras on `ℝ`, `H` and the value space (`L²(ν; ℝⁿ)` for `h`) and the evaluation
σ-algebra on `P₂(H)`. -/
structure CoeffBorel (T : ℝ) (C : Coeffs ν n m d) : Prop where
  /-- The drift is jointly measurable on `[0, T]`. -/
  b_meas : Measurable fun p : ℝ × TupleH ν n m d × P2 (TupleH ν n m d) =>
    (Set.Icc (0 : ℝ) T).indicator (fun t => C.b t p.2.1 p.2.2) p.1
  /-- The diffusion is jointly measurable on `[0, T]`. -/
  σ_meas : Measurable fun p : ℝ × TupleH ν n m d × P2 (TupleH ν n m d) =>
    (Set.Icc (0 : ℝ) T).indicator (fun t => C.σ t p.2.1 p.2.2) p.1
  /-- The jump coefficient is jointly measurable on `[0, T]` into `L²(ν; ℝⁿ)`. -/
  h_meas : Measurable fun p : ℝ × TupleH ν n m d × P2 (TupleH ν n m d) =>
    (Set.Icc (0 : ℝ) T).indicator (fun t => C.h t p.2.1 p.2.2) p.1
  /-- The driver is jointly measurable on `[0, T]`. -/
  f_meas : Measurable fun p : ℝ × TupleH ν n m d × P2 (TupleH ν n m d) =>
    (Set.Icc (0 : ℝ) T).indicator (fun t => C.f t p.2.1 p.2.2) p.1

/-- **A cut-off coefficient along a measurable law flow is jointly measurable**: for a cut-off
`(t, θ, μ) ↦ 1_{[0, T]}(t) ψ(t, θ, μ)` measurable on `ℝ × H × P₂(H)`, a measurable
`s ↦ μ_s` and a measurable `φ` fixing `0`, the map `(s, θ) ↦ 1_{[0, T]}(s) φ(ψ(s, θ, μ_s))` is
measurable. -/
theorem measurable_cutoff_along {T : ℝ} {W : Type*} [MeasurableSpace W] [Zero W]
    {ψ : ℝ → TupleH ν n m d → P2 (TupleH ν n m d) → W}
    (hψ : Measurable fun p : ℝ × TupleH ν n m d × P2 (TupleH ν n m d) =>
      (Set.Icc (0 : ℝ) T).indicator (fun t => ψ t p.2.1 p.2.2) p.1)
    {μ : ℝ → P2 (TupleH ν n m d)} (hμ : Measurable μ) {V : Type*} [MeasurableSpace V] [Zero V]
    {φ : W → V} (hφ : Measurable φ) (hφ0 : φ 0 = 0) :
    Measurable (Function.uncurry fun s θ =>
      (Set.Icc (0 : ℝ) T).indicator (fun t => φ (ψ t θ (μ t))) s) := by
  have h := hφ.comp (hψ.comp (measurable_fst.prodMk (measurable_snd.prodMk
    (hμ.comp measurable_fst))))
  convert h using 1
  funext ⟨s, θ⟩
  by_cases hs : s ∈ Set.Icc (0 : ℝ) T
  · simp only [Function.uncurry_apply_pair, Function.comp_apply, Set.indicator_of_mem hs]
  · simp only [Function.uncurry_apply_pair, Function.comp_apply, Set.indicator_of_notMem hs, hφ0]

variable [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {T : ℝ}
  {C : Coeffs ν n m d} {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ}
  {Z : Fin m → ℝ → Ω → Fin d → ℝ} {U : Fin m → ℝ → Ω → E → ℝ}

variable (P T C X Y Z U) in
/-- **The canonical representative of the jump coefficient along a tuple**:
`γ_{i,s}(ω, e) = Φ(1_{[0, T]}(s) h(s, Θ_s(ω), μ_s), e)_i`, with `Θ_s` the tuple of the
coordinate processes, `μ_s` its law and `Φ = lpRep` the jointly measurable representative of the
elements of `L²(ν; ℝⁿ)`. -/
noncomputable def coeffJump : Fin n → ℝ → Ω → E → ℝ := fun i s ω e =>
  lpRep ν (EuclideanSpace ℝ (Fin n))
    ((Set.Icc (0 : ℝ) T).indicator
      (fun t => C.h t (tupleAt ν X Y Z U s ω) (lawP2 P (tupleAt ν X Y Z U t))) s, e) i

/-- **`coeffJump` represents the jump coefficient** at every time of `[0, T]` and every sample
point: `e ↦ γ_s(ω, e)` is a representative of `h(s, Θ_s(ω), ·, μ_s) ∈ L²(ν; ℝⁿ)`. -/
theorem coeffJump_ae_eq {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) T) (ω : Ω) :
    (fun e => (WithLp.toLp 2 fun i => coeffJump P T C X Y Z U i s ω e :
        EuclideanSpace ℝ (Fin n)))
      =ᵐ[ν] C.h s (tupleAt ν X Y Z U s ω) (lawP2 P (tupleAt ν X Y Z U s)) := by
  have h := lpRep_ae_eq (C.h s (tupleAt ν X Y Z U s ω) (lawP2 P (tupleAt ν X Y Z U s)))
  filter_upwards [h] with e he
  rw [← he]
  simp only [coeffJump, Set.indicator_of_mem hs]

/-- `coeffJump` vanishes off `[0, T]`. -/
theorem coeffJump_of_notMem {s : ℝ} (hs : s ∉ Set.Icc (0 : ℝ) T) (i : Fin n) (ω : Ω) (e : E) :
    coeffJump P T C X Y Z U i s ω e = 0 := by
  simp only [coeffJump, Set.indicator_of_notMem hs, lpRep_zero]
  rfl

/-- The jump process of `coeffJump` is `coeffJump` itself. -/
theorem jumpProc_coeffJump (i : Fin n) (s : ℝ) (ω : Ω) (e : E) :
    jumpProc T (coeffJump P T C X Y Z U) i s ω e = coeffJump P T C X Y Z U i s ω e := by
  by_cases hs : s ∈ Set.Icc (0 : ℝ) T
  · exact Set.indicator_of_mem hs _
  · rw [coeffJump_of_notMem hs]
    exact Set.indicator_of_notMem hs _

/-- **(2.5) along a progressive tuple from the joint measurability of the coefficients.** For
coefficients with (2.3) and a progressive tuple `(X, Y, Z, U)` over any filtration, the drift,
diffusion and driver processes along the tuple are jointly and progressively measurable, and
`coeffJump` is a jointly measurable, marked progressively measurable representative of the jump
coefficient. -/
theorem CoeffBorel.crossEval (hC : CoeffBorel T C) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hΘ : ProgTuple ℱ P ν T X Y Z U) :
    CrossEval ℱ P T C X Y Z U (coeffJump P T C X Y Z U) := by
  have hΘm := hΘ.measurable_tupleAt
  have hΘp := hΘ.progressivelyMeasurable_tupleAt
  have hμ := hΘ.measurable_lawP2_tupleAt
  have hproj : ∀ {ι : Type} [Fintype ι] (i : ι),
      Measurable fun v : EuclideanSpace ℝ ι => v i := fun i =>
    (EuclideanSpace.proj i : EuclideanSpace ℝ _ →L[ℝ] ℝ).continuous.measurable
  have hjm : Measurable fun p : ℝ × TupleH ν n m d =>
      (Set.Icc (0 : ℝ) T).indicator
        (fun t => C.h t p.2 (lawP2 P (tupleAt ν X Y Z U t))) p.1 :=
    measurable_cutoff_along hC.h_meas hμ measurable_id rfl
  have hG : ∀ i, Measurable fun p : ℝ × TupleH ν n m d × E =>
      lpRep ν (EuclideanSpace ℝ (Fin n))
        ((Set.Icc (0 : ℝ) T).indicator
          (fun t => C.h t p.2.1 (lawP2 P (tupleAt ν X Y Z U t))) p.1, p.2.2) i := fun i =>
    (hproj i).comp (stronglyMeasurable_lpRep.measurable.comp
      ((hjm.comp (measurable_fst.prodMk measurable_snd.fst)).prodMk measurable_snd.snd))
  have hjump : ∀ i, (fun ω s e => jumpProc T (coeffJump P T C X Y Z U) i s ω e)
      = fun ω s e => lpRep ν (EuclideanSpace ℝ (Fin n))
        ((Set.Icc (0 : ℝ) T).indicator
          (fun t => C.h t (tupleAt ν X Y Z U s ω) (lawP2 P (tupleAt ν X Y Z U t))) s, e) i :=
    fun i => funext fun ω => funext₂ fun s e => jumpProc_coeffJump i s ω e
  refine
    { jump_rep := (ae_restrict_mem measurableSet_Icc).mono fun s hs =>
        Eventually.of_forall fun ω => coeffJump_ae_eq hs ω
      b_meas := fun i => ?_
      b_prog := fun i => ?_
      σ_meas := fun i j => ?_
      σ_prog := fun i j => ?_
      h_meas := fun i => ?_
      h_prog := fun i => ?_
      f_meas := fun k => ?_
      f_prog := fun k => ?_ }
  · exact (measurable_cutoff_along hC.b_meas hμ (hproj i) rfl).comp
      (measurable_snd.prodMk hΘm)
  · exact progressivelyMeasurable_comp_measurable hΘp
      (measurable_cutoff_along hC.b_meas hμ (hproj i) rfl)
  · exact (measurable_cutoff_along hC.σ_meas hμ (hproj (i, j)) rfl).comp
      (measurable_snd.prodMk hΘm)
  · exact progressivelyMeasurable_comp_measurable hΘp
      (measurable_cutoff_along hC.σ_meas hμ (hproj (i, j)) rfl)
  · have e := congrFun (hjump i)
    simp only [funext_iff] at e
    simp only [e]
    exact (hG i).comp (measurable_snd.fst.prodMk
      ((hΘm.comp (measurable_fst.prodMk measurable_snd.fst)).prodMk measurable_snd.snd))
  · rw [hjump i]
    exact markedProgressivelyMeasurable_comp_measurable (G := fun s θ e =>
      lpRep ν (EuclideanSpace ℝ (Fin n))
        ((Set.Icc (0 : ℝ) T).indicator
          (fun t => C.h t θ (lawP2 P (tupleAt ν X Y Z U t))) s, e) i) hΘp (hG i)
  · exact (measurable_cutoff_along hC.f_meas hμ (hproj k) rfl).comp
      (measurable_snd.prodMk hΘm)
  · exact progressivelyMeasurable_comp_measurable hΘp
      (measurable_cutoff_along hC.f_meas hμ (hproj k) rfl)

/-- **(2.5) along every progressive tuple from the joint measurability of the coefficients**, for
every filtration and probability measure. -/
theorem CoeffBorel.coeffRegular (hC : CoeffBorel T C) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (P : Measure Ω) [IsProbabilityMeasure P] : CoeffRegular ℱ P T C :=
  fun _ _ _ _ hΘ => ⟨_, hC.crossEval hΘ⟩

end Dissertation.WellPosedness.Existence
