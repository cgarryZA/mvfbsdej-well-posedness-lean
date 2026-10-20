/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.System.PaperWeakSolution
import MVFBSDEJ.WellPosedness.System.SolvesPredictable
import MVFBSDEJ.WellPosedness.System.SolvesS2
import MVFBSDEJ.WellPosedness.System.TupleLeft

/-!
# Solutions in the sense of the paper and the predicate `Solves`

`PaperSolution` states the well-posedness paper's definition of a solution of (1.1), and `Solves`
is the form of (1.1) on which the existence and uniqueness proofs run. The two differ in the
following ways, and this file passes between them.

* `Solves` asks every path of `X` and `Y` to be right-continuous at every time and each process
  to be adapted at every time, while `PaperSolution` asks this on `[0, T]` only. The process
  equal to `0` before `0`, to `X` on `[0, T]` and to `X_T` after `T` is adapted with
  right-continuous paths (`exists_adapted_rightCont_extension`), and the coefficient processes
  along it are those along `X`, since they only see `[0, T]` (`driftProc_eq_of_eqOn` and its
  analogues).
* `Solves` asks the identities almost surely at each time with the canonical Brownian integral,
  `PaperSolution` on one set of full measure with a càdlàg version of it. A version agrees
  almost surely with the canonical integral at each time; conversely, the identities of a
  solution of `Solves` hold on one set of full measure with any version with almost surely
  right-continuous paths (`LinearFSDEJ.ae_forall_eq`, `LinearBSDEJ.ae_forall_eq`), and a càdlàg
  version exists (`exists_ae_cadlag_brownianIntegral`).
* `Solves` evaluates the jump coefficient at `(Θ_s, μ_s)`, `PaperSolution` at `(Θ⁻_s, μ⁻_s)`.
  Almost every path of a solution in either sense has left limits on `(0, T]`, so it meets its
  left limits off a countable set of times, and `Θ⁻_s = Θ_s` almost surely for almost every `s`
  (`PaperSolution.ae_ae_tupleAt_leftLimProc_eq`, `SolvesForced.ae_ae_tupleAt_leftLimProc_eq`):
  a representative of one evaluation represents the other.
* `Solves` takes `Z` and `U` progressively measurable, `PaperSolution` predictable. A predictable
  integrand vanishing off `[0, T]` is progressively measurable
  (`progressivelyMeasurable_of_predictable_of_vanish`); a solution of `Solves` has predictable
  versions of `(Z, U)` with which it is again a solution (`SolvesForced.exists_predictable`),
  under (2.5) along every progressive tuple, `CoeffRegular`.
* `Solves` asks `ξ₀` and `g(X_T, Law X_T)` to be square integrable, `PaperSolution` asks the
  `S²` bounds; each gives the other, the second through Lemma 4.1 over a filtration whose null
  sets lie in its time-`0` field, whose right-continuation is constant before `0` and which
  admits a cross witness (`SolvesForced.lintegral_biSup_X_lt_top`).

The passage to `Solves` uses the `S²` bounds only for the square integrability of `ξ₀` and
`g(X_T, Law X_T)`, so it is stated for solutions in `ℍ²_weak` with these two conditions
(`PaperWeakSolution.exists_solves_of_memLp`), and the path argument for `Θ⁻_s = Θ_s` for tuples
of `ℍ²_weak` (`PaperWeakTuple.ae_ae_tupleAt_leftLimProc_eq`).

## Main statements

* `exists_adapted_rightCont_extension` — an adapted process on `[0, T]` with right-continuous
  paths on `[0, T)` extends to an adapted process with right-continuous paths.
* `energy_eq_of_eqOn`, `tupleAt_eq_of_eqOn`, `driftProc_eq_of_eqOn`, `diffusionProc_eq_of_eqOn`,
  `driverProc_eq_of_eqOn`, `terminalVal_eq_of_eq` — the energy on `[0, T]` and the coefficient
  processes see `X` and `Y` only on `[0, T]`, the terminal value only at `T`.
* `memLp_of_lintegral_biSup_esq_lt_top` — the coordinates of a process with finite `S²`-norm are
  square integrable at every time.
* `PaperWeakTuple.ae_ae_tupleAt_leftLimProc_eq`, `PaperWeakSolution.jump_rep_tupleAt` —
  `Θ⁻_s = Θ_s` almost surely at almost every time, for a tuple of `ℍ²_weak`.
* `PaperWeakSolution.exists_solves_of_memLp` — a solution in `ℍ²_weak` with square-integrable
  `ξ₀` and `g(X_T, Law X_T)`, extended off `[0, T]`, is a solution of `Solves`.
* `PaperSolution.memLp_initial`, `PaperSolution.memLp_terminal` — `ξ₀` and `g(X_T, Law X_T)` are
  square integrable.
* `PaperSolution.ae_ae_tupleAt_leftLimProc_eq`, `PaperSolution.jump_rep_tupleAt` — `Θ⁻_s = Θ_s`
  almost surely at almost every time, so `γ` represents `h(s, Θ_s, ·, μ_s)`.
* `PaperSolution.exists_solves` — a solution in the sense of the paper, extended off `[0, T]`,
  is a solution of `Solves`.
* `Solves.paperSolution` — a solution of `Solves` with predictable integrands is a solution in
  the sense of the paper.
* `Solves.exists_paperSolution` — a solution of `Solves` is one in the sense of the paper after
  passing to predictable versions of `(Z, U)`.
-/

open MeasureTheory Filter Topology MVFBSDEJ.Law
open scoped NNReal ENNReal

namespace MVFBSDEJ.WellPosedness.System

open MVFBSDEJ.WellPosedness.BrownianPoisson MVFBSDEJ.WellPosedness.Stability
  MVFBSDEJ.WellPosedness.Existence LevyStochCalc.BSDEJ.Solves LevyStochCalc

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]

/-! ### Extending a process on the horizon -/

/-- **An adapted process on `[0, T]` with right-continuous paths extends to all times**: if each
coordinate of `x` is adapted at every time of `[0, T]` and every path is right-continuous at
every time of `[0, T)`, there is an adapted process with right-continuous paths equal to `x` on
`[0, T]`: `0` before `0` and `x_T` after `T`. -/
theorem exists_adapted_rightCont_extension {ι : Type*} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {T : ℝ} {x : ι → ℝ → Ω → ℝ} (hT : 0 ≤ T)
    (hadapt : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T, Measurable[ℱ t] (x i t))
    (hrc : ∀ i ω, ∀ t ∈ Set.Ico (0 : ℝ) T,
      Tendsto (fun s => x i s ω) (𝓝[>] t) (𝓝 (x i t ω))) :
    ∃ x' : ι → ℝ → Ω → ℝ, (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T, x' i t = x i t)
      ∧ (∀ i, Adapted ℱ (x' i))
      ∧ ∀ i ω t, Tendsto (fun s => x' i s ω) (𝓝[>] t) (𝓝 (x' i t ω)) := by
  refine ⟨fun i t ω => if 0 ≤ t then x i (min t T) ω else 0, fun i t ht => ?_, fun i t => ?_,
    fun i ω t => ?_⟩
  · funext ω
    simp only [if_pos ht.1, min_eq_left ht.2]
  · by_cases ht : 0 ≤ t
    · simp only [if_pos ht]
      exact (hadapt i _ ⟨le_min ht hT, min_le_right t T⟩).mono (ℱ.mono (min_le_left t T)) le_rfl
    · simp only [if_neg ht]
      exact measurable_const
  · beta_reduce
    rcases lt_or_ge t 0 with ht0 | ht0
    · rw [if_neg (not_le.mpr ht0)]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT ht0] with s hs
      rw [if_neg (not_le.mpr hs.2)]
    rcases lt_or_ge t T with htT | htT
    · rw [if_pos ht0, min_eq_left htT.le]
      refine (hrc i ω t ⟨ht0, htT⟩).congr' ?_
      filter_upwards [Ioo_mem_nhdsGT htT] with s hs
      rw [if_pos (ht0.trans hs.1.le), min_eq_left hs.2.le]
    · rw [if_pos ht0, min_eq_right htT]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with s (hs : t < s)
      rw [if_pos (ht0.trans hs.le), min_eq_right (htT.trans hs.le)]

/-- **The energy on `[0, T]` sees a process only on `[0, T]`**: if `x' = x` at every time of
`[0, T]`, then `𝔼 ∫_0^T |x'_s|² ds = 𝔼 ∫_0^T |x_s|² ds`. -/
theorem energy_eq_of_eqOn {P : Measure Ω} {T : ℝ} {x x' : ℝ → Ω → ℝ}
    (h : ∀ t ∈ Set.Icc (0 : ℝ) T, x' t = x t) :
    Brownian.Ito.energy P T (fun ω s => x' s ω) = Brownian.Ito.energy P T (fun ω s => x s ω) :=
  lintegral_congr fun ω => setLIntegral_congr_fun measurableSet_Icc fun s hs => by
    simp only [h s hs]

/-! ### Square integrability from the `S²` bound -/

/-- **A coordinate of a process with finite `S²`-norm is square integrable** at every time of
`[0, T]` at which it is almost everywhere strongly measurable. -/
theorem memLp_of_lintegral_biSup_esq_lt_top {ι : Type*} [Fintype ι] {P : Measure Ω}
    {x : ι → ℝ → Ω → ℝ} {T : ℝ}
    (hsup : ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => x i t ω)) ∂P < ⊤)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) (i : ι) (hm : AEStronglyMeasurable (x i t) P) :
    MemLp (x i t) 2 P := by
  refine Brownian.Ito.memLp_two_of_lintegral_sq_lt_top hm
    (lt_of_le_of_lt (lintegral_mono fun ω => ?_) hsup)
  exact (Finset.single_le_sum (f := fun i => (‖x i t ω‖₊ : ℝ≥0∞) ^ 2)
    (fun _ _ => zero_le) (Finset.mem_univ i)).trans
    (le_iSup₂ (f := fun t (_ : t ∈ Set.Icc (0 : ℝ) T) => esq fun i => x i t ω) t ht)

variable {ν : Measure E} [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}
  {P : Measure Ω} [IsProbabilityMeasure P] {T : ℝ} {C : Coeffs ν n m d}
  {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ} {Z : Fin m → ℝ → Ω → Fin d → ℝ}
  {U : Fin m → ℝ → Ω → E → ℝ} {γ : Fin n → ℝ → Ω → E → ℝ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {ξ₀ : Fin n → Ω → ℝ}

/-! ### The coefficient processes along a process changed off the horizon -/

section Congr

variable {X' : Fin n → ℝ → Ω → ℝ} {Y' : Fin m → ℝ → Ω → ℝ}

omit [MeasurableSpace Ω] [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
/-- **The tuple at a time of `[0, T]` sees `X` and `Y` only on `[0, T]`**: if `X' = X` and
`Y' = Y` at every time of `[0, T]`, then `Θ'_s = Θ_s` for `s ∈ [0, T]`. -/
theorem tupleAt_eq_of_eqOn (hX : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T, X' i t = X i t)
    (hY : ∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T, Y' k t = Y k t) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) T) :
    tupleAt ν X' Y' Z U s = tupleAt ν X Y Z U s := by
  have hXs : ∀ i, X' i s = X i s := fun i => hX i s hs
  have hYs : ∀ k, Y' k s = Y k s := fun k => hY k s hs
  funext ω
  simp only [tupleAt, hXs, hYs]

/-- **The drift process sees `X` and `Y` only on `[0, T]`**: if `X' = X` and `Y' = Y` at every
time of `[0, T]`, the drift processes along `(X', Y', Z, U)` and `(X, Y, Z, U)` coincide. -/
theorem driftProc_eq_of_eqOn (hX : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T, X' i t = X i t)
    (hY : ∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T, Y' k t = Y k t) :
    driftProc P T C X' Y' Z U = driftProc P T C X Y Z U := by
  funext i ω s
  by_cases hs : s ∈ Set.Icc (0 : ℝ) T
  · simp only [driftProc, Set.indicator_of_mem hs, tupleAt_eq_of_eqOn hX hY hs]
  · rw [driftProc_of_notMem hs, driftProc_of_notMem hs]

/-- **The diffusion process sees `X` and `Y` only on `[0, T]`**: if `X' = X` and `Y' = Y` at every
time of `[0, T]`, the diffusion processes along `(X', Y', Z, U)` and `(X, Y, Z, U)` coincide. -/
theorem diffusionProc_eq_of_eqOn (hX : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T, X' i t = X i t)
    (hY : ∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T, Y' k t = Y k t) :
    diffusionProc P T C X' Y' Z U = diffusionProc P T C X Y Z U := by
  funext i s ω
  by_cases hs : s ∈ Set.Icc (0 : ℝ) T
  · funext j
    simp only [diffusionProc, Set.indicator_of_mem hs, tupleAt_eq_of_eqOn hX hY hs]
  · rw [diffusionProc_of_notMem hs, diffusionProc_of_notMem hs]

/-- **The driver process sees `X` and `Y` only on `[0, T]`**: if `X' = X` and `Y' = Y` at every
time of `[0, T]`, the driver processes along `(X', Y', Z, U)` and `(X, Y, Z, U)` coincide. -/
theorem driverProc_eq_of_eqOn (hX : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T, X' i t = X i t)
    (hY : ∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T, Y' k t = Y k t) :
    driverProc P T C X' Y' Z U = driverProc P T C X Y Z U := by
  funext k ω s
  by_cases hs : s ∈ Set.Icc (0 : ℝ) T
  · simp only [driverProc, Set.indicator_of_mem hs, tupleAt_eq_of_eqOn hX hY hs]
  · rw [driverProc_of_notMem hs, driverProc_of_notMem hs]

/-- **The terminal value sees `X` only at `T`**: if `X'_T = X_T`, then
`g(X'_T, Law X'_T) = g(X_T, Law X_T)`. -/
theorem terminalVal_eq_of_eq (hX : ∀ i, X' i T = X i T) :
    terminalVal P T C X' = terminalVal P T C X := by
  funext k ω
  simp only [terminalVal, hX]

end Congr

/-! ### Tuples and solutions of `ℍ²_weak` as solutions of `Solves` -/

/-- **The predictable tuple of a tuple of `ℍ²_weak` is its tuple at almost every time**: for
almost every `s ∈ [0, T]`, `Θ⁻_s = (X_{s−}, Y_{s−}, Z_s, U_s)` equals `Θ_s` almost surely. -/
theorem PaperWeakTuple.ae_ae_tupleAt_leftLimProc_eq (h : PaperWeakTuple ℱ P ν T X Y Z U)
    (hT : 0 ≤ T) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s =ᵐ[P] tupleAt ν X Y Z U s := by
  obtain ⟨X', hXe, hXa, hXr⟩ := exists_adapted_rightCont_extension hT h.X_adapted h.X_rightCont
  obtain ⟨Y', hYe, hYa, hYr⟩ := exists_adapted_rightCont_extension hT h.Y_adapted h.Y_rightCont
  have hXm : ∀ i, Measurable (Function.uncurry fun ω s => X' i s ω) := fun i =>
    (Probability.measurable_uncurry_of_rightContinuous (hXa i) (hXr i)).comp measurable_swap
  have hYm : ∀ k, Measurable (Function.uncurry fun ω s => Y' k s ω) := fun k =>
    (Probability.measurable_uncurry_of_rightContinuous (hYa k) (hYr k)).comp measurable_swap
  -- left limits of the extensions: those of `X` and `Y` on `(0, T]`
  have hext : ∀ {ι : Type} (x x' : ι → ℝ → Ω → ℝ),
      (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T, x' i t = x i t) → ∀ (i : ι) (ω : Ω) (t : ℝ) (L : ℝ),
      t ∈ Set.Ioc (0 : ℝ) T → Tendsto (fun s => x i s ω) (𝓝[<] t) (𝓝 L) →
      Tendsto (fun s => x' i s ω) (𝓝[<] t) (𝓝 L) := by
    intro ι x x' he i ω t L ht hL
    refine hL.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT ht.1] with s hs
    exact (congrFun (he i s ⟨hs.1.le, hs.2.le.trans ht.2⟩) ω).symm
  have hLX := ae_all_iff.mpr h.X_leftLim
  have hLY := ae_all_iff.mpr h.Y_leftLim
  have h1 := System.ae_leftLimProc_eq (P := P) (T := T) hXm (hLX.mono fun ω hω i =>
    ⟨hXr i ω, fun t ht => (hω i t ht).imp fun L hL => hext X X' hXe i ω t L ht hL⟩)
  have h2 := System.ae_leftLimProc_eq (P := P) (T := T) hYm (hLY.mono fun ω hω k =>
    ⟨hYr k ω, fun t ht => (hω k t ht).imp fun L hL => hext Y Y' hYe k ω t L ht hL⟩)
  have hIoo : ∀ᵐ p ∂(Brownian.Ito.energyMeasure P T), p.2 ∈ Set.Ioo (0 : ℝ) T := by
    rw [Brownian.Ito.energyMeasure]
    refine ae_prod_of_ae_snd ?_
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [(Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := T)).mem_iff]
      with s hs hsI
    exact hs.mpr hsI
  have hfst : ∀ᵐ p ∂(Brownian.Ito.energyMeasure P T),
      (∀ i, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ L : ℝ, Tendsto (fun s => X i s p.1) (𝓝[<] t) (𝓝 L))
        ∧ ∀ k, ∀ t ∈ Set.Ioc (0 : ℝ) T,
          ∃ L : ℝ, Tendsto (fun s => Y k s p.1) (𝓝[<] t) (𝓝 L) := by
    rw [Brownian.Ito.energyMeasure]
    exact Measure.quasiMeasurePreserving_fst.ae (hLX.and hLY)
  have hprod : ∀ᵐ p ∂(Brownian.Ito.energyMeasure P T),
      tupleAt ν (leftLimProc X) (leftLimProc Y) Z U p.2 p.1 = tupleAt ν X Y Z U p.2 p.1 := by
    filter_upwards [h1, h2, hfst, hIoo] with p hp1 hp2 hpl hs
    have hsI : p.2 ∈ Set.Icc (0 : ℝ) T := ⟨hs.1.le, hs.2.le⟩
    have hsI' : p.2 ∈ Set.Ioc (0 : ℝ) T := ⟨hs.1, hs.2.le⟩
    have hx : ∀ i, leftLimProc X i p.2 p.1 = X i p.2 p.1 := fun i => by
      obtain ⟨L, hL⟩ := hpl.1 i p.2 hsI'
      calc leftLimProc X i p.2 p.1 = L := leftLim_eq_of_tendsto hL
        _ = leftLimProc X' i p.2 p.1 :=
          (leftLim_eq_of_tendsto (hext X X' hXe i p.1 p.2 L hsI' hL)).symm
        _ = X' i p.2 p.1 := hp1 i
        _ = X i p.2 p.1 := congrFun (hXe i p.2 hsI) p.1
    have hy : ∀ k, leftLimProc Y k p.2 p.1 = Y k p.2 p.1 := fun k => by
      obtain ⟨L, hL⟩ := hpl.2 k p.2 hsI'
      calc leftLimProc Y k p.2 p.1 = L := leftLim_eq_of_tendsto hL
        _ = leftLimProc Y' k p.2 p.1 :=
          (leftLim_eq_of_tendsto (hext Y Y' hYe k p.1 p.2 L hsI' hL)).symm
        _ = Y' k p.2 p.1 := hp2 k
        _ = Y k p.2 p.1 := congrFun (hYe k p.2 hsI) p.1
    simp only [tupleAt, hx, hy]
  rw [Brownian.Ito.energyMeasure, ← Measure.prod_swap] at hprod
  exact Measure.ae_ae_of_ae_prod
    ((MeasurableEquiv.prodComm (α := ℝ) (β := Ω)).measurableEmbedding.ae_map_iff.mp hprod)

namespace PaperWeakSolution

variable (h : PaperWeakSolution D ℱ hℱW hℱN T C ξ₀ X Y Z U γ) (hT : 0 ≤ T)
include h hT

/-- **The jump coefficient at the tuple**: for a solution in `ℍ²_weak`, `γ` also represents
`e ↦ h(s, Θ_s(ω), e, μ_s)` in `L²(ν)` for almost every `s ∈ [0, T]` and almost every `ω`. -/
theorem jump_rep_tupleAt :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P,
      (fun e => (WithLp.toLp 2 fun i => γ i s ω e : EuclideanSpace ℝ (Fin n)))
        =ᵐ[ν] C.h s (tupleAt ν X Y Z U s ω) (lawP2 P (tupleAt ν X Y Z U s)) := by
  filter_upwards [h.jump_rep, h.toPaperWeakTuple.ae_ae_tupleAt_leftLimProc_eq hT] with s hs heq
  filter_upwards [hs, heq] with ω hω hωeq
  rw [← hωeq, ← lawP2_congr heq]
  exact hω

/-- **A solution in `ℍ²_weak` with square-integrable initial datum and terminal value solves
`Solves`.** For `T ≥ 0`, if `ξ₀` and `g(X_T, Law X_T)` are square integrable, there are `X'`,
`Y'` equal to `X`, `Y` at every time of `[0, T]` — adapted with right-continuous paths, `0` before
`0` and frozen after `T` — such that `(X', Y', Z, U)` solves the system (1.1) in the sense of
`Solves`, with the same `γ`. -/
theorem exists_solves_of_memLp (hξ : ∀ i, MemLp (ξ₀ i) 2 P)
    (hg : ∀ k, MemLp (terminalVal P T C X k) 2 P) :
    ∃ (X' : Fin n → ℝ → Ω → ℝ) (Y' : Fin m → ℝ → Ω → ℝ),
      (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T, X' i t = X i t)
      ∧ (∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T, Y' k t = Y k t)
      ∧ Solves D ℱ hℱW hℱN T C ξ₀ X' Y' Z U γ := by
  obtain ⟨X', hXe, hXa, hXr⟩ := exists_adapted_rightCont_extension hT h.X_adapted h.X_rightCont
  obtain ⟨Y', hYe, hYa, hYr⟩ := exists_adapted_rightCont_extension hT h.Y_adapted h.Y_rightCont
  have hdrift := driftProc_eq_of_eqOn (P := P) (C := C) (Z := Z) (U := U) hXe hYe
  have hdiff := diffusionProc_eq_of_eqOn (P := P) (C := C) (Z := Z) (U := U) hXe hYe
  have hdriver := driverProc_eq_of_eqOn (P := P) (C := C) (Z := Z) (U := U) hXe hYe
  have hterm := terminalVal_eq_of_eq (P := P) (C := C) fun i => hXe i T ⟨hT, le_rfl⟩
  refine ⟨X', Y', hXe, hYe, Solves.of_linear ?_ (fun i => ?_) (fun k => ?_)⟩
  · filter_upwards [h.jump_rep_tupleAt hT, ae_restrict_mem measurableSet_Icc] with s hs hsI
    rw [tupleAt_eq_of_eqOn hXe hYe hsI]
    exact hs
  · rw [hdrift, hdiff]
    obtain ⟨M, hMae, -, hid⟩ := h.fwd i
    exact
      { σ_meas := h.σ_meas i
        σ_prog := h.σ_prog i
        σ_vanish := fun ω s hs => diffusionProc_of_notMem hs i ω
        σ_sq := h.σ_sq i
        γ_meas := h.γ_meas i
        γ_prog := h.γ_prog i
        γ_vanish := fun ω s e hs => jumpProc_of_notMem hs i ω e
        γ_sq := h.γ_sq i
        b_meas := h.b_meas i
        b_prog := h.b_prog i
        b_vanish := fun ω s hs => driftProc_of_notMem hs i ω
        b_sq := h.b_sq i
        ξ₀_sq := hξ i
        X_adapted := hXa i
        X_rightCont := hXr i
        eqn := fun t ht => by
          filter_upwards [hid, hMae t ht] with ω h1 h2
          rw [congrFun (hXe i t ht) ω, h1 t ht, h2] }
  · rw [hterm, hdriver]
    obtain ⟨M, hMae, -, hid⟩ := h.bwd k
    exact
      { Z_meas := fun j => Brownian.Ito.measurable_uncurry_of_predictable (h.Z_pred k j)
        Z_prog := progressivelyMeasurable_of_predictable_of_vanish (h.Z_pred k) (h.Z_vanish k)
        Z_vanish := h.Z_vanish k
        Z_sq := h.Z_sq k
        U_meas := (h.U_pred k).mono (Probability.markedPredictableSigma_le ℱ ν) le_rfl
        U_prog := (h.U_pred k).markedProgressivelyMeasurable
        U_vanish := h.U_vanish k
        U_sq := h.U_sq k
        φ_meas := h.f_meas k
        φ_prog := h.f_prog k
        φ_vanish := fun ω s hs => driverProc_of_notMem hs k ω
        φ_sq := h.f_sq k
        ξ_sq := hg k
        Y_adapted := hYa k
        Y_rightCont := hYr k
        eqn := fun t ht => by
          filter_upwards [hid, hMae t ht, hMae T ⟨hT, le_rfl⟩] with ω h1 h2 h3
          rw [congrFun (hYe k t ht) ω, h1 t ht, h2, h3] }

end PaperWeakSolution

/-! ### Solutions in the sense of the paper as solutions of `Solves` -/

namespace PaperSolution

variable (h : PaperSolution D ℱ hℱW hℱN T C ξ₀ X Y Z U γ) (hT : 0 ≤ T)
include h hT

/-- **The initial datum of a solution is square integrable**: `ξ₀ = X_0` almost surely, and
`X_0` is square integrable by the `S²` bound. -/
theorem memLp_initial (i : Fin n) : MemLp (ξ₀ i) 2 P := by
  obtain ⟨M, hMae, -, hid⟩ := h.fwd i
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
  have hX0 : MemLp (X i 0) 2 P := memLp_of_lintegral_biSup_esq_lt_top h.X_sup h0 i
    ((h.X_adapted i 0 h0).mono (ℱ.le 0) le_rfl).aestronglyMeasurable
  refine hX0.ae_eq ?_
  filter_upwards [hid, hMae 0 h0,
    Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral_ae_zero_of_nonpos D.W ℱ hℱW _
      (h.σ_meas i) (h.σ_prog i)
      (sq_int_global_of_vanishing (fun ω s hs => diffusionProc_of_notMem hs i ω) (h.σ_sq i))
      le_rfl,
    Poisson.Compensated.stochasticIntegral_ae_zero_of_nonpos
      (φ := fun ω s e => jumpProc T γ i s ω e) D.N hℱN (h.γ_meas i) (h.γ_prog i)
      (marked_sq_int_global_of_vanishing (fun ω s e hs => jumpProc_of_notMem hs i ω e)
        (h.γ_sq i)) le_rfl] with ω hω hM hW hN
  simp only [Pi.zero_apply] at hW hN
  rw [hω 0 h0, hM, hW, hN, Set.Icc_self, Measure.restrict_singleton, measure_singleton, zero_smul,
    integral_zero_measure]
  ring

/-- **The terminal value of a solution is square integrable**: `g(X_T, Law X_T) = Y_T` almost
surely, and `Y_T` is square integrable by the `S²` bound. -/
theorem memLp_terminal (k : Fin m) : MemLp (terminalVal P T C X k) 2 P := by
  obtain ⟨M, -, -, hid⟩ := h.bwd k
  have hTm : T ∈ Set.Icc (0 : ℝ) T := ⟨hT, le_rfl⟩
  have hYT : MemLp (Y k T) 2 P := memLp_of_lintegral_biSup_esq_lt_top h.Y_sup hTm k
    ((h.Y_adapted k T hTm).mono (ℱ.le T) le_rfl).aestronglyMeasurable
  refine hYT.ae_eq ?_
  filter_upwards [hid] with ω hω
  rw [hω T hTm, Set.Icc_self, Measure.restrict_singleton, measure_singleton, zero_smul,
    integral_zero_measure]
  ring

/-- **The jump coefficient at the tuple**: for a solution in the sense of the paper, `γ` also
represents `e ↦ h(s, Θ_s(ω), e, μ_s)` in `L²(ν)` for almost every `s ∈ [0, T]` and almost every
`ω`. -/
theorem jump_rep_tupleAt :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P,
      (fun e => (WithLp.toLp 2 fun i => γ i s ω e : EuclideanSpace ℝ (Fin n)))
        =ᵐ[ν] C.h s (tupleAt ν X Y Z U s ω) (lawP2 P (tupleAt ν X Y Z U s)) :=
  h.toWeak.jump_rep_tupleAt hT

/-- **A solution in the sense of the paper solves `Solves`.** For `T ≥ 0`, there are `X'`, `Y'`
equal to `X`, `Y` at every time of `[0, T]` — adapted with right-continuous paths, `0` before
`0` and frozen after `T` — such that `(X', Y', Z, U)` solves the system (1.1) in the sense of
`Solves`, with the same `γ`. -/
theorem exists_solves :
    ∃ (X' : Fin n → ℝ → Ω → ℝ) (Y' : Fin m → ℝ → Ω → ℝ),
      (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T, X' i t = X i t)
      ∧ (∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T, Y' k t = Y k t)
      ∧ Solves D ℱ hℱW hℱN T C ξ₀ X' Y' Z U γ :=
  h.toWeak.exists_solves_of_memLp hT (h.memLp_initial hT) (h.memLp_terminal hT)

end PaperSolution

/-! ### Solutions of `Solves` as solutions in the sense of the paper -/

/-- **A solution with predictable integrands is a solution in the sense of the paper.** Over a
filtration whose null sets lie in its time-`0` field, whose right-continuation is constant before
`0` and which admits a cross witness, for `T > 0`, a solution `(X, Y, Z, U)` of `Solves` with
`Z` predictable and `U` marked predictable, coordinatewise, is a solution of (1.1) in the sense
of the paper, with the same `γ`. -/
theorem Solves.paperSolution (h : Solves D ℱ hℱW hℱN T C ξ₀ X Y Z U γ)
    (hZ : ∀ k j, Probability.Predictable ℱ fun ω s => Z k s ω j)
    (hU : ∀ k, Probability.MarkedPredictable ℱ ν fun ω s e => U k s ω e)
    (𝒲 : D.CrossWitness ℱ) (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T) :
    PaperSolution D ℱ hℱW hℱN T C ξ₀ X Y Z U γ where
  X_adapted i t _ := (h.linearFSDEJ i).X_adapted t
  X_rightCont i ω t _ := (h.linearFSDEJ i).X_rightCont ω t
  X_leftLim i := (h.linearFSDEJ i).ae_leftLim hT.le
  X_sup := SolvesForced.lintegral_biSup_X_lt_top h 𝒲 hℱ0 hnull hT
  Y_adapted k t _ := (h.linearBSDEJ k).Y_adapted t
  Y_rightCont k ω t _ := (h.linearBSDEJ k).Y_rightCont ω t
  Y_leftLim k := (h.linearBSDEJ k).ae_leftLim hT.le
  Y_sup := SolvesForced.lintegral_biSup_Y_lt_top h 𝒲 hℱ0 hnull hT
  Z_pred := hZ
  Z_vanish k := (h.linearBSDEJ k).Z_vanish
  Z_sq k := (h.linearBSDEJ k).Z_sq
  U_pred := hU
  U_vanish k := (h.linearBSDEJ k).U_vanish
  U_sq k := (h.linearBSDEJ k).U_sq
  b_meas i := (h.linearFSDEJ i).b_meas
  b_prog i := (h.linearFSDEJ i).b_prog
  b_sq i := (h.linearFSDEJ i).b_sq
  σ_meas i := (h.linearFSDEJ i).σ_meas
  σ_prog i := (h.linearFSDEJ i).σ_prog
  σ_sq i := (h.linearFSDEJ i).σ_sq
  γ_meas i := (h.linearFSDEJ i).γ_meas
  γ_prog i := (h.linearFSDEJ i).γ_prog
  γ_sq i := (h.linearFSDEJ i).γ_sq
  f_meas k := (h.linearBSDEJ k).φ_meas
  f_prog k := (h.linearBSDEJ k).φ_prog
  f_sq k := (h.linearBSDEJ k).φ_sq
  jump_rep := SolvesForced.jump_rep_left h hT.le
  fwd i := by
    have hi := h.linearFSDEJ i
    obtain ⟨M, -, hMae, hMcad⟩ := exists_ae_cadlag_brownianIntegral D.W ℱ hℱW _ hi.σ_meas
      hi.σ_prog (sq_int_global_of_vanishing hi.σ_vanish hi.σ_sq)
    exact ⟨M, fun t _ => hMae t, hMcad.mono fun _ hω => ⟨fun t _ => (hω t).1, fun t _ => (hω t).2⟩,
      hi.ae_forall_eq hT.le (fun t _ => hMae t) (hMcad.mono fun _ hω t => (hω t).1)⟩
  bwd k := by
    have hk := h.linearBSDEJ k
    obtain ⟨M, -, hMae, hMcad⟩ := exists_ae_cadlag_brownianIntegral D.W ℱ hℱW _ hk.Z_meas
      hk.Z_prog (sq_int_global_of_vanishing hk.Z_vanish hk.Z_sq)
    exact ⟨M, fun t _ => hMae t, hMcad.mono fun _ hω => ⟨fun t _ => (hω t).1, fun t _ => (hω t).2⟩,
      hk.ae_forall_eq hT.le (fun t _ => hMae t) (hMcad.mono fun _ hω t => (hω t).1)⟩

/-- **Every solution of `Solves` is a solution in the sense of the paper, up to versions of
`(Z, U)`.** Over a filtration whose null sets lie in its time-`0` field, whose right-continuation
is constant before `0` and which admits a cross witness, for coefficients with (2.5) along every
progressive tuple and `T > 0`, a solution `(X, Y, Z, U)` of `Solves` has `Z'` and `U'` with
`Z = Z'` `dP ⊗ ds`-almost everywhere on `Ω × [0, T]` and `U = U'` `dP ⊗ ds ⊗ ν`-almost everywhere
on `Ω × [0, T] × E`, coordinatewise, such that `(X, Y, Z', U')` is a solution of (1.1) in the
sense of the paper, with the same `γ`. -/
theorem Solves.exists_paperSolution (h : Solves D ℱ hℱW hℱN T C ξ₀ X Y Z U γ)
    (hC : CoeffRegular ℱ P T C) (𝒲 : D.CrossWitness ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T) :
    ∃ (Z' : Fin m → ℝ → Ω → Fin d → ℝ) (U' : Fin m → ℝ → Ω → E → ℝ),
      (∀ k j, ∀ᵐ p ∂(Brownian.Ito.energyMeasure P T), Z k p.2 p.1 j = Z' k p.2 p.1 j)
      ∧ (∀ k, ∀ᵐ q ∂(Poisson.Compensated.markedEnergyMeasure P ν T),
          U k q.2.1 q.1 q.2.2 = U' k q.2.1 q.1 q.2.2)
      ∧ PaperSolution D ℱ hℱW hℱN T C ξ₀ X Y Z' U' γ := by
  obtain ⟨Z', U', hZpred, hUpred, hZae, hUae, h'⟩ := SolvesForced.exists_predictable h hC hT
  exact ⟨Z', U', hZae, hUae, Solves.paperSolution h' hZpred hUpred 𝒲 hℱ0 hnull hT⟩

end MVFBSDEJ.WellPosedness.System
