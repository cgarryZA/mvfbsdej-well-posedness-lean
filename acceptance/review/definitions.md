# Reviews of the definitions the statements depend on

Every declaration of `MVFBSDEJ` or `LevyStochCalc` in the definition closure of a statement of
`MVFBSDEJ.PaperSpec` is read here against the mathematics it stands for. The marker records
the hash reviewed (type and value, proofs erased); a change reopens the entry. A definition named
by a definition claim of the inventory is read against that claim's passage, and its marker also
records the passage digest as read (`source=<claim>@<digest>`); a change of the passage reopens
it for that claim. Mathlib and the pinned upstream libraries are taken as foundations.

## Laws and the 2-Wasserstein distance (`MVFBSDEJ/Law/`)

* `IsCoupling μ ν γ`: `γ` is a measure on `E × E` with marginals `μ` and `ν` (`γ.fst = μ`,
  `γ.snd = ν`). The definition of a coupling (Villani, *Optimal transport*, Def. 1.1).
  <!-- def-review: MVFBSDEJ.Law.IsCoupling b0bdef6c32a05af44418b437fabafbee by=claude-author -->
  Review by claude-reviewer: faithful (report `reports/Dissertation.Law.IsCoupling--claude-reviewer--2026-10-17T12_04_51Z.md`).
  <!-- def-review: MVFBSDEJ.Law.IsCoupling b0bdef6c32a05af44418b437fabafbee by=claude-reviewer -->
  Review by claude-auditor: faithful (report `reports/Dissertation.Law.IsCoupling--claude-auditor--2026-10-19T03_27_44Z.md`).
  <!-- def-review: MVFBSDEJ.Law.IsCoupling b0bdef6c32a05af44418b437fabafbee by=claude-auditor -->
* `transportCostSq γ = ∫⁻ ‖x − y‖² dγ` in `[0, ∞]`: the quadratic transport cost.
  <!-- def-review: MVFBSDEJ.Law.transportCostSq 26527e1b01e0a835bf6cd2c0e3b72557 by=claude-author -->
  Review by claude-reviewer: faithful (report `reports/Dissertation.Law.transportCostSq--claude-reviewer--2026-10-17T15_50_55Z.md`).
  <!-- def-review: MVFBSDEJ.Law.transportCostSq 26527e1b01e0a835bf6cd2c0e3b72557 by=claude-reviewer -->
  Review by claude-auditor: faithful (report `reports/Dissertation.Law.transportCostSq--claude-auditor--2026-10-19T03_27_45Z.md`).
  <!-- def-review: MVFBSDEJ.Law.transportCostSq 26527e1b01e0a835bf6cd2c0e3b72557 by=claude-auditor -->
* `w2sq μ ν = inf over couplings γ of transportCostSq γ`: the squared 2-Wasserstein distance
  (Villani, Def. 6.1, `p = 2`), in `[0, ∞]`.
  <!-- def-review: MVFBSDEJ.Law.w2sq 6e694fea4529496c5ca60966807eca4e by=claude-author -->
  Review by claude-reviewer: faithful (report `reports/Dissertation.Law.w2sq--claude-reviewer--2026-10-17T15_50_56Z.md`).
  <!-- def-review: MVFBSDEJ.Law.w2sq 6e694fea4529496c5ca60966807eca4e by=claude-reviewer -->
  Review by claude-auditor: faithful (report `reports/Dissertation.Law.w2sq--claude-auditor--2026-10-19T03_27_45Z.md`).
  <!-- def-review: MVFBSDEJ.Law.w2sq 6e694fea4529496c5ca60966807eca4e by=claude-auditor -->
* `w2 μ ν = √(w2sq μ ν).toReal`: the distance as a real number. An infinite squared distance is
  sent to `0`; on laws of finite second moment the squared distance is finite
  (`w2sq_ne_top`), so there `w2` is the 2-Wasserstein distance.
  <!-- def-review: MVFBSDEJ.Law.w2 d92ca7948d3f7f2f2765327d97ac2fa7 by=claude-author -->
  Review by claude-reviewer: faithful (report `reports/Dissertation.Law.w2--claude-reviewer--2026-10-17T15_50_56Z.md`).
  <!-- def-review: MVFBSDEJ.Law.w2 d92ca7948d3f7f2f2765327d97ac2fa7 by=claude-reviewer -->
  Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.Law.w2--claude-auditor--2026-10-19T03_27_45Z.md`).
  <!-- def-review: MVFBSDEJ.Law.w2 d92ca7948d3f7f2f2765327d97ac2fa7 by=claude-auditor -->
* `secondMoment μ = ∫⁻ ‖x‖² dμ`: the second moment about the origin.
  <!-- def-review: MVFBSDEJ.Law.secondMoment f576c608076b2c8115cf34b105438676 by=claude-author -->
  Review by claude-reviewer: faithful (report `reports/Dissertation.Law.secondMoment--claude-reviewer--2026-10-17T15_50_55Z.md`).
  <!-- def-review: MVFBSDEJ.Law.secondMoment f576c608076b2c8115cf34b105438676 by=claude-reviewer -->
  Review by claude-auditor: faithful (report `reports/Dissertation.Law.secondMoment--claude-auditor--2026-10-19T03_27_45Z.md`).
  <!-- def-review: MVFBSDEJ.Law.secondMoment f576c608076b2c8115cf34b105438676 by=claude-auditor -->
* `P2 E`, with constructor `P2.mk` and projection `P2.law`: a probability measure on `E` with
  finite second moment, i.e. an element of `P₂(E)`.
  <!-- def-review: MVFBSDEJ.Law.P2 d98c9fdcb43519180000000000000000 by=claude-author -->
  Review by claude-reviewer: faithful (report `reports/Dissertation.Law.P2--claude-reviewer--2026-10-17T12_05_37Z.md`).
  <!-- def-review: MVFBSDEJ.Law.P2 d98c9fdcb43519180000000000000000 by=claude-reviewer -->
  Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.Law.P2--claude-auditor--2026-10-19T03_27_44Z.md`).
  <!-- def-review: MVFBSDEJ.Law.P2 d98c9fdcb43519180000000000000000 by=claude-auditor -->
  <!-- def-review: MVFBSDEJ.Law.P2.mk 74b6b76ffa4973e10000000000000000 by=claude-author -->
  Review by claude-reviewer: faithful (report `reports/Dissertation.Law.P2.mk--claude-reviewer--2026-10-17T15_50_55Z.md`).
  <!-- def-review: MVFBSDEJ.Law.P2.mk 74b6b76ffa4973e10000000000000000 by=claude-reviewer -->
  Review by claude-auditor: faithful (report `reports/Dissertation.Law.P2.mk--claude-auditor--2026-10-19T03_27_45Z.md`).
  <!-- def-review: MVFBSDEJ.Law.P2.mk 74b6b76ffa4973e10000000000000000 by=claude-auditor -->
  <!-- def-review: MVFBSDEJ.Law.P2.law bb2910c5480414c7e636219b4a85205b by=claude-author -->
  Review by claude-reviewer: faithful (report `reports/Dissertation.Law.P2.law--claude-reviewer--2026-10-17T15_50_56Z.md`).
  <!-- def-review: MVFBSDEJ.Law.P2.law bb2910c5480414c7e636219b4a85205b by=claude-reviewer -->
  Review by claude-auditor: faithful (report `reports/Dissertation.Law.P2.law--claude-auditor--2026-10-19T03_27_45Z.md`).
  <!-- def-review: MVFBSDEJ.Law.P2.law bb2910c5480414c7e636219b4a85205b by=claude-auditor -->
* `P2.dirac a`: the Dirac mass at `a`, an element of `P₂(E)`.
  <!-- def-review: MVFBSDEJ.Law.P2.dirac 55d8a13c1c0971398a19efe41838bdb9 by=claude-author -->
  Review by claude-reviewer: faithful (report `reports/Dissertation.Law.P2.dirac--claude-reviewer--2026-10-17T15_50_55Z.md`).
  <!-- def-review: MVFBSDEJ.Law.P2.dirac 55d8a13c1c0971398a19efe41838bdb9 by=claude-reviewer -->
  Review by claude-auditor: faithful (report `reports/Dissertation.Law.P2.dirac--claude-auditor--2026-10-19T03_27_45Z.md`).
  <!-- def-review: MVFBSDEJ.Law.P2.dirac 55d8a13c1c0971398a19efe41838bdb9 by=claude-auditor -->
* `w2P μ ν = w2 μ.law ν.law`: the 2-Wasserstein distance on `P₂(E)` for the norm of `E`.
  <!-- def-review: MVFBSDEJ.Law.w2P 1bfad47c6a95141e7abc87c84c84d2ff by=claude-author -->
  Review by claude-reviewer: faithful (report `reports/Dissertation.Law.w2P--claude-reviewer--2026-10-17T15_50_56Z.md`).
  <!-- def-review: MVFBSDEJ.Law.w2P 1bfad47c6a95141e7abc87c84c84d2ff by=claude-reviewer -->
  Review by claude-auditor: faithful (report `reports/Dissertation.Law.w2P--claude-auditor--2026-10-19T03_27_45Z.md`).
  <!-- def-review: MVFBSDEJ.Law.w2P 1bfad47c6a95141e7abc87c84c84d2ff by=claude-auditor -->
* `lawP2 P Θ`: the law `P ∘ Θ⁻¹` of `Θ` when `Θ ∈ L²(P)`, and `δ₀` otherwise. The manuscripts
  take laws of square-integrable variables only; the value off `L²` is a convention, and a
  statement quantifying over `L²` variables never reaches it (`REPRESENTATION_CHOICES.md` R9).
  <!-- def-review: MVFBSDEJ.Law.lawP2 ed84cd1114f294f90f45b5f95750d4cf by=claude-author -->
  Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.Law.lawP2--claude-reviewer--2026-10-17T12_12_13Z.md`).
  <!-- def-review: MVFBSDEJ.Law.lawP2 ed84cd1114f294f90f45b5f95750d4cf by=claude-reviewer -->
  Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.Law.lawP2--claude-auditor--2026-10-19T03_27_45Z.md`).
  <!-- def-review: MVFBSDEJ.Law.lawP2 ed84cd1114f294f90f45b5f95750d4cf by=claude-auditor -->

## The tuple space (`MVFBSDEJ/WellPosedness/`)

* `Tuple HX HY HZY HUY = HX × HY × HZY × HUY`, the product of the four channels, with the maximum of
  the channel norms (Mathlib's product norm), not the Hilbert norm
  `(‖x‖² + ‖y‖² + ‖z‖² + ‖u‖²)^{1/2}` of the paper's `H`; the two norms satisfy
  `‖θ‖_max ≤ ‖θ‖_H ≤ 2 ‖θ‖_max`, and the product with the Hilbert norm is `TupleL2` below.
  <!-- def-review: MVFBSDEJ.WellPosedness.Tuple efc2de5eec83280ededc740a2b5da27e by=claude-author -->
  Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.Tuple--claude-reviewer--2026-10-17T15_01_51Z.md`).
  <!-- def-review: MVFBSDEJ.WellPosedness.Tuple efc2de5eec83280ededc740a2b5da27e by=claude-reviewer -->
  Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.Tuple--claude-auditor--2026-10-19T03_27_25Z.md`).
  <!-- def-review: MVFBSDEJ.WellPosedness.Tuple efc2de5eec83280ededc740a2b5da27e by=claude-auditor -->
* `TupleH ν n m d`: the channels `ℝⁿ`, `ℝᵐ`, `ℝ^{m×d}` and `L²(ν; ℝᵐ)`, as
  `EuclideanSpace ℝ (Fin n)`, `EuclideanSpace ℝ (Fin m)`, `EuclideanSpace ℝ (Fin m × Fin d)` (whose
  norm is the Frobenius norm) and `Lp (EuclideanSpace ℝ (Fin m)) 2 ν`: the space `H` of the
  well-posedness paper, §2, as a set and a topological vector space, but with the maximum of the
  channel norms (`Tuple`) rather than the paper's Hilbert norm. The 2-Wasserstein distance of this
  norm, `w2P` on `P2 (TupleH ν n m d)`, lies within a factor `2` of the paper's
  (`w2P ≤ w2H ≤ 2 w2P`), and every statement with an exact `W₂` constant on laws of `H` uses the
  Hilbert-norm `w2H`.
  <!-- def-review: MVFBSDEJ.WellPosedness.System.TupleH fd49e3c7112f415532925681da98a93f by=claude-author -->
  Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.TupleH--claude-reviewer--2026-10-17T15_06_17Z.md`).
  <!-- def-review: MVFBSDEJ.WellPosedness.System.TupleH fd49e3c7112f415532925681da98a93f by=claude-reviewer -->
  Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.TupleH--claude-auditor--2026-10-19T03_27_23Z.md`).
  <!-- def-review: MVFBSDEJ.WellPosedness.System.TupleH fd49e3c7112f415532925681da98a93f by=claude-auditor -->
* `lpMeasurableSpace`: the Borel σ-algebra on `L²(ν; F)`.
  <!-- def-review: MVFBSDEJ.WellPosedness.System.lpMeasurableSpace fee4e2519c9a83360a35b3d1a9e70db3 by=claude-author -->
  Review by claude-reviewer: faithful (report `reports/Dissertation.WellPosedness.System.lpMeasurableSpace--claude-reviewer--2026-10-17T15_06_18Z.md`).
  <!-- def-review: MVFBSDEJ.WellPosedness.System.lpMeasurableSpace fee4e2519c9a83360a35b3d1a9e70db3 by=claude-reviewer -->
  Review by claude-auditor: faithful (report `reports/Dissertation.WellPosedness.System.lpMeasurableSpace--claude-auditor--2026-10-19T03_27_24Z.md`).
  <!-- def-review: MVFBSDEJ.WellPosedness.System.lpMeasurableSpace fee4e2519c9a83360a35b3d1a9e70db3 by=claude-auditor -->
* `TupleL2 HX HY HZY HUY`: the same four channels combined as nested `ℓ²` products
  (`WithLp 2`), so that `‖θ‖² = ‖x‖² + ‖y‖² + ‖z‖² + ‖u‖²`: `H` with its Hilbert norm.
  <!-- def-review: MVFBSDEJ.WellPosedness.System.TupleL2 5c620c846d4820ad66b1a5b8e7220ca2 by=claude-author -->
  Review by claude-reviewer: faithful (report `reports/Dissertation.WellPosedness.System.TupleL2--claude-reviewer--2026-10-17T15_06_17Z.md`).
  <!-- def-review: MVFBSDEJ.WellPosedness.System.TupleL2 5c620c846d4820ad66b1a5b8e7220ca2 by=claude-reviewer -->
  Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.TupleL2--claude-auditor--2026-10-19T03_27_23Z.md`).
  <!-- def-review: MVFBSDEJ.WellPosedness.System.TupleL2 5c620c846d4820ad66b1a5b8e7220ca2 by=claude-auditor -->
* `toL2 θ`: the identity of the underlying set, from the product with the maximum norm to the
  product with the Hilbert norm.
  <!-- def-review: MVFBSDEJ.WellPosedness.System.toL2 2a224662a8cd24601f2ae23bd1407b29 by=claude-author -->
  Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.toL2--claude-reviewer--2026-10-17T15_01_50Z.md`).
  <!-- def-review: MVFBSDEJ.WellPosedness.System.toL2 2a224662a8cd24601f2ae23bd1407b29 by=claude-reviewer -->
  Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.toL2--claude-auditor--2026-10-19T03_27_25Z.md`).
  <!-- def-review: MVFBSDEJ.WellPosedness.System.toL2 2a224662a8cd24601f2ae23bd1407b29 by=claude-auditor -->
* `w2H μ μ' = w2 (μ.law.map toL2) (μ'.law.map toL2)`: the 2-Wasserstein distance on `P₂(H)`
  for the Hilbert norm of `H`, the distance of the manuscript's §2.
  <!-- def-review: MVFBSDEJ.WellPosedness.System.w2H d31384069425cfac28b44407592bfdb6 by=claude-author -->
  Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.w2H--claude-reviewer--2026-10-17T15_01_51Z.md`).
  <!-- def-review: MVFBSDEJ.WellPosedness.System.w2H d31384069425cfac28b44407592bfdb6 by=claude-reviewer -->
  Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.w2H--claude-auditor--2026-10-19T03_27_25Z.md`).
  <!-- def-review: MVFBSDEJ.WellPosedness.System.w2H d31384069425cfac28b44407592bfdb6 by=claude-auditor -->

## Brownian motion and its filtrations (`LevyStochCalc/Brownian/`)

Manuscript (§2): the probability space carries a `d`-dimensional Brownian motion `W` and an
independent Poisson random measure `N`, and the filtration is the usual augmentation of the one
generated by `W`, `N` and an independent `ℱ₀`.

* `Brownian.BrownianMotion P`, with projection `W` and constructor `.mk`: a real process `W_t(ω)`
  indexed by `t ∈ ℝ`, measurable in `ω` for each `t` and jointly measurable in `(t, ω)`, with
  `W_0 = 0` almost surely, `W_t − W_s` of law `𝒩(0, t − s)` for `0 ≤ s < t`, almost surely
  continuous paths, `W_s = 0` almost surely for each `s < 0`, and `σ(W_u : u ≤ s)` independent of
  `W_t − W_s` for `0 ≤ s < t`: a one-dimensional Brownian motion; `W` is the path map. Choices, read
  alike for the structure, its projection and its constructor: the time axis is `ℝ`, with `W` almost
  surely `0` before time `0`, a convention under which the times `u < 0` add to `σ(W_u : u ≤ s)`
  only events of probability `0` or `1`; `W_0 = 0` and the continuity hold almost surely rather than
  for every path; the joint measurability is asked in addition, and a Brownian motion redefined as
  `0` on a measurable null set carrying its discontinuous paths has continuous paths, hence has it.
  Independence of the past from each later increment gives the joint independence of the increments
  by induction.
<!-- def-review: LevyStochCalc.Brownian.BrownianMotion caf7babc7d9b82d50000000000000000 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/LevyStochCalc.Brownian.BrownianMotion--claude-reviewer--2026-10-17T15_02_24Z.md`).
<!-- def-review: LevyStochCalc.Brownian.BrownianMotion caf7babc7d9b82d50000000000000000 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/LevyStochCalc.Brownian.BrownianMotion--claude-auditor--2026-10-19T03_27_25Z.md`).
<!-- def-review: LevyStochCalc.Brownian.BrownianMotion caf7babc7d9b82d50000000000000000 by=claude-auditor -->
<!-- def-review: LevyStochCalc.Brownian.BrownianMotion.W 37fa09fc2e9f5aed48543ee8d8bbca0f by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/LevyStochCalc.Brownian.BrownianMotion.W--claude-reviewer--2026-10-17T15_02_24Z.md`).
<!-- def-review: LevyStochCalc.Brownian.BrownianMotion.W 37fa09fc2e9f5aed48543ee8d8bbca0f by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/LevyStochCalc.Brownian.BrownianMotion.W--claude-auditor--2026-10-19T03_27_25Z.md`).
<!-- def-review: LevyStochCalc.Brownian.BrownianMotion.W 37fa09fc2e9f5aed48543ee8d8bbca0f by=claude-auditor -->
<!-- def-review: LevyStochCalc.Brownian.BrownianMotion.mk a9e961694b283fba0000000000000000 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/LevyStochCalc.Brownian.BrownianMotion.mk--claude-reviewer--2026-10-17T15_02_24Z.md`).
<!-- def-review: LevyStochCalc.Brownian.BrownianMotion.mk a9e961694b283fba0000000000000000 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/LevyStochCalc.Brownian.BrownianMotion.mk--claude-auditor--2026-10-19T03_27_25Z.md`).
<!-- def-review: LevyStochCalc.Brownian.BrownianMotion.mk a9e961694b283fba0000000000000000 by=claude-auditor -->
* `Brownian.IsBrownianFiltration W ℱ`, with constructor `.mk`: `W_t` is `ℱ_t`-measurable for every
  `t`, and for `s ≥ 0` the σ-algebra `ℱ_s` is independent of `σ(W_t − W_s : t > s)`: `W` is an
  `(ℱ_t)`-Brownian motion, in the usual form in which `ℱ_s` is independent of all the later
  increments at once. The filtration is indexed by `ℝ` and nothing is asked of it before time `0`.
<!-- def-review: LevyStochCalc.Brownian.IsBrownianFiltration 6b9d7c4909eee8db0000000000000000 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/LevyStochCalc.Brownian.IsBrownianFiltration--claude-reviewer--2026-10-17T15_02_24Z.md`).
<!-- def-review: LevyStochCalc.Brownian.IsBrownianFiltration 6b9d7c4909eee8db0000000000000000 by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/LevyStochCalc.Brownian.IsBrownianFiltration--claude-auditor--2026-10-19T03_27_25Z.md`).
<!-- def-review: LevyStochCalc.Brownian.IsBrownianFiltration 6b9d7c4909eee8db0000000000000000 by=claude-auditor -->
<!-- def-review: LevyStochCalc.Brownian.IsBrownianFiltration.mk 72b9d0c6dbc50a990000000000000000 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/LevyStochCalc.Brownian.IsBrownianFiltration.mk--claude-reviewer--2026-10-17T15_02_24Z.md`).
<!-- def-review: LevyStochCalc.Brownian.IsBrownianFiltration.mk 72b9d0c6dbc50a990000000000000000 by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/LevyStochCalc.Brownian.IsBrownianFiltration.mk--claude-auditor--2026-10-19T03_27_25Z.md`).
<!-- def-review: LevyStochCalc.Brownian.IsBrownianFiltration.mk 72b9d0c6dbc50a990000000000000000 by=claude-auditor -->
* `Brownian.sigmaBrownian W = ⨆_t σ(W_t)`: the σ-algebra generated by the path of `W`, in which the
  independence of `W` and `N` is stated.
<!-- def-review: LevyStochCalc.Brownian.sigmaBrownian badc0e2b10ae37cadc199bed86170e9f by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/LevyStochCalc.Brownian.sigmaBrownian--claude-reviewer--2026-10-17T15_01_46Z.md`).
<!-- def-review: LevyStochCalc.Brownian.sigmaBrownian badc0e2b10ae37cadc199bed86170e9f by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/LevyStochCalc.Brownian.sigmaBrownian--claude-auditor--2026-10-19T03_26_43Z.md`).
<!-- def-review: LevyStochCalc.Brownian.sigmaBrownian badc0e2b10ae37cadc199bed86170e9f by=claude-auditor -->
* `Brownian.Martingale.naturalFiltration W`: `t ↦ σ(W_u : u ≤ t)` (Mathlib's `Filtration.natural`),
  the natural filtration of `W`; the times `u < 0` add only events of probability `0` or `1`.
<!-- def-review: LevyStochCalc.Brownian.Martingale.naturalFiltration 54bfb40f60b0a75070cf2269380f1d3d by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/LevyStochCalc.Brownian.Martingale.naturalFiltration--claude-reviewer--2026-10-17T15_01_45Z.md`).
<!-- def-review: LevyStochCalc.Brownian.Martingale.naturalFiltration 54bfb40f60b0a75070cf2269380f1d3d by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/LevyStochCalc.Brownian.Martingale.naturalFiltration--claude-auditor--2026-10-19T03_26_43Z.md`).
<!-- def-review: LevyStochCalc.Brownian.Martingale.naturalFiltration 54bfb40f60b0a75070cf2269380f1d3d by=claude-auditor -->
* `Brownian.Multidim.MultidimBrownianMotion P d`, with projection `W` and constructor `.mk`: `d`
  one-dimensional Brownian motions `W¹, …, Wᵈ` (the projection `W`, the family of coordinates) on
  one probability space, independent as path-valued random variables (`iIndepFun` for the product
  σ-algebra on `ℝ → ℝ`), with almost surely continuous joint paths: a `d`-dimensional Brownian
  motion, with the choices of `BrownianMotion` in each coordinate.
<!-- def-review: LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion 3b79773f55ea8d890000000000000000 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion--claude-reviewer--2026-10-17T15_01_45Z.md`).
<!-- def-review: LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion 3b79773f55ea8d890000000000000000 by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion--claude-auditor--2026-10-19T03_26_43Z.md`).
<!-- def-review: LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion 3b79773f55ea8d890000000000000000 by=claude-auditor -->
<!-- def-review: LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.W 1cfeb648b43624357bd81521c555728a by=claude-author -->
Review by claude-reviewer: faithful (report `reports/LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.W--claude-reviewer--2026-10-17T15_01_45Z.md`).
<!-- def-review: LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.W 1cfeb648b43624357bd81521c555728a by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.W--claude-auditor--2026-10-19T03_26_43Z.md`).
<!-- def-review: LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.W 1cfeb648b43624357bd81521c555728a by=claude-auditor -->
<!-- def-review: LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.mk 2f29b9a2ad355ba10000000000000000 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.mk--claude-reviewer--2026-10-17T15_01_45Z.md`).
<!-- def-review: LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.mk 2f29b9a2ad355ba10000000000000000 by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.mk--claude-auditor--2026-10-19T03_26_43Z.md`).
<!-- def-review: LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.mk 2f29b9a2ad355ba10000000000000000 by=claude-auditor -->
* `MultidimBrownianMotion.naturalFiltration W = ⨆_i ℱ^{Wⁱ}`: the join of the natural filtrations of
  the coordinates, which is `t ↦ σ(W_u : u ≤ t)` for the vector process.
<!-- def-review: LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.naturalFiltration 925f72cc1b0a3caef8e2abe005107ea4 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.naturalFiltration--claude-reviewer--2026-10-17T15_01_46Z.md`).
<!-- def-review: LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.naturalFiltration 925f72cc1b0a3caef8e2abe005107ea4 by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.naturalFiltration--claude-auditor--2026-10-19T03_26_43Z.md`).
<!-- def-review: LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.naturalFiltration 925f72cc1b0a3caef8e2abe005107ea4 by=claude-auditor -->

Verdict: faithful with representation choices.

## The Poisson random measure and its filtrations (`LevyStochCalc/Poisson/`)

Manuscript (§2): `N` is a Poisson random measure on `ℝ₊ × E` with intensity `dt ν(de)`, `ν`
σ-finite, independent of `W`, and `Ñ(dt, de) = N(dt, de) − dt ν(de)` is its compensated measure.

* `Poisson.referenceIntensity ν = (Lebesgue on [0, ∞)) ⊗ ν` on `ℝ × E`: the intensity `dt ν(de)` of
  `N`, extended by `0` to negative times.
<!-- def-review: LevyStochCalc.Poisson.referenceIntensity 22b0e836f3d3268f75c31fc958e5d10d by=claude-author -->
Review by claude-reviewer: faithful (report `reports/LevyStochCalc.Poisson.referenceIntensity--claude-reviewer--2026-10-17T15_16_42Z.md`).
<!-- def-review: LevyStochCalc.Poisson.referenceIntensity 22b0e836f3d3268f75c31fc958e5d10d by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/LevyStochCalc.Poisson.referenceIntensity--claude-auditor--2026-10-19T03_27_25Z.md`).
<!-- def-review: LevyStochCalc.Poisson.referenceIntensity 22b0e836f3d3268f75c31fc958e5d10d by=claude-auditor -->
* `Poisson.poissonMeasureENN μ`: the Poisson law of mean `μ ≥ 0` carried to `[0, ∞]` along
  `ℕ ↪ [0, ∞]`, the law of a count read in `[0, ∞]`.
<!-- def-review: LevyStochCalc.Poisson.poissonMeasureENN 599fddfd2c12e9e4b502f9d73d19721c by=claude-author -->
Review by claude-reviewer: faithful (report `reports/LevyStochCalc.Poisson.poissonMeasureENN--claude-reviewer--2026-10-17T15_16_42Z.md`).
<!-- def-review: LevyStochCalc.Poisson.poissonMeasureENN 599fddfd2c12e9e4b502f9d73d19721c by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/LevyStochCalc.Poisson.poissonMeasureENN--claude-auditor--2026-10-19T03_27_25Z.md`).
<!-- def-review: LevyStochCalc.Poisson.poissonMeasureENN 599fddfd2c12e9e4b502f9d73d19721c by=claude-auditor -->
* `Poisson.PoissonRandomMeasure P ν`, with projection `N` and constructor `.mk`: an `ω`-indexed
  family `N(ω, ·)` of measures on `ℝ × E` (the projection `N`) whose counts `N(·, B)` are
  measurable; for `B` of finite intensity `N(·, B)` has the Poisson law with mean the intensity of
  `B` and is almost surely an integer, for `B` of infinite intensity `N(·, B) = ∞` almost surely;
  the counts of a countable disjoint family are independent; and the counts of the regions of
  `(−∞, s] × E` are independent of the count of `(s, t] × A`, `0 ≤ s < t`, `ν(A) < ∞`. This is the
  Poisson random measure of the paper with two choices, under which the structure, its projection
  and its constructor are read alike. The time axis is `ℝ`, and the zero intensity before time `0`
  makes every count there `0` almost surely. `N(ω, ·)` is not asked to be a counting measure for
  every `ω`, only each count to be almost surely an integer; the paper uses `N` through the laws of
  its counts and their independence (the compensation formula, the stochastic integrals, the
  representation property), which the fields record, and a Poisson random measure with
  counting-measure values satisfies them, the last field following from the independence on disjoint
  regions.
<!-- def-review: LevyStochCalc.Poisson.PoissonRandomMeasure 351b24f2cb8b3f890000000000000000 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/LevyStochCalc.Poisson.PoissonRandomMeasure--claude-reviewer--2026-10-17T15_16_41Z.md`).
<!-- def-review: LevyStochCalc.Poisson.PoissonRandomMeasure 351b24f2cb8b3f890000000000000000 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/LevyStochCalc.Poisson.PoissonRandomMeasure--claude-auditor--2026-10-19T03_27_25Z.md`).
<!-- def-review: LevyStochCalc.Poisson.PoissonRandomMeasure 351b24f2cb8b3f890000000000000000 by=claude-auditor -->
<!-- def-review: LevyStochCalc.Poisson.PoissonRandomMeasure.N d7f846758c36ed7d92e849bb24beb4db by=claude-author -->
Review by claude-reviewer: faithful (report `reports/LevyStochCalc.Poisson.PoissonRandomMeasure.N--claude-reviewer--2026-10-17T15_16_41Z.md`).
<!-- def-review: LevyStochCalc.Poisson.PoissonRandomMeasure.N d7f846758c36ed7d92e849bb24beb4db by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/LevyStochCalc.Poisson.PoissonRandomMeasure.N--claude-auditor--2026-10-19T03_27_25Z.md`).
<!-- def-review: LevyStochCalc.Poisson.PoissonRandomMeasure.N d7f846758c36ed7d92e849bb24beb4db by=claude-auditor -->
<!-- def-review: LevyStochCalc.Poisson.PoissonRandomMeasure.mk 9e96bd1e7398d9ca0000000000000000 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/LevyStochCalc.Poisson.PoissonRandomMeasure.mk--claude-reviewer--2026-10-17T15_16_41Z.md`).
<!-- def-review: LevyStochCalc.Poisson.PoissonRandomMeasure.mk 9e96bd1e7398d9ca0000000000000000 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/LevyStochCalc.Poisson.PoissonRandomMeasure.mk--claude-auditor--2026-10-19T03_27_25Z.md`).
<!-- def-review: LevyStochCalc.Poisson.PoissonRandomMeasure.mk 9e96bd1e7398d9ca0000000000000000 by=claude-auditor -->
* `PoissonRandomMeasure.compensated N B ω = N(ω, B) − (dt ν)(B)`, both read as reals: `Ñ(B)` for a
  region of finite intensity, whose count is almost surely finite. Otherwise the value follows
  Lean's `toReal` convention (`∞` read as `0`); the integrals use it only on regions `(a, b] × B`
  with `ν(B) < ∞`.
<!-- def-review: LevyStochCalc.Poisson.PoissonRandomMeasure.compensated 98b57d8ea9507e8faf4b33861dc8f3a1 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/LevyStochCalc.Poisson.PoissonRandomMeasure.compensated--claude-reviewer--2026-10-17T15_16_41Z.md`).
<!-- def-review: LevyStochCalc.Poisson.PoissonRandomMeasure.compensated 98b57d8ea9507e8faf4b33861dc8f3a1 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/LevyStochCalc.Poisson.PoissonRandomMeasure.compensated--claude-auditor--2026-10-19T03_27_25Z.md`).
<!-- def-review: LevyStochCalc.Poisson.PoissonRandomMeasure.compensated 98b57d8ea9507e8faf4b33861dc8f3a1 by=claude-auditor -->
* `Poisson.IsPoissonFiltration N ℱ`, with constructor `.mk`: for every `t` the counts `N(·, B)` of
  the measurable `B ⊆ (−∞, t] × E` are `ℱ_t`-measurable, and for `s ≥ 0` the σ-algebra `ℱ_s` is
  independent of the σ-algebra of the counts of the measurable regions of `(s, ∞) × E`: `N` is a
  Poisson random measure for `(ℱ_t)`, adapted and with future independent of the present, in the
  usual form in which `ℱ_s` is independent of all the future counts at once. The structure and its
  constructor are read alike; the filtration is indexed by `ℝ` and nothing is asked of it before
  time `0`.
<!-- def-review: LevyStochCalc.Poisson.IsPoissonFiltration e2b9154a25a8113f0000000000000000 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/LevyStochCalc.Poisson.IsPoissonFiltration--claude-reviewer--2026-10-17T15_16_41Z.md`).
<!-- def-review: LevyStochCalc.Poisson.IsPoissonFiltration e2b9154a25a8113f0000000000000000 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/LevyStochCalc.Poisson.IsPoissonFiltration--claude-auditor--2026-10-19T03_27_25Z.md`).
<!-- def-review: LevyStochCalc.Poisson.IsPoissonFiltration e2b9154a25a8113f0000000000000000 by=claude-auditor -->
<!-- def-review: LevyStochCalc.Poisson.IsPoissonFiltration.mk 32b14d502e31e2800000000000000000 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/LevyStochCalc.Poisson.IsPoissonFiltration.mk--claude-reviewer--2026-10-17T15_16_41Z.md`).
<!-- def-review: LevyStochCalc.Poisson.IsPoissonFiltration.mk 32b14d502e31e2800000000000000000 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/LevyStochCalc.Poisson.IsPoissonFiltration.mk--claude-auditor--2026-10-19T03_27_25Z.md`).
<!-- def-review: LevyStochCalc.Poisson.IsPoissonFiltration.mk 32b14d502e31e2800000000000000000 by=claude-auditor -->
* `Poisson.naturalFiltration N`: `t ↦ σ(N(·, B) : B ⊆ (−∞, t] × E measurable)`, the natural
  filtration of `N`.
<!-- def-review: LevyStochCalc.Poisson.naturalFiltration b85445b099adc2b315a246d0941d25b6 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/LevyStochCalc.Poisson.naturalFiltration--claude-reviewer--2026-10-17T15_16_41Z.md`).
<!-- def-review: LevyStochCalc.Poisson.naturalFiltration b85445b099adc2b315a246d0941d25b6 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/LevyStochCalc.Poisson.naturalFiltration--claude-auditor--2026-10-19T03_27_25Z.md`).
<!-- def-review: LevyStochCalc.Poisson.naturalFiltration b85445b099adc2b315a246d0941d25b6 by=claude-auditor -->

Verdict: faithful with representation choices (`PoissonRandomMeasure` with its projection `N` and
constructor `.mk`, and `IsPoissonFiltration` with its constructor `.mk`, alike).

## The driver and the filtration of the paper

Manuscript (§2): `W` and `N` are independent, and "the filtration `(ℱ_t)` is the usual augmentation
of the one generated by `W`, `N` and an independent initial σ-field `ℱ₀`"; the filtered probability
space satisfies the usual conditions.

* `Driver.LevyDriver P d ν`, with projections `W`, `N` and constructor `.mk`: a `d`-dimensional
  Brownian motion `W` and a Poisson random measure `N` with intensity `dt ν(de)` on one probability
  space, with `⨆_i sigmaBrownian Wⁱ = σ(W)` independent of `sigmaPoisson N = σ(N)`: the driving pair
  of the paper, `W` and an independent `N`, with the choices of the two structures. The projections
  are the two drivers.
<!-- def-review: LevyStochCalc.Driver.LevyDriver 62718398086e79200000000000000000 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/LevyStochCalc.Driver.LevyDriver--claude-reviewer--2026-10-17T15_01_46Z.md`).
<!-- def-review: LevyStochCalc.Driver.LevyDriver 62718398086e79200000000000000000 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/LevyStochCalc.Driver.LevyDriver--claude-auditor--2026-10-19T03_26_43Z.md`).
<!-- def-review: LevyStochCalc.Driver.LevyDriver 62718398086e79200000000000000000 by=claude-auditor -->
<!-- def-review: LevyStochCalc.Driver.LevyDriver.N 5a083be1dafe7d36f9ed1dcbab2d13fc by=claude-author -->
Review by claude-reviewer: faithful (report `reports/LevyStochCalc.Driver.LevyDriver.N--claude-reviewer--2026-10-17T15_01_47Z.md`).
<!-- def-review: LevyStochCalc.Driver.LevyDriver.N 5a083be1dafe7d36f9ed1dcbab2d13fc by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/LevyStochCalc.Driver.LevyDriver.N--claude-auditor--2026-10-19T03_26_43Z.md`).
<!-- def-review: LevyStochCalc.Driver.LevyDriver.N 5a083be1dafe7d36f9ed1dcbab2d13fc by=claude-auditor -->
<!-- def-review: LevyStochCalc.Driver.LevyDriver.W a4417688f8409d5aea3c41b147d06901 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/LevyStochCalc.Driver.LevyDriver.W--claude-reviewer--2026-10-17T15_01_47Z.md`).
<!-- def-review: LevyStochCalc.Driver.LevyDriver.W a4417688f8409d5aea3c41b147d06901 by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/LevyStochCalc.Driver.LevyDriver.W--claude-auditor--2026-10-19T03_26_43Z.md`).
<!-- def-review: LevyStochCalc.Driver.LevyDriver.W a4417688f8409d5aea3c41b147d06901 by=claude-auditor -->
<!-- def-review: LevyStochCalc.Driver.LevyDriver.mk 8b4f158ed4b608ae0000000000000000 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/LevyStochCalc.Driver.LevyDriver.mk--claude-reviewer--2026-10-17T15_01_47Z.md`).
<!-- def-review: LevyStochCalc.Driver.LevyDriver.mk 8b4f158ed4b608ae0000000000000000 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/LevyStochCalc.Driver.LevyDriver.mk--claude-auditor--2026-10-19T03_26_43Z.md`).
<!-- def-review: LevyStochCalc.Driver.LevyDriver.mk 8b4f158ed4b608ae0000000000000000 by=claude-auditor -->
* `Driver.sigmaPoisson N`: the σ-algebra generated by all the counts `N(·, B)`, `B ⊆ ℝ × E`
  measurable, i.e. by `N`.
<!-- def-review: LevyStochCalc.Driver.sigmaPoisson a2a2909ee119ac9ac46169345dbcc2fe by=claude-author -->
Review by claude-reviewer: faithful (report `reports/LevyStochCalc.Driver.sigmaPoisson--claude-reviewer--2026-10-17T15_01_47Z.md`).
<!-- def-review: LevyStochCalc.Driver.sigmaPoisson a2a2909ee119ac9ac46169345dbcc2fe by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/LevyStochCalc.Driver.sigmaPoisson--claude-auditor--2026-10-19T03_26_43Z.md`).
<!-- def-review: LevyStochCalc.Driver.sigmaPoisson a2a2909ee119ac9ac46169345dbcc2fe by=claude-auditor -->
* `Driver.LevyDriver.filtration D = (⨆_i ℱ^{Wⁱ}) ⊔ ℱ^N`: `t ↦ σ(W_u, N(·, B) : u ≤ t, B ⊆ (−∞, t] ×
  E)`, the filtration generated by `W` and `N`, before augmentation.
<!-- def-review: LevyStochCalc.Driver.LevyDriver.filtration 1788864ffc8d4806240c2702eece8252 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/LevyStochCalc.Driver.LevyDriver.filtration--claude-reviewer--2026-10-17T15_01_47Z.md`).
<!-- def-review: LevyStochCalc.Driver.LevyDriver.filtration 1788864ffc8d4806240c2702eece8252 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/LevyStochCalc.Driver.LevyDriver.filtration--claude-auditor--2026-10-19T03_26_43Z.md`).
<!-- def-review: LevyStochCalc.Driver.LevyDriver.filtration 1788864ffc8d4806240c2702eece8252 by=claude-auditor -->
* `Probability.aug m m₀ μ`: the `m₀`-measurable sets `A` with `μ(A ∆ B) = 0` for some `B ∈ m`, i.e.
  `m` augmented by the `μ`-null sets. These are the null sets of the ambient σ-algebra `m₀`, not of
  its completion; on a complete probability space, which the usual conditions presuppose, they are
  all the null sets.
<!-- def-review: LevyStochCalc.Probability.aug 14d37d0154cad2a45462fbc0e9dca39d by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/LevyStochCalc.Probability.aug--claude-reviewer--2026-10-17T15_16_42Z.md`).
<!-- def-review: LevyStochCalc.Probability.aug 14d37d0154cad2a45462fbc0e9dca39d by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/LevyStochCalc.Probability.aug--claude-auditor--2026-10-19T03_27_26Z.md`).
<!-- def-review: LevyStochCalc.Probability.aug 14d37d0154cad2a45462fbc0e9dca39d by=claude-auditor -->
* `Brownian.augFiltration ℱ μ`: `t ↦ aug (ℱ (max t 0))`, the filtration frozen at its time-`0` value
  before time `0` and augmented at each time by the null sets.
<!-- def-review: LevyStochCalc.Brownian.augFiltration 62f593ac7205c9672616e31e5936c2fa by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/LevyStochCalc.Brownian.augFiltration--claude-reviewer--2026-10-17T15_01_46Z.md`).
<!-- def-review: LevyStochCalc.Brownian.augFiltration 62f593ac7205c9672616e31e5936c2fa by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/LevyStochCalc.Brownian.augFiltration--claude-auditor--2026-10-19T03_26_43Z.md`).
<!-- def-review: LevyStochCalc.Brownian.augFiltration 62f593ac7205c9672616e31e5936c2fa by=claude-auditor -->
* `WellPosedness.Enlarged.initJoint 𝒢₀ D h𝒢₀`: `t ↦ ℱ^{W,N}_t ⊔ 𝒢₀`, the filtration generated by the
  driver and the initial σ-algebra `𝒢₀`, the paper's `ℱ₀`.
<!-- def-review: MVFBSDEJ.WellPosedness.Enlarged.initJoint c9ac55281f8264f86774558053262866 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.Enlarged.initJoint--claude-reviewer--2026-10-17T12_31_12Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Enlarged.initJoint c9ac55281f8264f86774558053262866 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.Enlarged.initJoint--claude-auditor--2026-10-19T03_28_16Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Enlarged.initJoint c9ac55281f8264f86774558053262866 by=claude-auditor -->
* `WellPosedness.Enlarged.enlJoint 𝒢₀ D h𝒢₀ = augFiltration (initJoint 𝒢₀ D h𝒢₀)₊ P`: the
  right-continuous version of `initJoint`, frozen before time `0` and augmented by the null sets:
  the usual augmentation of `ℱ^{W,N}_t ∨ ℱ₀`, the filtration of the paper. Augmentation commutes
  with the countable decreasing intersections of the right-continuous version
  (`aug_iInf_of_antitone`), so the order of the two steps does not matter. The independence of `𝒢₀`
  from the driver is not part of the definition; the statements assume it (`hind₀`).
<!-- def-review: MVFBSDEJ.WellPosedness.Enlarged.enlJoint c9ac55281f8264f87e82c4bf9bff8a94 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.Enlarged.enlJoint--claude-reviewer--2026-10-17T12_30_42Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Enlarged.enlJoint c9ac55281f8264f87e82c4bf9bff8a94 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.Enlarged.enlJoint--claude-auditor--2026-10-19T03_28_16Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Enlarged.enlJoint c9ac55281f8264f87e82c4bf9bff8a94 by=claude-auditor -->

Verdict: faithful with representation choices.

## Measurability classes of processes (`LevyStochCalc/Probability/`)

Manuscript (§2–§3): processes are progressively measurable or predictable on `Ω × [0, T]`, `𝒫` is
the predictable σ-field, and the jump integrands and the jump coefficient along a tuple are
`𝒫 ⊗ ℰ`-measurable.

* `Probability.ProgressivelyMeasurable ℱ H`: for every `t`, `(ω, s) ↦ 1_{s ≤ t} H(ω, s)` is strongly
  `ℱ_t ⊗ 𝔅(ℝ)`-measurable: progressive measurability. Choices: time runs over `ℝ`, and the window
  `s ≤ t` includes negative times; the condition splits into the usual one on `[0, t]` and a
  condition on the values before time `0`, which a process extended by `0` there meets and which
  does not involve its values on `[0, T]`. Strong measurability is measurability for the
  finite-dimensional value spaces and adds a separable range for a process with values in `L²(ν)`.
<!-- def-review: LevyStochCalc.Probability.ProgressivelyMeasurable 29ce1b1b7a20e5156d5f9c33b358fa7f by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/LevyStochCalc.Probability.ProgressivelyMeasurable--claude-reviewer--2026-10-17T15_16_42Z.md`).
<!-- def-review: LevyStochCalc.Probability.ProgressivelyMeasurable 29ce1b1b7a20e5156d5f9c33b358fa7f by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/LevyStochCalc.Probability.ProgressivelyMeasurable--claude-auditor--2026-10-19T03_27_26Z.md`).
<!-- def-review: LevyStochCalc.Probability.ProgressivelyMeasurable 29ce1b1b7a20e5156d5f9c33b358fa7f by=claude-auditor -->
* `Probability.MarkedProgressivelyMeasurable ℱ φ`: for every `t`, `(ω, s, e) ↦ 1_{s ≤ t} φ(ω, s, e)`
  is strongly `ℱ_t ⊗ 𝔅(ℝ) ⊗ ℰ`-measurable: progressive measurability of a mark-indexed process, with
  the same choices. It is weaker than `𝒫 ⊗ ℰ`-measurability: a marked-predictable field is marked
  progressive (`MarkedPredictable.markedProgressivelyMeasurable`), and the library's compensated
  integral of a marked progressive integrand is the isometric extension of the integral of adapted
  step integrands, which for a `𝒫 ⊗ ℰ`-measurable integrand is the paper's.
<!-- def-review: LevyStochCalc.Probability.MarkedProgressivelyMeasurable 3768ee472ea8756ac41aefffc2091b0b by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/LevyStochCalc.Probability.MarkedProgressivelyMeasurable--claude-reviewer--2026-10-17T15_16_42Z.md`).
<!-- def-review: LevyStochCalc.Probability.MarkedProgressivelyMeasurable 3768ee472ea8756ac41aefffc2091b0b by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/LevyStochCalc.Probability.MarkedProgressivelyMeasurable--claude-auditor--2026-10-19T03_27_26Z.md`).
<!-- def-review: LevyStochCalc.Probability.MarkedProgressivelyMeasurable 3768ee472ea8756ac41aefffc2091b0b by=claude-auditor -->
* `Probability.predictableSigma ℱ`: the σ-algebra on `ℝ × Ω` generated by `(−∞, 0] × A`, `A ∈ ℱ_0`,
  and `(r, ∞) × A`, `A ∈ ℱ_r`, `r ∈ ℝ`. On `[0, ∞) × Ω` these sets trace the usual generators
  `{0} × A`, `A ∈ ℱ_0`, and `(r, q] × A = ((r, ∞) \ (q, ∞)) × A`, `A ∈ ℱ_r`, so the trace is the
  predictable σ-field `𝒫`; the cell `(−∞, 0] × A` carries the time-`0` sets to negative times, which
  matter only for processes not vanishing there.
<!-- def-review: LevyStochCalc.Probability.predictableSigma 9af29befcf36c1f234d23c2a4611da87 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/LevyStochCalc.Probability.predictableSigma--claude-reviewer--2026-10-17T15_16_42Z.md`).
<!-- def-review: LevyStochCalc.Probability.predictableSigma 9af29befcf36c1f234d23c2a4611da87 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/LevyStochCalc.Probability.predictableSigma--claude-auditor--2026-10-19T03_27_26Z.md`).
<!-- def-review: LevyStochCalc.Probability.predictableSigma 9af29befcf36c1f234d23c2a4611da87 by=claude-auditor -->
* `Probability.Predictable ℱ H`: `(s, ω) ↦ H(ω, s)` is strongly measurable for `predictableSigma ℱ`:
  predictability, with the choices above.
<!-- def-review: LevyStochCalc.Probability.Predictable 15a7903d5fe90c1df6412e0a501eaa5b by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/LevyStochCalc.Probability.Predictable--claude-reviewer--2026-10-17T15_16_42Z.md`).
<!-- def-review: LevyStochCalc.Probability.Predictable 15a7903d5fe90c1df6412e0a501eaa5b by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/LevyStochCalc.Probability.Predictable--claude-auditor--2026-10-19T03_27_26Z.md`).
<!-- def-review: LevyStochCalc.Probability.Predictable 15a7903d5fe90c1df6412e0a501eaa5b by=claude-auditor -->
* `Probability.markedPredictableRect ℱ ν`: the rectangles `F × (r, q] × B` with `r ≥ 0`, `F ∈ ℱ_r`
  and `B` measurable of finite `ν`-measure, the predictable rectangles of the time–mark space.
<!-- def-review: LevyStochCalc.Probability.markedPredictableRect 87996b432b2b8cfe106f0f7a940c10d8 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/LevyStochCalc.Probability.markedPredictableRect--claude-reviewer--2026-10-17T15_16_42Z.md`).
<!-- def-review: LevyStochCalc.Probability.markedPredictableRect 87996b432b2b8cfe106f0f7a940c10d8 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/LevyStochCalc.Probability.markedPredictableRect--claude-auditor--2026-10-19T03_27_26Z.md`).
<!-- def-review: LevyStochCalc.Probability.markedPredictableRect 87996b432b2b8cfe106f0f7a940c10d8 by=claude-auditor -->
* `Probability.markedPredictableSigma ℱ ν`: the σ-algebra on `Ω × ℝ × E` generated by these
  rectangles. For σ-finite `ν` the mark sets of finite measure generate `ℰ`, so on positive times
  this is `𝒫 ⊗ ℰ`. The generating rectangles start at `r ≥ 0` and there are no time-`0` sets, so
  every set of the σ-algebra contains or misses all of `Ω × (−∞, 0] × E`; unlike `predictableSigma`,
  which has the time-`0` sets.
<!-- def-review: LevyStochCalc.Probability.markedPredictableSigma 802b939730e12ea992958da67e6f2150 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/LevyStochCalc.Probability.markedPredictableSigma--claude-reviewer--2026-10-17T15_16_42Z.md`).
<!-- def-review: LevyStochCalc.Probability.markedPredictableSigma 802b939730e12ea992958da67e6f2150 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/LevyStochCalc.Probability.markedPredictableSigma--claude-auditor--2026-10-19T03_27_26Z.md`).
<!-- def-review: LevyStochCalc.Probability.markedPredictableSigma 802b939730e12ea992958da67e6f2150 by=claude-auditor -->
* `Probability.MarkedPredictable ℱ ν ψ`: `(ω, s, e) ↦ ψ(ω, s, e)` is measurable for
  `markedPredictableSigma ℱ ν`: the paper's `𝒫 ⊗ ℰ`-measurability. By the remark above, a real
  marked-predictable field is constant for `t ≤ 0`; with the vanishing off `[0, T]` that the
  statements ask, `U_0 = 0`, at the `dt`-null time `0`, which no integral sees.
<!-- def-review: LevyStochCalc.Probability.MarkedPredictable 35cc10827f7a7db887e9099b1605e255 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/LevyStochCalc.Probability.MarkedPredictable--claude-reviewer--2026-10-17T15_16_42Z.md`).
<!-- def-review: LevyStochCalc.Probability.MarkedPredictable 35cc10827f7a7db887e9099b1605e255 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/LevyStochCalc.Probability.MarkedPredictable--claude-auditor--2026-10-19T03_27_26Z.md`).
<!-- def-review: LevyStochCalc.Probability.MarkedPredictable 35cc10827f7a7db887e9099b1605e255 by=claude-auditor -->

Verdict: faithful with representation choices.

## The Brownian Itô integral (`LevyStochCalc/Brownian/Ito*`)

Manuscript (§2–§3): `∫_0^t Z_s dW_s` is the standard `L²` Itô integral of a predictable `Z` with
`𝔼 ∫_0^T |Z_s|²_F ds < ∞`.

* `Brownian.Ito.energy P T H = 𝔼 ∫_{[0, T]} |H(ω, s)|² ds`, an iterated lower integral in `[0, ∞]`:
  the squared norm of `H` in `L²(Ω × [0, T], dP ⊗ dt)`, defined for every `H` with no measurability
  presupposed, `∞` when infinite.
<!-- def-review: LevyStochCalc.Brownian.Ito.energy d863e7f664002259c7c4c422b7f327c7 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/LevyStochCalc.Brownian.Ito.energy--claude-reviewer--2026-10-17T15_02_25Z.md`).
<!-- def-review: LevyStochCalc.Brownian.Ito.energy d863e7f664002259c7c4c422b7f327c7 by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/LevyStochCalc.Brownian.Ito.energy--claude-auditor--2026-10-19T03_26_42Z.md`).
<!-- def-review: LevyStochCalc.Brownian.Ito.energy d863e7f664002259c7c4c422b7f327c7 by=claude-auditor -->
* `Brownian.Ito.SimplePredictable Ω T`, with projections `N`, `partition`, `ξ` and constructor
  `.mk`: a partition `0 = t_0 < ⋯ < t_N ≤ T` (`partition`, with `N` pieces) and coefficients
  `ξ_0, …, ξ_{N−1}` (`ξ`), each bounded and measurable, standing for `∑_i ξ_i 1_{(t_i, t_{i+1}]}`.
  The structure and its constructor are broader than the paper's simple predictable integrands: they
  carry no filtration, and the coefficients are only bounded and measurable. The paper's notion is
  the structure together with adaptedness at the left end, `ξ_i` `ℱ_{t_i}`-measurable, which
  `masterApprox` imposes at every use (`masterApprox_adapt`). The projections read the number of
  pieces, the partition and the coefficients, as printed.
<!-- def-review: LevyStochCalc.Brownian.Ito.SimplePredictable 095844f503e4a7e50000000000000000 by=claude-author -->
Review by claude-reviewer: broader (report `reports/LevyStochCalc.Brownian.Ito.SimplePredictable--claude-reviewer--2026-10-17T15_02_24Z.md`).
<!-- def-review: LevyStochCalc.Brownian.Ito.SimplePredictable 095844f503e4a7e50000000000000000 by=claude-reviewer -->
Review by claude-auditor: broader (report `reports/LevyStochCalc.Brownian.Ito.SimplePredictable--claude-auditor--2026-10-19T03_26_42Z.md`).
<!-- def-review: LevyStochCalc.Brownian.Ito.SimplePredictable 095844f503e4a7e50000000000000000 by=claude-auditor -->
<!-- def-review: LevyStochCalc.Brownian.Ito.SimplePredictable.N 12c9ba642316c53035aaa7419ff6e7e7 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/LevyStochCalc.Brownian.Ito.SimplePredictable.N--claude-reviewer--2026-10-17T15_02_24Z.md`).
<!-- def-review: LevyStochCalc.Brownian.Ito.SimplePredictable.N 12c9ba642316c53035aaa7419ff6e7e7 by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/LevyStochCalc.Brownian.Ito.SimplePredictable.N--claude-auditor--2026-10-19T03_26_42Z.md`).
<!-- def-review: LevyStochCalc.Brownian.Ito.SimplePredictable.N 12c9ba642316c53035aaa7419ff6e7e7 by=claude-auditor -->
<!-- def-review: LevyStochCalc.Brownian.Ito.SimplePredictable.partition 8d3a8228f2eaa5da0cf79dfff5cea25d by=claude-author -->
Review by claude-reviewer: faithful (report `reports/LevyStochCalc.Brownian.Ito.SimplePredictable.partition--claude-reviewer--2026-10-17T15_02_25Z.md`).
<!-- def-review: LevyStochCalc.Brownian.Ito.SimplePredictable.partition 8d3a8228f2eaa5da0cf79dfff5cea25d by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/LevyStochCalc.Brownian.Ito.SimplePredictable.partition--claude-auditor--2026-10-19T03_26_42Z.md`).
<!-- def-review: LevyStochCalc.Brownian.Ito.SimplePredictable.partition 8d3a8228f2eaa5da0cf79dfff5cea25d by=claude-auditor -->
<!-- def-review: LevyStochCalc.Brownian.Ito.SimplePredictable.ξ a05453682c8999447dd6f53efb617007 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/LevyStochCalc.Brownian.Ito.SimplePredictable.ξ--claude-reviewer--2026-10-17T15_02_25Z.md`).
<!-- def-review: LevyStochCalc.Brownian.Ito.SimplePredictable.ξ a05453682c8999447dd6f53efb617007 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/LevyStochCalc.Brownian.Ito.SimplePredictable.ξ--claude-auditor--2026-10-19T03_26_42Z.md`).
<!-- def-review: LevyStochCalc.Brownian.Ito.SimplePredictable.ξ a05453682c8999447dd6f53efb617007 by=claude-auditor -->
<!-- def-review: LevyStochCalc.Brownian.Ito.SimplePredictable.mk 25ac9f29c6c3f9220000000000000000 by=claude-author -->
Review by claude-reviewer: broader (report `reports/LevyStochCalc.Brownian.Ito.SimplePredictable.mk--claude-reviewer--2026-10-17T15_02_24Z.md`).
<!-- def-review: LevyStochCalc.Brownian.Ito.SimplePredictable.mk 25ac9f29c6c3f9220000000000000000 by=claude-reviewer -->
Review by claude-auditor: broader (report `reports/LevyStochCalc.Brownian.Ito.SimplePredictable.mk--claude-auditor--2026-10-19T03_26_42Z.md`).
<!-- def-review: LevyStochCalc.Brownian.Ito.SimplePredictable.mk 25ac9f29c6c3f9220000000000000000 by=claude-auditor -->
* `SimplePredictable.eval H t ω = ∑_i ξ_i(ω) 1_{(t_i, t_{i+1}]}(t)`: the integrand as a process.
<!-- def-review: LevyStochCalc.Brownian.Ito.SimplePredictable.eval 3d79b84163943973343eb497386c5538 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/LevyStochCalc.Brownian.Ito.SimplePredictable.eval--claude-reviewer--2026-10-17T15_02_24Z.md`).
<!-- def-review: LevyStochCalc.Brownian.Ito.SimplePredictable.eval 3d79b84163943973343eb497386c5538 by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/LevyStochCalc.Brownian.Ito.SimplePredictable.eval--claude-auditor--2026-10-19T03_26_42Z.md`).
<!-- def-review: LevyStochCalc.Brownian.Ito.SimplePredictable.eval 3d79b84163943973343eb497386c5538 by=claude-auditor -->
* `Brownian.Ito.simpleIntegral W H t ω = ∑_i ξ_i(ω) (W_{t_{i+1} ∧ t} − W_{t_i ∧ t})`: the elementary
  integral `∫_0^t H dW`.
<!-- def-review: LevyStochCalc.Brownian.Ito.simpleIntegral 1a897ae182e91c2d9e8ab5364d5848bb by=claude-author -->
Review by claude-reviewer: faithful (report `reports/LevyStochCalc.Brownian.Ito.simpleIntegral--claude-reviewer--2026-10-17T15_02_25Z.md`).
<!-- def-review: LevyStochCalc.Brownian.Ito.simpleIntegral 1a897ae182e91c2d9e8ab5364d5848bb by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/LevyStochCalc.Brownian.Ito.simpleIntegral--claude-auditor--2026-10-19T03_26_42Z.md`).
<!-- def-review: LevyStochCalc.Brownian.Ito.simpleIntegral 1a897ae182e91c2d9e8ab5364d5848bb by=claude-auditor -->
* `Brownian.Ito.masterApprox ℱ H … n`: for `H` jointly measurable, progressive and of finite energy
  on every horizon, a chosen simple integrand on `[0, n + 1]` whose coefficients are
  `ℱ_{t_i}`-measurable (`masterApprox_adapt`) and whose energy distance to `H` on `[0, n + 1]` is
  below `1/(n + 1)` (`masterApprox_within`), from the density of the adapted simple integrands: the
  approximating sequence of the construction. The choice does not affect the limit, which the
  isometry determines.
<!-- def-review: LevyStochCalc.Brownian.Ito.masterApprox 8590dd88f726df792bc395a002d2695e by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/LevyStochCalc.Brownian.Ito.masterApprox--claude-reviewer--2026-10-17T15_02_25Z.md`).
<!-- def-review: LevyStochCalc.Brownian.Ito.masterApprox 8590dd88f726df792bc395a002d2695e by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/LevyStochCalc.Brownian.Ito.masterApprox--claude-auditor--2026-10-19T03_26_42Z.md`).
<!-- def-review: LevyStochCalc.Brownian.Ito.masterApprox 8590dd88f726df792bc395a002d2695e by=claude-auditor -->
* `Brownian.Ito.masterLp … t n`: the class in `L²(P)` of `simpleIntegral W (masterApprox n) t` for
  `0 ≤ t ≤ n + 1`, and `0` otherwise.
<!-- def-review: LevyStochCalc.Brownian.Ito.masterLp ed9f750f32d4e782710be84c23dfa758 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/LevyStochCalc.Brownian.Ito.masterLp--claude-reviewer--2026-10-17T15_02_25Z.md`).
<!-- def-review: LevyStochCalc.Brownian.Ito.masterLp ed9f750f32d4e782710be84c23dfa758 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/LevyStochCalc.Brownian.Ito.masterLp--claude-auditor--2026-10-19T03_26_42Z.md`).
<!-- def-review: LevyStochCalc.Brownian.Ito.masterLp ed9f750f32d4e782710be84c23dfa758 by=claude-auditor -->
* `Brownian.Ito.stochasticIntegralBrownianLp … t`: the limit in `L²(P)` (`limUnder`) of
  `masterLp … t n` as `n → ∞`. The sequence is Cauchy at every `t ≥ 0` and `0` for `t < 0`, so
  `limUnder` never takes its junk value: this is the `L²` Itô integral `∫_0^t H dW` as an element of
  `L²(P)`, `0` before time `0`.
<!-- def-review: LevyStochCalc.Brownian.Ito.stochasticIntegralBrownianLp 06fc0ca46cd58663ccf8a97ed9638128 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/LevyStochCalc.Brownian.Ito.stochasticIntegralBrownianLp--claude-reviewer--2026-10-17T15_01_45Z.md`).
<!-- def-review: LevyStochCalc.Brownian.Ito.stochasticIntegralBrownianLp 06fc0ca46cd58663ccf8a97ed9638128 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/LevyStochCalc.Brownian.Ito.stochasticIntegralBrownianLp--claude-auditor--2026-10-19T03_26_43Z.md`).
<!-- def-review: LevyStochCalc.Brownian.Ito.stochasticIntegralBrownianLp 06fc0ca46cd58663ccf8a97ed9638128 by=claude-auditor -->
* `Brownian.Ito.stochasticIntegralBrownian … t`: an `ℱ_t`-measurable function in that class
  (`AEStronglyMeasurable.mk`), chosen at each time separately: a version of `∫_0^t H dW` at each
  `t`, with no path regularity; the solution notion reads the Brownian integrals through a càdlàg
  version (`PaperWeakSolutionInt`).
<!-- def-review: LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian 2c173e4f8affd8d994743b6229ec7957 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian--claude-reviewer--2026-10-17T15_01_45Z.md`).
<!-- def-review: LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian 2c173e4f8affd8d994743b6229ec7957 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian--claude-auditor--2026-10-19T03_26_43Z.md`).
<!-- def-review: LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian 2c173e4f8affd8d994743b6229ec7957 by=claude-auditor -->
* `Brownian.Ito.stochasticIntegral W ℱ hℱ H … T = stochasticIntegralBrownian … T`: the Itô integral
  `∫_0^T H dW` against a one-dimensional `(ℱ_t)`-Brownian motion, for `H` jointly measurable,
  progressive and of finite energy on every horizon. The integrands are progressive rather than
  predictable, the class of the `L²` integral of Karatzas–Shreve §3.2; for a predictable `H` it is
  the paper's integral. The integrands of the statements vanish off `[0, T]`, which gives the finite
  energy on every horizon.
<!-- def-review: LevyStochCalc.Brownian.Ito.stochasticIntegral 2c173e4f8affd8d9fb9c03a2213aee2d by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/LevyStochCalc.Brownian.Ito.stochasticIntegral--claude-reviewer--2026-10-17T15_02_25Z.md`).
<!-- def-review: LevyStochCalc.Brownian.Ito.stochasticIntegral 2c173e4f8affd8d9fb9c03a2213aee2d by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/LevyStochCalc.Brownian.Ito.stochasticIntegral--claude-auditor--2026-10-19T03_26_42Z.md`).
<!-- def-review: LevyStochCalc.Brownian.Ito.stochasticIntegral 2c173e4f8affd8d9fb9c03a2213aee2d by=claude-auditor -->
* `MultidimBrownianMotion.stochasticIntegral W ℱ hℱ Z … T = ∑_j ∫_0^T Z^j dW^j`: the integral of a
  vector integrand against the `d`-dimensional `W`, coordinate by coordinate, one row of `∫ Z dW`
  for `Z ∈ ℝ^{m×d}`.
<!-- def-review: LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral 7a8c23649dc43d3d0eb5bb888b122b88 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral--claude-reviewer--2026-10-17T15_01_46Z.md`).
<!-- def-review: LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral 7a8c23649dc43d3d0eb5bb888b122b88 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral--claude-auditor--2026-10-19T03_26_43Z.md`).
<!-- def-review: LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral 7a8c23649dc43d3d0eb5bb888b122b88 by=claude-auditor -->

Verdict: faithful with representation choices; `SimplePredictable` (with its constructor `.mk`)
broader, the paper's simple predictable integrands being its instances with every `ξ_i`
`ℱ_{t_i}`-measurable, the form in which it is used (`masterApprox_adapt`).

## The compensated Poisson integral (`LevyStochCalc/Poisson/Compensated*`, `MarkStep*`)

Manuscript (§2): `∫_0^t ∫_E U_s(e) Ñ(ds, de)` is the compensated Poisson integral of a
`𝒫 ⊗ ℰ`-measurable `U` with `𝔼 ∫_0^T ‖U_s‖²_{L²(ν)} ds < ∞`, read through such a representative
(2.4).

* `Poisson.Compensated.markedEnergy P ν T φ = 𝔼 ∫_{[0, T]} ∫_E |φ(ω, s, e)|² ν(de) ds`, an iterated
  lower integral in `[0, ∞]`: the squared norm of `φ` in `L²(dP ⊗ dt ⊗ ν)` on `[0, T]`, with no
  measurability presupposed.
<!-- def-review: LevyStochCalc.Poisson.Compensated.markedEnergy 2cb843d4d0d59f2db65e60392e647c8a by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/LevyStochCalc.Poisson.Compensated.markedEnergy--claude-reviewer--2026-10-17T15_01_49Z.md`).
<!-- def-review: LevyStochCalc.Poisson.Compensated.markedEnergy 2cb843d4d0d59f2db65e60392e647c8a by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/LevyStochCalc.Poisson.Compensated.markedEnergy--claude-auditor--2026-10-19T03_27_24Z.md`).
<!-- def-review: LevyStochCalc.Poisson.Compensated.markedEnergy 2cb843d4d0d59f2db65e60392e647c8a by=claude-auditor -->
* `Poisson.Compensated.TimeGrid`, with projections `N₀`, `p` and constructor `.mk`: a grid
  `0 = p_0 < p_1 < ⋯ < p_{N₀}`, the values of `p` beyond `N₀` unused.
<!-- def-review: LevyStochCalc.Poisson.Compensated.TimeGrid f743d5d40f14218f0000000000000000 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/LevyStochCalc.Poisson.Compensated.TimeGrid--claude-reviewer--2026-10-17T15_01_48Z.md`).
<!-- def-review: LevyStochCalc.Poisson.Compensated.TimeGrid f743d5d40f14218f0000000000000000 by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/LevyStochCalc.Poisson.Compensated.TimeGrid--claude-auditor--2026-10-19T03_27_23Z.md`).
<!-- def-review: LevyStochCalc.Poisson.Compensated.TimeGrid f743d5d40f14218f0000000000000000 by=claude-auditor -->
<!-- def-review: LevyStochCalc.Poisson.Compensated.TimeGrid.N₀ 96a3829b277b5ce438918b7312dbff61 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/LevyStochCalc.Poisson.Compensated.TimeGrid.N₀--claude-reviewer--2026-10-17T15_01_48Z.md`).
<!-- def-review: LevyStochCalc.Poisson.Compensated.TimeGrid.N₀ 96a3829b277b5ce438918b7312dbff61 by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/LevyStochCalc.Poisson.Compensated.TimeGrid.N₀--claude-auditor--2026-10-19T03_27_23Z.md`).
<!-- def-review: LevyStochCalc.Poisson.Compensated.TimeGrid.N₀ 96a3829b277b5ce438918b7312dbff61 by=claude-auditor -->
<!-- def-review: LevyStochCalc.Poisson.Compensated.TimeGrid.p 57d3a20338cbc4687e319ddece66a22f by=claude-author -->
Review by claude-reviewer: faithful (report `reports/LevyStochCalc.Poisson.Compensated.TimeGrid.p--claude-reviewer--2026-10-17T15_01_49Z.md`).
<!-- def-review: LevyStochCalc.Poisson.Compensated.TimeGrid.p 57d3a20338cbc4687e319ddece66a22f by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/LevyStochCalc.Poisson.Compensated.TimeGrid.p--claude-auditor--2026-10-19T03_27_24Z.md`).
<!-- def-review: LevyStochCalc.Poisson.Compensated.TimeGrid.p 57d3a20338cbc4687e319ddece66a22f by=claude-auditor -->
<!-- def-review: LevyStochCalc.Poisson.Compensated.TimeGrid.mk 33f8672dd33944890000000000000000 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/LevyStochCalc.Poisson.Compensated.TimeGrid.mk--claude-reviewer--2026-10-17T15_01_48Z.md`).
<!-- def-review: LevyStochCalc.Poisson.Compensated.TimeGrid.mk 33f8672dd33944890000000000000000 by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/LevyStochCalc.Poisson.Compensated.TimeGrid.mk--claude-auditor--2026-10-19T03_27_24Z.md`).
<!-- def-review: LevyStochCalc.Poisson.Compensated.TimeGrid.mk 33f8672dd33944890000000000000000 by=claude-auditor -->
* `TimeGrid.dyadic T hT n`: the grid `p_i = i T / 2ⁿ`, `i ≤ 2ⁿ`, of `[0, T]`.
<!-- def-review: LevyStochCalc.Poisson.Compensated.TimeGrid.dyadic 95a28fb6db0dc434182c96d67c581601 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/LevyStochCalc.Poisson.Compensated.TimeGrid.dyadic--claude-reviewer--2026-10-17T15_01_48Z.md`).
<!-- def-review: LevyStochCalc.Poisson.Compensated.TimeGrid.dyadic 95a28fb6db0dc434182c96d67c581601 by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/LevyStochCalc.Poisson.Compensated.TimeGrid.dyadic--claude-auditor--2026-10-19T03_27_24Z.md`).
<!-- def-review: LevyStochCalc.Poisson.Compensated.TimeGrid.dyadic 95a28fb6db0dc434182c96d67c581601 by=claude-auditor -->
* `Poisson.Compensated.MarkStep Ω E ν g`, with projections `K`, `B`, `ξ` and constructor `.mk`: mark
  sets `B_1, …, B_K` of finite `ν`-measure and coefficients `ξ_{ik}`, bounded and measurable,
  standing for `∑_i 1_{(p_i, p_{i+1}]}(s) ∑_k ξ_{ik}(ω) 1_{B_k}(e)` on the grid `g`. As for
  `SimplePredictable`, the structure and its constructor are broader than the paper's simple
  predictable integrands: they carry no filtration, and the coefficients are only bounded and
  measurable. The paper's notion is the structure together with adaptedness at the left end of each
  piece, `MarkStep.Adapted`, which every approximant of the construction carries (`master_adapted`).
  The projections read the number of mark sets, the mark sets and the coefficients, as printed.
<!-- def-review: LevyStochCalc.Poisson.Compensated.MarkStep a1ee2ea0e1457b990000000000000000 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/LevyStochCalc.Poisson.Compensated.MarkStep--claude-reviewer--2026-10-17T15_01_47Z.md`).
<!-- def-review: LevyStochCalc.Poisson.Compensated.MarkStep a1ee2ea0e1457b990000000000000000 by=claude-reviewer -->
Review by claude-auditor: broader (report `reports/LevyStochCalc.Poisson.Compensated.MarkStep--claude-auditor--2026-10-19T03_26_43Z.md`).
<!-- def-review: LevyStochCalc.Poisson.Compensated.MarkStep a1ee2ea0e1457b990000000000000000 by=claude-auditor -->
<!-- def-review: LevyStochCalc.Poisson.Compensated.MarkStep.K 69b93339d92d0211761d8983c191e8a4 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/LevyStochCalc.Poisson.Compensated.MarkStep.K--claude-reviewer--2026-10-17T15_01_48Z.md`).
<!-- def-review: LevyStochCalc.Poisson.Compensated.MarkStep.K 69b93339d92d0211761d8983c191e8a4 by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/LevyStochCalc.Poisson.Compensated.MarkStep.K--claude-auditor--2026-10-19T03_27_23Z.md`).
<!-- def-review: LevyStochCalc.Poisson.Compensated.MarkStep.K 69b93339d92d0211761d8983c191e8a4 by=claude-auditor -->
<!-- def-review: LevyStochCalc.Poisson.Compensated.MarkStep.B cd1a4d6799bbdd79ee01c9f6b801a7a2 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/LevyStochCalc.Poisson.Compensated.MarkStep.B--claude-reviewer--2026-10-17T15_01_48Z.md`).
<!-- def-review: LevyStochCalc.Poisson.Compensated.MarkStep.B cd1a4d6799bbdd79ee01c9f6b801a7a2 by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/LevyStochCalc.Poisson.Compensated.MarkStep.B--claude-auditor--2026-10-19T03_26_44Z.md`).
<!-- def-review: LevyStochCalc.Poisson.Compensated.MarkStep.B cd1a4d6799bbdd79ee01c9f6b801a7a2 by=claude-auditor -->
<!-- def-review: LevyStochCalc.Poisson.Compensated.MarkStep.ξ 0be3e10909ab07b6258c2d3d03a8b983 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/LevyStochCalc.Poisson.Compensated.MarkStep.ξ--claude-reviewer--2026-10-17T15_01_48Z.md`).
<!-- def-review: LevyStochCalc.Poisson.Compensated.MarkStep.ξ 0be3e10909ab07b6258c2d3d03a8b983 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/LevyStochCalc.Poisson.Compensated.MarkStep.ξ--claude-auditor--2026-10-19T03_27_23Z.md`).
<!-- def-review: LevyStochCalc.Poisson.Compensated.MarkStep.ξ 0be3e10909ab07b6258c2d3d03a8b983 by=claude-auditor -->
<!-- def-review: LevyStochCalc.Poisson.Compensated.MarkStep.mk 3c5a9069f74059b30000000000000000 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/LevyStochCalc.Poisson.Compensated.MarkStep.mk--claude-reviewer--2026-10-17T15_01_48Z.md`).
<!-- def-review: LevyStochCalc.Poisson.Compensated.MarkStep.mk 3c5a9069f74059b30000000000000000 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/LevyStochCalc.Poisson.Compensated.MarkStep.mk--claude-auditor--2026-10-19T03_27_23Z.md`).
<!-- def-review: LevyStochCalc.Poisson.Compensated.MarkStep.mk 3c5a9069f74059b30000000000000000 by=claude-auditor -->
* `MarkStep.Adapted ℱ G`: `ξ_{ik}` strongly `ℱ_{p_i}`-measurable for every piece `i < N₀` and mark
  set `k`: adaptedness at the left end of each piece.
<!-- def-review: LevyStochCalc.Poisson.Compensated.MarkStep.Adapted ecd786abe075b89b145b9c7361973099 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/LevyStochCalc.Poisson.Compensated.MarkStep.Adapted--claude-reviewer--2026-10-17T15_01_47Z.md`).
<!-- def-review: LevyStochCalc.Poisson.Compensated.MarkStep.Adapted ecd786abe075b89b145b9c7361973099 by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/LevyStochCalc.Poisson.Compensated.MarkStep.Adapted--claude-auditor--2026-10-19T03_26_44Z.md`).
<!-- def-review: LevyStochCalc.Poisson.Compensated.MarkStep.Adapted ecd786abe075b89b145b9c7361973099 by=claude-auditor -->
* `MarkStep.eval G s e ω = ∑_i 1_{(p_i, p_{i+1}]}(s) ∑_k ξ_{ik}(ω) 1_{B_k}(e)`: the integrand as a
  field.
<!-- def-review: LevyStochCalc.Poisson.Compensated.MarkStep.eval 29db58ad6d1eaba10f37be13a59482ea by=claude-author -->
Review by claude-reviewer: faithful (report `reports/LevyStochCalc.Poisson.Compensated.MarkStep.eval--claude-reviewer--2026-10-17T15_01_48Z.md`).
<!-- def-review: LevyStochCalc.Poisson.Compensated.MarkStep.eval 29db58ad6d1eaba10f37be13a59482ea by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/LevyStochCalc.Poisson.Compensated.MarkStep.eval--claude-auditor--2026-10-19T03_27_23Z.md`).
<!-- def-review: LevyStochCalc.Poisson.Compensated.MarkStep.eval 29db58ad6d1eaba10f37be13a59482ea by=claude-auditor -->
* `MarkStep.integral N G t ω = ∑_i ∑_k ξ_{ik}(ω) Ñ((p_i ∧ t, p_{i+1} ∧ t] × B_k)(ω)`: the elementary
  compensated integral up to `t`.
<!-- def-review: LevyStochCalc.Poisson.Compensated.MarkStep.integral 3186dcea8bb974d243fe79cd74ac17f2 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/LevyStochCalc.Poisson.Compensated.MarkStep.integral--claude-reviewer--2026-10-17T15_01_48Z.md`).
<!-- def-review: LevyStochCalc.Poisson.Compensated.MarkStep.integral 3186dcea8bb974d243fe79cd74ac17f2 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/LevyStochCalc.Poisson.Compensated.MarkStep.integral--claude-auditor--2026-10-19T03_27_23Z.md`).
<!-- def-review: LevyStochCalc.Poisson.Compensated.MarkStep.integral 3186dcea8bb974d243fe79cd74ac17f2 by=claude-auditor -->
* `Poisson.Compensated.stageHorizon n = 2ⁿ`: the horizon of stage `n`.
<!-- def-review: LevyStochCalc.Poisson.Compensated.stageHorizon c8740e4d49db17c3a53710c3133d9af0 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/LevyStochCalc.Poisson.Compensated.stageHorizon--claude-reviewer--2026-10-17T15_16_41Z.md`).
<!-- def-review: LevyStochCalc.Poisson.Compensated.stageHorizon c8740e4d49db17c3a53710c3133d9af0 by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/LevyStochCalc.Poisson.Compensated.stageHorizon--claude-auditor--2026-10-19T03_27_24Z.md`).
<!-- def-review: LevyStochCalc.Poisson.Compensated.stageHorizon c8740e4d49db17c3a53710c3133d9af0 by=claude-auditor -->
* `Poisson.Compensated.stageErr φ P n G = 𝔼 ∫_{[0, 2ⁿ]} ∫_E |φ − G.eval|² dν ds`: the energy
  distance of a step integrand to `φ` on the horizon of stage `n`.
<!-- def-review: LevyStochCalc.Poisson.Compensated.stageErr b9fbd75c3a71823527cf969f16cf7a60 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/LevyStochCalc.Poisson.Compensated.stageErr--claude-reviewer--2026-10-17T15_16_41Z.md`).
<!-- def-review: LevyStochCalc.Poisson.Compensated.stageErr b9fbd75c3a71823527cf969f16cf7a60 by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/LevyStochCalc.Poisson.Compensated.stageErr--claude-auditor--2026-10-19T03_27_24Z.md`).
<!-- def-review: LevyStochCalc.Poisson.Compensated.stageErr b9fbd75c3a71823527cf969f16cf7a60 by=claude-auditor -->
* `Poisson.Compensated.master N ℱ φ … n`: a chosen pair of a dyadic level `ℓ_n` and an adapted step
  integrand on the dyadic grid of level `ℓ_n` of `[0, 2ⁿ]`, within `1/(n + 1)` of `φ` in energy
  (`master_adapted`, `master_err`), the levels increasing (`master_level_succ`); `master._f` and
  `master.match_1` are the auxiliary declarations Lean generates for this recursion on `n`, with no
  content of their own. The choice does not affect the limit.
<!-- def-review: LevyStochCalc.Poisson.Compensated.master fe975a59e5bdb39048afe361b1d43cfe by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/LevyStochCalc.Poisson.Compensated.master--claude-reviewer--2026-10-17T15_16_41Z.md`).
<!-- def-review: LevyStochCalc.Poisson.Compensated.master fe975a59e5bdb39048afe361b1d43cfe by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/LevyStochCalc.Poisson.Compensated.master--claude-auditor--2026-10-19T03_27_24Z.md`).
<!-- def-review: LevyStochCalc.Poisson.Compensated.master fe975a59e5bdb39048afe361b1d43cfe by=claude-auditor -->
<!-- def-review: LevyStochCalc.Poisson.Compensated.master._f 424be9f1c393f5ccd609f8b82c95bb19 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/LevyStochCalc.Poisson.Compensated.master._f--claude-reviewer--2026-10-17T15_16_41Z.md`).
<!-- def-review: LevyStochCalc.Poisson.Compensated.master._f 424be9f1c393f5ccd609f8b82c95bb19 by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/LevyStochCalc.Poisson.Compensated.master._f--claude-auditor--2026-10-19T03_27_24Z.md`).
<!-- def-review: LevyStochCalc.Poisson.Compensated.master._f 424be9f1c393f5ccd609f8b82c95bb19 by=claude-auditor -->
<!-- def-review: LevyStochCalc.Poisson.Compensated.master.match_1 39be9c3f3ff3768c322be17b50fb7b55 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/LevyStochCalc.Poisson.Compensated.master.match_1--claude-reviewer--2026-10-17T15_16_41Z.md`).
<!-- def-review: LevyStochCalc.Poisson.Compensated.master.match_1 39be9c3f3ff3768c322be17b50fb7b55 by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/LevyStochCalc.Poisson.Compensated.master.match_1--claude-auditor--2026-10-19T03_27_24Z.md`).
<!-- def-review: LevyStochCalc.Poisson.Compensated.master.match_1 39be9c3f3ff3768c322be17b50fb7b55 by=claude-auditor -->
* `Poisson.Compensated.stageIntegral … n t = (master n).integral N t`: the integral of the stage-`n`
  approximant up to `t`.
<!-- def-review: LevyStochCalc.Poisson.Compensated.stageIntegral 684f75cf6cc2aa0c47441d48e213f8c3 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/LevyStochCalc.Poisson.Compensated.stageIntegral--claude-reviewer--2026-10-17T15_16_41Z.md`).
<!-- def-review: LevyStochCalc.Poisson.Compensated.stageIntegral 684f75cf6cc2aa0c47441d48e213f8c3 by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/LevyStochCalc.Poisson.Compensated.stageIntegral--claude-auditor--2026-10-19T03_27_25Z.md`).
<!-- def-review: LevyStochCalc.Poisson.Compensated.stageIntegral 684f75cf6cc2aa0c47441d48e213f8c3 by=claude-auditor -->
* `Poisson.Compensated.stageLp … t n`: its class in `L²(P)`.
<!-- def-review: LevyStochCalc.Poisson.Compensated.stageLp 3b161903923f1566d14a46b6c0b141a8 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/LevyStochCalc.Poisson.Compensated.stageLp--claude-reviewer--2026-10-17T15_16_41Z.md`).
<!-- def-review: LevyStochCalc.Poisson.Compensated.stageLp 3b161903923f1566d14a46b6c0b141a8 by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/LevyStochCalc.Poisson.Compensated.stageLp--claude-auditor--2026-10-19T03_27_25Z.md`).
<!-- def-review: LevyStochCalc.Poisson.Compensated.stageLp 3b161903923f1566d14a46b6c0b141a8 by=claude-auditor -->
* `Poisson.Compensated.processLp … t`: the limit in `L²(P)` (`limUnder`) of `stageLp … t n`, a
  Cauchy sequence at every `t` (`stageLp_cauchySeq`), so never the junk value of `limUnder`:
  `∫_0^t ∫_E φ dÑ` as an element of `L²(P)`.
<!-- def-review: LevyStochCalc.Poisson.Compensated.processLp f8fb86e34b629e10db696374a7fa3068 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/LevyStochCalc.Poisson.Compensated.processLp--claude-reviewer--2026-10-17T15_16_41Z.md`).
<!-- def-review: LevyStochCalc.Poisson.Compensated.processLp f8fb86e34b629e10db696374a7fa3068 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/LevyStochCalc.Poisson.Compensated.processLp--claude-auditor--2026-10-19T03_27_24Z.md`).
<!-- def-review: LevyStochCalc.Poisson.Compensated.processLp f8fb86e34b629e10db696374a7fa3068 by=claude-auditor -->
* `Poisson.Compensated.process … t`: an `ℱ_t`-measurable function in that class, chosen at each time
  separately.
<!-- def-review: LevyStochCalc.Poisson.Compensated.process 0f01c66ebd3c9ea130e0117d5d2cc43b by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/LevyStochCalc.Poisson.Compensated.process--claude-reviewer--2026-10-17T15_16_41Z.md`).
<!-- def-review: LevyStochCalc.Poisson.Compensated.process 0f01c66ebd3c9ea130e0117d5d2cc43b by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/LevyStochCalc.Poisson.Compensated.process--claude-auditor--2026-10-19T03_27_24Z.md`).
<!-- def-review: LevyStochCalc.Poisson.Compensated.process 0f01c66ebd3c9ea130e0117d5d2cc43b by=claude-auditor -->
* `Poisson.Compensated.stochasticIntegral N ℱ hℱ φ … T`: the value at `T` of a chosen modification
  of `process` that is adapted to `ℱ₊` and has almost surely càdlàg paths
  (`exists_cadlag_modification`): the compensated Poisson integral `∫_0^T ∫_E φ(s, e) Ñ(ds, de)`,
  for `φ` jointly measurable, marked progressive and of finite marked energy on every horizon.
  Choices: the version is càdlàg and adapted to the right-continuous version `ℱ₊`, which is `ℱ` for
  the right-continuous filtrations of the statements (`enlJoint`); the integrand is marked
  progressive rather than `𝒫 ⊗ ℰ`-measurable, and for a `𝒫 ⊗ ℰ`-measurable integrand the integral is
  the paper's.
<!-- def-review: LevyStochCalc.Poisson.Compensated.stochasticIntegral 0f01c66ebd3c9ea16c0e39e9314f702b by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/LevyStochCalc.Poisson.Compensated.stochasticIntegral--claude-reviewer--2026-10-17T15_16_41Z.md`).
<!-- def-review: LevyStochCalc.Poisson.Compensated.stochasticIntegral 0f01c66ebd3c9ea16c0e39e9314f702b by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/LevyStochCalc.Poisson.Compensated.stochasticIntegral--claude-auditor--2026-10-19T03_27_25Z.md`).
<!-- def-review: LevyStochCalc.Poisson.Compensated.stochasticIntegral 0f01c66ebd3c9ea16c0e39e9314f702b by=claude-auditor -->

Verdict: faithful with representation choices; `MarkStep` (with its constructor `.mk`) broader, the
paper's simple predictable integrands being its instances with `MarkStep.Adapted`, the form in which
it is used (`master_adapted`).

## Laws with the Wasserstein topology and the `L²(ν)` representative

Manuscript (§2): `P₂(H)` and `P₂(ℝⁿ)` are metric spaces under `W₂`, `H` with its Hilbert norm; the
coefficients are Borel on them ((2.3) for `h`), and the Fubini isometry (2.4) supplies jointly
measurable representatives of `L²(ν)`-valued integrands.

* `Law.P2W E`: the type `P2 E` of the laws of finite second moment, carrying the 2-Wasserstein
  distance `w2P`, its topology and the Borel σ-algebra of that topology; a type synonym, so that
  this σ-algebra and the evaluation σ-algebra of `P2 E` stay apart.
<!-- def-review: MVFBSDEJ.Law.P2W d98c9fdcb435191872f24816c5ace010 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/Dissertation.Law.P2W--claude-reviewer--2026-10-17T15_50_56Z.md`).
<!-- def-review: MVFBSDEJ.Law.P2W d98c9fdcb435191872f24816c5ace010 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.Law.P2W--claude-auditor--2026-10-19T03_27_45Z.md`).
<!-- def-review: MVFBSDEJ.Law.P2W d98c9fdcb435191872f24816c5ace010 by=claude-auditor -->
* `Law.P2.toP2W`: the identity map from `P2 E` to `P2W E`.
<!-- def-review: MVFBSDEJ.Law.P2.toP2W 6364ddbc2460c93ce43fdfac1320068b by=claude-author -->
Review by claude-reviewer: faithful (report `reports/Dissertation.Law.P2.toP2W--claude-reviewer--2026-10-17T15_50_56Z.md`).
<!-- def-review: MVFBSDEJ.Law.P2.toP2W 6364ddbc2460c93ce43fdfac1320068b by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/Dissertation.Law.P2.toP2W--claude-auditor--2026-10-19T03_27_45Z.md`).
<!-- def-review: MVFBSDEJ.Law.P2.toP2W 6364ddbc2460c93ce43fdfac1320068b by=claude-auditor -->
* `Law.P2W.toP2`: the identity map back.
<!-- def-review: MVFBSDEJ.Law.P2W.toP2 aa48515eb706b87c558e415eccf852f1 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/Dissertation.Law.P2W.toP2--claude-reviewer--2026-10-17T15_50_56Z.md`).
<!-- def-review: MVFBSDEJ.Law.P2W.toP2 aa48515eb706b87c558e415eccf852f1 by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/Dissertation.Law.P2W.toP2--claude-auditor--2026-10-19T03_27_45Z.md`).
<!-- def-review: MVFBSDEJ.Law.P2W.toP2 aa48515eb706b87c558e415eccf852f1 by=claude-auditor -->
* `Law.P2W.instPseudoMetricSpace`: the distance `w2P` on `P2W E`, for `E` complete, Borel and second
  countable: the paper's `(P₂(E), W₂)`. It is recorded as a pseudometric, the separation of `W₂`
  (vanishing only on equal laws) not being used; the topology is the `W₂` topology all the same.
<!-- def-review: MVFBSDEJ.Law.P2W.instPseudoMetricSpace deb697e07b323d68c07f1938ba527f40 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.Law.P2W.instPseudoMetricSpace--claude-reviewer--2026-10-17T15_50_56Z.md`).
<!-- def-review: MVFBSDEJ.Law.P2W.instPseudoMetricSpace deb697e07b323d68c07f1938ba527f40 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.Law.P2W.instPseudoMetricSpace--claude-auditor--2026-10-19T03_27_45Z.md`).
<!-- def-review: MVFBSDEJ.Law.P2W.instPseudoMetricSpace deb697e07b323d68c07f1938ba527f40 by=claude-auditor -->
* `Law.P2.mapOfLe μ hφ hc`: the image law `φ_# μ` for `φ` measurable with `‖φ x‖ ≤ c ‖x‖`, an
  element of `P₂(F)`, its second moment being at most `c²` times that of `μ`.
<!-- def-review: MVFBSDEJ.Law.P2.mapOfLe a3027fda85c8a68e15b12b295b9c5b34 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/Dissertation.Law.P2.mapOfLe--claude-reviewer--2026-10-17T12_07_47Z.md`).
<!-- def-review: MVFBSDEJ.Law.P2.mapOfLe a3027fda85c8a68e15b12b295b9c5b34 by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/Dissertation.Law.P2.mapOfLe--claude-auditor--2026-10-19T03_27_45Z.md`).
<!-- def-review: MVFBSDEJ.Law.P2.mapOfLe a3027fda85c8a68e15b12b295b9c5b34 by=claude-auditor -->
* `System.lawToL2 μ = toL2_# μ`: a law on the tuple space carried to the same set with the Hilbert
  norm (`TupleL2`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.lawToL2 cd26c5371a931d00b9d2620e4a601586 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/Dissertation.WellPosedness.System.lawToL2--claude-reviewer--2026-10-17T15_06_18Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.lawToL2 cd26c5371a931d00b9d2620e4a601586 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.lawToL2--claude-auditor--2026-10-19T03_27_24Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.lawToL2 cd26c5371a931d00b9d2620e4a601586 by=claude-auditor -->
* `System.P2WH HX HY HZY HUY`: the laws of finite second moment on the tuple space, carrying the
  2-Wasserstein distance of the Hilbert norm and the Borel σ-algebra of its topology; a type synonym
  of `P2 (Tuple HX HY HZY HUY)`, kept apart from its evaluation σ-algebra as `P2W` is.
<!-- def-review: MVFBSDEJ.WellPosedness.System.P2WH 8b570604f2bfe77fd02ea1946ed372f6 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.P2WH--claude-reviewer--2026-10-17T15_50_57Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.P2WH 8b570604f2bfe77fd02ea1946ed372f6 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.P2WH--claude-auditor--2026-10-19T03_27_23Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.P2WH 8b570604f2bfe77fd02ea1946ed372f6 by=claude-auditor -->
* `System.P2WH.toP2`: the identity map back to `P2 (Tuple HX HY HZY HUY)`.
<!-- def-review: MVFBSDEJ.WellPosedness.System.P2WH.toP2 5dd79877dc9f47e46540cd4157bdedf5 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/Dissertation.WellPosedness.System.P2WH.toP2--claude-reviewer--2026-10-17T16_00_14Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.P2WH.toP2 5dd79877dc9f47e46540cd4157bdedf5 by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/Dissertation.WellPosedness.System.P2WH.toP2--claude-auditor--2026-10-19T03_27_23Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.P2WH.toP2 5dd79877dc9f47e46540cd4157bdedf5 by=claude-auditor -->
* `System.P2WH.instPseudoMetricSpace`: the pseudometric induced by `μ ↦ (lawToL2 μ).toP2W`, whose
  distance is `w2H` (`P2WH.dist_toP2WH`): `P₂(H)` with the paper's `W₂`.
<!-- def-review: MVFBSDEJ.WellPosedness.System.P2WH.instPseudoMetricSpace e0b05718e48c06230c179aa7e26ebdeb by=claude-author -->
Review by claude-reviewer: faithful (report `reports/Dissertation.WellPosedness.System.P2WH.instPseudoMetricSpace--claude-reviewer--2026-10-17T12_39_50Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.P2WH.instPseudoMetricSpace e0b05718e48c06230c179aa7e26ebdeb by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.P2WH.instPseudoMetricSpace--claude-auditor--2026-10-19T03_27_23Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.P2WH.instPseudoMetricSpace e0b05718e48c06230c179aa7e26ebdeb by=claude-auditor -->
* `System.TupleP2WH ν n m d`: `P2WH` for the channels `ℝⁿ`, `ℝᵐ`, `ℝ^{m×d}` and `L²(ν; ℝᵐ)`: the
  paper's `(P₂(H), W₂)`.
<!-- def-review: MVFBSDEJ.WellPosedness.System.TupleP2WH 18ca34ab14491b05ceae08abe9f47d1f by=claude-author -->
Review by claude-reviewer: faithful (report `reports/Dissertation.WellPosedness.System.TupleP2WH--claude-reviewer--2026-10-17T15_06_17Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.TupleP2WH 18ca34ab14491b05ceae08abe9f47d1f by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.TupleP2WH--claude-auditor--2026-10-19T03_27_24Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.TupleP2WH 18ca34ab14491b05ceae08abe9f47d1f by=claude-auditor -->
* `Law.lpRep ν V`: for a separable `L²(ν; V)`, a chosen `Φ : L²(ν; V) × E → V`, strongly measurable
  for the Borel σ-algebra of `L²(ν; V)`, with `Φ(u, ·) = u` `ν`-almost everywhere for every `u` and
  `Φ(0, ·) = 0`: a jointly measurable choice of representatives, by which a measurable
  `L²(ν)`-valued process is read as a measurable function of `(ω, s, e)`, as (2.4) does. It is
  defined only when `L²(ν; V)` is separable, the paper's setting, so it has no junk value; the
  statements use only the two properties above, so the choice does not matter.
<!-- def-review: MVFBSDEJ.Law.lpRep 4d8f19766d30be6bf897d6959240d0e7 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.Law.lpRep--claude-reviewer--2026-10-17T12_13_10Z.md`).
<!-- def-review: MVFBSDEJ.Law.lpRep 4d8f19766d30be6bf897d6959240d0e7 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.Law.lpRep--claude-auditor--2026-10-19T03_34_13Z.md`).
<!-- def-review: MVFBSDEJ.Law.lpRep 4d8f19766d30be6bf897d6959240d0e7 by=claude-auditor -->

Verdict: faithful with representation choices.

## The coefficients, the tuple and the coupling matrix (`MVFBSDEJ/WellPosedness/System/`)

Manuscript (§2): `b, σ, h, f` map `[0, T] × H × P₂(H)` to `ℝⁿ`, `ℝ^{n×d}`, `L²(ν; ℝⁿ)` and `ℝᵐ`, and
`g` maps `ℝⁿ × P₂(ℝⁿ)` to `ℝᵐ`; `Θ_t = (X_t, Y_t, Z_t, U_t)` and
`Θ⁻_t = (X_{t−}, Y_{t−}, Z_t, U_t)`; `𝒟_t` is the diagonal of Definition 2.1; `G ∈ ℝ^{m×n}` acts on
the channels, and `s_min(G)` is its smallest singular value (Assumption 2.4).

* `System.Coeffs ν n m d`, with projections `b`, `σ`, `h`, `f`, `g` and constructor `.mk`: the five
  coefficient functions with the printed signatures, `σ` valued in
  `EuclideanSpace ℝ (Fin n × Fin d)` (whose norm is the Frobenius norm), `h` in `L²(ν; ℝⁿ)`, the law
  argument in `P2 (TupleH ν n m d)`, and `g` a function of a point of `ℝⁿ` and a law of `P₂(ℝⁿ)`.
  Choices: time ranges over `ℝ`, of which only `[0, T]` enters the statements; no measurability is
  part of the structure, (2.3) being `JointBorel`, assumed where the paper assumes it. The
  projections are the five coefficients and the constructor takes them.
<!-- def-review: MVFBSDEJ.WellPosedness.System.Coeffs fd49e3c7112f41550000000000000000 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.Coeffs--claude-reviewer--2026-10-17T15_50_55Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.Coeffs fd49e3c7112f41550000000000000000 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.Coeffs--claude-auditor--2026-10-19T03_26_58Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.Coeffs fd49e3c7112f41550000000000000000 by=claude-auditor -->
<!-- def-review: MVFBSDEJ.WellPosedness.System.Coeffs.b bc08e9996ff84737d8975b81de3fa439 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.Coeffs.b--claude-reviewer--2026-10-17T15_50_56Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.Coeffs.b bc08e9996ff84737d8975b81de3fa439 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.Coeffs.b--claude-auditor--2026-10-19T03_26_58Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.Coeffs.b bc08e9996ff84737d8975b81de3fa439 by=claude-auditor -->
<!-- def-review: MVFBSDEJ.WellPosedness.System.Coeffs.σ 9ce740f2b9edaee531a774987db0342b by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.Coeffs.σ--claude-reviewer--2026-10-17T15_50_56Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.Coeffs.σ 9ce740f2b9edaee531a774987db0342b by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.Coeffs.σ--claude-auditor--2026-10-19T03_26_58Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.Coeffs.σ 9ce740f2b9edaee531a774987db0342b by=claude-auditor -->
<!-- def-review: MVFBSDEJ.WellPosedness.System.Coeffs.h 789edd1ca0ce74d33c81453fc8e552a4 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.Coeffs.h--claude-reviewer--2026-10-17T15_50_57Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.Coeffs.h 789edd1ca0ce74d33c81453fc8e552a4 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.Coeffs.h--claude-auditor--2026-10-19T03_26_58Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.Coeffs.h 789edd1ca0ce74d33c81453fc8e552a4 by=claude-auditor -->
<!-- def-review: MVFBSDEJ.WellPosedness.System.Coeffs.f c6dd01bda978de4685de4003d1087973 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.Coeffs.f--claude-reviewer--2026-10-17T15_50_56Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.Coeffs.f c6dd01bda978de4685de4003d1087973 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.Coeffs.f--claude-auditor--2026-10-19T03_26_58Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.Coeffs.f c6dd01bda978de4685de4003d1087973 by=claude-auditor -->
<!-- def-review: MVFBSDEJ.WellPosedness.System.Coeffs.g e49c4b30976b5706c3a3b861d7256ce0 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/Dissertation.WellPosedness.System.Coeffs.g--claude-reviewer--2026-10-17T15_50_56Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.Coeffs.g e49c4b30976b5706c3a3b861d7256ce0 by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/Dissertation.WellPosedness.System.Coeffs.g--claude-auditor--2026-10-19T03_26_58Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.Coeffs.g e49c4b30976b5706c3a3b861d7256ce0 by=claude-auditor -->
<!-- def-review: MVFBSDEJ.WellPosedness.System.Coeffs.mk 04e3837a08a0193e0000000000000000 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.Coeffs.mk--claude-reviewer--2026-10-17T15_59_56Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.Coeffs.mk 04e3837a08a0193e0000000000000000 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.Coeffs.mk--claude-auditor--2026-10-19T03_26_58Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.Coeffs.mk 04e3837a08a0193e0000000000000000 by=claude-auditor -->
* `System.uLift ν u`: the `L²(ν)` class of a mark-indexed vector `e ↦ u(e) ∈ ℝ^ι` when it is square
  integrable (and almost everywhere strongly measurable), and `0` otherwise, a junk value that a
  tuple of finite marked energy meets only on a `dt ⊗ dP`-null set of `(s, ω)`.
<!-- def-review: MVFBSDEJ.WellPosedness.System.uLift 20342aeccd26489f2122117451a2a160 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.uLift--claude-reviewer--2026-10-17T15_01_51Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.uLift 20342aeccd26489f2122117451a2a160 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.uLift--claude-auditor--2026-10-19T03_27_25Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.uLift 20342aeccd26489f2122117451a2a160 by=claude-auditor -->
* `System.tupleAt ν X Y Z U s ω = (X_s(ω), Y_s(ω), Z_s(ω), U_s(ω, ·))`: `Θ_s(ω)` read from the
  coordinate processes, the rows `Z_{k,s}(ω)` forming the `m × d` channel and the jump channel the
  class `uLift` of `e ↦ (U_{k,s}(ω, e))_k`.
<!-- def-review: MVFBSDEJ.WellPosedness.System.tupleAt 5c7223a86c8e2dcd94922741f04aaf78 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.tupleAt--claude-reviewer--2026-10-17T15_01_50Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.tupleAt 5c7223a86c8e2dcd94922741f04aaf78 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.tupleAt--claude-auditor--2026-10-19T03_27_25Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.tupleAt 5c7223a86c8e2dcd94922741f04aaf78 by=claude-auditor -->
* `System.leftLimProc X i s ω = Function.leftLim (r ↦ X_i(r, ω)) s`: the left limit `X_{s−}(ω)`.
  Where the path has no left limit, Mathlib's `leftLim` returns `X_s(ω)`, a value the statements
  reach only on the null set of paths without left limits, the solution notions asking left limits
  almost surely. With it, `tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s` is `Θ⁻_s`.
<!-- def-review: MVFBSDEJ.WellPosedness.System.leftLimProc 9171262935c3b1fde4f555261cd0b9ba by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.leftLimProc--claude-reviewer--2026-10-17T15_06_18Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.leftLimProc 9171262935c3b1fde4f555261cd0b9ba by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.leftLimProc--claude-auditor--2026-10-19T03_27_24Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.leftLimProc 9171262935c3b1fde4f555261cd0b9ba by=claude-auditor -->
* `System.diagonalInputs ν n m d ℱ P t`: the pairs `(Θ, μ)` with `Θ : Ω → H` strongly
  `ℱ_t`-measurable and square integrable and `μ = lawP2 P Θ`: `𝒟_t` of Definition 2.1, an element of
  `L²(Ω, ℱ_t; H)` being represented by a function in its class, which loses no class.
<!-- def-review: MVFBSDEJ.WellPosedness.System.diagonalInputs fcf89264f7b3c575afbaf0b8c6eade06 by=claude-author source=A:def:diag@952765bd095132205c2a2ed30a292f5a88840f96e56d5a877f906f6a21524a94 -->
Review by claude-reviewer: faithful (report `reports/Dissertation.WellPosedness.System.diagonalInputs--claude-reviewer--2026-10-17T15_06_18Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.diagonalInputs fcf89264f7b3c575afbaf0b8c6eade06 by=claude-reviewer source=A:def:diag@952765bd095132205c2a2ed30a292f5a88840f96e56d5a877f906f6a21524a94 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.diagonalInputs--claude-auditor--2026-10-19T03_27_24Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.diagonalInputs fcf89264f7b3c575afbaf0b8c6eade06 by=claude-auditor source=A:def:diag@952765bd095132205c2a2ed30a292f5a88840f96e56d5a877f906f6a21524a94 -->
* `System.GX G`: `x ↦ G x`, `ℝⁿ → ℝᵐ`, as a continuous linear map; `GX Gᵀ` is the adjoint, the
  paper's `Gᵀ` (`adjoint_GX`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.GX 63e2a9453a1500d8567ae4e516472ab8 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/Dissertation.WellPosedness.System.GX--claude-reviewer--2026-10-17T15_50_56Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.GX 63e2a9453a1500d8567ae4e516472ab8 by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/Dissertation.WellPosedness.System.GX--claude-auditor--2026-10-19T03_26_59Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.GX 63e2a9453a1500d8567ae4e516472ab8 by=claude-auditor -->
* `System.GZ G`: `σ ↦ G σ` column by column, `ℝ^{n×d} → ℝ^{m×d}`, the Kronecker product `G ⊗ I_d` in
  the coordinates `(i, j)`: the action of `G` on the matrix channel.
<!-- def-review: MVFBSDEJ.WellPosedness.System.GZ c2eb31a2cb944229321c531fa6d8a32a by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.GZ--claude-reviewer--2026-10-17T15_50_56Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.GZ c2eb31a2cb944229321c531fa6d8a32a by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.GZ--claude-auditor--2026-10-19T03_27_23Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.GZ c2eb31a2cb944229321c531fa6d8a32a by=claude-auditor -->
* `System.GU G ν`: `u ↦ (e ↦ G u(e))`, `L²(ν; ℝⁿ) → L²(ν; ℝᵐ)` (`compLpL`): the action of `G` on the
  jump channel, mark by mark almost everywhere (`coeFn_GU`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.GU af77e6209c5a6f021476723ff9b94c95 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.GU--claude-reviewer--2026-10-17T15_50_56Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.GU af77e6209c5a6f021476723ff9b94c95 by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/Dissertation.WellPosedness.System.GU--claude-auditor--2026-10-19T03_26_59Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.GU af77e6209c5a6f021476723ff9b94c95 by=claude-auditor -->
* `System.sMin G`: the square root of the least eigenvalue of `Gᵀ G` when `n ≤ m` and of `G Gᵀ` when
  `m < n`: the smallest singular value `s_min(G)`. When the matrix whose eigenvalues are taken is
  empty (`n = 0`, or `m = 0 < n`) the infimum is Lean's `0`, outside the paper's `n, m ≥ 1`.
<!-- def-review: MVFBSDEJ.WellPosedness.System.sMin 42b2e53d2f710588e25de988c32456ea by=claude-author -->
Review by claude-reviewer: faithful (report `reports/Dissertation.WellPosedness.System.sMin--claude-reviewer--2026-10-17T15_01_50Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.sMin 42b2e53d2f710588e25de988c32456ea by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/Dissertation.WellPosedness.System.sMin--claude-auditor--2026-10-19T03_27_24Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.sMin 42b2e53d2f710588e25de988c32456ea by=claude-auditor -->

Verdict: faithful with representation choices.

## Coefficient processes and sizes

Manuscript (§2–§4): along a tuple, `ψ(s, Θ_s, μ_s)` for `ψ ∈ {b, σ, f}`, the jump coefficient at
`(Θ⁻_s, μ⁻_s)`, the terminal value `g(X_T, Law(X_T))`; the norm of `ℍ` (§3) and the right sides of
(3.1) and (4.14).

* `System.driftProc P T C X Y Z U i ω s`: coordinate `i` of `b(s, Θ_s(ω), μ_s)` for `s ∈ [0, T]` and
  `0` off `[0, T]`, with `Θ_s = tupleAt ν X Y Z U s` and `μ_s = lawP2 P Θ_s`. Choices: the cut-off
  to `[0, T]`, outside of which (1.1) uses no value; `μ_s` is the law at every time, where the paper
  takes the Borel representative of Lemma A.1, which agrees with it for almost every `s`; where
  `Θ_s ∉ L²` the law is the junk `δ₀` of `lawP2`, on a `ds`-null set for the tuples of the
  statements.
<!-- def-review: MVFBSDEJ.WellPosedness.System.driftProc fb883e117d3ab2fe2788affb6a069047 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.driftProc--claude-reviewer--2026-10-17T15_06_18Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.driftProc fb883e117d3ab2fe2788affb6a069047 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.driftProc--claude-auditor--2026-10-19T03_27_24Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.driftProc fb883e117d3ab2fe2788affb6a069047 by=claude-auditor -->
* `System.diffusionProc P T C X Y Z U i s ω j`: entry `(i, j)` of `σ(s, Θ_s(ω), μ_s)`, with the same
  choices.
<!-- def-review: MVFBSDEJ.WellPosedness.System.diffusionProc 2b164a230bfa865bab8693203c4b1ee8 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.diffusionProc--claude-reviewer--2026-10-17T15_06_18Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.diffusionProc 2b164a230bfa865bab8693203c4b1ee8 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.diffusionProc--claude-auditor--2026-10-19T03_27_24Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.diffusionProc 2b164a230bfa865bab8693203c4b1ee8 by=claude-auditor -->
* `System.driverProc P T C X Y Z U k ω s`: coordinate `k` of `f(s, Θ_s(ω), μ_s)`, with the same
  choices.
<!-- def-review: MVFBSDEJ.WellPosedness.System.driverProc 73a119504de32e3e6e17c4225604f734 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.driverProc--claude-reviewer--2026-10-17T15_06_18Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.driverProc 73a119504de32e3e6e17c4225604f734 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.driverProc--claude-auditor--2026-10-19T03_27_24Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.driverProc 73a119504de32e3e6e17c4225604f734 by=claude-auditor -->
* `System.terminalVal P T C X k ω`: coordinate `k` of `g(X_T(ω), lawP2 P X_T)`, the paper's
  `g(X_T, Law(X_T))` for `X_T ∈ L²`, which the solution notions ask.
<!-- def-review: MVFBSDEJ.WellPosedness.System.terminalVal 0c1ad34f7c8c5cdbe0cc1f1dfea8adf8 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.terminalVal--claude-reviewer--2026-10-17T15_01_50Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.terminalVal 0c1ad34f7c8c5cdbe0cc1f1dfea8adf8 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.terminalVal--claude-auditor--2026-10-19T03_27_25Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.terminalVal 0c1ad34f7c8c5cdbe0cc1f1dfea8adf8 by=claude-auditor -->
* `System.jumpProc T γ i s ω e = 1_{[0, T]}(s) γ_i(s, ω, e)`: a representative `γ` of the jump
  coefficient, cut to `[0, T]`.
<!-- def-review: MVFBSDEJ.WellPosedness.System.jumpProc bfa4317d32adaf7b2cab0921e18838d1 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.jumpProc--claude-reviewer--2026-10-17T15_50_56Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.jumpProc bfa4317d32adaf7b2cab0921e18838d1 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.jumpProc--claude-auditor--2026-10-19T03_27_24Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.jumpProc bfa4317d32adaf7b2cab0921e18838d1 by=claude-auditor -->
* `Existence.coeffJump P T C X Y Z U i s ω e`: coordinate `i` of
  `lpRep (1_{[0, T]}(s) h(s, Θ_s(ω), μ_s), e)`, with `Θ_s` and `μ_s` taken from the tuple
  `(X, Y, Z, U)` it is given: a jointly measurable representative of the jump coefficient along that
  tuple at every `s ∈ [0, T]` (`coeffJump_ae_eq`), `0` off `[0, T]`. The definition is generic in
  the tuple; every statement passes it the left limits, `coeffJump P T C (leftLimProc X)
  (leftLimProc Y) Z U`, so it is evaluated at `Θ⁻_s` and `μ⁻_s = Law(Θ⁻_s)`, as (3.1) prescribes for
  `δh`.
<!-- def-review: MVFBSDEJ.WellPosedness.Existence.coeffJump 18400ae9b3362bfb78e13212c01211ec by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.Existence.coeffJump--claude-reviewer--2026-10-17T15_04_37Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Existence.coeffJump 18400ae9b3362bfb78e13212c01211ec by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.Existence.coeffJump--claude-auditor--2026-10-19T03_34_13Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Existence.coeffJump 18400ae9b3362bfb78e13212c01211ec by=claude-auditor -->
* `Stability.esq x = ∑_i x_i²` in `[0, ∞]`: the squared Euclidean norm of a coordinate vector.
<!-- def-review: MVFBSDEJ.WellPosedness.Stability.esq 6cf496fa6f75fac11490c95295dbf617 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/Dissertation.WellPosedness.Stability.esq--claude-reviewer--2026-10-17T15_50_55Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Stability.esq 6cf496fa6f75fac11490c95295dbf617 by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/Dissertation.WellPosedness.Stability.esq--claude-auditor--2026-10-19T03_26_58Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Stability.esq 6cf496fa6f75fac11490c95295dbf617 by=claude-auditor -->
* `Stability.supSize P ν T X Y Z U`: `𝔼 sup_{[0, T]} |X|² + 𝔼 sup_{[0, T]} |Y|²` plus the energies
  of the entries of `Z` and the marked energies of the coordinates of `U`, in `[0, ∞]`: `‖Θ‖²_ℍ` of
  §3, the left side of (3.1) and (4.14) for a difference. Choices: the value lies in `[0, ∞]`, so no
  integrability is presupposed, and the supremum over the uncountable `[0, T]` sits inside a lower
  integral, which needs no measurability.
<!-- def-review: MVFBSDEJ.WellPosedness.Stability.supSize 8d946a220ee9b35c64d6f1cdebece750 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.Stability.supSize--claude-reviewer--2026-10-17T12_33_20Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Stability.supSize 8d946a220ee9b35c64d6f1cdebece750 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.Stability.supSize--claude-auditor--2026-10-19T03_36_10Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Stability.supSize 8d946a220ee9b35c64d6f1cdebece750 by=claude-auditor -->
* `Stability.dataSize P ν T ξ₀ qb qσ qh qf qg = 𝔼|ξ₀|² + 𝔼|q^g|² + 𝔼 ∫_0^T (|q^b|² + |q^σ|²_F +
  ‖q^h‖²_{L²(ν)} + |q^f|²) dt` in `[0, ∞]`, the `L²(ν; ℝⁿ)` norm of `q^h` as the sum of the marked
  energies of its coordinates: the bracket on the right of (3.1) and of (4.14).
<!-- def-review: MVFBSDEJ.WellPosedness.Stability.dataSize f5b22d1ca3f4de883c0845083e402eae by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.Stability.dataSize--claude-reviewer--2026-10-17T12_32_21Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Stability.dataSize f5b22d1ca3f4de883c0845083e402eae by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/Dissertation.WellPosedness.Stability.dataSize--claude-auditor--2026-10-19T03_34_13Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Stability.dataSize f5b22d1ca3f4de883c0845083e402eae by=claude-auditor -->

Verdict: faithful with representation choices.

## Assumptions 2.2–2.5 and (2.3) (`MVFBSDEJ/WellPosedness/Spec/Assumptions.lean`)

Manuscript (§2): the coefficients are jointly Borel, `h` through (2.3); Assumption 2.2
(`ξ₀ ∈ L²(Ω, ℱ₀; ℝⁿ)` and the origin values in `L²(0, T)`), Assumption 2.3 (the interior bound along
`𝒟_t` and (2.6)) and Assumption 2.5 (the terminal inequality, (2.7) and the conditions on
`α, β₁, β₂`).

* `Spec.JointBorel T C`, with constructor `.mk`: each `(t, θ, μ) ↦ ψ(t, θ, μ)`, `ψ ∈ {b, σ, h, f}`,
  is measurable from the Borel σ-algebra of the product topology on `[0, T] × H × P₂(H)`, `P₂(H)`
  with the Hilbert-norm `W₂` (`TupleP2WH`), to the Borel σ-algebra of its value space (`L²(ν; ℝⁿ)`
  for `h`), and `(x, ρ) ↦ g(x, ρ)` is Borel on `ℝⁿ × P₂(ℝⁿ)` with `W₂` (`P2W`): the joint Borel
  measurability of §2, with (2.3) for `h`. The maximum norm and the Hilbert norm give `H` the same
  topology.
<!-- def-review: MVFBSDEJ.WellPosedness.Spec.JointBorel 6f73c7a1734b55b30000000000000000 by=claude-author source=A:eq:hborel@e96f0d4c4f81b393c2119f66e1766cb7561f3cf1fa43458d01f4d5c4892a910a -->
Review by claude-reviewer: faithful (report `reports/Dissertation.WellPosedness.Spec.JointBorel--claude-reviewer--2026-10-17T15_04_38Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Spec.JointBorel 6f73c7a1734b55b30000000000000000 by=claude-reviewer source=A:eq:hborel@e96f0d4c4f81b393c2119f66e1766cb7561f3cf1fa43458d01f4d5c4892a910a -->
Review by claude-auditor: faithful (report `reports/Dissertation.WellPosedness.Spec.JointBorel--claude-auditor--2026-10-19T03_26_57Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Spec.JointBorel 6f73c7a1734b55b30000000000000000 by=claude-auditor source=A:eq:hborel@e96f0d4c4f81b393c2119f66e1766cb7561f3cf1fa43458d01f4d5c4892a910a -->
<!-- def-review: MVFBSDEJ.WellPosedness.Spec.JointBorel.mk 02ba655dbb053b0b0000000000000000 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/Dissertation.WellPosedness.Spec.JointBorel.mk--claude-reviewer--2026-10-17T15_04_38Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Spec.JointBorel.mk 02ba655dbb053b0b0000000000000000 by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/Dissertation.WellPosedness.Spec.JointBorel.mk--claude-auditor--2026-10-19T03_26_57Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Spec.JointBorel.mk 02ba655dbb053b0b0000000000000000 by=claude-auditor -->
* `Spec.OriginValues T C`, with constructor `.mk`: `b(·, 0, δ₀)`, `σ(·, 0, δ₀)`, `h(·, 0, δ₀)` and
  `f(·, 0, δ₀)` lie in `L²` of Lebesgue measure on `(0, T)` (Bochner, with values in `L²(ν; ℝⁿ)` for
  `h`), `δ₀ = P2.dirac 0`: the origin values of Assumption 2.2. The open interval differs from
  `[0, T]` by a null set.
<!-- def-review: MVFBSDEJ.WellPosedness.Spec.OriginValues 6f73c7a1734b55b30000000000000000 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.Spec.OriginValues--claude-reviewer--2026-10-17T15_04_37Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Spec.OriginValues 6f73c7a1734b55b30000000000000000 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.Spec.OriginValues--claude-auditor--2026-10-19T03_26_58Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Spec.OriginValues 6f73c7a1734b55b30000000000000000 by=claude-auditor -->
<!-- def-review: MVFBSDEJ.WellPosedness.Spec.OriginValues.mk 5ccb5872806ad4950000000000000000 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.Spec.OriginValues.mk--claude-reviewer--2026-10-17T15_04_37Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Spec.OriginValues.mk 5ccb5872806ad4950000000000000000 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.Spec.OriginValues.mk--claude-auditor--2026-10-19T03_26_58Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Spec.OriginValues.mk 5ccb5872806ad4950000000000000000 by=claude-auditor -->
* `Spec.Assumption22 ℱ P T C ξ₀`, with constructor `.mk`: `ξ₀` strongly `ℱ_0`-measurable and square
  integrable, and `OriginValues T C`: Assumption 2.2, the element `ξ₀` of `L²(Ω, ℱ₀; ℝⁿ)`
  represented by a function in its class.
<!-- def-review: MVFBSDEJ.WellPosedness.Spec.Assumption22 4d16dbea7ba49fec0000000000000000 by=claude-author source=A:ass:integ@ef9a3acbfb5b5d7c874f4f8a54ca3a7d5a23e6dce6483f2e6391407799f2925e -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.Spec.Assumption22--claude-reviewer--2026-10-17T15_04_37Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Spec.Assumption22 4d16dbea7ba49fec0000000000000000 by=claude-reviewer source=A:ass:integ@ef9a3acbfb5b5d7c874f4f8a54ca3a7d5a23e6dce6483f2e6391407799f2925e -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.Spec.Assumption22--claude-auditor--2026-10-19T03_26_57Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Spec.Assumption22 4d16dbea7ba49fec0000000000000000 by=claude-auditor source=A:ass:integ@ef9a3acbfb5b5d7c874f4f8a54ca3a7d5a23e6dce6483f2e6391407799f2925e -->
<!-- def-review: MVFBSDEJ.WellPosedness.Spec.Assumption22.mk 3cfe22ea044c06020000000000000000 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.Spec.Assumption22.mk--claude-reviewer--2026-10-17T15_04_37Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Spec.Assumption22.mk 3cfe22ea044c06020000000000000000 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.Spec.Assumption22.mk--claude-auditor--2026-10-19T03_26_57Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Spec.Assumption22.mk 3cfe22ea044c06020000000000000000 by=claude-auditor -->
* `Spec.LipInteriorAt ℱ P t L C`: for all `(Θ, μ), (Θ', μ') ∈ 𝒟_t`, almost surely `|δb| + |δσ|_F +
  ‖δh‖ + |δf| ≤ L (|δX| + |δY| + |δZ|_F + ‖δU‖ + W₂(μ, μ'))`, the coefficients at `t` and `W₂` the
  Hilbert-norm `w2H`: the interior bound of Assumption 2.3 at one time.
<!-- def-review: MVFBSDEJ.WellPosedness.Spec.LipInteriorAt 5ad9199da021d476f2be26fbc20e44ad by=claude-author -->
Review by claude-reviewer: faithful (report `reports/Dissertation.WellPosedness.Spec.LipInteriorAt--claude-reviewer--2026-10-17T15_04_38Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Spec.LipInteriorAt 5ad9199da021d476f2be26fbc20e44ad by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/Dissertation.WellPosedness.Spec.LipInteriorAt--claude-auditor--2026-10-19T03_26_58Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Spec.LipInteriorAt 5ad9199da021d476f2be26fbc20e44ad by=claude-auditor -->
* `Spec.LipInterior ℱ P T L C`: `LipInteriorAt ℱ P t L C` for almost every `t ∈ [0, T]`.
<!-- def-review: MVFBSDEJ.WellPosedness.Spec.LipInterior 5ad9199da021d4764670fe9b35f8c1e4 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/Dissertation.WellPosedness.Spec.LipInterior--claude-reviewer--2026-10-17T15_04_38Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Spec.LipInterior 5ad9199da021d4764670fe9b35f8c1e4 by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/Dissertation.WellPosedness.Spec.LipInterior--claude-auditor--2026-10-19T03_26_57Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Spec.LipInterior 5ad9199da021d4764670fe9b35f8c1e4 by=claude-auditor -->
* `Spec.LipTerminal ℱ P T L g`: for strongly `ℱ_T`-measurable square-integrable `X_T, X'_T`, almost
  surely `|g(X_T, ρ) − g(X'_T, ρ')| ≤ L (|X_T − X'_T| + W₂(ρ, ρ'))`, `ρ, ρ'` their laws on `ℝⁿ`
  (`lawP2`, `w2P`): (2.6).
<!-- def-review: MVFBSDEJ.WellPosedness.Spec.LipTerminal ba56bc4929aee90fc20042d257c95726 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/Dissertation.WellPosedness.Spec.LipTerminal--claude-reviewer--2026-10-17T15_04_39Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Spec.LipTerminal ba56bc4929aee90fc20042d257c95726 by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/Dissertation.WellPosedness.Spec.LipTerminal--claude-auditor--2026-10-19T03_26_58Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Spec.LipTerminal ba56bc4929aee90fc20042d257c95726 by=claude-auditor -->
* `Spec.Assumption23 ℱ P T L C`, with constructor `.mk`: `L ≥ 0`, `LipInterior` and `LipTerminal`
  with `L`: Assumption 2.3.
<!-- def-review: MVFBSDEJ.WellPosedness.Spec.Assumption23 5ad9199da021d4760000000000000000 by=claude-author source=A:ass:lip@9c7bbbc5ca7a20286ef27d4eb7edb07d33d9787563041cadef820d833345f085 -->
Review by claude-reviewer: faithful (report `reports/Dissertation.WellPosedness.Spec.Assumption23--claude-reviewer--2026-10-17T15_04_38Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Spec.Assumption23 5ad9199da021d4760000000000000000 by=claude-reviewer source=A:ass:lip@9c7bbbc5ca7a20286ef27d4eb7edb07d33d9787563041cadef820d833345f085 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.Spec.Assumption23--claude-auditor--2026-10-19T03_26_57Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Spec.Assumption23 5ad9199da021d4760000000000000000 by=claude-auditor source=A:ass:lip@9c7bbbc5ca7a20286ef27d4eb7edb07d33d9787563041cadef820d833345f085 -->
<!-- def-review: MVFBSDEJ.WellPosedness.Spec.Assumption23.mk e6fadc3dde19b05c0000000000000000 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/Dissertation.WellPosedness.Spec.Assumption23.mk--claude-reviewer--2026-10-17T15_04_38Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Spec.Assumption23.mk e6fadc3dde19b05c0000000000000000 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.Spec.Assumption23.mk--claude-auditor--2026-10-19T03_26_57Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Spec.Assumption23.mk e6fadc3dde19b05c0000000000000000 by=claude-auditor -->
* `Constants n m α β₁ β₂`, with constructor `.mk`: `α, β₁, β₂ ≥ 0`, `α + β₁ > 0`, `β₁ + β₂ > 0`,
  `β₁ > 0` if `m < n`, and `α, β₂ > 0` if `m > n`: the conditions on the constants in Assumption
  2.5.
<!-- def-review: MVFBSDEJ.WellPosedness.Constants 523a9f9cc9be2abd0000000000000000 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/Dissertation.WellPosedness.Constants--claude-reviewer--2026-10-17T12_28_18Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Constants 523a9f9cc9be2abd0000000000000000 by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/Dissertation.WellPosedness.Constants--claude-auditor--2026-10-19T03_28_16Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Constants 523a9f9cc9be2abd0000000000000000 by=claude-auditor -->
<!-- def-review: MVFBSDEJ.WellPosedness.Constants.mk a0377c08c7c65e970000000000000000 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/Dissertation.WellPosedness.Constants.mk--claude-reviewer--2026-10-17T12_28_40Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Constants.mk a0377c08c7c65e970000000000000000 by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/Dissertation.WellPosedness.Constants.mk--claude-auditor--2026-10-19T03_28_16Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Constants.mk a0377c08c7c65e970000000000000000 by=claude-auditor -->
* `Spec.pairing27 G C t θ θ' μ μ'`: `⟨δb, Gᵀ δy⟩ + ⟨δσ, Gᵀ δz⟩_F + ⟨−δf, G δx⟩ + ∫_E ⟨δh(e), Gᵀ
  δu(e)⟩ ν(de)` at two points and two laws: the integrand of the left side of (2.7). The mark
  integral is the Bochner integral of the product of two `L²(ν)` representatives, which is
  integrable and does not depend on the representatives.
<!-- def-review: MVFBSDEJ.WellPosedness.Spec.pairing27 3951ca541ad316db35cf5a08ab3dce91 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/Dissertation.WellPosedness.Spec.pairing27--claude-reviewer--2026-10-17T12_30_10Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Spec.pairing27 3951ca541ad316db35cf5a08ab3dce91 by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/Dissertation.WellPosedness.Spec.pairing27--claude-auditor--2026-10-19T03_26_58Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Spec.pairing27 3951ca541ad316db35cf5a08ab3dce91 by=claude-auditor -->
* `Spec.Mono27At ℱ P t G β₁ β₂ C`: for all `(Θ, μ), (Θ', μ') ∈ 𝒟_t`, `pairing27` along them is
  integrable and its expectation is at most `−β₁ 𝔼[|Gᵀ δY|² + |Gᵀ δZ|²_F + ‖Gᵀ δU‖²] − β₂ 𝔼|G δX|²`
  (Bochner integrals): (2.7) at one time. Choice: the existence of the expectation of the pairing is
  asked, which the printed display presupposes; under (2.3) and Assumption 2.3 it holds at almost
  every time for all square-integrable inputs, the coefficient differences being then measurable and
  square integrable.
<!-- def-review: MVFBSDEJ.WellPosedness.Spec.Mono27At f8eb12ff2eed71b8d19f4b54d2691948 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.Spec.Mono27At--claude-reviewer--2026-10-17T15_04_37Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Spec.Mono27At f8eb12ff2eed71b8d19f4b54d2691948 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.Spec.Mono27At--claude-auditor--2026-10-19T03_26_58Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Spec.Mono27At f8eb12ff2eed71b8d19f4b54d2691948 by=claude-auditor -->
* `Spec.Assumption25 ℱ P T G α β₁ β₂ C`, with constructor `.mk`: the terminal inequality
  `𝔼⟨δg_T, G δX_T⟩ ≥ α 𝔼|G δX_T|²` for strongly `ℱ_T`-measurable square-integrable `X_T, X'_T`, its
  pairing integrable; `Mono27At` for almost every `t ∈ [0, T]`; and `Constants`: Assumption 2.5,
  with the same choice for the terminal pairing.
<!-- def-review: MVFBSDEJ.WellPosedness.Spec.Assumption25 a0fc1ba9071e126c0000000000000000 by=claude-author source=A:ass:mono@a60a526e8cdd9d0ae4441e25895e5af1cc39a45df41a9028fe0f60371ce998ff -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.Spec.Assumption25--claude-reviewer--2026-10-17T15_04_37Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Spec.Assumption25 a0fc1ba9071e126c0000000000000000 by=claude-reviewer source=A:ass:mono@a60a526e8cdd9d0ae4441e25895e5af1cc39a45df41a9028fe0f60371ce998ff -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.Spec.Assumption25--claude-auditor--2026-10-19T03_26_57Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Spec.Assumption25 a0fc1ba9071e126c0000000000000000 by=claude-auditor source=A:ass:mono@a60a526e8cdd9d0ae4441e25895e5af1cc39a45df41a9028fe0f60371ce998ff -->
<!-- def-review: MVFBSDEJ.WellPosedness.Spec.Assumption25.mk 8e9681ce0d5f98640000000000000000 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.Spec.Assumption25.mk--claude-reviewer--2026-10-17T15_04_37Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Spec.Assumption25.mk 8e9681ce0d5f98640000000000000000 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.Spec.Assumption25.mk--claude-auditor--2026-10-19T03_26_57Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Spec.Assumption25.mk 8e9681ce0d5f98640000000000000000 by=claude-auditor -->

Verdict: faithful with representation choices.

## The solution notion of §3

Manuscript (§3): `S²(ℝʲ)` is the space of càdlàg adapted `V` with `𝔼 sup_{t ≤ T} |V_t|² < ∞`,
`ℍ = S²(ℝⁿ) × S²(ℝᵐ) × H²_W × H²_N`, and "a solution of (1.1) is a tuple `Θ ∈ ℍ` satisfying both
identities of (1.1) almost surely for every `t ∈ [0, T]`, with `h` evaluated at the predictable
tuple `(Θ⁻_t, μ⁻_t)`"; `ℍ ⊂ ℍ_weak`.

* `PaperSpec.A.Solution D h𝒢₀ hind₀ T C ξ₀ X Y Z U`: `WeakSolution` together with
  `𝔼 sup_{t ≤ T} |X_t|² < ∞` and `𝔼 sup_{t ≤ T} |Y_t|² < ∞` (`esq` the squared Euclidean norm in
  `[0, ∞]`, the supremum over `[0, T]` inside the lower integral). As `S² ⊂ L²_ad`
  (`sec3_HH_inclusion`), this is the paper's notion: a tuple of `ℍ` satisfying (1.1), with the
  representation choices of `WeakSolution`. The drift and driver integrals are pathwise, so no
  square integrability of `b(·, Θ, μ)` or `f(·, Θ, μ)` is asked; that matters only outside
  Assumptions 2.2–2.3 (Remark 3.4, the drift `t^{-1/2}`). Under (2.3) and Assumptions 2.2–2.3 the
  notion coincides with the implementation's `PaperSolutionEnl`, which asks those processes to have
  finite energy (`Solution.paperSolutionEnl`, `solution_of_paperSolutionEnl`). The left limits
  `Θ⁻_s` are `Function.leftLim` of each path; at `s = 0` they read the values at negative times,
  and `s = 0` is a `dt`-null time of the integrals of (1.1).

Verdict: faithful with representation choices.
<!-- def-review: MVFBSDEJ.PaperSpec.Solution 3220c6ff72b9eb8278fda8b917b2b13b by=claude-author source=A:intro:mvfbsdej@0d85452f18880ddaaf63d57d1760fe13bf46552331679aa18ef206bbdea64300 source=A:eq:mvfbsdej@0d85452f18880ddaaf63d57d1760fe13bf46552331679aa18ef206bbdea64300 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.Solution--claude-auditor--2026-10-19T05_48_40Z.md`).
<!-- def-review: MVFBSDEJ.PaperSpec.Solution 3220c6ff72b9eb8278fda8b917b2b13b by=claude-auditor source=A:intro:mvfbsdej@0d85452f18880ddaaf63d57d1760fe13bf46552331679aa18ef206bbdea64300 source=A:eq:mvfbsdej@0d85452f18880ddaaf63d57d1760fe13bf46552331679aa18ef206bbdea64300 -->

## The weak solution notion of §3 (`ℍ_weak`)

Manuscript (§3, "Solution space"): `L²_ad(ℝʲ)` is the space of càdlàg adapted `V` with
`𝔼 ∫_0^T |V_t|² dt < ∞`, `H²_W` that of the predictable `Z` with `𝔼 ∫_0^T |Z_t|²_F dt < ∞`,
`H²_N` that of the predictable `L²(ν)`-valued `U` with `𝔼 ∫_0^T ‖U_t‖² dt < ∞`, and
`ℍ_weak = L²_ad(ℝⁿ) × L²_ad(ℝᵐ) × H²_W × H²_N`. A tuple satisfies (1.1) when both identities hold
almost surely for every `t ∈ [0, T]`, with `h` at the predictable tuple `(Θ⁻_t, μ⁻_t)`.

* `System.PaperWeakTuple ℱ P ν T X Y Z U`: coordinates `X_i`, `Y_k` adapted at every `t ∈ [0, T]`,
  every path right-continuous on `[0, T)`, almost every path with left limits on `(0, T]`, finite
  `𝔼 ∫_0^T |·|² dt` (`energy`); `Z_{k,j}` predictable, `U_k` marked predictable (a jointly
  measurable function of `(ω, s, e)`), each of finite energy and vanishing off `[0, T]`. This is
  `ℍ_weak` coordinate by coordinate; the vanishing off `[0, T]` is a normalisation (the values off
  the horizon do not enter (1.1)); the marked-predictable σ-algebra has no time-`0` sets, so
  `U_0 = 0`, a `dt`-null time. `.mk` is its constructor.
<!-- def-review: MVFBSDEJ.WellPosedness.System.PaperWeakTuple f8659178ce7276550000000000000000 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.PaperWeakTuple--claude-reviewer--2026-10-17T15_06_16Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.PaperWeakTuple f8659178ce7276550000000000000000 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.PaperWeakTuple--claude-auditor--2026-10-19T03_36_34Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.PaperWeakTuple f8659178ce7276550000000000000000 by=claude-auditor -->
<!-- def-review: MVFBSDEJ.WellPosedness.System.PaperWeakTuple.mk 84e84b13114cd1940000000000000000 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.PaperWeakTuple.mk--claude-reviewer--2026-10-17T15_06_16Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.PaperWeakTuple.mk 84e84b13114cd1940000000000000000 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.PaperWeakTuple.mk--claude-auditor--2026-10-19T03_36_34Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.PaperWeakTuple.mk 84e84b13114cd1940000000000000000 by=claude-auditor -->
* `System.PaperAdmissibleInt ℱ P T C X Y Z U γ`: the integrals of (1.1) along `Θ` exist. The
  drift `b(s, Θ_s, μ_s)` and driver `f(s, Θ_s, μ_s)` (`driftProc`, `driverProc`, cut to `[0, T]`,
  `μ_s = lawP2 P Θ_s`) are jointly and progressively measurable with almost every path integrable
  on `[0, T]`, so the Lebesgue integrals of (1.1) exist; the diffusion `σ(s, Θ_s, μ_s)` is jointly
  and progressively measurable with finite energy, and `γ` cut to `[0, T]` is jointly and marked
  progressively measurable with finite marked energy, so the `L²` stochastic integrals of the
  library exist; and `γ` represents `e ↦ h(s, Θ⁻_s, e, μ⁻_s)` in `L²(ν)` for almost every `s`,
  almost surely (`jump_rep`). Choices: the stochastic integrals are `L²` ones (under Assumption 2.3
  the coefficient processes along a tuple of `ℍ_weak` have finite energy, (4.2), so no tuple the
  paper integrates is lost); `γ` is marked progressive rather than `𝒫 ⊗ ℰ`-measurable, which the
  `L²` integral does not see; `μ_s` is the law at each time, the junk `δ₀` of `lawP2` only on the
  `dt`-null set of times where `Θ_s ∉ L²`. `.mk` is its constructor.
<!-- def-review: MVFBSDEJ.WellPosedness.System.PaperAdmissibleInt 920b75f0f6cfc8ef0000000000000000 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.PaperAdmissibleInt--claude-reviewer--2026-10-17T15_06_15Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.PaperAdmissibleInt 920b75f0f6cfc8ef0000000000000000 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.PaperAdmissibleInt--claude-auditor--2026-10-19T03_36_34Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.PaperAdmissibleInt 920b75f0f6cfc8ef0000000000000000 by=claude-auditor -->
<!-- def-review: MVFBSDEJ.WellPosedness.System.PaperAdmissibleInt.mk 8c7c2b1a226bff7a0000000000000000 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.PaperAdmissibleInt.mk--claude-reviewer--2026-10-17T15_06_15Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.PaperAdmissibleInt.mk 8c7c2b1a226bff7a0000000000000000 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.PaperAdmissibleInt.mk--claude-auditor--2026-10-19T03_36_34Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.PaperAdmissibleInt.mk 8c7c2b1a226bff7a0000000000000000 by=claude-auditor -->
* `System.PaperWeakSolutionInt D ℱ hℱW hℱN T C ξ₀ X Y Z U γ`: `PaperWeakTuple` and
  `PaperAdmissibleInt`, `X_T ∈ L²` (so that `Law(X_T) ∈ P₂` and `g(X_T, Law X_T)` is the paper's),
  and the two identities of (1.1) off one null set for every `t ∈ [0, T]`, the Brownian integrals
  read through a version `M` with almost surely càdlàg paths (`fwd`, `bwd`). The paper's
  "almost surely for every `t`" is equivalent, both sides being càdlàg (`sec3_one_null_set`).
  `.mk` is its constructor; `Spec.PaperWeakSolutionIntEnl` is it over `enlJoint 𝒢₀ D h𝒢₀`.
<!-- def-review: MVFBSDEJ.WellPosedness.System.PaperWeakSolutionInt 327523dba68d2a760000000000000000 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.PaperWeakSolutionInt--claude-reviewer--2026-10-17T15_06_16Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.PaperWeakSolutionInt 327523dba68d2a760000000000000000 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.PaperWeakSolutionInt--claude-auditor--2026-10-19T03_36_34Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.PaperWeakSolutionInt 327523dba68d2a760000000000000000 by=claude-auditor -->
<!-- def-review: MVFBSDEJ.WellPosedness.System.PaperWeakSolutionInt.mk d799dadbb45890ae0000000000000000 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.PaperWeakSolutionInt.mk--claude-reviewer--2026-10-17T15_06_16Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.PaperWeakSolutionInt.mk d799dadbb45890ae0000000000000000 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.PaperWeakSolutionInt.mk--claude-auditor--2026-10-19T03_36_34Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.PaperWeakSolutionInt.mk d799dadbb45890ae0000000000000000 by=claude-auditor -->
<!-- def-review: MVFBSDEJ.WellPosedness.Spec.PaperWeakSolutionIntEnl fee486406b67239ed77b642b59569585 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.Spec.PaperWeakSolutionIntEnl--claude-reviewer--2026-10-17T12_28_46Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Spec.PaperWeakSolutionIntEnl fee486406b67239ed77b642b59569585 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.Spec.PaperWeakSolutionIntEnl--claude-auditor--2026-10-19T03_36_01Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Spec.PaperWeakSolutionIntEnl fee486406b67239ed77b642b59569585 by=claude-auditor -->
* `PaperSpec.A.WeakSolution D h𝒢₀ hind₀ T C ξ₀ X Y Z U`: some `γ` with
  `PaperWeakSolutionIntEnl`, and every path of `X` and of `Y` with left limits on `(0, T]` (with
  the every-path right-continuity, every path càdlàg on `[0, T]`), over `enlJoint 𝒢₀ D h𝒢₀`, the
  usual augmentation of `ℱ^{W,N}_t ∨ 𝒢₀` with `𝒢₀` independent of the driver (`hind₀`). This is
  the paper's "`Θ ∈ ℍ_weak` satisfying (1.1)", with the choices above.

Verdict: faithful with representation choices.
<!-- def-review: MVFBSDEJ.PaperSpec.WeakSolution 3220c6ff72b9eb82a9071b16fb195fd0 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.WeakSolution--claude-reviewer--2026-10-17T16_01_26Z.md`).
<!-- def-review: MVFBSDEJ.PaperSpec.WeakSolution 3220c6ff72b9eb82a9071b16fb195fd0 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.WeakSolution--claude-auditor--2026-10-19T03_35_36Z.md`).
<!-- def-review: MVFBSDEJ.PaperSpec.WeakSolution 3220c6ff72b9eb82a9071b16fb195fd0 by=claude-auditor -->

## The drift (3.6) of Proposition 3.8 (`MVFBSDEJ/WellPosedness/ExpectedVsPointwise*.lean`)

Manuscript (Proposition 3.8, (3.6)): `n = m = 1`, `d ≥ 1`, `b(t, θ, μ) = −β₁ y + ε g₀(y − m_Y(μ))`,
`g₀(r) = max{−1, min{1, r}}`, `m_Y(μ) = ∫_H y μ(dθ)` the `Y`-marginal mean.

* `WellPosedness.clamp01 r = max(−1, min(1, r))`: `g₀`.
<!-- def-review: MVFBSDEJ.WellPosedness.clamp01 29fbc050c7ff42ca65cda76e668193a3 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/Dissertation.WellPosedness.clamp01--claude-reviewer--2026-10-17T15_01_51Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.clamp01 29fbc050c7ff42ca65cda76e668193a3 by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/Dissertation.WellPosedness.clamp01--claude-auditor--2026-10-19T03_31_21Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.clamp01 29fbc050c7ff42ca65cda76e668193a3 by=claude-auditor -->
* `System.clampVec v`: `g₀` applied to the coordinate of `v ∈ ℝ¹`.
<!-- def-review: MVFBSDEJ.WellPosedness.System.clampVec 72826a95517d7c68ac773b0a675fe7c6 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/Dissertation.WellPosedness.System.clampVec--claude-reviewer--2026-10-17T15_06_18Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.clampVec 72826a95517d7c68ac773b0a675fe7c6 by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/Dissertation.WellPosedness.System.clampVec--claude-auditor--2026-10-19T03_31_21Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.clampVec 72826a95517d7c68ac773b0a675fe7c6 by=claude-auditor -->
* `System.meanY μ = ∫_H y μ(dθ)` (Bochner) for `μ ∈ P₂(H)`, `H = ℝ × ℝ × ℝ^{1×d} × L²(ν; ℝ)`:
  `m_Y(μ)`. The `Y`-channel is integrable under a law of finite second moment and takes values in
  `ℝ¹`, so the integral is the mean and never Lean's junk value.
<!-- def-review: MVFBSDEJ.WellPosedness.System.meanY 079456e1a0252b309db53184102a12d2 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.meanY--claude-reviewer--2026-10-17T15_01_50Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.meanY 079456e1a0252b309db53184102a12d2 by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/Dissertation.WellPosedness.System.meanY--claude-auditor--2026-10-19T03_31_21Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.meanY 079456e1a0252b309db53184102a12d2 by=claude-auditor -->
* `System.clampDrift β₁ ε t θ μ = −β₁ y + ε g₀(y − m_Y(μ))`: (3.6), at every `d` and `ν`.
<!-- def-review: MVFBSDEJ.WellPosedness.System.clampDrift 55fa37350d2f6c9f1f4d1b9e5a9a22b7 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/Dissertation.WellPosedness.System.clampDrift--claude-reviewer--2026-10-17T15_06_17Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.clampDrift 55fa37350d2f6c9f1f4d1b9e5a9a22b7 by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/Dissertation.WellPosedness.System.clampDrift--claude-auditor--2026-10-19T03_31_21Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.clampDrift 55fa37350d2f6c9f1f4d1b9e5a9a22b7 by=claude-auditor -->

Verdict: faithful.

## Corollary 3.6: the perturbation, the margin and the pairing bounds (`Spec/CorollaryHyps.lean`, `Spec/Cor36Law.lean`, `Robustness/Perturb.lean`)

Manuscript (Corollary 3.6, Remark 2.11): the perturbations `p_b, p_σ, p_h, p_f`, the perturbed
system `(b₀ + p_b, σ₀ + p_σ, h₀ + p_h, f₀ + p_f, g)`, the margin in the unweighted form (2.13), the
pairing bound (3.4), the independence of `θ` and the bound (3.5).

* `Spec.LawLip35 ℱ P T L_p p`: for almost every `t ∈ [0, T]` and all `(Θ, μ), (Θ', μ') ∈ 𝒟_t`,
  almost surely `|δp_b| + |δp_σ|_F + ‖δp_h‖ + |δp_f| ≤ L_p W₂(μ, μ')`, `W₂` the Hilbert-norm `w2H`:
  (3.5).
<!-- def-review: MVFBSDEJ.WellPosedness.Spec.LawLip35 5ad9199da021d4764dfc416a7d21faa6 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/Dissertation.WellPosedness.Spec.LawLip35--claude-reviewer--2026-10-17T15_04_38Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Spec.LawLip35 5ad9199da021d4764dfc416a7d21faa6 by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/Dissertation.WellPosedness.Spec.LawLip35--claude-auditor--2026-10-19T03_37_18Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Spec.LawLip35 5ad9199da021d4764dfc416a7d21faa6 by=claude-auditor -->
* `Spec.Margin213 ℱ P T G β₁ β₂ c C`: for almost every `t ∈ [0, T]` and all pairs of `𝒟_t`,
  `pairing27` is integrable and its expectation is at most `−β₁ 𝔼[|Gᵀ δY|² + |Gᵀ δZ|²_F + ‖Gᵀ δU‖²]
  − β₂ 𝔼|G δX|² − c 𝔼[|δY|² + |δZ|²_F + ‖δU‖² + |δX|²]`: (2.13), with the integrability choice of
  `Mono27At`.
<!-- def-review: MVFBSDEJ.WellPosedness.Spec.Margin213 a0fc1ba9071e126c345eefe1f9893670 by=claude-author source=A:eq:monomarginu@f626420b93b36f0e86aa29e8fb81b7b1a6e5de7e8721ca40a618d662ddd39b54 -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.Spec.Margin213--claude-reviewer--2026-10-17T15_04_37Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Spec.Margin213 a0fc1ba9071e126c345eefe1f9893670 by=claude-reviewer source=A:eq:monomarginu@f626420b93b36f0e86aa29e8fb81b7b1a6e5de7e8721ca40a618d662ddd39b54 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.Spec.Margin213--claude-auditor--2026-10-19T03_26_58Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Spec.Margin213 a0fc1ba9071e126c345eefe1f9893670 by=claude-auditor source=A:eq:monomarginu@f626420b93b36f0e86aa29e8fb81b7b1a6e5de7e8721ca40a618d662ddd39b54 -->
* `Spec.PairingBound34 ℱ P T G c p`: for almost every `t ∈ [0, T]` and all pairs of `𝒟_t`, the
  pairing `pairing27` of the perturbation differences is integrable and its expectation is at most
  `c 𝔼[|δX|² + |δY|² + |δZ|²_F + ‖δU‖²]`: (3.4), with the same choice.
<!-- def-review: MVFBSDEJ.WellPosedness.Spec.PairingBound34 089030da41aceea5ca6f78cb208c2943 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.Spec.PairingBound34--claude-reviewer--2026-10-17T15_04_38Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Spec.PairingBound34 089030da41aceea5ca6f78cb208c2943 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.Spec.PairingBound34--claude-auditor--2026-10-19T03_37_18Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Spec.PairingBound34 089030da41aceea5ca6f78cb208c2943 by=claude-auditor -->
* `System.Coeffs.TupleIndep p`, with constructor `.mk`: `p_ψ(t, θ, μ) = p_ψ(t, θ', μ)` for
  `ψ ∈ {b, σ, h, f}` and all `t, θ, θ', μ`: "the perturbations are independent of `θ`".
<!-- def-review: MVFBSDEJ.WellPosedness.System.Coeffs.TupleIndep 3bda15e66940560c0000000000000000 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/Dissertation.WellPosedness.System.Coeffs.TupleIndep--claude-reviewer--2026-10-17T15_50_56Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.Coeffs.TupleIndep 3bda15e66940560c0000000000000000 by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/Dissertation.WellPosedness.System.Coeffs.TupleIndep--claude-auditor--2026-10-19T03_37_27Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.Coeffs.TupleIndep 3bda15e66940560c0000000000000000 by=claude-auditor -->
<!-- def-review: MVFBSDEJ.WellPosedness.System.Coeffs.TupleIndep.mk bfa8145b0a07aa4a0000000000000000 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/Dissertation.WellPosedness.System.Coeffs.TupleIndep.mk--claude-reviewer--2026-10-17T12_39_50Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.Coeffs.TupleIndep.mk bfa8145b0a07aa4a0000000000000000 by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/Dissertation.WellPosedness.System.Coeffs.TupleIndep.mk--claude-auditor--2026-10-19T03_37_27Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.Coeffs.TupleIndep.mk bfa8145b0a07aa4a0000000000000000 by=claude-auditor -->
* `System.Coeffs.perturb C p = (b + p_b, σ + p_σ, h + p_h, f + p_f, g)`: the perturbed system of the
  corollary; the perturbation is recorded as a coefficient system whose terminal function is not
  used.
<!-- def-review: MVFBSDEJ.WellPosedness.System.Coeffs.perturb cf8326886c388246c2a105556e30345a by=claude-author -->
Review by claude-reviewer: faithful (report `reports/Dissertation.WellPosedness.System.Coeffs.perturb--claude-reviewer--2026-10-17T15_50_57Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.Coeffs.perturb cf8326886c388246c2a105556e30345a by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/Dissertation.WellPosedness.System.Coeffs.perturb--claude-auditor--2026-10-19T03_37_27Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.Coeffs.perturb cf8326886c388246c2a105556e30345a by=claude-auditor -->

Verdict: faithful with representation choices.

## The `U`-marginal of a law (`MVFBSDEJ/Law/P2.lean`, `MVFBSDEJ/Law/TupleMarginal.lean`)

Manuscript (Remark 2.6): `μ^U ∈ P₂(L²(ν))` is the `U`-marginal of `μ ∈ P₂(H)`.

* `Law.P2.map μ hP hlip`: the image law `P_# μ` along a measurable `P` with `‖P x‖ ≤ ‖x‖`, an
  element of `P₂(F)`.
<!-- def-review: MVFBSDEJ.Law.P2.map c2ab784ca43e0741f94705fcffdd5e14 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.Law.P2.map--claude-reviewer--2026-10-17T15_50_57Z.md`).
<!-- def-review: MVFBSDEJ.Law.P2.map c2ab784ca43e0741f94705fcffdd5e14 by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/Dissertation.Law.P2.map--claude-auditor--2026-10-19T03_27_45Z.md`).
<!-- def-review: MVFBSDEJ.Law.P2.map c2ab784ca43e0741f94705fcffdd5e14 by=claude-auditor -->
* `Law.P2.margU μ = (projUH)_# μ`: the `U`-marginal `μ^U`.
<!-- def-review: MVFBSDEJ.Law.P2.margU 7505583a3e0f25f97aff92a3543d54ff by=claude-author -->
Review by claude-reviewer: faithful (report `reports/Dissertation.Law.P2.margU--claude-reviewer--2026-10-17T12_08_36Z.md`).
<!-- def-review: MVFBSDEJ.Law.P2.margU 7505583a3e0f25f97aff92a3543d54ff by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/Dissertation.Law.P2.margU--claude-auditor--2026-10-19T03_27_45Z.md`).
<!-- def-review: MVFBSDEJ.Law.P2.margU 7505583a3e0f25f97aff92a3543d54ff by=claude-auditor -->
* `System.projUH`: `θ = (x, y, z, u) ↦ u`, a continuous linear map `H → L²(ν; ℝᵐ)`.
<!-- def-review: MVFBSDEJ.WellPosedness.System.projUH f17c7a5068951c3ea6290bd22991b5b8 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/Dissertation.WellPosedness.System.projUH--claude-reviewer--2026-10-17T15_01_50Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.projUH f17c7a5068951c3ea6290bd22991b5b8 by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/Dissertation.WellPosedness.System.projUH--claude-auditor--2026-10-19T03_27_24Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.projUH f17c7a5068951c3ea6290bd22991b5b8 by=claude-auditor -->

Verdict: faithful.

## The forced system (4.1) and `WP(λ)` of §4

Manuscript (§4): for `λ ∈ [0, 1]` and a square-integrable forcing `q = (q^b, q^σ, q^h, q^f, q^g_T)`
(`q^b, q^σ, q^f` progressively measurable and in `L²(Ω × [0, T])`, `q^h` predictable,
`𝒫 ⊗ ℰ`-measurable and in `L²(dP ⊗ dt ⊗ ν)`, `q^g_T ∈ L²(Ω, ℱ_T)`), the system (4.1) is (1.1)
with every coefficient multiplied by `λ` and the forcing added; `WP(λ)`: (4.1) has a unique
solution in `ℍ` for every such forcing.

* `System.Forcing ℱ P ν T qb qσ qh qf qg`: `q^b, q^σ, q^f` jointly and progressively measurable,
  `q^h` jointly and marked progressively measurable, each vanishing off `[0, T]` and of finite
  (marked) energy; `q^g` strongly `ℱ_T`-measurable and in `L²`. The vanishing off `[0, T]` is a
  normalisation (extension by `0`); `.mk` is its constructor.
<!-- def-review: MVFBSDEJ.WellPosedness.System.Forcing a3ba59f5823fbe6a0000000000000000 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.Forcing--claude-reviewer--2026-10-17T15_50_57Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.Forcing a3ba59f5823fbe6a0000000000000000 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.Forcing--claude-auditor--2026-10-19T03_37_35Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.Forcing a3ba59f5823fbe6a0000000000000000 by=claude-auditor -->
<!-- def-review: MVFBSDEJ.WellPosedness.System.Forcing.mk 0746ae482299e6580000000000000000 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.Forcing.mk--claude-reviewer--2026-10-17T16_02_38Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.Forcing.mk 0746ae482299e6580000000000000000 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.Forcing.mk--claude-auditor--2026-10-19T03_37_40Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.Forcing.mk 0746ae482299e6580000000000000000 by=claude-auditor -->
* `System.PredForcing`: a `Forcing` whose `q^h` is marked predictable, the paper's `𝒫 ⊗ ℰ`
  class; the marked-predictable σ-algebra has no time-`0` sets, so `q^h_0 = 0`, a `dt`-null time
  that does not enter (4.1). `.mk` is its constructor.
<!-- def-review: MVFBSDEJ.WellPosedness.System.PredForcing 467cf5000b974ed10000000000000000 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.PredForcing--claude-reviewer--2026-10-17T15_06_16Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.PredForcing 467cf5000b974ed10000000000000000 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.PredForcing--claude-auditor--2026-10-19T03_37_56Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.PredForcing 467cf5000b974ed10000000000000000 by=claude-auditor -->
<!-- def-review: MVFBSDEJ.WellPosedness.System.PredForcing.mk 65b91a24a06a08760000000000000000 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.PredForcing.mk--claude-reviewer--2026-10-17T15_06_17Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.PredForcing.mk 65b91a24a06a08760000000000000000 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.PredForcing.mk--claude-auditor--2026-10-19T03_38_02Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.PredForcing.mk 65b91a24a06a08760000000000000000 by=claude-auditor -->
* `System.PaperWeakSolutionForcedInt D ℱ hℱW hℱN T λ C ξ₀ q X Y Z U γ`: `PaperWeakTuple`; `q` a
  `Forcing`; the forced drift and driver `λ b + q^b`, `λ f + q^f` jointly and progressively
  measurable with almost every path integrable on `[0, T]`; the forced diffusion `λ σ + q^σ` and
  jump integrand `λ γ + q^h` jointly and (marked) progressively measurable with finite energy;
  `γ` representing `h(s, Θ⁻_s, ·, μ⁻_s)` as in `PaperAdmissibleInt`; `X_T ∈ L²`; and the two
  identities of (4.1) off one null set for every `t ∈ [0, T]`, with càdlàg versions of the
  Brownian integrals. Each forced integrand `λ ψ + q^ψ` is integrated as one process, which is the
  sum of the two printed integrals since `q` is square integrable. `.mk` is its constructor.
<!-- def-review: MVFBSDEJ.WellPosedness.System.PaperWeakSolutionForcedInt 0c1292246c71c5070000000000000000 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.PaperWeakSolutionForcedInt--claude-reviewer--2026-10-17T15_06_16Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.PaperWeakSolutionForcedInt 0c1292246c71c5070000000000000000 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.PaperWeakSolutionForcedInt--claude-auditor--2026-10-19T03_38_36Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.PaperWeakSolutionForcedInt 0c1292246c71c5070000000000000000 by=claude-auditor -->
<!-- def-review: MVFBSDEJ.WellPosedness.System.PaperWeakSolutionForcedInt.mk d748d1e1231aa2640000000000000000 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.PaperWeakSolutionForcedInt.mk--claude-reviewer--2026-10-17T15_06_16Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.PaperWeakSolutionForcedInt.mk d748d1e1231aa2640000000000000000 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.PaperWeakSolutionForcedInt.mk--claude-auditor--2026-10-19T03_38_45Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.PaperWeakSolutionForcedInt.mk d748d1e1231aa2640000000000000000 by=claude-auditor -->
* `PaperSpec.A.WeakForcedSolution`: some `γ` with `PaperWeakSolutionForcedInt` over
  `enlJoint 𝒢₀ D h𝒢₀`, and every path of `X` and of `Y` with left limits on `(0, T]`: (4.1) in
  `ℍ_weak` with `X_T ∈ L²`, the class of Lemma 4.3.
<!-- def-review: MVFBSDEJ.PaperSpec.WeakForcedSolution bde81c401c9ac90991383a009c3a500d by=claude-author source=A:sec4:WP-def@17962fe037ff7de888f26d2b0c9f51427d790ab6422e549a1d661ef69141a32e -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.WeakForcedSolution--claude-reviewer--2026-10-17T16_02_24Z.md`).
<!-- def-review: MVFBSDEJ.PaperSpec.WeakForcedSolution bde81c401c9ac90991383a009c3a500d by=claude-reviewer source=A:sec4:WP-def@17962fe037ff7de888f26d2b0c9f51427d790ab6422e549a1d661ef69141a32e -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.WeakForcedSolution--claude-auditor--2026-10-19T03_38_16Z.md`).
<!-- def-review: MVFBSDEJ.PaperSpec.WeakForcedSolution bde81c401c9ac90991383a009c3a500d by=claude-auditor source=A:sec4:WP-def@17962fe037ff7de888f26d2b0c9f51427d790ab6422e549a1d661ef69141a32e -->
* `PaperSpec.A.ForcedSolution`: `WeakForcedSolution` together with `𝔼 sup_{t ≤ T} |X_t|² < ∞`
  and `𝔼 sup_{t ≤ T} |Y_t|² < ∞`: a tuple of `ℍ` satisfying (4.1), as `Solution` is for (1.1). The
  forced drift and driver integrals are pathwise; under (2.3) and Assumptions 2.2–2.3 the notion
  coincides with the implementation's `PaperSolutionForced`, which asks them finite energy
  (`ForcedSolution.paperSolutionForced`, `forcedSolution_of_paperSolutionForced`). The forcing's
  admissibility is part of the predicate (`Forcing`, where `q^h` need only be marked
  progressive); `WP` quantifies over `PredForcing`, the printed predictable class.
<!-- def-review: MVFBSDEJ.PaperSpec.ForcedSolution bde81c401c9ac909f447baae21c89992 by=claude-author source=A:eq:forced@134e01a0256ffc7a16425886631cfe88968f942fb53d500c263ce1cf361b3cf8 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.ForcedSolution--claude-auditor--2026-10-19T05_48_40Z.md`).
<!-- def-review: MVFBSDEJ.PaperSpec.ForcedSolution bde81c401c9ac909f447baae21c89992 by=claude-auditor source=A:eq:forced@134e01a0256ffc7a16425886631cfe88968f942fb53d500c263ce1cf361b3cf8 -->
* `PaperSpec.A.WP D h𝒢₀ hind₀ T λ C ξ₀`: for every `PredForcing` `q` over `enlJoint 𝒢₀ D h𝒢₀`,
  a `ForcedSolution` exists, and any two have `X` and `Y` indistinguishable on `[0, T]` and the
  energies of the differences of `Z` and of `U` equal to zero: uniqueness in `ℍ` up to its
  identifications.

Verdict: faithful with representation choices.
<!-- def-review: MVFBSDEJ.PaperSpec.WP 839d627ccda37855ed1ac20fb346a349 by=claude-author source=A:sec4:WP-def@17962fe037ff7de888f26d2b0c9f51427d790ab6422e549a1d661ef69141a32e -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.WP--claude-reviewer--2026-10-17T16_01_36Z.md`).
<!-- def-review: MVFBSDEJ.PaperSpec.WP 839d627ccda37855ed1ac20fb346a349 by=claude-reviewer source=A:sec4:WP-def@17962fe037ff7de888f26d2b0c9f51427d790ab6422e549a1d661ef69141a32e -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.WP--claude-auditor--2026-10-19T03_37_30Z.md`).
<!-- def-review: MVFBSDEJ.PaperSpec.WP 839d627ccda37855ed1ac20fb346a349 by=claude-auditor source=A:sec4:WP-def@17962fe037ff7de888f26d2b0c9f51427d790ab6422e549a1d661ef69141a32e -->

## The coefficient systems of Example 5.1 (`Existence/AffineExample.lean`, `Existence/ClampAffine.lean`, `Examples/MeanField.lean`)

Manuscript (Example 5.1): (i) `n = m = d = 1`, `b = −β₁ y`, `σ = σ_c − β₁ z`,
`h(e) = h_c(e) − β₁ u(e)`, `f = β₂ x`, `g(x, ρ) = x`, with `σ_c ∈ ℝ`, `h_c ∈ L²(ν)` and
`β₁, β₂ > 0`, and the same system with the drift (3.6); (ii) `b = −2y − m_Y(μ)`, `σ = −2z − m_Z(μ)`,
`h(e) = −2u(e) − m_U(μ)(e)`, `f = 2x + m_X(μ)`, `g(x, ρ) = 2x + 𝔟(ρ)`, with the marginal means
`m_Ψ(μ) = ∫_H π_Ψ(θ) μ(dθ)` and the barycentre `𝔟(ρ) = ∫ x ρ(dx)`.

* `Existence.affineCoeffs β₁ β₂ σ_c h_c`: the coefficients of (i), `b = −β₁ y`, `σ = σ_c − β₁ z`,
  `h = h_c − β₁ u`, `f = β₂ x`, `g(x, ρ) = x`, on `TupleH ν n n d` for general `n = m` and `d`, with
  `σ_c ∈ ℝ^{n×d}`, `h_c ∈ L²(ν; ℝⁿ)` and real `β₁, β₂`: broader than the printed instance
  `n = d = 1`, which it is at `n = d = 1`. The constants are unrestricted; the propositions assume
  `β₁, β₂ > 0` where printed.
<!-- def-review: MVFBSDEJ.WellPosedness.Existence.affineCoeffs 79b8f5d22ca305705c5f63bf3e931a89 by=claude-author -->
Review by claude-reviewer: broader (report `reports/Dissertation.WellPosedness.Existence.affineCoeffs--claude-reviewer--2026-10-17T15_50_57Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Existence.affineCoeffs 79b8f5d22ca305705c5f63bf3e931a89 by=claude-reviewer -->
Review by claude-auditor: broader (report `reports/Dissertation.WellPosedness.Existence.affineCoeffs--claude-auditor--2026-10-19T03_26_57Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Existence.affineCoeffs 79b8f5d22ca305705c5f63bf3e931a89 by=claude-auditor -->
* `Existence.clampAffineCoeffs β₁ β₂ ε σ_c h_c`: `affineCoeffs` at `n = m = 1` with the drift
  replaced by `clampDrift β₁ ε`, the system of "replacing its drift `−β₁ y` by (3.6)", for every
  `d`: broader, the printed system at `d = 1`.
<!-- def-review: MVFBSDEJ.WellPosedness.Existence.clampAffineCoeffs 6cb4ed79c2cef570940d7db3b3ec6088 by=claude-author -->
Review by claude-reviewer: broader (report `reports/Dissertation.WellPosedness.Existence.clampAffineCoeffs--claude-reviewer--2026-10-17T15_04_36Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Existence.clampAffineCoeffs 6cb4ed79c2cef570940d7db3b3ec6088 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.Existence.clampAffineCoeffs--claude-auditor--2026-10-19T03_31_21Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Existence.clampAffineCoeffs 6cb4ed79c2cef570940d7db3b3ec6088 by=claude-auditor -->
* `Existence.meanFieldCoeffs ν n d`: the coefficients of (ii) on `TupleH ν n n d`, `m_Ψ(μ)` the
  channels of `tupleMean μ` and `𝔟` the `barycentre`, for general `n = m` and `d`: broader, the
  printed system at `n = d = 1`, the instance the statements use.
<!-- def-review: MVFBSDEJ.WellPosedness.Existence.meanFieldCoeffs 9258c0d2d1763065daedb69b81b21cd5 by=claude-author -->
Review by claude-reviewer: broader (report `reports/Dissertation.WellPosedness.Existence.meanFieldCoeffs--claude-reviewer--2026-10-17T15_04_36Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Existence.meanFieldCoeffs 9258c0d2d1763065daedb69b81b21cd5 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.Existence.meanFieldCoeffs--claude-auditor--2026-10-19T03_31_21Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Existence.meanFieldCoeffs 9258c0d2d1763065daedb69b81b21cd5 by=claude-auditor -->
* `System.barycentre ρ = ∫ x ρ(dx)` (Bochner) for `ρ ∈ P₂(ℝⁿ)`: `𝔟(ρ)`; the identity is integrable
  under a law of finite second moment.
<!-- def-review: MVFBSDEJ.WellPosedness.System.barycentre d95f5f6816c664c9d2b2466a9a20df79 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/Dissertation.WellPosedness.System.barycentre--claude-reviewer--2026-10-17T15_06_17Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.barycentre d95f5f6816c664c9d2b2466a9a20df79 by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/Dissertation.WellPosedness.System.barycentre--claude-auditor--2026-10-19T03_31_21Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.barycentre d95f5f6816c664c9d2b2466a9a20df79 by=claude-auditor -->
* `System.tupleMean μ = ∫_H θ μ(dθ)` (Bochner): the vector `(m_X, m_Y, m_Z, m_U)(μ)` of the marginal
  means. When `L²(ν)` is separable (`E` countably generated and `ν` σ-finite, the paper's setting)
  the identity is integrable under `μ ∈ P₂(H)` and this is the mean. Without separability the
  identity need not be almost everywhere strongly measurable, and the integral can take Lean's junk
  value `0`; the statements that use `tupleMean` assume the paper's setting.
<!-- def-review: MVFBSDEJ.WellPosedness.System.tupleMean 0f984890fededa2abc6a565b493b6a39 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.tupleMean--claude-reviewer--2026-10-17T15_01_51Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.tupleMean 0f984890fededa2abc6a565b493b6a39 by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/Dissertation.WellPosedness.System.tupleMean--claude-auditor--2026-10-19T03_31_21Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.tupleMean 0f984890fededa2abc6a565b493b6a39 by=claude-auditor -->

Verdict: faithful with representation choices; `affineCoeffs`, `clampAffineCoeffs` and
`meanFieldCoeffs` broader, the printed systems their instances at `n = d = 1` (`d = 1` for
`clampAffineCoeffs`).

## The reduced tuple space of Example 5.2 (`Examples/Brownian.lean`)

Manuscript (Example 5.2): "Delete the `U`-coordinate from the tuple, reducing `H` to
`ℝⁿ × ℝᵐ × ℝ^{m×d}`"; the coefficients depend on the joint law of `(X, Y, Z)` under `W₂`.

* `System.ReducedTuple n m d`: `ℝⁿ × ℝᵐ × ℝ^{m×d}` with the Hilbert norm
  `(|x|² + |y|² + |z|²_F)^{1/2}` (nested `WithLp 2` products), the reduced `H`.
<!-- def-review: MVFBSDEJ.WellPosedness.System.ReducedTuple d68fe71f65d1320f648e397a6f92aa48 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/Dissertation.WellPosedness.System.ReducedTuple--claude-reviewer--2026-10-17T15_06_17Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.ReducedTuple d68fe71f65d1320f648e397a6f92aa48 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.ReducedTuple--claude-auditor--2026-10-19T03_26_15Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.ReducedTuple d68fe71f65d1320f648e397a6f92aa48 by=claude-auditor -->
* `System.projB θ = (x, y, z)`: deleting the `U`-coordinate.
<!-- def-review: MVFBSDEJ.WellPosedness.System.projB 73d9b93f57af07f1488467cea55fd063 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/Dissertation.WellPosedness.System.projB--claude-reviewer--2026-10-17T15_01_50Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.projB 73d9b93f57af07f1488467cea55fd063 by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/Dissertation.WellPosedness.System.projB--claude-auditor--2026-10-19T03_26_27Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.projB 73d9b93f57af07f1488467cea55fd063 by=claude-auditor -->
* `System.projP2 μ = (projB)_# μ` in `P₂` of the reduced space: the law of `(X, Y, Z)` when `μ` is
  that of `(X, Y, Z, U)`; `w2P` on it is the `W₂` of the reduced Hilbert norm.
<!-- def-review: MVFBSDEJ.WellPosedness.System.projP2 c7b2936a55d940d2ccaaedd3091be842 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/Dissertation.WellPosedness.System.projP2--claude-reviewer--2026-10-17T15_01_50Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.projP2 c7b2936a55d940d2ccaaedd3091be842 by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/Dissertation.WellPosedness.System.projP2--claude-auditor--2026-10-19T03_26_27Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.projP2 c7b2936a55d940d2ccaaedd3091be842 by=claude-auditor -->

Verdict: faithful.

## The perturbation of Example 5.4 (`PaperSpec/Sec5.lean`, `Robustness/Perturb.lean`)

Manuscript (Example 5.4): with `m = n`, `f = f₀ + ε q(W₂(μ, μ₀)) w₀ + ε Q(∫ φ_1 dμ^U, …, ∫ φ_J dμ^U)
w₁`, `b = b₀ + ε q̃(W₂(μ^U, Λ₀)) v₀`, `h = h₀ + ε q̂(W₂(μ^U, Λ₀)) ĥ`, for `q, q̃, q̂ : ℝ₊ → ℝ`,
`Q : ℝᴶ → ℝ` and features `φ_j : L²(ν) → ℝ`, bounded and Lipschitz.

* `PaperSpec.A.ex54Pert ν n d J ε q qb qh Q φ μ₀ Λ₀ w₀ w₁ v₀ ĥ`: `Coeffs.ofLaw` of
  `p_b = ε qb(W₂(μ^U, Λ₀)) v₀`, `p_σ = 0`, `p_h = ε qh(W₂(μ^U, Λ₀)) ĥ` and `p_f = ε q(W₂(μ, μ₀))
  w₀ + ε Q(∫ φ_1 dμ^U, …, ∫ φ_J dμ^U) w₁`, with `W₂(μ, μ₀)` the Hilbert-norm `w2H` and `W₂(μ^U, Λ₀)`
  that of `L²(ν; ℝⁿ)`; `qb`, `qh` are the printed `q̃`, `q̂`, and `C.perturb (ex54Pert …)` is the
  printed perturbed system, with `m = n`. Choices: the profiles are functions on `ℝ`, of which only
  the values on `[0, ∞)` enter, as for the printed `ℝ₊ → ℝ`; boundedness and Lipschitz continuity of
  the profiles, of `Q` and of the features are hypotheses of the propositions, not of the
  definition; `∫ φ_j dμ^U` is a Bochner integral, the mean of `φ_j` for the Lipschitz features the
  propositions assume, which grow at most linearly and are integrable under a law of finite second
  moment.
<!-- def-review: MVFBSDEJ.PaperSpec.ex54Pert ce9a4548ab82e1fefedcf09ce26ce86a by=claude-author -->
Review by claude-reviewer: faithful (report `reports/Dissertation.PaperSpec.A.ex54Pert--claude-reviewer--2026-10-17T16_01_44Z.md`).
<!-- def-review: MVFBSDEJ.PaperSpec.ex54Pert ce9a4548ab82e1fefedcf09ce26ce86a by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.ex54Pert--claude-auditor--2026-10-19T03_37_12Z.md`).
<!-- def-review: MVFBSDEJ.PaperSpec.ex54Pert ce9a4548ab82e1fefedcf09ce26ce86a by=claude-auditor -->
* `System.Coeffs.ofLaw p_b p_σ p_h p_f`: the coefficient system `(t, θ, μ) ↦ p_ψ(t, μ)`,
  `ψ ∈ {b, σ, h, f}`, independent of `θ`, with terminal function `0`, which `perturb` does not use.
<!-- def-review: MVFBSDEJ.WellPosedness.System.Coeffs.ofLaw 76a7e1e7c0080f581b950936a86db4bd by=claude-author -->
Review by claude-reviewer: faithful (report `reports/Dissertation.WellPosedness.System.Coeffs.ofLaw--claude-reviewer--2026-10-17T16_01_31Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.Coeffs.ofLaw 76a7e1e7c0080f581b950936a86db4bd by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/Dissertation.WellPosedness.System.Coeffs.ofLaw--claude-auditor--2026-10-19T03_37_27Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.System.Coeffs.ofLaw 76a7e1e7c0080f581b950936a86db4bd by=claude-auditor -->

Verdict: faithful with representation choices.

## The crowding correction of Example 5.5 (`PaperSpec/Sec5.lean`)

Manuscript (Example 5.5): `𝒜_λ(u) = ∫_{L²(ν)} ∇V(u − v) λ(dv)`, `∇V(w) = w / √(1 + ‖w‖²)`,
`λ ∈ P₂(L²(ν))`.

* `PaperSpec.A.ex55Crowd Λ u = ∫_F (1 + ‖u − v‖²)^{−1/2} (u − v) Λ(dv)` (Bochner), for a measure `Λ`
  on a real Hilbert space `F`: `𝒜_Λ(u)`. Choices: `F` and `Λ` are general, and the integral is
  Lean's Bochner integral, `0` when the integrand is not integrable (an infinite `Λ`, or an `F` on
  which the integrand is not almost everywhere strongly measurable). The statements take
  `F = L²(ν)`, separable, and `Λ` a probability law (`μ.margU.law`, or the two-point laws), where
  the integrand, continuous and bounded by `1`, is integrable and the value is the printed `𝒜_Λ(u)`.
<!-- def-review: MVFBSDEJ.PaperSpec.ex55Crowd 8d3f49063f9d40bd91804eeb64810052 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.ex55Crowd--claude-reviewer--2026-10-17T15_50_57Z.md`).
<!-- def-review: MVFBSDEJ.PaperSpec.ex55Crowd 8d3f49063f9d40bd91804eeb64810052 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.ex55Crowd--claude-auditor--2026-10-19T03_28_16Z.md`).
<!-- def-review: MVFBSDEJ.PaperSpec.ex55Crowd 8d3f49063f9d40bd91804eeb64810052 by=claude-auditor -->

Verdict: faithful with representation choices.

## The coefficients of Example 5.5 (`PaperSpec/Sec5Dealer.lean`)

* `PaperSpec.A.ex55Coeffs ν β₁ β₂ σ_c h_c h_x ε`: the coefficient system of Example 5.5 at
  `n = m = d = 1`, at `θ = (x, y, z, u)` and a law `μ` of `P₂(H)`: `b = −β₁ y`,
  `σ = σ_c − β₁ z` (`σ_c ∈ ℝ^{1×1}`), `h = h_c + x h_x − β₁ u − ε A_{μ^U}(u)` in `L²(ν)` (`x` the
  single coordinate of the forward state), `f = β₂ x + ⟨h_x, u⟩_{L²(ν)}` (as a vector of `ℝ¹`)
  and `g(x, ρ) = x`, where `A = ex55Crowd` is evaluated at the law `μ.margU.law` of the
  `U`-marginal of `μ`, the printed "`μ^U` the `U`-marginal of the measure argument". No
  coefficient depends on `t`. This is the printed display. The constants are arbitrary reals; the
  propositions assume `β₁, β₂ > 0` and `ε ≥ 0` where printed. Along a solution the jump
  coefficient is evaluated at `(Θ⁻_t, μ⁻_t)` by the solution notion, as for every system. At
  `ε = 0`, `h_x = 0` it is `affineCoeffs` (`ex_dealer_coeffs`).
  <!-- def-review: MVFBSDEJ.PaperSpec.ex55Coeffs cad9f6a453fea8b2448eb82f1bab2f5a by=claude-author -->
  Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.ex55Coeffs--claude-auditor--2026-10-19T03_28_16Z.md`).
  <!-- def-review: MVFBSDEJ.PaperSpec.ex55Coeffs cad9f6a453fea8b2448eb82f1bab2f5a by=claude-auditor -->
* `PaperSpec.A.ex55Marks ϱ`: `dealerMarks` with `c_{±1} = (2 − ϱ)/2` and exponent `ϱ`, the mark
  measure `c_ς q^{−1−ϱ} dq` on `{−1, +1} × (0, 1]` of the specialisation ("`c_{±1} = (2 − ϱ)/2`").
  <!-- def-review: MVFBSDEJ.PaperSpec.ex55Marks 0a7cd5acabebe270a7faa508a4fc53a1 by=claude-author -->
  Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.ex55Marks--claude-auditor--2026-10-19T03_28_16Z.md`).
  <!-- def-review: MVFBSDEJ.PaperSpec.ex55Marks 0a7cd5acabebe270a7faa508a4fc53a1 by=claude-auditor -->
* `PaperSpec.A.ex55Linear 𝒢₀ ϱ P D h𝒢₀ hind₀ T X`: `LinearFSDEJ` (reviewed below) over
  `enlJoint 𝒢₀ D h𝒢₀` on `[0, T]` with initial value `0`, drift `−X_s` on `[0, T]`, diffusion `½`
  on `[0, T]` and Poisson integrand `½ (ς q + q X_{s−})` on `(0, T]`, the left limit taken by
  `leftLimProc`: the printed linear equation
  `X⁰_t = ∫_0^t (−X⁰_s ds + ½ dW_s) + ½ ∫_0^t ∫_E (h_c(e) + h_x(e) X⁰_{s−}) Ñ(ds, de)` with
  `h_c(ς, q) = ς q`, `h_x(ς, q) = q` (`ς = +1` for `true`), for an adapted `X` with
  right-continuous paths, almost surely at each `t ∈ [0, T]`. The cut-offs to `[0, T]` and
  `(0, T]` do not change the equation on `[0, T]`.
  <!-- def-review: MVFBSDEJ.PaperSpec.ex55Linear c9077e9374bc32f7d53120b45672c1a4 by=claude-author -->
  Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.ex55Linear--claude-auditor--2026-10-19T03_28_16Z.md`).
  <!-- def-review: MVFBSDEJ.PaperSpec.ex55Linear c9077e9374bc32f7d53120b45672c1a4 by=claude-auditor -->

## The mark space of Example 5.5 and the linear forward equation (`Examples/Dealer/Marks.lean`, `Stability/ForwardEq.lean`)

Manuscript (Example 5.5): `E = {−1, +1} × (0, 1]`, `e = (ς, q)` for side and size,
`ν(dς, dq) = c_ς q^{−1−ϱ} dq` with `c_ς > 0` and `0 < ϱ < 2`, and the linear equation `X⁰_t = ∫_0^t
(−X⁰_s ds + ½ dW_s) + ½ ∫_0^t ∫_E (h_c(e) + h_x(e) X⁰_{s−}) Ñ(ds, de)`.

* `Existence.DealerMark = Bool × (0, 1]`: the mark space `{−1, +1} × (0, 1]`, the side `true`
  standing for `+1`, with the discrete σ-algebra on the sides and the Borel σ-algebra of `(0, 1]` on
  the sizes.
<!-- def-review: MVFBSDEJ.WellPosedness.Existence.DealerMark f743d5d40f14218fb917137b1ad4a2ae by=claude-author -->
Review by claude-auditor: faithful (report `reports/Dissertation.WellPosedness.Existence.DealerMark--claude-auditor--2026-10-19T03_28_16Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Existence.DealerMark f743d5d40f14218fb917137b1ad4a2ae by=claude-auditor -->
* `Existence.dealerMarks c ϱ`: the measure with density `c_ς q^{−1−ϱ}` (through `ofReal`) against
  counting measure on the sides times Lebesgue measure on the sizes: `ν(dς, dq) = c_ς q^{−1−ϱ} dq`,
  the printed `dq` with counting measure in `ς`. `ofReal` would read a negative density as `0`; the
  propositions take `c_ς > 0` (or the specialisation `c_ς = (2 − ϱ)/2` with `0 < ϱ < 2`).
<!-- def-review: MVFBSDEJ.WellPosedness.Existence.dealerMarks 688cf878d3c1a61efd74d2a30f11000f by=claude-author -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.Existence.dealerMarks--claude-auditor--2026-10-19T03_26_57Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Existence.dealerMarks 688cf878d3c1a61efd74d2a30f11000f by=claude-auditor -->
* `Existence.sizeLeb`: Lebesgue measure on the sizes `(0, 1]`, the comap of Lebesgue measure along
  the inclusion into `ℝ`.
<!-- def-review: MVFBSDEJ.WellPosedness.Existence.sizeLeb f531e248a597ba7e291a0506aba7a0a6 by=claude-author -->
Review by claude-auditor: faithful (report `reports/Dissertation.WellPosedness.Existence.sizeLeb--claude-auditor--2026-10-19T03_26_57Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Existence.sizeLeb f531e248a597ba7e291a0506aba7a0a6 by=claude-auditor -->
* `Stability.LinearFSDEJ D ℱ hℱW hℱN T ξ₀ b X σ γ`, with constructor `.mk`: `b`, the coordinates of
  `σ` and `γ` jointly measurable, progressive (`γ` marked progressive), vanishing off `[0, T]` and
  of finite (marked) energy there; `ξ₀ ∈ L²`; `X` adapted with every path right-continuous; and
  almost surely at each `t ∈ [0, T]`, `X_t = ξ₀ + ∫_0^t b_s ds + ∫_0^t σ_s dW_s + ∫_0^t ∫_E γ_s(e)
  Ñ(ds, de)`, with the library's integrals for `ℱ`: a solution of a linear forward equation with
  jumps whose integrands are given. Choices: the drift is asked square integrable rather than
  integrable in time, which the integrands of the statements are; the vanishing off `[0, T]` is a
  normalisation; the equation holds almost surely at each time, the paper's reading of a linear
  equation for a right-continuous solution.
<!-- def-review: MVFBSDEJ.WellPosedness.Stability.LinearFSDEJ 61bb9f1d9c8aba870000000000000000 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.Stability.LinearFSDEJ--claude-reviewer--2026-10-17T12_31_12Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Stability.LinearFSDEJ 61bb9f1d9c8aba870000000000000000 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.Stability.LinearFSDEJ--claude-auditor--2026-10-19T03_26_58Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Stability.LinearFSDEJ 61bb9f1d9c8aba870000000000000000 by=claude-auditor -->
<!-- def-review: MVFBSDEJ.WellPosedness.Stability.LinearFSDEJ.mk ea015c0d53b57f5d0000000000000000 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.Stability.LinearFSDEJ.mk--claude-reviewer--2026-10-17T12_31_35Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Stability.LinearFSDEJ.mk ea015c0d53b57f5d0000000000000000 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.Stability.LinearFSDEJ.mk--claude-auditor--2026-10-19T03_26_58Z.md`).
<!-- def-review: MVFBSDEJ.WellPosedness.Stability.LinearFSDEJ.mk ea015c0d53b57f5d0000000000000000 by=claude-auditor -->

Verdict: faithful with representation choices.

## The weighted margin (2.12) (`PaperSpec/Sec2Remarks.lean`)

Manuscript (Remark 2.11): (2.7) holds with margin `c > 0` if (2.12) holds.

* `PaperSpec.A.Margin212 ℱ P T G β₁ β₂ c C`: for almost every `t ∈ [0, T]` and all pairs of `𝒟_t`,
  `pairing27` is integrable and its expectation is at most `−β₁ 𝔼[|Gᵀ δY|² + |Gᵀ δZ|²_F + ‖Gᵀ δU‖²]
  − β₂ 𝔼|G δX|² − c 𝔼[|Gᵀ δY|² + |Gᵀ δZ|²_F + ‖Gᵀ δU‖² + |G δX|²]`: (2.12), with the integrability
  choice of `Mono27At`.
<!-- def-review: MVFBSDEJ.PaperSpec.Margin212 a0fc1ba9071e126ca6e512bffcfb0a22 by=claude-author source=A:eq:monomargin@3bf398680ece348005cee018ad83bc5cf40f4671bc0e6c341b0bf437325b642e -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.Margin212--claude-reviewer--2026-10-17T12_22_34Z.md`).
<!-- def-review: MVFBSDEJ.PaperSpec.Margin212 a0fc1ba9071e126ca6e512bffcfb0a22 by=claude-reviewer source=A:eq:monomargin@3bf398680ece348005cee018ad83bc5cf40f4671bc0e6c341b0bf437325b642e -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.Margin212--claude-auditor--2026-10-19T03_38_08Z.md`).
<!-- def-review: MVFBSDEJ.PaperSpec.Margin212 a0fc1ba9071e126ca6e512bffcfb0a22 by=claude-auditor source=A:eq:monomargin@3bf398680ece348005cee018ad83bc5cf40f4671bc0e6c341b0bf437325b642e -->

Verdict: faithful with representation choices.

## A representation of a martingale (`PaperSpec/Sec2Basics.lean`)

Manuscript (§2): every square-integrable `(ℱ_t)`-martingale `M` can be written `M_t = M_0 + ∫_0^t
Z_s dW_s + ∫_0^t ∫_E U_s(e) Ñ(ds, de)` for every `t ∈ [0, T]`, for an `ℱ₀`-measurable `M_0` and a
predictable square-integrable pair `(Z, U)`.

* `PaperSpec.A.RepresentsMart D h𝒢₀ hind₀ T M Z U`: the coordinates of `Z` predictable for
  `enlJoint 𝒢₀ D h𝒢₀` and `U` marked predictable, both vanishing off `[0, T]` and of finite energy
  there, and for every `t ∈ [0, T]`, almost surely `M_t = M_0 + ∫_0^t Z dW + ∫_0^t ∫_E U Ñ`, with
  the library's integrals: `(Z, U)` represents `M` on `[0, T]`. Choices: the identity holds almost
  surely at each time, the Brownian integral being a version at each time; the vanishing off
  `[0, T]` is a normalisation, with which the marked predictability makes `U_0 = 0`, a `dt`-null
  time.
<!-- def-review: MVFBSDEJ.PaperSpec.RepresentsMart 596b7f79cacb7e8081c7e3deb62ddc0b by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.RepresentsMart--claude-reviewer--2026-10-17T12_24_26Z.md`).
<!-- def-review: MVFBSDEJ.PaperSpec.RepresentsMart 596b7f79cacb7e8081c7e3deb62ddc0b by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.RepresentsMart--claude-auditor--2026-10-19T03_34_12Z.md`).
<!-- def-review: MVFBSDEJ.PaperSpec.RepresentsMart 596b7f79cacb7e8081c7e3deb62ddc0b by=claude-auditor -->

Verdict: faithful with representation choices.

## The energy measures of the integrands (`LevyStochCalc/Brownian/`, `LevyStochCalc/Poisson/`)

* `LevyStochCalc.Brownian.Ito.energyMeasure P T = P ⊗ (Lebesgue on [0, T])` on `Ω × ℝ`, and
  `LevyStochCalc.Poisson.Compensated.markedEnergyMeasure P ν T = P ⊗ ((Lebesgue on [0, T]) ⊗ ν)`
  on `Ω × ℝ × E`: the measures `dP ⊗ dt` and `dP ⊗ dt ⊗ ν` of the `L²` classes of the integrands.
  <!-- def-review: LevyStochCalc.Brownian.Ito.energyMeasure 8bb90a671c0f63eba6329d346b422bc3 by=claude-author -->
  Review by claude-reviewer: faithful (report `reports/LevyStochCalc.Brownian.Ito.energyMeasure--claude-reviewer--2026-10-17T15_02_25Z.md`).
  <!-- def-review: LevyStochCalc.Brownian.Ito.energyMeasure 8bb90a671c0f63eba6329d346b422bc3 by=claude-reviewer -->
  Review by claude-auditor: faithful (report `reports/LevyStochCalc.Brownian.Ito.energyMeasure--claude-auditor--2026-10-19T03_34_37Z.md`).
  <!-- def-review: LevyStochCalc.Brownian.Ito.energyMeasure 8bb90a671c0f63eba6329d346b422bc3 by=claude-auditor -->
  <!-- def-review: LevyStochCalc.Poisson.Compensated.markedEnergyMeasure 6a70d753259c930a27f458a6e2a44d87 by=claude-author -->
  Review by claude-reviewer: faithful (report `reports/LevyStochCalc.Poisson.Compensated.markedEnergyMeasure--claude-reviewer--2026-10-17T15_16_41Z.md`).
  <!-- def-review: LevyStochCalc.Poisson.Compensated.markedEnergyMeasure 6a70d753259c930a27f458a6e2a44d87 by=claude-reviewer -->
  Review by claude-auditor: faithful (report `reports/LevyStochCalc.Poisson.Compensated.markedEnergyMeasure--claude-auditor--2026-10-19T03_34_37Z.md`).
  <!-- def-review: LevyStochCalc.Poisson.Compensated.markedEnergyMeasure 6a70d753259c930a27f458a6e2a44d87 by=claude-auditor -->

## Progressive tuples and cross-evaluation (`MVFBSDEJ/WellPosedness/Existence/WPZero.lean`, `MVFBSDEJ/WellPosedness/System/CrossEval.lean`, `MVFBSDEJ/WellPosedness/System/HilbertW2Space.lean`)

* `WellPosedness.Existence.ProgTuple ℱ P ν T X Y Z U`: `X, Y` adapted with right-continuous paths,
  `Z` jointly and progressively measurable, `U` jointly and marked progressively measurable, both of
  finite energy on `[0, T]`. `.mk` is its constructor.
  <!-- def-review: MVFBSDEJ.WellPosedness.Existence.ProgTuple f8659178ce7276550000000000000000 by=claude-author -->
  Review by claude-reviewer: broader (report `reports/Dissertation.WellPosedness.Existence.ProgTuple--claude-reviewer--2026-10-17T15_50_57Z.md`).
  <!-- def-review: MVFBSDEJ.WellPosedness.Existence.ProgTuple f8659178ce7276550000000000000000 by=claude-reviewer -->
  Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.Existence.ProgTuple--claude-auditor--2026-10-19T03_31_22Z.md`).
  <!-- def-review: MVFBSDEJ.WellPosedness.Existence.ProgTuple f8659178ce7276550000000000000000 by=claude-auditor -->
  <!-- def-review: MVFBSDEJ.WellPosedness.Existence.ProgTuple.mk 91d4cf273bd63c2c0000000000000000 by=claude-author -->
  Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.Existence.ProgTuple.mk--claude-reviewer--2026-10-17T16_02_09Z.md`).
  <!-- def-review: MVFBSDEJ.WellPosedness.Existence.ProgTuple.mk 91d4cf273bd63c2c0000000000000000 by=claude-reviewer -->
  Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.Existence.ProgTuple.mk--claude-auditor--2026-10-19T03_31_22Z.md`).
  <!-- def-review: MVFBSDEJ.WellPosedness.Existence.ProgTuple.mk 91d4cf273bd63c2c0000000000000000 by=claude-auditor -->
* `WellPosedness.System.CrossEval ℱ P T C X Y Z U γ`: along the tuple, the drift, diffusion and
  driver processes of `C` are jointly and progressively measurable, and `γ` is a jointly measurable,
  marked progressively measurable representative of `e ↦ h(s, Θ_s, e, μ_s)` in `L²(ν)` for a.e.
  `s ∈ [0, T]`, a.s. The first part is the first line of (2.5); the jump part asks a
  marked-progressive `L²(ν)` representative at `(Θ_s, μ_s)`, which is weaker than the second line of
  (2.5), the predictability of `(s, ω, e) ↦ h(s, Θ_{s−}(ω), e, μ⁻_s)`. `.mk` is its constructor.
  <!-- def-review: MVFBSDEJ.WellPosedness.System.CrossEval e1db0cc7db4708710000000000000000 by=claude-author -->
  Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.CrossEval--claude-reviewer--2026-10-17T16_00_50Z.md`).
  <!-- def-review: MVFBSDEJ.WellPosedness.System.CrossEval e1db0cc7db4708710000000000000000 by=claude-reviewer -->
  Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.CrossEval--claude-auditor--2026-10-19T03_31_22Z.md`).
  <!-- def-review: MVFBSDEJ.WellPosedness.System.CrossEval e1db0cc7db4708710000000000000000 by=claude-auditor -->
  <!-- def-review: MVFBSDEJ.WellPosedness.System.CrossEval.mk d5755d6547b57eb60000000000000000 by=claude-author -->
  Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.CrossEval.mk--claude-reviewer--2026-10-17T12_39_50Z.md`).
  <!-- def-review: MVFBSDEJ.WellPosedness.System.CrossEval.mk d5755d6547b57eb60000000000000000 by=claude-reviewer -->
  Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.CrossEval.mk--claude-auditor--2026-10-19T03_31_22Z.md`).
  <!-- def-review: MVFBSDEJ.WellPosedness.System.CrossEval.mk d5755d6547b57eb60000000000000000 by=claude-auditor -->
* `WellPosedness.Existence.CoeffRegular ℱ P T C`: every progressive tuple has some `γ` with
  `CrossEval`: the first line of (2.5) along every progressive tuple, and for the jump coefficient a
  marked-progressive `L²(ν)` representative at `(Θ_s, μ_s)`, weaker than the second line of (2.5),
  which asks predictability at `(Θ⁻_s, μ⁻_s)`.
  <!-- def-review: MVFBSDEJ.WellPosedness.Existence.CoeffRegular 74bd12994c7599d5fefcbcb42ba10cbe by=claude-author -->
  Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.Existence.CoeffRegular--claude-reviewer--2026-10-17T12_33_27Z.md`).
  <!-- def-review: MVFBSDEJ.WellPosedness.Existence.CoeffRegular 74bd12994c7599d5fefcbcb42ba10cbe by=claude-reviewer -->
  Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.Existence.CoeffRegular--claude-auditor--2026-10-19T03_31_22Z.md`).
  <!-- def-review: MVFBSDEJ.WellPosedness.Existence.CoeffRegular 74bd12994c7599d5fefcbcb42ba10cbe by=claude-auditor -->
* `WellPosedness.System.P2WH.instMeasurableSpace`: the Borel σ-algebra of the Hilbert-norm
  2-Wasserstein topology on `P₂(H)`, the σ-algebra of "Borel law flows".
  <!-- def-review: MVFBSDEJ.WellPosedness.System.P2WH.instMeasurableSpace 80bb9d815e50f42553ee1291a5da7bae by=claude-author -->
  Review by claude-reviewer: faithful (report `reports/Dissertation.WellPosedness.System.P2WH.instMeasurableSpace--claude-reviewer--2026-10-17T12_39_50Z.md`).
  <!-- def-review: MVFBSDEJ.WellPosedness.System.P2WH.instMeasurableSpace 80bb9d815e50f42553ee1291a5da7bae by=claude-reviewer -->
  Review by claude-auditor: faithful (report `reports/Dissertation.WellPosedness.System.P2WH.instMeasurableSpace--claude-auditor--2026-10-19T03_31_22Z.md`).
  <!-- def-review: MVFBSDEJ.WellPosedness.System.P2WH.instMeasurableSpace 80bb9d815e50f42553ee1291a5da7bae by=claude-auditor -->

## Law flows and their tuples (`MVFBSDEJ/WellPosedness/System/LawFlow.lean`, `MVFBSDEJ/WellPosedness/System/HilbertW2Space.lean`)

* `WellPosedness.System.CadlagPredTuple ℱ P ν T X Y Z U`: `X, Y` adapted with right-continuous paths
  having left limits everywhere, `Z, U` predictable (marked predictable for `U`), and every
  coordinate of finite energy on `[0, T]`: the hypotheses of Lemma A.1 of the well-posedness paper.
  `.mk` is its constructor.
  <!-- def-review: MVFBSDEJ.WellPosedness.System.CadlagPredTuple 36dfb143d7b151d50000000000000000 by=claude-author -->
  Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.CadlagPredTuple--claude-reviewer--2026-10-17T12_39_50Z.md`).
  <!-- def-review: MVFBSDEJ.WellPosedness.System.CadlagPredTuple 36dfb143d7b151d50000000000000000 by=claude-reviewer -->
  Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.CadlagPredTuple--claude-auditor--2026-10-19T03_36_27Z.md`).
  <!-- def-review: MVFBSDEJ.WellPosedness.System.CadlagPredTuple 36dfb143d7b151d50000000000000000 by=claude-auditor -->
  <!-- def-review: MVFBSDEJ.WellPosedness.System.CadlagPredTuple.mk 984b72f0b09f1f3b0000000000000000 by=claude-author -->
  Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.CadlagPredTuple.mk--claude-reviewer--2026-10-17T16_02_32Z.md`).
  <!-- def-review: MVFBSDEJ.WellPosedness.System.CadlagPredTuple.mk 984b72f0b09f1f3b0000000000000000 by=claude-reviewer -->
  Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.CadlagPredTuple.mk--claude-auditor--2026-10-19T03_36_33Z.md`).
  <!-- def-review: MVFBSDEJ.WellPosedness.System.CadlagPredTuple.mk 984b72f0b09f1f3b0000000000000000 by=claude-auditor -->
* `Law.P2.toP2WH μ`: a law of finite second moment on the tuple space as a point of `P2WH`, the
  same laws with the Hilbert-norm 2-Wasserstein distance.
  <!-- def-review: MVFBSDEJ.Law.P2.toP2WH 9f66cfadccaf0b20fcfc2344d158d542 by=claude-author -->
  Review by claude-reviewer: faithful (report `reports/Dissertation.Law.P2.toP2WH--claude-reviewer--2026-10-17T16_01_48Z.md`).
  <!-- def-review: MVFBSDEJ.Law.P2.toP2WH 9f66cfadccaf0b20fcfc2344d158d542 by=claude-reviewer -->
  Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.Law.P2.toP2WH--claude-auditor--2026-10-19T03_36_21Z.md`).
  <!-- def-review: MVFBSDEJ.Law.P2.toP2WH 9f66cfadccaf0b20fcfc2344d158d542 by=claude-auditor -->

## the system of Example 3.2 of Li and Min (`MVFBSDEJ/PaperSpec/Sec5Preamble.lean`)

* `liMinCoeffs ν` (`n = m = d = 1`): on `H = ℝ × ℝ × ℝ^{1×1} × L²(ν; ℝ)` with `θ = (x, y, z, u)`,
  `b(t, θ, μ) = m_Y(μ)`, `σ = 1`, `h(t, θ, μ) = u`, `f(t, θ, μ) = m_X(μ)`, `g(x, ρ) = −𝔟(ρ)`, with
  `m_X, m_Y` the `X`- and `Y`-channels of `tupleMean μ` and `𝔟` the barycentre. Along a tuple,
  (1.1) reads `dX = 𝔼[Y] dt + dW + ∫ U dÑ`, `−dY = 𝔼[X] dt − Z dW − ∫ U dÑ`,
  `Y_T = −𝔼[X_T]`: the system transcribed in the module docstring as Example 3.2 of Li and Min,
  with the forward jump integrand equal to the backward one and the initial value left to the
  statement. The manuscript cites the example without printing it, and the cited paper is not in
  the repository, so the identification with the printed Example 3.2 of Li and Min rests on that
  transcription and is not checked here; the statements using `liMinCoeffs` prove their claims
  about this system directly and do not depend on the identification.
  <!-- def-review: MVFBSDEJ.WellPosedness.System.liMinCoeffs 4a85f9437d277c3a5bbccf7981b2432d by=claude-author -->
  Review by claude-reviewer: faithful (report `reports/Dissertation.WellPosedness.System.liMinCoeffs--claude-reviewer--2026-10-17T15_06_18Z.md`).
  <!-- def-review: MVFBSDEJ.WellPosedness.System.liMinCoeffs 4a85f9437d277c3a5bbccf7981b2432d by=claude-reviewer -->
  Review by claude-auditor: faithful (report `reports/Dissertation.WellPosedness.System.liMinCoeffs--claude-auditor--2026-10-19T03_31_22Z.md`).
  <!-- def-review: MVFBSDEJ.WellPosedness.System.liMinCoeffs 4a85f9437d277c3a5bbccf7981b2432d by=claude-auditor -->

## the weighted pairing bound of Remark 3.7 (`MVFBSDEJ/PaperSpec/Sec3GeneralRank.lean`)

* `PaperSpec.A.PairingBound34W ℱ P T G c p`: for almost every `t ∈ [0, T]` and all
  `(Θ, μ), (Θ', μ') ∈ 𝒟_t`, the pairing `pairing27 G p` of the perturbation differences (the
  left side of (3.4)) is integrable and its expectation is at most
  `c 𝔼[|Gᵀ δY|² + |Gᵀ δZ|²_F + ‖Gᵀ δU‖²_{L²(ν)} + |G δX|²]`: (3.4) with its right side recorded in
  the weighted quantity of (2.12), as Remark 3.7 prescribes. The integrability conjunct is the
  one of `PairingBound34`.
  <!-- def-review: MVFBSDEJ.PaperSpec.PairingBound34W 089030da41aceea52dd1d1c86c0b71e0 by=claude-author -->
  Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.PairingBound34W--claude-reviewer--2026-10-17T12_23_19Z.md`).
  <!-- def-review: MVFBSDEJ.PaperSpec.PairingBound34W 089030da41aceea52dd1d1c86c0b71e0 by=claude-reviewer -->
  Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.PairingBound34W--claude-auditor--2026-10-19T03_36_24Z.md`).
  <!-- def-review: MVFBSDEJ.PaperSpec.PairingBound34W 089030da41aceea52dd1d1c86c0b71e0 by=claude-auditor -->

## the singular drift against Remark 3.4 (`MVFBSDEJ/WellPosedness/Examples/SingularDrift.lean`)

* `WellPosedness.System.Coeffs.addDrift C c`: the coefficients `C` with the deterministic drift
  `c(t)` added to `b`, the other coefficients unchanged.
  <!-- def-review: MVFBSDEJ.WellPosedness.System.Coeffs.addDrift 666b78c0f9712f69cd292f9e88faba91 by=claude-author -->
  Review by claude-reviewer: faithful (report `reports/Dissertation.WellPosedness.System.Coeffs.addDrift--claude-reviewer--2026-10-17T16_00_01Z.md`).
  <!-- def-review: MVFBSDEJ.WellPosedness.System.Coeffs.addDrift 666b78c0f9712f69cd292f9e88faba91 by=claude-reviewer -->
  Review by claude-auditor: faithful (report `reports/Dissertation.WellPosedness.System.Coeffs.addDrift--claude-auditor--2026-10-19T03_36_17Z.md`).
  <!-- def-review: MVFBSDEJ.WellPosedness.System.Coeffs.addDrift 666b78c0f9712f69cd292f9e88faba91 by=claude-auditor -->
* `WellPosedness.System.singularDrift t`: the vector `(√t)⁻¹ ∈ ℝ¹`, which is `t^{-1/2}` for
  `t > 0` and `0` for `t ≤ 0` (Lean's `√t = 0` and `0⁻¹ = 0`); the drift `t^{-1/2}`, whose value
  at `t = 0` is not defined and does not affect any integral against `dt`.
  <!-- def-review: MVFBSDEJ.WellPosedness.System.singularDrift 52bed42bcf81ba997be36c4ad7c8d90e by=claude-author -->
  Review by claude-reviewer: faithful (report `reports/Dissertation.WellPosedness.System.singularDrift--claude-reviewer--2026-10-17T15_50_57Z.md`).
  <!-- def-review: MVFBSDEJ.WellPosedness.System.singularDrift 52bed42bcf81ba997be36c4ad7c8d90e by=claude-reviewer -->
  Review by claude-auditor: faithful (report `reports/Dissertation.WellPosedness.System.singularDrift--claude-auditor--2026-10-19T03_36_54Z.md`).
  <!-- def-review: MVFBSDEJ.WellPosedness.System.singularDrift 52bed42bcf81ba997be36c4ad7c8d90e by=claude-auditor -->
* `WellPosedness.System.singularCoeffs`: the affine coefficients of Example 5.1(i) (`affineCoeffs`)
  taken at `n = m = 1`, `β₁ = 1`, `β₂ = 0`, `σ_c = 0`, `h_c = 0`, outside the example's `β₂ > 0`,
  with `singularDrift` added: `b = t^{-1/2} − y`, `σ = −z`, `h = −u`, `f = 0`, `g(x, ρ) = x`. The
  affine part satisfies Assumptions 2.2–2.5; with the drift added, Assumption 2.2 fails.
  <!-- def-review: MVFBSDEJ.WellPosedness.System.singularCoeffs 7e516c47c5a521634ba3c7cf935a2ca7 by=claude-author -->
  Review by claude-reviewer: faithful (report `reports/Dissertation.WellPosedness.System.singularCoeffs--claude-reviewer--2026-10-17T15_59_39Z.md`).
  <!-- def-review: MVFBSDEJ.WellPosedness.System.singularCoeffs 7e516c47c5a521634ba3c7cf935a2ca7 by=claude-reviewer -->
  Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.System.singularCoeffs--claude-auditor--2026-10-19T03_36_54Z.md`).
  <!-- def-review: MVFBSDEJ.WellPosedness.System.singularCoeffs 7e516c47c5a521634ba3c7cf935a2ca7 by=claude-auditor -->
* `PaperSpec.A.translateTuple r θ = (θ.1 + r, θ.2)`: the translation `(x, y, z, u) ↦ (x + r, y, z, u)`
  of the forward coordinate of `H`.
  <!-- def-review: MVFBSDEJ.PaperSpec.translateTuple 05a266e9013def67cdd0b97424fd4e8c by=claude-author -->
  Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.translateTuple--claude-auditor--2026-10-19T03_35_49Z.md`).
  <!-- def-review: MVFBSDEJ.PaperSpec.translateTuple 05a266e9013def67cdd0b97424fd4e8c by=claude-auditor -->
* `PaperSpec.A.translatedCoeffs C r T`: `ψ̃(t, θ, μ) = ψ(t, θ + r_t, lawP2 μ (translateTuple r_t))`
  for `ψ ∈ {b, σ, h, f}` and `g̃(x, ρ) = g(x + r_T, lawP2 ρ (· + r_T))`. For `μ ∈ P₂` the
  translation is square integrable under `μ`, so `lawP2` returns the push-forward
  `μ ∘ (· + r)⁻¹` and not its fallback value: the coefficients of the state `X − r` when `X` solves
  the system with coefficients `C` and the drift `ṙ` added, the law argument translated
  accordingly, as Remark 3.4 describes for `r_t = 2√t e`.
  <!-- def-review: MVFBSDEJ.PaperSpec.translatedCoeffs 31edf12a7565d595f40d8fb3a4647dd0 by=claude-author -->
  Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.translatedCoeffs--claude-auditor--2026-10-19T03_35_50Z.md`).
  <!-- def-review: MVFBSDEJ.PaperSpec.translatedCoeffs 31edf12a7565d595f40d8fb3a4647dd0 by=claude-auditor -->

## the linear backward equation and the frozen step of Lemma 4.2 (`MVFBSDEJ/WellPosedness/BrownianPoisson/Hypotheses.lean`, `MVFBSDEJ/PaperSpec/Sec4Horizon.lean`)

* `LinearBSDEJ D ℱ hℱW hℱN T ξ φ Y Z U`: `Y` is adapted to `ℱ` with every path right-continuous;
  `Z`, `U`, `φ` are jointly measurable, progressive (`U` marked progressive), vanish off `[0, T]`
  and have finite energy there; `ξ ∈ L²`; and almost surely at each `t ∈ [0, T]`,
  `Y_t = ξ + ∫_t^T φ_s ds − (∫_0^T Z dW − ∫_0^t Z dW) − (∫_0^T ∫_E U Ñ − ∫_0^t ∫_E U Ñ)`, with the
  library's Brownian and compensated Poisson integrals for `ℱ` (reviewed with the driver): a
  solution of the linear backward equation with jumps with the given drift, with `Y` adapted and
  right-continuous as Lemma 4.1 assumes (its left limits exist almost surely, from the equation);
  `Y ∈ S²` is a conclusion of Lemma 4.1, not part of the notion. `.mk` is its constructor.
  <!-- def-review: MVFBSDEJ.WellPosedness.BrownianPoisson.LinearBSDEJ 61bb9f1d9c8aba870000000000000000 by=claude-author -->
  Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.BrownianPoisson.LinearBSDEJ--claude-reviewer--2026-10-17T16_00_39Z.md`).
  <!-- def-review: MVFBSDEJ.WellPosedness.BrownianPoisson.LinearBSDEJ 61bb9f1d9c8aba870000000000000000 by=claude-reviewer -->
  Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.BrownianPoisson.LinearBSDEJ--claude-auditor--2026-10-19T03_35_53Z.md`).
  <!-- def-review: MVFBSDEJ.WellPosedness.BrownianPoisson.LinearBSDEJ 61bb9f1d9c8aba870000000000000000 by=claude-auditor -->
  <!-- def-review: MVFBSDEJ.WellPosedness.BrownianPoisson.LinearBSDEJ.mk 0257a8785c1bb61f0000000000000000 by=claude-author -->
  Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.BrownianPoisson.LinearBSDEJ.mk--claude-reviewer--2026-10-17T12_27_45Z.md`).
  <!-- def-review: MVFBSDEJ.WellPosedness.BrownianPoisson.LinearBSDEJ.mk 0257a8785c1bb61f0000000000000000 by=claude-reviewer -->
  Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.BrownianPoisson.LinearBSDEJ.mk--claude-auditor--2026-10-19T03_35_59Z.md`).
  <!-- def-review: MVFBSDEJ.WellPosedness.BrownianPoisson.LinearBSDEJ.mk 0257a8785c1bb61f0000000000000000 by=claude-auditor -->
* `PaperSpec.A.BrownianFrozenStep 𝒢₀ D h𝒢₀ hind₀ T C X Y Z U X' Y' Z' U'`, for `n = m = d = 1`, `E` a
  point and `ν = 0`, over `enlJoint 𝒢₀ D h𝒢₀`: each coordinate of `X'` solves `LinearFSDEJ` with
  initial value `0`, drift `driftProc` and diffusion `diffusionProc` of `C` along the trial
  `(X, Y, Z, U)` and Poisson integrand `0`, and each coordinate of `(Y', Z', U')` solves
  `LinearBSDEJ` with terminal value `terminalVal` of `C` at `X'_T` (`g(X̄_T, Law(X̄_T))`) and drift
  `driverProc` of `C` along the trial. This is (4.7)–(4.8) at `λ = 1`, `q = 0`, `ξ₀ = 0`; with
  `ν = 0` the compensated Poisson integral in (4.7) vanishes, so the integrand `0` loses nothing.
  The output is a relation, not a function; the forward and backward linear equations determine it
  up to the identification of `ℍ`.
  <!-- def-review: MVFBSDEJ.PaperSpec.BrownianFrozenStep 638702db50f83c537b65e82c8eb52419 by=claude-author -->
  Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.BrownianFrozenStep--claude-reviewer--2026-10-17T12_18_02Z.md`).
  <!-- def-review: MVFBSDEJ.PaperSpec.BrownianFrozenStep 638702db50f83c537b65e82c8eb52419 by=claude-reviewer -->
  Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.BrownianFrozenStep--claude-auditor--2026-10-19T03_35_46Z.md`).
  <!-- def-review: MVFBSDEJ.PaperSpec.BrownianFrozenStep 638702db50f83c537b65e82c8eb52419 by=claude-auditor -->

## The Brownian forms of Example 5.2 (`MVFBSDEJ/WellPosedness/Spec/BrownianForms.lean`, `MVFBSDEJ/PaperSpec/Sec5BrownianReduction.lean`, `MVFBSDEJ/WellPosedness/Examples/BrownianFiltration.lean`)

* `WellPosedness.Existence.enlBrownian 𝒢₀ W h𝒢₀`: `augFiltration (W.naturalFiltration ⊔
  Filtration.const ℝ 𝒢₀ h𝒢₀).rightCont P`, the usual augmentation (right-continuous version,
  augmented by the `P`-null sets) of `t ↦ ℱ^W_t ⊔ 𝒢₀`: the filtration generated by the Brownian
  motion `W` and the initial σ-algebra `𝒢₀`. It is the expression of clause (a) of
  `ex_brownian`, written as an abbreviation.
  <!-- def-review: MVFBSDEJ.WellPosedness.Existence.enlBrownian 5721f67c4734358587f5377d953b5ca1 by=claude-author -->
  Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.Existence.enlBrownian--claude-reviewer--2026-10-17T16_00_09Z.md`).
  <!-- def-review: MVFBSDEJ.WellPosedness.Existence.enlBrownian 5721f67c4734358587f5377d953b5ca1 by=claude-reviewer -->
  Review by claude-auditor: faithful (report `reports/Dissertation.WellPosedness.Existence.enlBrownian--claude-auditor--2026-10-19T03_34_13Z.md`).
  <!-- def-review: MVFBSDEJ.WellPosedness.Existence.enlBrownian 5721f67c4734358587f5377d953b5ca1 by=claude-auditor -->
* `WellPosedness.Spec.BrownianLipInteriorAt ℱ P t L C`, for `C : Coeffs 0 n m d`:
  `LipInteriorAt ℱ P t L C` with the terms `‖C.h t Θ μ − C.h t Θ' μ'‖` and `‖δU‖` deleted and
  `w2H μ μ'` replaced by `w2P (projP2 μ) (projP2 μ')`: for all `(Θ, μ), (Θ', μ') ∈ 𝒟_t`
  (`diagonalInputs 0 n m d ℱ P t`), almost surely
  `|δb| + |δσ|_F + |δf| ≤ L (|δX| + |δY| + |δZ|_F + W₂(μ^{XYZ}, μ'^{XYZ}))`, the coefficients at
  `t`, with `W₂` that of the laws of `(X, Y, Z)` on `ReducedTuple n m d`.
  <!-- def-review: MVFBSDEJ.WellPosedness.Spec.BrownianLipInteriorAt 9a9ab559e6b2be35f13fe13e5b1fc588 by=claude-author -->
  Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.Spec.BrownianLipInteriorAt--claude-reviewer--2026-10-17T16_00_30Z.md`).
  <!-- def-review: MVFBSDEJ.WellPosedness.Spec.BrownianLipInteriorAt 9a9ab559e6b2be35f13fe13e5b1fc588 by=claude-reviewer -->
  Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.Spec.BrownianLipInteriorAt--claude-auditor--2026-10-19T03_34_13Z.md`).
  <!-- def-review: MVFBSDEJ.WellPosedness.Spec.BrownianLipInteriorAt 9a9ab559e6b2be35f13fe13e5b1fc588 by=claude-auditor -->
* `WellPosedness.Spec.BrownianLipInterior ℱ P T L C`: `BrownianLipInteriorAt ℱ P t L C` for
  almost every `t ∈ [0, T]` (Lebesgue measure restricted to `Icc 0 T`), as `LipInterior` is for
  `LipInteriorAt`.
  <!-- def-review: MVFBSDEJ.WellPosedness.Spec.BrownianLipInterior 9a9ab559e6b2be355d289558f2916b67 by=claude-author -->
  Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.Spec.BrownianLipInterior--claude-reviewer--2026-10-17T16_00_24Z.md`).
  <!-- def-review: MVFBSDEJ.WellPosedness.Spec.BrownianLipInterior 9a9ab559e6b2be355d289558f2916b67 by=claude-reviewer -->
  Review by claude-auditor: faithful (report `reports/Dissertation.WellPosedness.Spec.BrownianLipInterior--claude-auditor--2026-10-19T03_34_13Z.md`).
  <!-- def-review: MVFBSDEJ.WellPosedness.Spec.BrownianLipInterior 9a9ab559e6b2be355d289558f2916b67 by=claude-auditor -->
* `WellPosedness.Spec.BrownianAssumption23 ℱ P T L C`: `0 ≤ L ∧ BrownianLipInterior ℱ P T L C ∧
  LipTerminal ℱ P T L C.g`, the three fields of `Assumption23` with the interior bound replaced
  by its Brownian form; the terminal bound (2.6) has no jump term and is unchanged.
  <!-- def-review: MVFBSDEJ.WellPosedness.Spec.BrownianAssumption23 9a9ab559e6b2be35613ba6068888a4ec by=claude-author -->
  Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.Spec.BrownianAssumption23--claude-reviewer--2026-10-17T16_00_19Z.md`).
  <!-- def-review: MVFBSDEJ.WellPosedness.Spec.BrownianAssumption23 9a9ab559e6b2be35613ba6068888a4ec by=claude-reviewer -->
  Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.Spec.BrownianAssumption23--claude-auditor--2026-10-19T03_34_13Z.md`).
  <!-- def-review: MVFBSDEJ.WellPosedness.Spec.BrownianAssumption23 9a9ab559e6b2be35613ba6068888a4ec by=claude-auditor -->
* `WellPosedness.Spec.brownianPairing G C t θ θ' μ μ'`:
  `⟨δb, Gᵀ δY⟩ + ⟨δσ, Gᵀ δZ⟩_F + ⟨−δf, G δX⟩` with `δψ = ψ(t, θ, μ) − ψ(t, θ', μ')`, through
  `GX Gᵀ`, `GZ Gᵀ`, `GX G`: `pairing27` without its last term
  `∫_E ⟨δh(e), Gᵀ δU(e)⟩ ν(de)`.
  <!-- def-review: MVFBSDEJ.WellPosedness.Spec.brownianPairing 0c1bc774565270e3a8e6259ff280c701 by=claude-author -->
  Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.Spec.brownianPairing--claude-reviewer--2026-10-17T16_01_16Z.md`).
  <!-- def-review: MVFBSDEJ.WellPosedness.Spec.brownianPairing 0c1bc774565270e3a8e6259ff280c701 by=claude-reviewer -->
  Review by claude-auditor: faithful (report `reports/Dissertation.WellPosedness.Spec.brownianPairing--claude-auditor--2026-10-19T03_34_13Z.md`).
  <!-- def-review: MVFBSDEJ.WellPosedness.Spec.brownianPairing 0c1bc774565270e3a8e6259ff280c701 by=claude-auditor -->
* `WellPosedness.Spec.BrownianMonoAt ℱ P t G β₁ β₂ C`: `Mono27At` with `brownianPairing` in place
  of `pairing27` and the term `‖GU Gᵀ ν δU‖²` deleted from the first expectation of the right
  side: for all `(Θ, μ), (Θ', μ') ∈ 𝒟_t`, the pairing is integrable and
  `𝔼[⟨δb, Gᵀ δY⟩ + ⟨δσ, Gᵀ δZ⟩_F + ⟨−δf, G δX⟩] ≤ −β₁ 𝔼[|Gᵀ δY|² + |Gᵀ δZ|²_F] − β₂ 𝔼|G δX|²`.
  <!-- def-review: MVFBSDEJ.WellPosedness.Spec.BrownianMonoAt 22723559c045ea9d5b9977457e8292a1 by=claude-author -->
  Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.Spec.BrownianMonoAt--claude-reviewer--2026-10-17T16_00_44Z.md`).
  <!-- def-review: MVFBSDEJ.WellPosedness.Spec.BrownianMonoAt 22723559c045ea9d5b9977457e8292a1 by=claude-reviewer -->
  Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.Spec.BrownianMonoAt--claude-auditor--2026-10-19T03_34_13Z.md`).
  <!-- def-review: MVFBSDEJ.WellPosedness.Spec.BrownianMonoAt 22723559c045ea9d5b9977457e8292a1 by=claude-auditor -->
* `WellPosedness.Spec.BrownianAssumption25 ℱ P T G α β₁ β₂ C`: the conjunction of the terminal
  inequality of `Assumption25` (the field `terminal`, copied verbatim: integrability and
  `𝔼⟨δg_T, G δX_T⟩ ≥ α 𝔼|G δX_T|²` for all `X_T, X'_T ∈ L²(Ω, ℱ_T; ℝⁿ)`), `BrownianMonoAt` for
  almost every `t ∈ [0, T]`, and `Constants n m α β₁ β₂`: `Assumption25` with the interior
  inequality replaced by its Brownian form.
  <!-- def-review: MVFBSDEJ.WellPosedness.Spec.BrownianAssumption25 4eb7e54f1817fb74caf7612d2c8f94d9 by=claude-author -->
  Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.Spec.BrownianAssumption25--claude-reviewer--2026-10-17T16_00_55Z.md`).
  <!-- def-review: MVFBSDEJ.WellPosedness.Spec.BrownianAssumption25 4eb7e54f1817fb74caf7612d2c8f94d9 by=claude-reviewer -->
  Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.Spec.BrownianAssumption25--claude-auditor--2026-10-19T03_34_13Z.md`).
  <!-- def-review: MVFBSDEJ.WellPosedness.Spec.BrownianAssumption25 4eb7e54f1817fb74caf7612d2c8f94d9 by=claude-auditor -->
* `WellPosedness.Spec.BrownianPaperWeakSolution W ℱ hℱW T C ξ₀ X Y Z`, for a `d`-dimensional
  Brownian motion `W` whose coordinates are Brownian motions for `ℱ`: the fields of
  `PaperWeakSolutionInt` (with those of `PaperWeakTuple` and `PaperAdmissibleInt`) with `D.W`
  replaced by `W`, the fields of `U` and of `γ` and `jump_rep` deleted, every coefficient process
  taken along the zero jump integrand (`driftProc P T C X Y Z 0`, …) and the compensated Poisson
  integrals deleted from the identities: `X, Y` adapted, right-continuous on `[0, T)`, left
  limits a.s., of finite energy; `Z` predictable, vanishing off `[0, T]`, of finite energy; the
  drift and driver processes along `(X, Y, Z, 0)` jointly and progressively measurable with a.s.
  integrable paths, the diffusion process jointly and progressively measurable with finite energy;
  `X_T ∈ L²`; the two identities without the Poisson integrals. `BrownianPaperWeakSolution.mk` is
  its constructor.
  <!-- def-review: MVFBSDEJ.WellPosedness.Spec.BrownianPaperWeakSolution 016eda74a59f39fc0000000000000000 by=claude-author -->
  Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.Spec.BrownianPaperWeakSolution--claude-reviewer--2026-10-17T16_01_05Z.md`).
  <!-- def-review: MVFBSDEJ.WellPosedness.Spec.BrownianPaperWeakSolution 016eda74a59f39fc0000000000000000 by=claude-reviewer -->
  Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.Spec.BrownianPaperWeakSolution--claude-auditor--2026-10-19T03_34_13Z.md`).
  <!-- def-review: MVFBSDEJ.WellPosedness.Spec.BrownianPaperWeakSolution 016eda74a59f39fc0000000000000000 by=claude-auditor -->
  <!-- def-review: MVFBSDEJ.WellPosedness.Spec.BrownianPaperWeakSolution.mk 9f60bcd4483b94d90000000000000000 by=claude-author -->
  Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.WellPosedness.Spec.BrownianPaperWeakSolution.mk--claude-reviewer--2026-10-17T16_02_51Z.md`).
  <!-- def-review: MVFBSDEJ.WellPosedness.Spec.BrownianPaperWeakSolution.mk 9f60bcd4483b94d90000000000000000 by=claude-reviewer -->
  Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.WellPosedness.Spec.BrownianPaperWeakSolution.mk--claude-auditor--2026-10-19T03_34_13Z.md`).
  <!-- def-review: MVFBSDEJ.WellPosedness.Spec.BrownianPaperWeakSolution.mk 9f60bcd4483b94d90000000000000000 by=claude-auditor -->
* `PaperSpec.A.BrownianSolution W h𝒢₀ hW T C ξ₀ X Y Z`: `BrownianWeakSolution` together with
  `𝔼 sup_{t ≤ T} |X_t|² < ∞` and `𝔼 sup_{t ≤ T} |Y_t|² < ∞`: `PaperSpec.A.Solution` with the jump
  channel deleted, over the Brownian filtration. It is a notion of its own over a Brownian basis
  (the usual augmentation of the filtration generated by `W` and `𝒢₀`), not (1.1) at `h = 0` over
  a Brownian–Poisson basis. The coefficients keep the trivial channel `L²(0) = {0}` of
  `Coeffs (0 : Measure E)`, and that each `W_j` is a Brownian motion for this filtration is the
  parameter `hW`, which independence of `𝒢₀` and `W` gives.
  <!-- def-review: MVFBSDEJ.PaperSpec.BrownianSolution 4f65aba6aba7ed1f3790f3246b35f308 by=claude-author -->
  Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.BrownianSolution--claude-auditor--2026-10-19T05_48_40Z.md`).
  <!-- def-review: MVFBSDEJ.PaperSpec.BrownianSolution 4f65aba6aba7ed1f3790f3246b35f308 by=claude-auditor -->
* `PaperSpec.A.BrownianWeakSolution W h𝒢₀ hW T C ξ₀ X Y Z`: the same with
  `BrownianPaperWeakSolution`: `PaperSpec.A.WeakSolution` with the jump channel deleted.
  <!-- def-review: MVFBSDEJ.PaperSpec.BrownianWeakSolution 4f65aba6aba7ed1f1c8fd0d2955d1a89 by=claude-author -->
  Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.BrownianWeakSolution--claude-reviewer--2026-10-17T16_02_01Z.md`).
  <!-- def-review: MVFBSDEJ.PaperSpec.BrownianWeakSolution 4f65aba6aba7ed1f1c8fd0d2955d1a89 by=claude-reviewer -->
  Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.BrownianWeakSolution--claude-auditor--2026-10-19T03_34_12Z.md`).
  <!-- def-review: MVFBSDEJ.PaperSpec.BrownianWeakSolution 4f65aba6aba7ed1f1c8fd0d2955d1a89 by=claude-auditor -->
* `PaperSpec.A.RepresentsMartBrownian W h𝒢₀ hW T M Z`: `PaperSpec.A.RepresentsMart` with `U`, its
  three conditions and the compensated Poisson integral deleted, over `enlBrownian 𝒢₀ W h𝒢₀`:
  `Z` predictable, vanishing off `[0, T]`, of finite energy, and `M_t = M_0 + ∫_0^t Z dW`
  almost surely for every `t ∈ [0, T]`.
  <!-- def-review: MVFBSDEJ.PaperSpec.RepresentsMartBrownian 40f5a59e8126ece13d10efad24ece961 by=claude-author -->
  Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.RepresentsMartBrownian--claude-reviewer--2026-10-17T16_01_20Z.md`).
  <!-- def-review: MVFBSDEJ.PaperSpec.RepresentsMartBrownian 40f5a59e8126ece13d10efad24ece961 by=claude-reviewer -->
  Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.RepresentsMartBrownian--claude-auditor--2026-10-19T03_34_12Z.md`).
  <!-- def-review: MVFBSDEJ.PaperSpec.RepresentsMartBrownian 40f5a59e8126ece13d10efad24ece961 by=claude-auditor -->
