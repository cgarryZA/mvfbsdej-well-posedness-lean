# Reviews of the definitions the statements depend on

Every declaration of `Dissertation` or `LevyStochCalc` in the definition closure of a statement of
`Dissertation.PaperSpec` is read here against the mathematics it stands for. The marker records
the hash reviewed (type and value, proofs erased); a change reopens the entry. Mathlib and the
pinned upstream libraries are taken as foundations.

## Laws and the 2-Wasserstein distance (`Dissertation/Law/`)

* `IsCoupling μ ν γ`: `γ` is a measure on `E × E` with marginals `μ` and `ν` (`γ.fst = μ`,
  `γ.snd = ν`). The definition of a coupling (Villani, *Optimal transport*, Def. 1.1).
  <!-- def-review: Dissertation.Law.IsCoupling b0bdef6c32a05af44418b437fabafbee by=claude-author -->
* `transportCostSq γ = ∫⁻ ‖x − y‖² dγ` in `[0, ∞]`: the quadratic transport cost.
  <!-- def-review: Dissertation.Law.transportCostSq 26527e1b01e0a835bf6cd2c0e3b72557 by=claude-author -->
* `w2sq μ ν = inf over couplings γ of transportCostSq γ`: the squared 2-Wasserstein distance
  (Villani, Def. 6.1, `p = 2`), in `[0, ∞]`.
  <!-- def-review: Dissertation.Law.w2sq 6e694fea4529496c920fecf03305481e by=claude-author -->
* `w2 μ ν = √(w2sq μ ν).toReal`: the distance as a real number. An infinite squared distance is
  sent to `0`; on laws of finite second moment the squared distance is finite
  (`w2sq_ne_top`), so there `w2` is the 2-Wasserstein distance.
  <!-- def-review: Dissertation.Law.w2 d92ca7948d3f7f2f101d7b3c9f02c50c by=claude-author -->
* `secondMoment μ = ∫⁻ ‖x‖² dμ`: the second moment about the origin.
  <!-- def-review: Dissertation.Law.secondMoment f576c608076b2c8115cf34b105438676 by=claude-author -->
* `P2 E`, with constructor `P2.mk` and projection `P2.law`: a probability measure on `E` with
  finite second moment, i.e. an element of `P₂(E)`.
  <!-- def-review: Dissertation.Law.P2 d98c9fdcb43519180000000000000000 by=claude-author -->
  <!-- def-review: Dissertation.Law.P2.mk e023fd4949a53c620000000000000000 by=claude-author -->
  <!-- def-review: Dissertation.Law.P2.law 95237fec8092f7fab2f918509fc14ff5 by=claude-author -->
* `P2.dirac a`: the Dirac mass at `a`, an element of `P₂(E)`.
  <!-- def-review: Dissertation.Law.P2.dirac 75de1c8e6f6e6877f394cd3c14d76536 by=claude-author -->
* `w2P μ ν = w2 μ.law ν.law`: the 2-Wasserstein distance on `P₂(E)` for the norm of `E`.
  <!-- def-review: Dissertation.Law.w2P 588aff30f5cf1efb222cb5540209de44 by=claude-author -->
* `lawP2 P Θ`: the law `P ∘ Θ⁻¹` of `Θ` when `Θ ∈ L²(P)`, and `δ₀` otherwise. The manuscripts
  take laws of square-integrable variables only; the value off `L²` is a convention, and a
  statement quantifying over `L²` variables never reaches it (`REPRESENTATION_CHOICES.md` R9).
  <!-- def-review: Dissertation.Law.lawP2 8e02ec4a91100180227c044dc87cf8fe by=claude-author -->

## The tuple space (`Dissertation/WellPosedness/`)

* `Tuple HX HY HZY HUY = HX × HY × HZY × HUY`, the product of the four channels, with the
  maximum of the channel norms (Mathlib's product norm).
  <!-- def-review: Dissertation.WellPosedness.Tuple efc2de5eec83280ededc740a2b5da27e by=claude-author -->
* `TupleH ν n m d`: the channels `ℝⁿ`, `ℝᵐ`, `ℝ^{m×d}` and `L²(ν; ℝᵐ)`, as
  `EuclideanSpace ℝ (Fin n)`, `EuclideanSpace ℝ (Fin m)`, `EuclideanSpace ℝ (Fin m × Fin d)`
  (whose norm is the Frobenius norm) and `Lp (EuclideanSpace ℝ (Fin m)) 2 ν`: the space `H` of the
  well-posedness paper, §2.
  <!-- def-review: Dissertation.WellPosedness.System.TupleH fd49e3c7112f4155a292d8ceeae04f54 by=claude-author -->
* `lpMeasurableSpace`: the Borel σ-algebra on `L²(ν; F)`.
  <!-- def-review: Dissertation.WellPosedness.System.lpMeasurableSpace fee4e2519c9a83360a35b3d1a9e70db3 by=claude-author -->
* `TupleL2 HX HY HZY HUY`: the same four channels combined as nested `ℓ²` products
  (`WithLp 2`), so that `‖θ‖² = ‖x‖² + ‖y‖² + ‖z‖² + ‖u‖²`: `H` with its Hilbert norm.
  <!-- def-review: Dissertation.WellPosedness.System.TupleL2 5c620c846d4820ad66b1a5b8e7220ca2 by=claude-author -->
* `toL2 θ`: the identity of the underlying set, from the product with the maximum norm to the
  product with the Hilbert norm.
  <!-- def-review: Dissertation.WellPosedness.System.toL2 1b85677bb776b2573729ab86adfa97aa by=claude-author -->
* `w2H μ μ' = w2 (μ.law.map toL2) (μ'.law.map toL2)`: the 2-Wasserstein distance on `P₂(H)`
  for the Hilbert norm of `H`, the distance of the manuscript's §2.
  <!-- def-review: Dissertation.WellPosedness.System.w2H 9b325b0ab6c710a41121705bb1470821 by=claude-author -->

## Brownian motion and its filtrations (`LevyStochCalc/Brownian/`)

<!-- def-review: LevyStochCalc.Brownian.BrownianMotion caf7babc7d9b82d50000000000000000 by=claude-author -->
<!-- def-review: LevyStochCalc.Brownian.BrownianMotion.W 37fa09fc2e9f5aed48543ee8d8bbca0f by=claude-author -->
<!-- def-review: LevyStochCalc.Brownian.BrownianMotion.mk a9e961694b283fba0000000000000000 by=claude-author -->
<!-- def-review: LevyStochCalc.Brownian.IsBrownianFiltration 6b9d7c4909eee8db0000000000000000 by=claude-author -->
<!-- def-review: LevyStochCalc.Brownian.IsBrownianFiltration.mk 72b9d0c6dbc50a990000000000000000 by=claude-author -->
<!-- def-review: LevyStochCalc.Brownian.sigmaBrownian badc0e2b10ae37cadc199bed86170e9f by=claude-author -->
<!-- def-review: LevyStochCalc.Brownian.Martingale.naturalFiltration 54bfb40f60b0a75070cf2269380f1d3d by=claude-author -->
<!-- def-review: LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion 3b79773f55ea8d890000000000000000 by=claude-author -->
<!-- def-review: LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.W 1cfeb648b43624357bd81521c555728a by=claude-author -->
<!-- def-review: LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.mk 2f29b9a2ad355ba10000000000000000 by=claude-author -->
<!-- def-review: LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.naturalFiltration 925f72cc1b0a3caef8e2abe005107ea4 by=claude-author -->

## The Poisson random measure and its filtrations (`LevyStochCalc/Poisson/`)

<!-- def-review: LevyStochCalc.Poisson.referenceIntensity 22b0e836f3d3268f75c31fc958e5d10d by=claude-author -->
<!-- def-review: LevyStochCalc.Poisson.poissonMeasureENN 599fddfd2c12e9e4b502f9d73d19721c by=claude-author -->
<!-- def-review: LevyStochCalc.Poisson.PoissonRandomMeasure 351b24f2cb8b3f890000000000000000 by=claude-author -->
<!-- def-review: LevyStochCalc.Poisson.PoissonRandomMeasure.N d7f846758c36ed7d92e849bb24beb4db by=claude-author -->
<!-- def-review: LevyStochCalc.Poisson.PoissonRandomMeasure.mk 9e96bd1e7398d9ca0000000000000000 by=claude-author -->
<!-- def-review: LevyStochCalc.Poisson.PoissonRandomMeasure.compensated 98b57d8ea9507e8faf4b33861dc8f3a1 by=claude-author -->
<!-- def-review: LevyStochCalc.Poisson.IsPoissonFiltration e2b9154a25a8113f0000000000000000 by=claude-author -->
<!-- def-review: LevyStochCalc.Poisson.IsPoissonFiltration.mk 32b14d502e31e2800000000000000000 by=claude-author -->
<!-- def-review: LevyStochCalc.Poisson.naturalFiltration b85445b099adc2b315a246d0941d25b6 by=claude-author -->

## The driver and the filtration of the paper

<!-- def-review: LevyStochCalc.Driver.LevyDriver 62718398086e79200000000000000000 by=claude-author -->
<!-- def-review: LevyStochCalc.Driver.LevyDriver.N 5a083be1dafe7d36f9ed1dcbab2d13fc by=claude-author -->
<!-- def-review: LevyStochCalc.Driver.LevyDriver.W a4417688f8409d5aea3c41b147d06901 by=claude-author -->
<!-- def-review: LevyStochCalc.Driver.LevyDriver.mk 8b4f158ed4b608ae0000000000000000 by=claude-author -->
<!-- def-review: LevyStochCalc.Driver.sigmaPoisson a2a2909ee119ac9ac46169345dbcc2fe by=claude-author -->
<!-- def-review: LevyStochCalc.Driver.LevyDriver.filtration 1788864ffc8d4806240c2702eece8252 by=claude-author -->
<!-- def-review: LevyStochCalc.Probability.aug 14d37d0154cad2a45462fbc0e9dca39d by=claude-author -->
<!-- def-review: LevyStochCalc.Brownian.augFiltration 62f593ac7205c9672616e31e5936c2fa by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.Enlarged.initJoint c9ac55281f8264f86774558053262866 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.Enlarged.enlJoint c9ac55281f8264f8917f56a053f4c361 by=claude-author -->

## Measurability classes of processes (`LevyStochCalc/Probability/`)

<!-- def-review: LevyStochCalc.Probability.ProgressivelyMeasurable 29ce1b1b7a20e5156d5f9c33b358fa7f by=claude-author -->
<!-- def-review: LevyStochCalc.Probability.MarkedProgressivelyMeasurable 3768ee472ea8756ac41aefffc2091b0b by=claude-author -->
<!-- def-review: LevyStochCalc.Probability.predictableSigma 9af29befcf36c1f234d23c2a4611da87 by=claude-author -->
<!-- def-review: LevyStochCalc.Probability.Predictable 15a7903d5fe90c1df6412e0a501eaa5b by=claude-author -->
<!-- def-review: LevyStochCalc.Probability.markedPredictableRect 87996b432b2b8cfe106f0f7a940c10d8 by=claude-author -->
<!-- def-review: LevyStochCalc.Probability.markedPredictableSigma 802b939730e12ea992958da67e6f2150 by=claude-author -->
<!-- def-review: LevyStochCalc.Probability.MarkedPredictable 35cc10827f7a7db887e9099b1605e255 by=claude-author -->

## The Brownian Itô integral (`LevyStochCalc/Brownian/Ito*`)

<!-- def-review: LevyStochCalc.Brownian.Ito.energy d863e7f664002259c7c4c422b7f327c7 by=claude-author -->
<!-- def-review: LevyStochCalc.Brownian.Ito.SimplePredictable 095844f503e4a7e50000000000000000 by=claude-author -->
<!-- def-review: LevyStochCalc.Brownian.Ito.SimplePredictable.N 12c9ba642316c53035aaa7419ff6e7e7 by=claude-author -->
<!-- def-review: LevyStochCalc.Brownian.Ito.SimplePredictable.partition 8d3a8228f2eaa5da0cf79dfff5cea25d by=claude-author -->
<!-- def-review: LevyStochCalc.Brownian.Ito.SimplePredictable.ξ a05453682c8999447dd6f53efb617007 by=claude-author -->
<!-- def-review: LevyStochCalc.Brownian.Ito.SimplePredictable.mk 25ac9f29c6c3f9220000000000000000 by=claude-author -->
<!-- def-review: LevyStochCalc.Brownian.Ito.SimplePredictable.eval 3d79b84163943973343eb497386c5538 by=claude-author -->
<!-- def-review: LevyStochCalc.Brownian.Ito.simpleIntegral 1a897ae182e91c2d9e8ab5364d5848bb by=claude-author -->
<!-- def-review: LevyStochCalc.Brownian.Ito.masterApprox 8590dd88f726df792bc395a002d2695e by=claude-author -->
<!-- def-review: LevyStochCalc.Brownian.Ito.masterLp ed9f750f32d4e782710be84c23dfa758 by=claude-author -->
<!-- def-review: LevyStochCalc.Brownian.Ito.stochasticIntegralBrownianLp 06fc0ca46cd58663ccf8a97ed9638128 by=claude-author -->
<!-- def-review: LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian 2c173e4f8affd8d994743b6229ec7957 by=claude-author -->
<!-- def-review: LevyStochCalc.Brownian.Ito.stochasticIntegral 2c173e4f8affd8d9fb9c03a2213aee2d by=claude-author -->
<!-- def-review: LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral 7a8c23649dc43d3d0eb5bb888b122b88 by=claude-author -->

## The compensated Poisson integral (`LevyStochCalc/Poisson/Compensated*`, `MarkStep*`)

<!-- def-review: LevyStochCalc.Poisson.Compensated.markedEnergy 2cb843d4d0d59f2db65e60392e647c8a by=claude-author -->
<!-- def-review: LevyStochCalc.Poisson.Compensated.TimeGrid f743d5d40f14218f0000000000000000 by=claude-author -->
<!-- def-review: LevyStochCalc.Poisson.Compensated.TimeGrid.N₀ 96a3829b277b5ce438918b7312dbff61 by=claude-author -->
<!-- def-review: LevyStochCalc.Poisson.Compensated.TimeGrid.p 57d3a20338cbc4687e319ddece66a22f by=claude-author -->
<!-- def-review: LevyStochCalc.Poisson.Compensated.TimeGrid.mk 33f8672dd33944890000000000000000 by=claude-author -->
<!-- def-review: LevyStochCalc.Poisson.Compensated.TimeGrid.dyadic 95a28fb6db0dc434182c96d67c581601 by=claude-author -->
<!-- def-review: LevyStochCalc.Poisson.Compensated.MarkStep a1ee2ea0e1457b990000000000000000 by=claude-author -->
<!-- def-review: LevyStochCalc.Poisson.Compensated.MarkStep.K 69b93339d92d0211761d8983c191e8a4 by=claude-author -->
<!-- def-review: LevyStochCalc.Poisson.Compensated.MarkStep.B cd1a4d6799bbdd79ee01c9f6b801a7a2 by=claude-author -->
<!-- def-review: LevyStochCalc.Poisson.Compensated.MarkStep.ξ 0be3e10909ab07b6258c2d3d03a8b983 by=claude-author -->
<!-- def-review: LevyStochCalc.Poisson.Compensated.MarkStep.mk 3c5a9069f74059b30000000000000000 by=claude-author -->
<!-- def-review: LevyStochCalc.Poisson.Compensated.MarkStep.Adapted ecd786abe075b89b145b9c7361973099 by=claude-author -->
<!-- def-review: LevyStochCalc.Poisson.Compensated.MarkStep.eval 29db58ad6d1eaba10f37be13a59482ea by=claude-author -->
<!-- def-review: LevyStochCalc.Poisson.Compensated.MarkStep.integral 3186dcea8bb974d243fe79cd74ac17f2 by=claude-author -->
<!-- def-review: LevyStochCalc.Poisson.Compensated.stageHorizon c8740e4d49db17c3a53710c3133d9af0 by=claude-author -->
<!-- def-review: LevyStochCalc.Poisson.Compensated.stageErr b9fbd75c3a71823527cf969f16cf7a60 by=claude-author -->
<!-- def-review: LevyStochCalc.Poisson.Compensated.master fe975a59e5bdb39048afe361b1d43cfe by=claude-author -->
<!-- def-review: LevyStochCalc.Poisson.Compensated.master._f 424be9f1c393f5ccd609f8b82c95bb19 by=claude-author -->
<!-- def-review: LevyStochCalc.Poisson.Compensated.master.match_1 39be9c3f3ff3768c322be17b50fb7b55 by=claude-author -->
<!-- def-review: LevyStochCalc.Poisson.Compensated.stageIntegral 684f75cf6cc2aa0c47441d48e213f8c3 by=claude-author -->
<!-- def-review: LevyStochCalc.Poisson.Compensated.stageLp 3b161903923f1566d14a46b6c0b141a8 by=claude-author -->
<!-- def-review: LevyStochCalc.Poisson.Compensated.processLp f8fb86e34b629e10db696374a7fa3068 by=claude-author -->
<!-- def-review: LevyStochCalc.Poisson.Compensated.process 0f01c66ebd3c9ea130e0117d5d2cc43b by=claude-author -->
<!-- def-review: LevyStochCalc.Poisson.Compensated.stochasticIntegral 0f01c66ebd3c9ea16c0e39e9314f702b by=claude-author -->

## Laws with the Wasserstein topology and the `L²(ν)` representative

<!-- def-review: Dissertation.Law.P2W d98c9fdcb4351918cf1dd08443113a27 by=claude-author -->
<!-- def-review: Dissertation.Law.P2.toP2W 0f7eb5b8b5cd79140f4d89429f83896b by=claude-author -->
<!-- def-review: Dissertation.Law.P2W.toP2 99b2138b782dec9c2e3540286ca704ff by=claude-author -->
<!-- def-review: Dissertation.Law.P2W.instPseudoMetricSpace d8135c73ef7d5f4d483de4c4ee2c3223 by=claude-author -->
<!-- def-review: Dissertation.Law.P2.mapOfLe eacf22aaa85ca476d2e3ad477d111a93 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.System.lawToL2 4034513072b6f988f8b3198000db33c5 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.System.P2WH 8b570604f2bfe77f0b8346109edf1c66 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.System.P2WH.toP2 b2c514cdcbc3e600531d47474362065f by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.System.P2WH.instPseudoMetricSpace 82d8357fc285df8b92c2893645916ccb by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.System.TupleP2WH 18ca34ab14491b05044bed0aa14c68fb by=claude-author -->
<!-- def-review: Dissertation.Law.lpRep 4d8f19766d30be6bf897d6959240d0e7 by=claude-author -->

## The coefficients, the tuple and the coupling matrix (`Dissertation/WellPosedness/System/`)

<!-- def-review: Dissertation.WellPosedness.System.Coeffs fd49e3c7112f41550000000000000000 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.System.Coeffs.b dc86c23810efa40cc43dc5c78836ad86 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.System.Coeffs.σ b8b7ad45d5043ac9ea56b20d79cc8746 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.System.Coeffs.h c58d95cc2421d2507fe92427d04f5611 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.System.Coeffs.f e2af0d025a8b0b0a1f17d136a425c783 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.System.Coeffs.g 0e65b7c74973b4bd44624f07d09771b2 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.System.Coeffs.mk 53675b51c8cc7afa0000000000000000 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.System.uLift 20342aeccd26489f2122117451a2a160 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.System.tupleAt 0b900ec4a75a6b31755afe5c94aee280 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.System.leftLimProc 9171262935c3b1fde4f555261cd0b9ba by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.System.diagonalInputs 43fba323e088abc4f9c7fc5ffd25f8a4 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.System.GX 63e2a9453a1500d8567ae4e516472ab8 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.System.GZ c2eb31a2cb944229321c531fa6d8a32a by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.System.GU af77e6209c5a6f02054d4dc4b9937972 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.System.sMin 42b2e53d2f710588e25de988c32456ea by=claude-author -->

## Coefficient processes and sizes

<!-- def-review: Dissertation.WellPosedness.System.driftProc 12c9183ed27748868bc8011ce72cfb14 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.System.diffusionProc 38de1bfa70e0d9f65621b71beed53a93 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.System.driverProc 1491f35f9b5cef0eabae931fed61c587 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.System.terminalVal 553a1e2dd57f8bc4ed26c8f55d7a65f7 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.System.jumpProc bfa4317d32adaf7b2cab0921e18838d1 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.Existence.coeffJump 90dd30b497d4dd12d6d4dda771a35c05 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.Stability.esq 6cf496fa6f75fac11490c95295dbf617 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.Stability.supSize 8d946a220ee9b35c3ccfc7f258215a40 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.Stability.dataSize f5b22d1ca3f4de88514ab122da58813f by=claude-author -->

## Assumptions 2.2–2.5 and (2.3) (`Dissertation/WellPosedness/Spec/Assumptions.lean`)

<!-- def-review: Dissertation.WellPosedness.Spec.JointBorel 4b26c5076ea2f4260000000000000000 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.Spec.JointBorel.mk 472156baffd503850000000000000000 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.Spec.OriginValues 4b26c5076ea2f4260000000000000000 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.Spec.OriginValues.mk 4f791247b92d220e0000000000000000 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.Spec.Assumption22 5efdb45a84324ede0000000000000000 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.Spec.Assumption22.mk f08ed69f41bd56a20000000000000000 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.Spec.LipInteriorAt 0d5048c72ef913b66bcf6ee4c960f28a by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.Spec.LipInterior 0d5048c72ef913b6b4ca87ec39905193 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.Spec.LipTerminal 50fea10a492649962d326ec49234e618 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.Spec.Assumption23 0d5048c72ef913b60000000000000000 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.Spec.Assumption23.mk 6c3bcf190c1a21530000000000000000 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.Constants 523a9f9cc9be2abd0000000000000000 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.Constants.mk 0851194a5962ef650000000000000000 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.Spec.pairing27 ede49a3a3551d3de0749c24d2bf7198b by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.Spec.Mono27At a59346236526d219b3e1099916102f71 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.Spec.Assumption25 2ad64300a1211b960000000000000000 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.Spec.Assumption25.mk 0f5949362ae546510000000000000000 by=claude-author -->

## The solution notion of §3

<!-- def-review: Dissertation.WellPosedness.System.PaperSolution 0dd47e8a79576bf20000000000000000 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.System.PaperSolution.mk 07f48ea7fa37d0240000000000000000 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.Existence.PaperSolutionEnl a03b8b3d0b5b5f35c55bf194cd675c69 by=claude-author -->
<!-- def-review: Dissertation.PaperSpec.A.Solution bf42c97d226817ae1c792ec3d931211c by=claude-author -->

## The weak solution notion of §3 (`ℍ_weak`)

<!-- def-review: Dissertation.WellPosedness.System.PaperWeakTuple f8659178ce7276550000000000000000 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.System.PaperWeakTuple.mk bd25e780ca59bc0f0000000000000000 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.System.PaperAdmissibleInt 6be52fa0d3961fab0000000000000000 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.System.PaperAdmissibleInt.mk 9e454a38d7aa3b8f0000000000000000 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.System.PaperWeakSolutionInt 0dd47e8a79576bf20000000000000000 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.System.PaperWeakSolutionInt.mk 88d41182691dfcb90000000000000000 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.Spec.PaperWeakSolutionIntEnl a03b8b3d0b5b5f35dc54c302d2c70a24 by=claude-author -->
<!-- def-review: Dissertation.PaperSpec.A.WeakSolution bf42c97d226817ae58445a0e39aa5d15 by=claude-author -->

## The drift (3.6) of Proposition 3.8 (`Dissertation/WellPosedness/ExpectedVsPointwise*.lean`)

<!-- def-review: Dissertation.WellPosedness.clamp01 29fbc050c7ff42ca65cda76e668193a3 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.System.clampVec 72826a95517d7c68486a411354533973 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.System.meanY b1bbcb6b80a91cb129a220d0bfbb8cc1 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.System.clampDrift b25f794b96410650c732095ab6aa7055 by=claude-author -->

## Corollary 3.6: the perturbation, the margin and the pairing bounds (`Spec/CorollaryHyps.lean`, `Spec/Cor36Law.lean`, `Robustness/Perturb.lean`)

<!-- def-review: Dissertation.WellPosedness.Spec.LawLip35 0d5048c72ef913b6c77335f6574c1c01 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.Spec.Margin213 2ad64300a1211b964de2010be9bc24c1 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.Spec.PairingBound34 2b1db421079e9e767580b40b6b9fa24b by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.System.Coeffs.TupleIndep bb2f84e84c27fd8b0000000000000000 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.System.Coeffs.TupleIndep.mk 54322416b320749b0000000000000000 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.System.Coeffs.perturb 4810e11e4c9f2ac6af25365b8feb2717 by=claude-author -->

## The `U`-marginal of a law (`Dissertation/Law/P2.lean`, `Dissertation/Law/TupleMarginal.lean`)

<!-- def-review: Dissertation.Law.P2.map ea792c02836fa5e80da2ef5c07e4b0e0 by=claude-author -->
<!-- def-review: Dissertation.Law.P2.margU 537c6d484c8f0e8b128e7c03175bc3a7 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.System.projUH 5ed7e50cc9210991ccbb6cdcbcc90dbb by=claude-author -->

## The forced system (4.1) and `WP(λ)` of §4

<!-- def-review: Dissertation.WellPosedness.System.Forcing a3ba59f5823fbe6a0000000000000000 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.System.Forcing.mk de3e0249fbf732c50000000000000000 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.System.PredForcing 467cf5000b974ed10000000000000000 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.System.PredForcing.mk 72571516b42bad8d0000000000000000 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.System.PaperSolutionForced 879f49cf215ebc960000000000000000 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.System.PaperSolutionForced.mk f826ed5f5757258c0000000000000000 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.System.PaperWeakSolutionForcedInt 879f49cf215ebc960000000000000000 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.System.PaperWeakSolutionForcedInt.mk abbc9a6411f109000000000000000000 by=claude-author -->
<!-- def-review: Dissertation.PaperSpec.A.ForcedSolution 6d8e8f373c5e26da1ce1add2f80b1ed8 by=claude-author -->
<!-- def-review: Dissertation.PaperSpec.A.WeakForcedSolution 6d8e8f373c5e26dad42e89a4945d5642 by=claude-author -->
<!-- def-review: Dissertation.PaperSpec.A.WP 4c83187e460bc5017fcd19712e7de906 by=claude-author -->

## The coefficient systems of Example 5.1 (`Existence/AffineExample.lean`, `Existence/ClampAffine.lean`, `Examples/MeanField.lean`)

<!-- def-review: Dissertation.WellPosedness.Existence.affineCoeffs f17e5fb23dc1dc13867a3e931c8f06af by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.Existence.clampAffineCoeffs 5dc0669bb7724f483dd7fd8e2ba08292 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.Existence.meanFieldCoeffs e170fd42ef8bf937a752d819f1e43056 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.System.barycentre 66075b028164ca3c9fd5e49e2c579b19 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.System.tupleMean f12c7462da3145629603ec2e2a9cd3c9 by=claude-author -->

## The reduced tuple space of Example 5.2 (`Examples/Brownian.lean`)

<!-- def-review: Dissertation.WellPosedness.System.ReducedTuple d68fe71f65d1320f648e397a6f92aa48 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.System.projB f41c30f5a4e6eb53b63a9ca646ce41dd by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.System.projP2 09e433978a0199240fd17c10afb2cd5e by=claude-author -->

## The perturbation of Example 5.4 (`PaperSpec/A/Sec5.lean`, `Robustness/Perturb.lean`)

<!-- def-review: Dissertation.PaperSpec.A.ex54Pert a358f11639418d450e7e870df0a64a0c by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.System.Coeffs.ofLaw 078c486754be7860fbd98d3584940f30 by=claude-author -->

## The crowding correction and the coefficients of Example 5.5 (`PaperSpec/A/Sec5.lean`, `Examples/Dealer/ExposureCoeffs.lean`)

<!-- def-review: Dissertation.PaperSpec.A.ex55Crowd 8d3f49063f9d40bd91804eeb64810052 by=claude-author -->
<!-- def-review: Dissertation.PaperSpec.A.ex55Coeffs 27812db92b9f6ca56f3c507797b09d6e by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.Existence.exposureOp 3029e746baaeff13a812ce9479e5168f by=claude-author -->

## The mark space of Example 5.5 and the linear forward equation (`Examples/Dealer/Marks.lean`, `Stability/ForwardEq.lean`)

<!-- def-review: Dissertation.WellPosedness.Existence.DealerMark f743d5d40f14218fb917137b1ad4a2ae by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.Existence.dealerMarks 96b401180d83fd5a2c4547d7b1f3b8b5 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.Existence.sizeLeb f531e248a597ba7e291a0506aba7a0a6 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.Stability.LinearFSDEJ 61bb9f1d9c8aba870000000000000000 by=claude-author -->
<!-- def-review: Dissertation.WellPosedness.Stability.LinearFSDEJ.mk 302302b2a85c5d690000000000000000 by=claude-author -->

## The weighted margin (2.12) (`PaperSpec/A/Sec2Remarks.lean`)

<!-- def-review: Dissertation.PaperSpec.A.Margin212 2ad64300a1211b9647d3727884567824 by=claude-author -->

## A representation of a martingale (`PaperSpec/A/Sec2Basics.lean`)

<!-- def-review: Dissertation.PaperSpec.A.RepresentsMart 596b7f79cacb7e809185e74555b5b132 by=claude-author -->

## The energy measures of the integrands (`LevyStochCalc/Brownian/`, `LevyStochCalc/Poisson/`)

* `LevyStochCalc.Brownian.Ito.energyMeasure P T = P ⊗ (Lebesgue on [0, T])` on `Ω × ℝ`, and
  `LevyStochCalc.Poisson.Compensated.markedEnergyMeasure P ν T = P ⊗ ((Lebesgue on [0, T]) ⊗ ν)`
  on `Ω × ℝ × E`: the measures `dP ⊗ dt` and `dP ⊗ dt ⊗ ν` of the `L²` classes of the integrands.
  <!-- def-review: LevyStochCalc.Brownian.Ito.energyMeasure 8bb90a671c0f63eba6329d346b422bc3 by=claude-author -->
  <!-- def-review: LevyStochCalc.Poisson.Compensated.markedEnergyMeasure 6a70d753259c930a27f458a6e2a44d87 by=claude-author -->

## Progressive tuples and cross-evaluation (`Dissertation/WellPosedness/Existence/WPZero.lean`, `Dissertation/WellPosedness/System/CrossEval.lean`, `Dissertation/WellPosedness/System/HilbertW2Space.lean`)

* `WellPosedness.Existence.ProgTuple ℱ P ν T X Y Z U`: `X, Y` adapted with right-continuous paths,
  `Z` jointly and progressively measurable, `U` jointly and marked progressively measurable, both
  of finite energy on `[0, T]`.
  <!-- def-review: Dissertation.WellPosedness.Existence.ProgTuple f8659178ce7276550000000000000000 by=claude-author -->
  <!-- def-review: Dissertation.WellPosedness.Existence.ProgTuple.mk e1108dc351d6859c0000000000000000 by=claude-author -->
* `WellPosedness.System.CrossEval ℱ P T C X Y Z U γ`: along the tuple, the drift, diffusion and
  driver processes of `C` are jointly and progressively measurable, and `γ` is a jointly
  measurable, marked progressively measurable representative of `e ↦ h(s, Θ_s, e, μ_s)` in
  `L²(ν)` for a.e. `s ∈ [0, T]`, a.s.
  <!-- def-review: Dissertation.WellPosedness.System.CrossEval c32e743968a018740000000000000000 by=claude-author -->
  <!-- def-review: Dissertation.WellPosedness.System.CrossEval.mk 73ff8f763f31638d0000000000000000 by=claude-author -->
* `WellPosedness.Existence.CoeffRegular ℱ P T C`: every progressive tuple has some `γ` with
  `CrossEval`: (2.5), the measurability of the coefficient evaluations along tuples.
  <!-- def-review: Dissertation.WellPosedness.Existence.CoeffRegular d55f353de2cd99bf9dda27c57cbbc263 by=claude-author -->
* `WellPosedness.System.P2WH.instMeasurableSpace`: the Borel σ-algebra of the Hilbert-norm
  2-Wasserstein topology on `P₂(H)`, the σ-algebra of "Borel law flows".
  <!-- def-review: Dissertation.WellPosedness.System.P2WH.instMeasurableSpace a4c49061e0a86f8748fc4dc167e3a85e by=claude-author -->

## Law flows and their tuples (`Dissertation/WellPosedness/System/LawFlow.lean`, `Dissertation/WellPosedness/System/HilbertW2Space.lean`)

* `WellPosedness.System.CadlagPredTuple ℱ P ν T X Y Z U`: `X, Y` adapted with right-continuous
  paths having left limits everywhere, `Z, U` predictable (marked predictable for `U`), and every
  coordinate of finite energy on `[0, T]`: the hypotheses of Lemma A.1 of the well-posedness
  paper.
  <!-- def-review: Dissertation.WellPosedness.System.CadlagPredTuple 36dfb143d7b151d50000000000000000 by=claude-author -->
  <!-- def-review: Dissertation.WellPosedness.System.CadlagPredTuple.mk b59a6e73ab9651290000000000000000 by=claude-author -->
* `Law.P2.toP2WH μ`: a law of finite second moment on the tuple space as a point of `P2WH`, the
  same laws with the Hilbert-norm 2-Wasserstein distance.
  <!-- def-review: Dissertation.Law.P2.toP2WH d1c4f8da3396bc50d397270158b14316 by=claude-author -->

## the system of Example 3.2 of Li and Min (`Dissertation/PaperSpec/A/Sec5Preamble.lean`)

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
  <!-- def-review: Dissertation.WellPosedness.System.liMinCoeffs 0d9a685aa46f2a71719d94d7674f9ea4 by=claude-author -->

## the weighted pairing bound of Remark 3.7 (`Dissertation/PaperSpec/A/Sec3GeneralRank.lean`)

* `PaperSpec.A.PairingBound34W ℱ P T G c p`: for almost every `t ∈ [0, T]` and all
  `(Θ, μ), (Θ', μ') ∈ 𝒟_t`, the pairing `pairing27 G p` of the perturbation differences (the
  left side of (3.4)) is integrable and its expectation is at most
  `c 𝔼[|Gᵀ δY|² + |Gᵀ δZ|²_F + ‖Gᵀ δU‖²_{L²(ν)} + |G δX|²]`: (3.4) with its right side recorded in
  the weighted quantity of (2.12), as Remark 3.7 prescribes. The integrability conjunct is the
  one of `PairingBound34`.
  <!-- def-review: Dissertation.PaperSpec.A.PairingBound34W 2b1db421079e9e76f26e2afdddf6a5b4 by=claude-author -->

## the singular drift of Remark 3.4 (`Dissertation/WellPosedness/Examples/SingularDrift.lean`)

* `WellPosedness.System.Coeffs.addDrift C c`: the coefficients `C` with the deterministic drift
  `c(t)` added to `b`, the other coefficients unchanged: "adding the deterministic drift … to the
  `b`" of Remark 3.4.
  <!-- def-review: Dissertation.WellPosedness.System.Coeffs.addDrift ebd318299326fb1ff7058f79aad54724 by=claude-author -->
* `WellPosedness.System.singularDrift t`: the vector `(√t)⁻¹ ∈ ℝ¹`, which is `t^{-1/2}` for
  `t > 0` and `0` for `t ≤ 0` (Lean's `√t = 0` and `0⁻¹ = 0`); the manuscript's `t^{-1/2}`, whose
  value at `t = 0` is not defined and does not affect any integral against `dt`.
  <!-- def-review: Dissertation.WellPosedness.System.singularDrift 52bed42bcf81ba997be36c4ad7c8d90e by=claude-author -->
* `WellPosedness.System.singularCoeffs`: Example 5.1(i) (`affineCoeffs`) at `n = m = 1`,
  `β₁ = 1`, `β₂ = 0`, `σ_c = 0`, `h_c = 0` with `singularDrift` added: `b = t^{-1/2} − y`,
  `σ = −z`, `h = −u`, `f = 0`, `g(x, ρ) = x`. One instance of the manuscript's "a system satisfying
  Assumptions 2.2–2.5" with the drift added.
  <!-- def-review: Dissertation.WellPosedness.System.singularCoeffs 9cbaca3d28850a562cb0f143b2b54981 by=claude-author -->

## the translated system of Remark 3.4 and the frozen step of Lemma 4.2 (`Dissertation/WellPosedness/BrownianPoisson/Hypotheses.lean`, `Dissertation/PaperSpec/A/Sec3Rem34.lean`, `Dissertation/PaperSpec/A/Sec4Horizon.lean`)

* `LinearBSDEJ D ℱ hℱW hℱN T ξ φ Y Z U`: `Y` is adapted to `ℱ` with every path right-continuous;
  `Z`, `U`, `φ` are jointly measurable, progressive (`U` marked progressive), vanish off `[0, T]`
  and have finite energy there; `ξ ∈ L²`; and almost surely at each `t ∈ [0, T]`,
  `Y_t = ξ + ∫_t^T φ_s ds − (∫_0^T Z dW − ∫_0^t Z dW) − (∫_0^T ∫_E U Ñ − ∫_0^t ∫_E U Ñ)`, with the
  library's Brownian and compensated Poisson integrals for `ℱ` (reviewed with the driver): a
  solution of the linear backward equation with jumps with the given drift, in the sense of the
  paper's `S²` processes except that `𝔼 sup |Y|²` is not part of it (the propositions that need it
  state it).
  <!-- def-review: Dissertation.WellPosedness.BrownianPoisson.LinearBSDEJ 61bb9f1d9c8aba870000000000000000 by=claude-author -->
  <!-- def-review: Dissertation.WellPosedness.BrownianPoisson.LinearBSDEJ.mk a259997f09ec23780000000000000000 by=claude-author -->
* `PaperSpec.A.translateTuple r θ = (θ.1 + r, θ.2)`: the translation `(x, y, z, u) ↦ (x + r, y, z, u)`
  of the forward coordinate of `H`.
  <!-- def-review: Dissertation.PaperSpec.A.translateTuple 25b128e1a8bd16214207e456ab04981b by=claude-author -->
* `PaperSpec.A.translatedCoeffs C r T`: `ψ̃(t, θ, μ) = ψ(t, θ + r_t, lawP2 μ (translateTuple r_t))`
  for `ψ ∈ {b, σ, h, f}` and `g̃(x, ρ) = g(x + r_T, lawP2 ρ (· + r_T))`. For `μ ∈ P₂` the
  translation is square integrable under `μ`, so `lawP2` returns the push-forward
  `μ ∘ (· + r)⁻¹` and not its fallback value: the coefficients of the state `X − r` when `X` solves
  the system with coefficients `C` and the drift `ṙ` added, the law argument translated
  accordingly, as the remark describes for `r_t = 2√t e`.
  <!-- def-review: Dissertation.PaperSpec.A.translatedCoeffs a6d589d1c49f1879976bb03fd33b7999 by=claude-author -->
* `PaperSpec.A.BrownianFrozenStep 𝒢₀ D h𝒢₀ hind₀ T C X Y Z U X' Y' Z' U'`, for `n = m = d = 1`, `E` a
  point and `ν = 0`, over `enlJoint 𝒢₀ D h𝒢₀`: each coordinate of `X'` solves `LinearFSDEJ` with
  initial value `0`, drift `driftProc` and diffusion `diffusionProc` of `C` along the trial
  `(X, Y, Z, U)` and Poisson integrand `0`, and each coordinate of `(Y', Z', U')` solves
  `LinearBSDEJ` with terminal value `terminalVal` of `C` at `X'_T` (`g(X̄_T, Law(X̄_T))`) and drift
  `driverProc` of `C` along the trial. This is (4.10)–(4.11) at `λ = 1`, `q = 0`, `ξ₀ = 0`; with
  `ν = 0` the compensated Poisson integral in (4.10) vanishes, so the integrand `0` loses nothing.
  The output is a relation, not a function; the forward and backward linear equations determine it
  up to the identification of `ℍ`.
  <!-- def-review: Dissertation.PaperSpec.A.BrownianFrozenStep 98bd6b9787534217c971d1dc13a30cc3 by=claude-author -->
