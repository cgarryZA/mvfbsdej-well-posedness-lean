### A:cor:robust, A:eq:forced, A:eq:mvfbsdej, A:ex:brownian, A:ex:concrete, A:intro:mvfbsdej, A:lem:bpbsde, A:lem:cont, A:lem:pert, A:lem:small, A:rem:cwp-class, A:rem:generalrank, A:sec2:prp, A:sec4:WP-def, A:sec4:horizon-not-contractive, A:sec:examples, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: LevyStochCalc.Brownian.Ito.SimplePredictable.mk
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 25ac9f29c6c3f9220000000000000000 (pl-fp-v1:4e20d3a8f4edb6015e4083ee5e0acc8a2b919d7ed281d56857dd441d8de6cab4)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:02:24Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:34:24Z):
Reading for def:LevyStochCalc.Brownian.Ito.SimplePredictable.mk (written before seeing any Lean).

Paper notion. The constructor of a simple predictable integrand from its data: a number of
intervals N, a monotone partition t_0 <= ... <= t_N in [0, infinity) (or [0,T]), coefficients
xi_i, and proofs that xi_i is F_{t_i}-measurable (left endpoint) and square-integrable / bounded.
Its type is the field list; faithful iff the fields are those of my reading of
SimplePredictable (nothing missing, in particular adaptedness at the left endpoint and the
integrability needed for the isometry, and nothing that prevents the usual density argument).
Comparison (verdict recorded 2026-10-17T15:01:15Z):
Comparison for SimplePredictable.mk.
The constructor's type takes N, partition, partition 0 = 0, partition last ≤ T, StrictMono,
ξ, boundedness of each ξ_i, and ambient measurability of each ξ_i. As for the structure, it does
NOT take the F_{t_i}-measurability of ξ_i (left-endpoint adaptedness) that my reading required, so
the constructor builds non-adapted step processes as well. The paper's simple predictable
integrands are those built by mk whose ξ_i also satisfy the separate hypothesis
StronglyMeasurable[ℱ (partition i)] (ξ i), which every consumer that needs predictability takes
(see SimplePredictable).
Verdict: broader.
Witness: —
Verdict: broader — Broader. The constructor requires only boundedness and ambient measurability of the coefficients,
not F_{t_i}-measurability. The paper's simple predictable integrand is mk N t ht0 htT hmono ξ hb hm
together with h_adapt : ∀ i, StronglyMeasurable[ℱ (t i.castSucc)] (ξ i). The consumers that need
predictability carry this hypothesis (the simple-integral L² and isometry lemmas,
exists_adaptedSimple_within, masterApprox_adapt).
Disagreements with the author's review (shown 2026-10-17T15:01:52Z): Disagreement, as for SimplePredictable. The author's entry records only the marker. The
constructor does not take the F_{t_i}-measurability of the coefficients, so it builds
non-adapted step processes too, and it is broader than the paper's simple predictable integrand.
That notion is mk … together with the separate adaptedness hypothesis h_adapt, which the
consumers carry. The review entry should record this.
