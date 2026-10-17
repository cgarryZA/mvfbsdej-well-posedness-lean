### A:cor:robust, A:eq:forced, A:eq:mvfbsdej, A:ex:brownian, A:ex:concrete, A:intro:mvfbsdej, A:lem:bpbsde, A:lem:cont, A:lem:pert, A:lem:small, A:rem:cwp-class, A:rem:generalrank, A:sec2:prp, A:sec4:WP-def, A:sec4:horizon-not-contractive, A:sec:examples, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: LevyStochCalc.Brownian.Ito.SimplePredictable
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 095844f503e4a7e50000000000000000 (pl-fp-v1:76bbed7d96cdad1d3508aa8cc2c41e4feac1e59fcc607decd1e5e28726f92cd7)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:02:24Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:34:24Z):
Reading for def:LevyStochCalc.Brownian.Ito.SimplePredictable (written before seeing any Lean).

Paper notion. The paper uses the Ito integral int_0^t Z_s dW_s for predictable square-integrable
Z (H^2_W), and the Brownian--Poisson isometries; the standard construction goes through simple
predictable integrands: Z_t(omega) = sum_{i<N} xi_i(omega) 1_{(t_i, t_{i+1}]}(t) with a finite
partition 0 <= t_0 < t_1 < ... < t_N (<= T), each xi_i F_{t_i}-measurable (with respect to the
filtration of the setting) and square-integrable (often bounded). Simple predictable processes
are dense in the square-integrable predictable (or progressive) integrands for the norm
(E int_0^T |Z|^2 dt)^{1/2}.

A faithful Lean structure "SimplePredictable" must:
- consist of a finite number N of intervals, a partition t_0 <= ... <= t_N (monotone; strict or
  non-strict both harmless since degenerate intervals contribute nothing), and coefficients
  xi_i : Omega -> R (or the relevant vector space);
- require each xi_i to be F_{t_i}-measurable for the LEFT endpoint t_i (this is what makes the
  integrand predictable and the integral a martingale; measurability w.r.t. F_{t_{i+1}} or
  F_T would be wrong), and square-integrable or bounded;
- evaluation: the process is xi_i on (t_i, t_{i+1}] (or [t_i, t_{i+1}); the a.e.-in-time
  difference is harmless for the integral and the energy, but left-open/right-closed is the
  predictable convention).
If the coefficients are only required measurable (not L^2), then the integral and isometry need
the L^2 condition elsewhere; it must not be missing where the isometry is used.
Comparison (verdict recorded 2026-10-17T15:01:14Z):
Comparison for Ito.SimplePredictable (structure, parameters Ω and horizon T).
Fields: N : ℕ; partition : Fin (N+1) → ℝ with partition 0 = 0, partition (last) ≤ T, StrictMono;
ξ : Fin N → Ω → ℝ, each bounded (∃ M, ∀ ω, |ξ i ω| ≤ M) and measurable for the AMBIENT σ-algebra.
Against my reading:
- Finite partition 0 = t_0 < … < t_N ≤ T, with coefficients on each piece. Matches. Bounded
  coefficients are the usual dense class.
- MISSING from the structure: F_{t_i}-measurability of ξ_i (left-endpoint adaptedness), which my
  reading required. The structure is not parametrised by a filtration at all. The docstring says
  "ξ_i is ℱ_{t_i}-measurable", but the field comment says adaptedness "is a separate hypothesis of
  the consumers". So the type contains non-adapted step processes, which are not simple
  predictable, and the Itô isometry fails for them.
- I checked the consumers relevant here. simpleIntegral_memLp_intermediate_brownian and the
  difference isometry take h_adapt : ∀ i, StronglyMeasurable[ℱ (partition i)] (ξ i).
  exists_adaptedSimple_within returns approximants together with that adaptedness, and
  masterApprox_adapt records it for the master sequence that defines stochasticIntegral. So
  wherever predictability matters, the hypothesis is supplied.
- One-dimensional, real coefficients (the multi-dimensional integral is assembled elsewhere).
Thus the structure on its own is broader than the paper's notion of a simple predictable
integrand. The paper's notion is the structure together with the left-endpoint adaptedness
hypothesis that every consumer adds.
Verdict: broader.
Witness: —
Verdict: broader — Broader than the notion it names. SimplePredictable Ω T has no filtration parameter, and the
coefficients ξ_i are required only to be bounded and measurable for the ambient σ-algebra, not
F_{t_i}-measurable. The docstring's "ξ_i is ℱ_{t_i}-measurable" is not enforced by the type. The
paper's (standard) simple predictable integrand Σ ξ_i 1_{(t_i,t_{i+1}]} with ξ_i F_{t_i}-measurable
is obtained as a SimplePredictable G together with the hypothesis
h_adapt : ∀ i : Fin G.N, StronglyMeasurable[ℱ (G.partition i.castSucc)] (G.ξ i). That is exactly
the hypothesis carried by every consumer that needs predictability:
simpleIntegral_memLp_intermediate_brownian, the isometry lemmas, exists_adaptedSimple_within, and
masterApprox_adapt for the sequence defining stochasticIntegral. Any statement that quantifies
over SimplePredictable without h_adapt does not quantify over simple predictable processes.
Disagreements with the author's review (shown 2026-10-17T15:01:52Z): Disagreement. The author's entry records only the marker, which reads as an acceptance of the
definition as the paper's "simple predictable" integrand. It is not that. The structure requires
the coefficients ξ_i only to be bounded and measurable for the ambient σ-algebra. It has no
filtration parameter and no F_{t_i}-measurability (left-endpoint adaptedness) field, although its
docstring says "ξ_i is ℱ_{t_i}-measurable". The type therefore contains non-adapted step
processes, for which the Itô isometry fails. It is broader than the paper's notion. The paper's
notion is the structure together with h_adapt : ∀ i, StronglyMeasurable[ℱ (partition i)] (ξ i).
That hypothesis is carried by every consumer that needs it (the simple-integral L² and isometry
lemmas, exists_adaptedSimple_within, masterApprox_adapt), so the stochastic integral built on it
is correct. The review entry should say so, and so should the docstring, which overstates the
field list.
