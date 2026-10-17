### A:cor:robust, A:eq:forced, A:eq:mvfbsdej, A:ex:brownian, A:ex:concrete, A:intro:mvfbsdej, A:lem:bpbsde, A:lem:cont, A:lem:pert, A:lem:small, A:rem:cwp-class, A:rem:generalrank, A:sec2:prp, A:sec4:WP-def, A:sec4:horizon-not-contractive, A:sec:examples, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: LevyStochCalc.Brownian.Ito.stochasticIntegral
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 2c173e4f8affd8d9fb9c03a2213aee2d (pl-fp-v1:eead44e8b28444c61895e8e5fcf2fe002dc98e51e1ca3b772dc0c21be9826c7b)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:02:25Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:34:25Z):
Reading for def:LevyStochCalc.Brownian.Ito.stochasticIntegral (written before seeing any Lean).

Paper notion. The Ito integral int_0^t Z_s dW_s for Z predictable (H^2_W) or progressively
measurable with E int_0^T |Z_s|^2 ds < infinity, W the (F_t)-Brownian motion: the
L^2(P)-limit of simple integrals of simple predictable approximants (isometric extension); it is
a square-integrable martingale with a continuous version, and E|int_0^t Z dW|^2 = E int_0^t |Z|^2.
The paper's solution notion requires the identities a.s. for every t ("both sides are cadlag,
so the null set may be taken independent of t"), so a version of the integral at each t is used.
For matrix-valued Z in R^{m x d} and W in R^d, int Z dW = (sum_j int Z_{ij} dW^j)_i.

A faithful Lean definition must:
- agree a.s. (at each t) with the L^2(P)-limit of the simple integrals for every admissible
  approximating sequence (independence of the sequence), i.e. be the classical Ito integral;
- be with respect to the given BM W and filtration F (the approximants must be F-predictable,
  the coefficients F_{t_i}-measurable);
- cover the integrands the paper uses: predictable or progressive, square-integrable on [0,T]
  (equivalently energy finite); integrands outside this class may receive junk (e.g. 0) only if
  every use is guarded;
- a pointwise-in-t choice of representative is acceptable for "a.s. for every t" statements; a
  claim requiring continuity of t |-> int_0^t Z dW pathwise would need a continuous version
  (if the paper's statements are formulated as "for every t, a.s.", a per-t representative is
  enough).
Comparison (verdict recorded 2026-10-17T15:01:17Z):
Comparison for Ito.stochasticIntegral.
Lean: stochasticIntegral W ℱ hℱ H h_meas h_progMeas h_sq_int_global t := stochasticIntegralBrownian
…, which is an ℱ_t-strongly-measurable representative (AEStronglyMeasurable[ℱ t].mk) of
stochasticIntegralBrownianLp t = L²(P)-lim_n of the simple integrals at t of the adapted master
approximants of H.
- It is the L²(P) limit of simple integrals of adapted simple approximants converging in energy,
  i.e. the classical Itô integral at each t. Independence of the approximating sequence follows
  from the isometry. Matches.
- Relative to the given W and ℱ, with hℱ : IsBrownianFiltration W ℱ (adaptedness and
  independence of future increments). The approximants are ℱ-adapted. Matches.
- Integrand class: H : Ω → ℝ → ℝ, jointly measurable, ℱ-progressively measurable, and
  E∫_0^T|H|² < ∞ for EVERY T > 0. This covers the paper's predictable (hence progressive)
  square-integrable integrands on [0,T] once they are extended beyond T (e.g. by 0, as the
  coefficient processes of the specs are cut off by indicators of [0,T]). Integrands outside the
  class cannot be passed (the hypotheses are arguments), so there is no junk value.
- Per-t representative: the value at each t is a version (ℱ_t-measurable) of the L² limit. No
  pathwise-continuous version is chosen in this definition. The paper's solution notion ("a.s. for
  every t") is per t, so this suffices, as my reading noted. The value is 0 for t < 0.
- One-dimensional. The ℝ^{m×d} · ℝ^d integral is assembled from these (multi-dimensional wrapper
  used by the specs, not in this chunk).
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices. (1) The integral is one-dimensional (real integrand, one Brownian
component), and the paper's matrix integral is assembled elsewhere. (2) The integrand class is
progressive + jointly measurable + square integrable on every horizon [0,T], T > 0, with
integrands defined on all of ℝ. The paper's H²_W integrands on [0,T] enter after extension off
[0,T] (e.g. by zero), which changes nothing on [0,t], t ≤ T. (3) The value at each t is an
ℱ_t-measurable representative of the L²(P) limit of the simple integrals of a chosen adapted
approximating sequence. By the isometry, it is a.s. equal to the limit along any approximating
sequence. No continuous version is selected, which is enough for "for every t, a.s." statements.
(4) The value is 0 for t < 0, outside the paper's range.
Disagreements with the author's review (shown 2026-10-17T15:01:53Z): No disagreement on the substance. The author's entry (acceptance/review/definitions.md) records only the review marker, or a section heading, and no comparison with the paper. It does not state the points I relied on: the value is the ℱ_t-measurable representative of the L²(P) limit of the simple integrals of adapted approximants, per t, with no continuous version chosen. The integrand class is progressive and square integrable on every horizon (the paper's integrands enter extended beyond T), and the integral is one-dimensional.
