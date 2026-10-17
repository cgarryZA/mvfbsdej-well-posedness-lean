### A:cor:robust, A:eq:forced, A:eq:mvfbsdej, A:ex:brownian, A:ex:concrete, A:intro:mvfbsdej, A:lem:bpbsde, A:lem:cont, A:lem:pert, A:lem:small, A:rem:cwp-class, A:rem:generalrank, A:sec2:prp, A:sec4:WP-def, A:sec4:horizon-not-contractive, A:sec:examples, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: LevyStochCalc.Brownian.Ito.masterApprox
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 8590dd88f726df792bc395a002d2695e (pl-fp-v1:07faec4fb4722c6759ec5faa7670209f2f6abbb30ae03e326dab033a063d792c)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:02:25Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:34:25Z):
Reading for def:LevyStochCalc.Brownian.Ito.masterApprox (written before seeing any Lean).

Paper notion. No such object is named in the paper; it is a step of the standard construction of
the Ito integral int_0^t Z dW for predictable (or progressive) Z with E int_0^T |Z|^2 dt <
infinity: choose simple predictable Z^k with E int_0^T |Z^k - Z|^2 dt -> 0 (density), then
int Z dW := L^2(P)-lim int Z^k dW, independent of the approximating sequence by the isometry.
"masterApprox" is presumably the chosen approximating sequence of simple predictable integrands.

A faithful Lean definition must:
- produce, for each square-integrable predictable/progressive integrand, a sequence of
  SimplePredictable processes converging to it in the energy norm (dt x dP on [0,T]); any choice
  (e.g. via Classical.choose of a density theorem) is fine, since the limit of integrals does not
  depend on it — provided the density fact is proved, not assumed;
- if the integrand is not square-integrable/measurable, a junk value (e.g. zero sequence) is
  harmless only if the stochastic integral is then also junk/unused.
Comparison (verdict recorded 2026-10-17T15:01:16Z):
Comparison for Ito.masterApprox.
Lean: for H jointly measurable, ℱ-progressively measurable, with E∫_0^T|H|² < ∞ for every T > 0,
masterApprox n is the SimplePredictable on horizon n+1 chosen (Classical choice of
exists_adaptedSimple_within) to be ℱ-adapted at left endpoints (masterApprox_adapt) and within
(n+1)⁻¹ of H in E∫_0^{n+1}|H − G_n|².
- An approximating sequence of adapted simple integrands converging to H in energy on each compact
  horizon. Matches my reading. The density fact is a proved lemma
  (adaptedSimple_dense_L2_brownian / exists_adaptedSimple_within), not an assumption.
- The choice is arbitrary. The integral built from it is the L²(P) limit (Cauchy by the
  difference isometry), and any other approximating adapted sequence gives the same limit by the
  isometry.
- Its type SimplePredictable lacks the adaptedness field, but here the adaptedness is supplied by
  the choice and recorded (masterApprox_adapt). So the master sequence does consist of simple
  predictable integrands.
- The integrand class is progressive + jointly measurable + locally square integrable on [0,∞).
  The paper's predictable H²_W integrands on [0,T] belong to it after extension beyond T, e.g. by 0.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices. (1) The approximating sequence is a choice, made with Classical.choose,
of adapted simple integrands on the growing horizons [0, n+1], with tolerance (n+1)⁻¹. The limit
does not depend on the choice, by the Itô isometry. (2) The integrand class is the progressively
measurable, jointly measurable integrands that are square integrable on every [0,T]. It is
defined on all of ℝ, so the paper's [0,T]-integrands are used after an extension, e.g. by zero
off [0,T]. (3) Left-endpoint adaptedness of the approximants is a separate proved fact,
masterApprox_adapt, because the SimplePredictable type does not carry it.
Disagreements with the author's review (shown 2026-10-17T15:01:53Z): No disagreement on the substance. The author's entry (acceptance/review/definitions.md) records only the review marker, or a section heading, and no comparison with the paper. It does not state the points I relied on: the master sequence consists of adapted simple integrands chosen by Classical.choose from the proved density lemma (exists_adaptedSimple_within), their adaptedness recorded separately (masterApprox_adapt). The integrand class is progressive and square integrable on every horizon, so the paper's [0,T]-integrands need an extension beyond T.
