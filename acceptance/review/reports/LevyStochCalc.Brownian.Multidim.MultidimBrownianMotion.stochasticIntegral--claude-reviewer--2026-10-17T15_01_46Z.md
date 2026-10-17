### A:cor:robust, A:eq:forced, A:eq:mvfbsdej, A:ex:brownian, A:ex:concrete, A:intro:mvfbsdej, A:lem:bpbsde, A:lem:cont, A:lem:pert, A:lem:small, A:rem:cwp-class, A:rem:generalrank, A:sec2:prp, A:sec4:WP-def, A:sec4:horizon-not-contractive, A:sec:examples, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 7a8c23649dc43d3d0eb5bb888b122b88 (pl-fp-v1:07205e025ff3b449a6564f4f5f69170cbc594fac0603b879f71c840a6bb1915d)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:01:46Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:35:33Z):
Unit: def:LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral (reading locked before any Lean is seen)

Paper notion. The matrix/vector Ito integral int_0^t sigma_s dW_s (sigma in R^{n x d}) and
int_t^T Z_s dW_s (Z in R^{m x d}) of system (1.1), Section 2, against the d-dimensional BM W:
the i-th component is (int_0^t phi_s dW_s)^i = sum_{j=1..d} int_0^t phi^{ij}_s dW^j_s, each summand the
scalar Ito integral of unit 01 of a square-integrable predictable/progressive integrand against
the component W^j, over the standing filtration (F_t).

What a faithful Lean definition must be.
- For phi : time -> Omega -> (row index) x (Fin d) -> R (or a matrix-valued process), component i of the
  result equals sum_j I^{W^j}_t(phi^{ij}) (scalar Ito integrals against the components W^j), or for a
  row-vector integrand (real-valued result) sum_j I^{W^j}(phi^j). The integration filtration must be the
  standing one (W an (F_t)-BM; components independent so the cross-variations vanish, which the paper
  uses through Ito's formula and BDG).
- Determined a.s. per t; junk outside the square-integrable predictable class harmless if propositions
  only integrate class members.
- Integration upper limit t and the dependence on t as in unit 01; the backward integral int_t^T is the
  difference I_T - I_t (a convention of use, not of this definition).
Comparison (verdict recorded 2026-10-17T15:01:13Z):
Comparison: def:LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral
(Brownian/MultidimIto.lean:50-74; LevyStochCalc.Brownian.Ito.stochasticIntegral in
ItoL2CompletionApi.lean:470 is definitionally stochasticIntegralBrownian.)

- Reading: component i of int phi dW is sum_j int phi^{ij} dW^j (scalar Ito integrals against the
  components), or for a row-vector integrand the real number sum_j int phi^j dW^j; over the standing
  filtration with each W^j an (F_t)-BM; a.s. per t; junk outside the class harmless.
- Lean: for Z : R -> Omega -> Fin d -> R (a row vector at each (s, omega)), the real-valued
  sum_{i : Fin d} stochasticIntegral (W.W i) F (hF i) (fun omega s => Z s omega i) ... T, i.e.
  sum_i int_0^T Z^i dW^i, each summand the scalar L^2 Ito integral reviewed in unit 01. Requirements: each
  component W^i an (F)-BM (IsBrownianFiltration per component), each Z^i jointly measurable, progressive
  and square integrable on every horizon. Hypotheses are arguments (no junk). A matrix integrand
  (sigma in R^{n x d}, Z in R^{m x d}) is integrated row by row by applying this to each row, which is the
  row-vector reading.
- Upper limit: the time argument T plays the role of t in int_0^t; value 0 at negative times.
- Cross-variations: the definition is the sum of the component integrals; the independence of components
  (used for vanishing cross-variation in the paper's Ito formula/BDG) is a property of the structure, not
  part of the definition's meaning.

Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless:
1. The integrand is a row vector Z : R -> Omega -> Fin d -> R and the result is real
   (sum_i int Z^i dW^i); a matrix integrand is integrated row by row, giving the components
   (int sigma dW)^k = sum_j int sigma^{kj} dW^j of the paper.
2. Each summand is the scalar L^2 Ito integral of unit 01, with that unit's choices: R-indexed time,
   progressive jointly measurable integrands square integrable on every [0,T'], per-t F_t-measurable
   representative, value 0 at negative times.
3. The (F_t)-BM requirement is stated per component (IsBrownianFiltration (W.W i) F); this is what the
   componentwise integrals need, and the paper's filtration satisfies it.
Disagreements with the author's review (shown 2026-10-17T15:01:25Z): No disagreement about the meaning. The author's entry is a bare def-review marker with no recorded comparison, so it does not record the representation choices this review lists (each judged harmless):
1. The integrand is a row vector Z : R -> Omega -> Fin d -> R and the result is real
   (sum_i int Z^i dW^i); a matrix integrand is integrated row by row, giving the components
   (int sigma dW)^k = sum_j int sigma^{kj} dW^j of the paper.
2. Each summand is the scalar L^2 Ito integral of unit 01, with that unit's choices: R-indexed time,
   progressive jointly measurable integrands square integrable on every [0,T'], per-t F_t-measurable
   representative, value 0 at negative times.
3. The (F_t)-BM requirement is stated per component (IsBrownianFiltration (W.W i) F); this is what the
   componentwise integrals need, and the paper's filtration satisfies it.
