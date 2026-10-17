### A:ex:brownian: Dissertation.WellPosedness.Spec.BrownianAssumption25
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 0d4cac9166e43d4d18e17cffed3382aa (pl-fp-v1:6e46a3a15bbcdb53ccca74a912cb65ace98ecc5598a1b2edcaae4f7b4a9e995a)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T16:00:55Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T15:42:31Z):
Reading for def:Dissertation.WellPosedness.Spec.BrownianAssumption25 (locked before seeing Lean).

Brownian version of Assumption 2.5 (terminal and interior G-monotonicity) for given G in
R^{m x n}, alpha, beta1, beta2:
 (terminal) for all X_T, X'_T in L^2(Omega,F_T;R^n):
   E<g(X_T,Law X_T) - g(X'_T,Law X'_T), G(X_T - X'_T)> >= alpha E|G(X_T - X'_T)|^2;
 (interior) for a.e. t in [0,T], BrownianMonoAt(t) (see that unit) for all diagonal inputs;
 (constants) alpha, beta1, beta2 >= 0, alpha + beta1 > 0, beta1 + beta2 > 0, beta1 > 0 if
   m < n, and alpha > 0 and beta2 > 0 if m > n.
F_t, F_T: the Brownian filtration (W, F_0). The constants may be existential inside the def or
parameters. "a.e. t" w.r.t. Lebesgue on [0,T]. The full-rank G (Ass 2.4) is a separate
assumption. Junk: integrals of non-integrable functions are 0 in Lean; with L^2 inputs and
Lipschitz g the terminal terms are integrable.
Comparison (verdict recorded 2026-10-17T15:51:54Z):
Comparison for def:Dissertation.WellPosedness.Spec.BrownianAssumption25.

Lean: (terminal) for all X_T, X'_T strongly F_T-measurable with MemLp 2: the pairing
<g(X_T, law X_T) - g(X'_T, law X'_T), G(X_T - X'_T)> is integrable and its expectation is
>= alpha E|G(X_T - X'_T)|^2; (interior) for a.e. t in [0,T], BrownianMonoAt F P t G beta1 beta2 C;
(constants) Constants n m alpha beta1 beta2 = alpha, beta1, beta2 >= 0, alpha + beta1 > 0,
beta1 + beta2 > 0, m < n -> beta1 > 0, n < m -> alpha > 0 ∧ beta2 > 0.

Against my reading:
- terminal inequality over all X_T, X'_T in L^2(Omega, F_T; R^n), with the induced terminal laws:
  yes; the extra integrability conjunct makes the Lean integral the genuine expectation (the paper
  presupposes the expectation exists; automatic under the terminal Lipschitz bound).
- interior: Lebesgue-a.e. t in [0,T], exceptional set independent of inputs: yes (BrownianMonoAt
  compared in its own unit; it also carries an integrability conjunct).
- constants: exactly the paper's list, with the rank conditions (beta1 > 0 if m < n; alpha, beta2 > 0
  if m > n): yes.
- Brownian setting: nu = 0, so no U-terms: yes. G full rank (Ass 2.4) separate: yes.
- G, alpha, beta1, beta2 are parameters (existential at the proposition level): fine.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices: (1) Brownian reduction at nu = 0 (no U-coordinate, no jump pairing);
(2) both the terminal and (through BrownianMonoAt) the interior conditions include integrability
of the pairing, so that the Lean integral is the genuine expectation; the paper presupposes these
expectations exist, and they are automatic under Assumption 2.3 with L^2 inputs; (3) G and the
constants are parameters of the predicate.
Disagreements with the author's review (shown 2026-10-17T16:00:51Z): none
