### A:thm:uniq, A:rem:uniq-no-integ, A:abstract, A:conclusion: Dissertation.PaperSpec.A.thm_uniq
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba1b8815741b34ba4e5 (pl-fp-v1:29befa06a8ddb87b3a7b3e4b037eae6a466f96caa9406f4d8cda5becf9cfcd0d)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:35:38Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:15:37Z):
Reading (locked before any Lean): spec thm_uniq, Theorem 3.3 (with Remark 3.4), clauses "main;
the uniqueness only requires Assumptions 2.3-2.5; uniqueness".

Paper content. Under Assumptions 2.3-2.5 (NOT 2.2), (1.1) has at most one solution. More
precisely, if Theta^1, Theta^2 in Hweak satisfy (1.1) with the same initial condition, then
Theta^1 = Theta^2; furthermore Theta^1 - Theta^2 in HH.
Hweak = L2(0,T;R^n) x L2(0,T;R^m) x H^2_W x H^2_N, with the L2 factor = cadlag adapted V with
E int_0^T |V_t|^2 dt < inf. "Satisfy (1.1)": both identities a.s. for every t, h at the
predictable tuple; the terminal condition presupposes Law(X_T) in P_2(R^n), i.e. X_T in L2
(proof, line 162); the integrals of (1.1) are presupposed to exist.

A faithful formal statement must contain:
- arbitrary setting (T>0, dims, sigma-finite nu, basis), deterministic Borel coefficients;
- hypotheses: Assumptions 2.3, 2.4, 2.5 only (no origin integrability of coefficients, no
  xi_0 in L2 - xi_0 just F_0-measurable, or at least not more than what the Hweak solution notion
  forces);
- Theta^1, Theta^2 in the Hweak class (cadlag adapted X, Y with E int |X|^2, E int |Y|^2 finite;
  Z, U predictable square-integrable), each satisfying (1.1) with the same xi_0 (and X^k_T in L2 as
  presupposed by the terminal law);
- conclusion: Theta^1 = Theta^2 in the identification sense (X^1, X^2 indistinguishable, Y
  likewise, Z^1 = Z^2 dt x dP-a.e., U^1 = U^2 dt x dP x nu-a.e. / in L2(nu) for a.e. (t, omega));
  plus the (then trivial) Theta^1 - Theta^2 in HH.
- Narrowing watch: requiring Theta^k in HH (not Hweak), requiring Assumption 2.2, xi_0 in L2,
  finite nu, or extra integrability beyond what "satisfy (1.1)" needs would lose the clause "the
  uniqueness only requires Assumptions 2.3-2.5" / the Hweak class. Solution notion for the Hweak
  class must make sense without Assumption 2.2 (coefficient processes along Theta may not be in
  L2 individually; the integrals must still be required to exist, e.g. local integrability, which
  is part of "satisfies (1.1)").
Comparison (verdict recorded 2026-10-19T03:25:46Z):
Comparison: spec thm_uniq (Sec3.lean:90-117) against my locked reading.

Hypotheses: standing setting (G0 independent, enlJoint, nu sigma-finite, n, m, d > 0, T > 0);
JointBorel ((2.3), standing); Assumption23 (L), G.rank = min m n (2.4), Assumption25 (G, alpha,
beta1, beta2). No Assumption 2.2: no origin integrability of the coefficients, no condition on
xi0 (not even L2). Matches "the uniqueness only requires Assumptions 2.3-2.5".

Solution class: WeakSolution = exists gamma, PaperWeakSolutionInt over enlJoint, with every path
cadlag: X, Y adapted on [0,T], right-continuous, left limits, E int_0^T |.|^2 finite (Hweak);
Z predictable, U marked predictable, finite energies (H^2_W, H^2_N); X_T in L2 (the paper's
presupposition Law X_T in P2(R^n), proof of Thm 3.3); the integrals of (1.1) exist
(PaperAdmissibleInt): drift and driver pathwise, a.s. integrable on [0,T] (as Remark 3.4's
t^{-1/2} example needs), diffusion and jump integrand with finite energy (L2 stochastic
integrals); gamma represents h at the predictable tuple; both identities on one null set for all t
with the same xi0. Matches "Theta^1, Theta^2 in Hweak satisfy (1.1) with the same initial
condition". On the L2 stochastic integrals: for the Brownian channel this loses nothing, since a.s.
local square integrability of sigma(s, Theta_s, mu_s) forces sigma(., 0, delta_0) in L2(0,T) by
Assumption 2.3 (at a.e. s, (Theta_s, mu_s) is a diagonal input) and hence finite energy along
Theta. For the jump channel it is the paper's framework (§2: Poisson integrals of square-integrable
L2(nu)-valued predictable integrands); the same Lipschitz argument applies in the L2 theory.

Conclusion: X^1, X^2 and Y^1, Y^2 indistinguishable on [0,T]; zero energy of the Z- and
U-differences (Theta^1 = Theta^2 in the identification); and supSize(Theta^1 - Theta^2) < inf,
i.e. Theta^1 - Theta^2 in HH. Matches all three sentences.

Witness thm_uniq_hypotheses: at Example 5.1(i) the hypotheses hold and two weak solutions exist
(the same one twice). Not vacuous.

Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless:
1. "Satisfy (1.1)" in Hweak is encoded as PaperWeakSolutionInt: drift and driver integrals
   pathwise (a.s. integrable paths), Brownian and Poisson integrals in the L2 sense (finite energy
   of sigma along Theta and of the jump representative gamma), X_T in L2. The L2 requirement is no
   loss for the Brownian channel (with Assumption 2.3, a.s. local square integrability along an
   Hweak tuple already forces finite energy) and is the paper's L2 framework for Poisson integrals
   (§2, (2.4)).
2. The law flow is lawP2 P Theta_s at every s (a.e. equal to the paper's Borel representative);
   gamma is a marked progressive representative of the predictable h(s, Theta^-_s, ., mu^-_s).
3. The identities hold on one null set for all t, equivalent to "a.s. for every t" (cadlag
   sides); paths cadlag for every omega; Z, U vanish off [0,T].
4. Equality Theta^1 = Theta^2 is indistinguishability of X, Y on [0,T] and zero energy of the
   Z-, U-differences; Theta^1 - Theta^2 in HH is finiteness of supSize of the differences.
5. Assumption 2.5 in Lean demands integrable pairings, automatic under Assumption 2.3.
Disagreements with the author's review (shown 2026-10-19T03:35:26Z): Labelling only. The review records "faithful" and I record "faithful with representation
choices", listing the solution-notion encodings explicitly. One of them is worth recording: the
weak solution class takes the stochastic integrals in the L2 sense (finite energy of sigma along
Theta and of the jump representative). I argue this loses no paper solution in the Brownian
channel under Assumption 2.3 and is the paper's L2 framework for Poisson integrals. The review
lists "stochastic integrals in L^2" as part of the class without that justification. No
disagreement on the verdict group.
