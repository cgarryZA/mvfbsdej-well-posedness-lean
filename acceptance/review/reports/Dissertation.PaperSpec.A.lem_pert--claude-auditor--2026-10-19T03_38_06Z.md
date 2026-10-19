### A:lem:pert: Dissertation.PaperSpec.A.lem_pert
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba1eefcd4522364d865 (pl-fp-v1:d021001f46f0e743847fce65845ce37df792ad7727231b430b91851e6b99ecb3)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:38:06Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:15:38Z):
Reading (locked before any Lean): spec lem_pert, Lemma 4.3, clause "main".

Paper content. Let Assumptions 2.3-2.5 hold (NOT 2.2), fix underline-lambda in (0,1] and lambda
in [underline-lambda, 1]. Let Theta^1, Theta^2 solve the forced lambda-system (4.1) with
F_0-measurable initial data xi_0^1, xi_0^2 (replacing the system's xi_0) and forcings q^1, q^2
(square-integrable forcings in the sense of §4: q^b, q^sigma, q^f progressively measurable in
L2(Omega x [0,T]), q^h predictable P x calE-measurable in L2(dP dt nu), q^g_T in L2(F_T)), where
for each k: X^k, Y^k cadlag adapted with E int_0^T (|X^k|^2 + |Y^k|^2) dt < inf and X^k_T in
L2(F_T), Z^k in H^2_W, U^k in H^2_N, and Theta^1 - Theta^2 in HH. Then (4.3):
  E sup|dX|^2 + E sup|dY|^2 + E int (|dZ|^2 + ||dU||^2) <= C_B ( E|d xi_0|^2 + E|dq^g_T|^2 +
  E int (|dq^b|^2 + |dq^sigma|_F^2 + ||dq^h||^2 + |dq^f|^2) dt ),
C_B depending only on T, L, ||G||, c_G, alpha, beta1, beta2, underline-lambda, c_BDG.

A faithful formal statement must contain:
- Quantifier order: for all T, L, ||G||, c_G, alpha, beta1, beta2, underline-lambda there is C_B,
  chosen before dims, nu, basis, coefficients, lambda, data, forcings, solutions;
- hypotheses: coefficient system under Assumptions 2.3, 2.4, 2.5 only (with those constants);
  underline-lambda in (0,1], lambda in [underline-lambda, 1];
- xi_0^k F_0-measurable only (no L2 requirement beyond what follows);
- Theta^k weak forced solutions (the weak class above, identities of (4.1) a.s. for every t with
  lambda-scaled coefficients plus forcings, law flows of Theta^k) and Theta^1 - Theta^2 in HH
  (E sup |dX|^2, E sup |dY|^2 finite; dZ, dU square-integrable - automatic);
- conclusion (4.3), with dq = q^1 - q^2 componentwise.
- Narrowing watch: requiring Assumption 2.2, Theta^k in HH, xi_0^k in L2, zero forcings, finite
  nu, or a constant depending on the dims/nu/G-matrix; using a forcing class smaller than the
  paper's (e.g. continuous, bounded) would also narrow (as hypotheses it would weaken the lemma).
Comparison (verdict recorded 2026-10-19T03:31:59Z):
Comparison: spec lem_pert (Sec4.lean:114-152) against my locked reading.

Quantifier order: exists CB : R^8 -> R first, evaluated at (T, L, ||GX G||, (sMin G^2)^{-1},
alpha, beta1, beta2, lamLow): depends only on T, L, ||G||, c_G, alpha, beta1, beta2, underline-
lambda (c_BDG universal), before dims, nu, basis, coefficients, lambda, data, forcings, solutions.
Matches.

Hypotheses: standing setting (n, m, d > 0, T > 0, arbitrary sigma-finite nu); JointBorel,
Assumption23 (L), G.rank = min m n, Assumption25 (G, alpha, beta1, beta2) — Assumptions 2.3-2.5,
no 2.2. lamLow in (0, 1], lam in [lamLow, 1]. xi1, xi2 F_0-measurable (no L2). Forcings q^1, q^2 in
PredForcing: the paper's square-integrable forcings (q^b, q^sigma, q^f jointly and progressively
measurable, square integrable on [0,T], normalised to vanish off [0,T]; q^h marked predictable,
square integrable; q^g_T F_T-measurable in L2). Theta^k WeakForcedSolution at lam with (xi_k, q^k):
X^k, Y^k cadlag adapted with E int (|X|^2 + |Y|^2) < inf, X^k_T in L2, Z^k in H^2_W, U^k in H^2_N,
the identities of (4.1) (lambda on b, sigma, h, f, g; forcings unscaled; h at the predictable
tuple). Theta^1 - Theta^2 in HH: supSize of the difference < inf. Matches the printed hypotheses.

Conclusion: supSize(Theta^1 - Theta^2) <= CB * dataSize(xi1 - xi2, q^1 - q^2) in [0, inf] (left side
finite by hypothesis): E sup|dX|^2 + E sup|dY|^2 + E int(|dZ|^2 + ||dU||^2) <= C_B (E|dxi|^2 +
E|dq^g|^2 + E int(|dq^b|^2 + |dq^sigma|^2 + ||dq^h||^2 + |dq^f|^2)). Matches (4.3).

The weak forced solution notion requires the forced diffusion and jump integrands to have finite
energy (L2 stochastic integrals) and the forced drift and driver to have a.s. integrable paths.
As for Theorem 3.3 this loses no paper solution in the Brownian channel and is the paper's L2
framework in the jump channel (see my comparison of WeakForcedSolution).

Witness lem_pert_two_data_hypotheses: two Thm 3.5 solutions of Example 5.1(i) from initial data
0 and e1, zero forcing, lambda = lamLow = 1, difference in HH; hypotheses met with nonzero right
side.

Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless:
1. The estimate is in [0, inf] (energies as lintegrals, ofReal of the constant), with
   Theta^1 - Theta^2 in HH as finiteness of supSize of the difference.
2. C_B is a function of (T, L, ||G||, c_G, alpha, beta1, beta2, underline-lambda) with
   ||G|| = ||GX G||, c_G = s_min(G)^{-2}; c_BDG universal.
3. Forcings are normalised to vanish off [0,T]; q^h is marked predictable (the P x calE class).
4. The weak forced solution notion (WeakForcedSolution) uses L2 stochastic integrals and pathwise
   drift and driver integrals, law flows lawP2 at every time, cadlag versions of the Ito
   integrals, and every path cadlag (a null-set modification of any paper solution, which changes
   neither hypotheses nor conclusion).
5. Assumption 2.5 in Lean demands integrable pairings, automatic under Assumption 2.3.
Disagreements with the author's review (shown 2026-10-19T03:37:46Z): none (the review's caveat that the linked witness is degenerate is out of date: the current linked witness lem_pert_two_data_hypotheses uses two different initial data, 0 and e1, with right-hand side E|dxi0|^2 = 1)
