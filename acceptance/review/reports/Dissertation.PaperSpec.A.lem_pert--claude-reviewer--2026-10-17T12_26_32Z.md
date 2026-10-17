### A:lem:pert: Dissertation.PaperSpec.A.lem_pert
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash ed839d34f480cba1eefcd4522364d865 (pl-fp-v1:d021001f46f0e743847fce65845ce37df792ad7727231b430b91851e6b99ecb3)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T12:26:32Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:25:41Z):
Reading of Lemma 4.3 (lem:pert).
Constant first: C_B = C_B(T, L, ||G||, c_G, alpha, beta1, beta2, underline-lambda) (c_BDG universal),
chosen before everything; independent of lambda (in [underline-lambda, 1]), of the data, forcings,
dimensions and nu.
Setting: standing setting, n, m, d >= 1, T > 0.
Hypotheses: coefficients with (2.3)-Borel measurability satisfying Assumptions 2.3 (L), 2.4 (G full
rank), 2.5 (alpha, beta1, beta2) — no Assumption 2.2; underline-lambda in (0,1]; lambda in
[underline-lambda, 1]; for k = 1, 2: F_0-measurable initial data xi0^k (not required L2 individually),
square-integrable forcings q^k of the Section 4 class (q^b, q^sigma, q^f progressive, q^h predictable,
all L2, q^g_T in L2(F_T)), and Theta^k solving (4.1) at lambda with (xi0^k, q^k), in the weak class:
X^k, Y^k cadlag adapted with E int_0^T (|X^k|^2 + |Y^k|^2) dt < inf, X^k_T in L2(F_T), Z^k in H^2_W,
U^k in H^2_N; and Theta^1 - Theta^2 in S (finite S-norm of the difference).
Conclusion (4.13): E sup|dX|^2 + E sup|dY|^2 + E int (|dZ|^2 + ||dU||^2) <= C_B (E|dxi0|^2 + E|dq^g_T|^2 +
E int (|dq^b|^2 + |dq^sigma|_F^2 + ||dq^h||^2 + |dq^f|^2) dt), d = (.)^1 - (.)^2, in [0, inf].
Quantifiers: exists C_B (function) forall setting, coefficients, underline-lambda, lambda, data,
forcings, tuples.
Comparison (verdict recorded 2026-10-17T12:26:17Z):
Comparison: lem_pert vs Lemma 4.3.
Constant: exists CB : R^8 -> R first, at (T, L, ||G||, c_G, alpha, beta1, beta2, underline-lambda):
matches "C_B depends only on T, L, ||G||, c_G, alpha, beta1, beta2, underline-lambda and c_BDG"; it does
not depend on lambda, the data or the forcings.
Setting: standing setting, n, m, d > 0, T > 0.
Hypotheses: JointBorel, Assumption23 L, full-rank G, Assumption25 (no Assumption 2.2, as printed);
0 < lamLow <= 1, lamLow <= lam <= 1; xi^k F_0-measurable (enlJoint 0), not required L2 (as printed);
both forcings in PredForcing (q^b, q^sigma, q^f progressive with finite energy, q^h marked predictable
with finite marked energy, q^g F_T-measurable L2); Theta^k WeakForcedSolutions of (4.1) at lam with
(xi^k, q^k): X^k, Y^k adapted with cadlag paths and finite energy (H_weak), Z^k, U^k in H^2_W, H^2_N,
X^k_T in L2, forced drift/driver pathwise integrable, forced diffusion/jump integrands of finite
energy (for the L2 stochastic integrals), identities on one null set for all t; supSize(Theta^1 -
Theta^2) < inf (Theta^1 - Theta^2 in S). Matches the printed hypotheses.
Conclusion: supSize(dTheta) <= ofReal(CB(...)) * dataSize(dxi0, dq^b, dq^sigma, dq^h, dq^f, dq^g), i.e.
(4.13). Matches.
Witness lem_pert_hypotheses: Example 5.1(i) at lamLow = lam = 1, zero forcing, the Theorem 3.5
solution taken twice: hypotheses met (a degenerate instance with both sides 0, but the hypotheses
are shown satisfiable at an intended instance — the uniqueness use of the lemma).
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — 1. The weak forced solutions are encoded by WeakForcedSolution (H_weak tuple, X_T in L2, pathwise forced
   drift/driver integrals, L2 stochastic integrals of the forced diffusion and jump integrands with
   the jump coefficient through a representative gamma, identities on one null set for all t).
2. Forcings in the normal form of PredForcing (vanishing off [0,T], q^h marked predictable).
3. Theta^1 - Theta^2 in S as finite supSize; inequality in [0, inf].
4. The linked witness is degenerate (Theta^1 = Theta^2), which still shows the hypotheses can be met.
Disagreements with the author's review (shown 2026-10-17T12:26:17Z): none (minor: the linked witness is degenerate — Theta^1 = Theta^2, both sides of (4.13) zero — though it does show the hypotheses can be met).
