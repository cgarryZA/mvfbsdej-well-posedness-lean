### A:thm3.1:companion: Dissertation.PaperSpec.A.thm_stab_companion
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash ed839d34f480cba10ff3a550a92ccddf (pl-fp-v1:c738aa963a46c3aacd60002b1c64659e768d0308e5a31194da327d951157c790)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T12:19:01Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:18:29Z):
Reading of the paragraph after Theorem 3.1, clause (a): the companion bound.
"If system 2 also satisfies Assumptions 2.4-2.5, with its own coupling matrix and constants,
exchanging the roles gives the companion bound with the differences evaluated along solution 1 and
the constant built from system 2's data."
Formal content: the same constant function C_stab of Theorem 3.1 (chosen first, a function of
(T, L, ||G||, c_G, alpha, beta1, beta2) only) such that, in the standing setting (n, m, d >= 1, T > 0):
if system 2 (with xi2) satisfies (2.3), Assumptions 2.2-2.5 with its Lipschitz constant L2, its own
full-rank coupling matrix G2 and constants alpha2, beta1', beta2', and system 1 (with xi1) satisfies
(2.3), 2.2-2.3 with L (system 1 may or may not satisfy 2.4-2.5; the paragraph's premise is that it
does, as in Theorem 3.1, but only 2.2-2.3 are used), and Theta^k in S solves (1.1) for system k, then
E sup|dX|^2 + E sup|dY|^2 + E int (|dZ|^2 + ||dU||^2) <= C_stab(T, L2, ||G2||, c_{G2}, alpha2, beta1',
beta2') * (E|dxi|^2 + E|g1(X1_T, Law X1_T) - g2(X1_T, Law X1_T)|^2 + E int (|b1 - b2|^2 + ... )(t,
Theta^1_t, mu^1_t) dt), the h-difference at the predictable tuple of solution 1.
Whether the constant must be literally the Theorem 3.1 function or merely some function of system
2's parameters: "the constant built from system 2's data" — a function of (T, L2, ||G2||, c_{G2},
alpha2, beta1', beta2') chosen first suffices.
Comparison (verdict recorded 2026-10-17T12:18:49Z):
Comparison: thm_stab_companion vs clause (a) of the paragraph after Theorem 3.1.
Constant: exists Cstab : R^7 -> R first, applied to (T, L, ||G||, c_G, alpha, beta1, beta2) of SYSTEM 2
(L, G, alpha, beta1, beta2 are the constants with which C2 satisfies 2.3-2.5). Matches "the constant
built from system 2's data", chosen before everything.
Hypotheses: system 1: JointBorel, Assumption22 C1 xi1, Assumption23 L1 C1; system 2: JointBorel,
Assumption22 C2 xi2, Assumption23 L C2, G full rank, Assumption25 G alpha beta1 beta2 C2; Solutions of
both. The paragraph's premise has system 1 under 2.2-2.5 as in Theorem 3.1, but the exchanged bound
uses only 2.2-2.3 of system 1, so dropping 2.4-2.5 for system 1 is broader (the printed claim is
the instance where system 1 also satisfies them).
Conclusion: supSize(Theta^1 - Theta^2) <= ofReal(Cstab(T, L, ||G||, c_G, alpha, beta1, beta2)) *
dataSize(xi1 - xi2, (psi1 - psi2) along solution 1 (b, sigma, f at (Theta^1_s, lawP2 Theta^1_s); h via
coeffJump at the left-limit tuple of solution 1; g at (X1_T, Law X1_T))). The roles are exchanged
exactly; signs of the differences are irrelevant (squared norms). Matches.
Witness thm_stab_nonzero_hypotheses: both systems are Example 5.1(i), which satisfies 2.2-2.5, with
different data; hypotheses met nontrivially.
Representation choices: as for thm_stab.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — 1. System 1 is only required to satisfy (2.3), 2.2-2.3 (the paragraph's premise also has 2.4-2.5 for
   system 1, which the exchanged estimate does not use): broader, the printed claim is an instance.
2. The constant function is a fresh existential (not literally Theorem 3.1's), evaluated at system
   2's parameters: matches "the constant built from system 2's data".
3. Shared solution-notion and jump-difference encodings as in thm_stab.
Disagreements with the author's review (shown 2026-10-17T12:18:49Z): none
