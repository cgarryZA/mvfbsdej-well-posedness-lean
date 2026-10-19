### A:thm3.1:companion: Dissertation.PaperSpec.A.thm_stab_companion
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba10ff3a550a92ccddf (pl-fp-v1:c738aa963a46c3aacd60002b1c64659e768d0308e5a31194da327d951157c790)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:37:17Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:15:38Z):
Reading (locked before any Lean): spec thm_stab_companion, clause "(a) the companion bound: with
system 2 under Assumptions 2.2-2.5, (3.1) with the differences along solution 1 and the constant
of system 2".

Paper content. "If system 2 also satisfies Assumptions 2.4-2.5, with its own coupling matrix and
constants, exchanging the roles gives the companion bound with the differences evaluated along
solution 1 and the constant built from system 2's data." So: system 1 under 2.2-2.3 (at least;
in context of Thm 3.1, under 2.2-2.5), system 2 under 2.2-2.5 with constants L', G', alpha',
beta1', beta2'; Theta^k in HH solve (1.1)_k. Then
  E sup|dX|^2 + E sup|dY|^2 + E int(|dZ|^2+||dU||^2)
  <= C_stab(T, L', ||G'||, c_G', alpha', beta1', beta2') ( E|d xi_0|^2 +
     E|g^2(X^1_T, Law X^1_T) - g^1(X^1_T, Law X^1_T)|^2 + E int (|psi^2(t,Theta^1_t,mu^1_t) -
     psi^1(t,Theta^1_t,mu^1_t)|^2 ...) dt ),
h at the predictable tuple of solution 1.

A faithful formal statement must contain:
- C_stab as a function of system 2's constants only, chosen before dims, nu, basis, systems (it
  is the same function as in Thm 3.1, applied to system 2's data - a separately quantified
  constant with the same dependence is equally faithful);
- system 2 under 2.2-2.5; system 1 under (at least) 2.2-2.3 - requiring system 1 under 2.2-2.5
  too (as in the setting of Thm 3.1, "If system 2 ALSO satisfies...") is the printed context, so
  either is acceptable (2.2-2.3 only would be broader);
- the differences along solution 1 (sign irrelevant under the square), LHS symmetric;
- the solution class HH.
Comparison (verdict recorded 2026-10-19T03:30:36Z):
Comparison: spec thm_stab_companion (Sec3Stability.lean:36-73) against my locked reading.

Quantifier order: exists Cstab : R^7 -> R first, evaluated at system 2's data (T, L, ||G||, c_G,
alpha, beta1, beta2) where L, G, alpha, beta1, beta2 are system 2's constants: "the constant built
from system 2's data", chosen before everything. Matches.

Hypotheses: system 1 (C1, xi1): JointBorel, Assumptions 2.2-2.3 with L1 only; system 2 (C2, xi2):
JointBorel, Assumptions 2.2, 2.3 (L), 2.4 (G full rank), 2.5 (G, alpha, beta1, beta2); Theta^k
Solutions in HH. The printed companion sits in the context of Theorem 3.1, where system 1 also
satisfies Assumptions 2.4-2.5 ("If system 2 ALSO satisfies Assumptions 2.4-2.5"); the proposition
does not require 2.4-2.5 of system 1, so it is broader (those hypotheses are unused by the
exchanged argument).

Conclusion: supSize(Theta^1 - Theta^2) <= Cstab(system 2) * dataSize with E|xi1 - xi2|^2,
E|g1(X^1_T, Law X^1_T) - g2(X^1_T, Law X^1_T)|^2 and the energies of psi1 - psi2 along Theta^1 (and
h at the predictable tuple of solution 1): the differences evaluated along solution 1. The sign
convention psi1 - psi2 (rather than psi2 - psi1) is irrelevant under the squares; the left side is
symmetric. Matches.

Witness thm_stab_nonzero_hypotheses: instance with both systems of Example 5.1(i); hypotheses met.

Verdict: broader.
Witness: —
Verdict: broader — Broader: system 1 is required to satisfy only (2.3) and Assumptions 2.2-2.3, whereas the printed
companion bound sits in the setting of Theorem 3.1 where system 1 also satisfies Assumptions
2.4-2.5. Instantiation giving the printed claim: take system 1 satisfying (2.3) and Assumptions
2.2-2.5 (as in Theorem 3.1) and system 2 also satisfying Assumptions 2.4-2.5 with its own G,
alpha, beta1, beta2 (and L); the proposition then gives (3.1) with the differences evaluated along
solution 1 and the constant C_stab(T, L, ||G||, c_G, alpha, beta1, beta2) of system 2. Other
encodings ([0, inf] reading, coeffJump representative, solution notion) as in thm_stab.
Disagreements with the author's review (shown 2026-10-19T03:37:06Z): none (labelling only: the review notes the same broadening, system 1 not required to satisfy Assumptions 2.4-2.5, but labels it faithful with representation choices; I label it broader with that instantiation)
