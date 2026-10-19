### A:thm:stab, A:thm:cwp, A:abstract, A:conclusion: Dissertation.PaperSpec.A.thm_stab
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba16bc55062de98e587 (pl-fp-v1:a1922bea7f0286b25bd001c7c470584fe6c024ee6d8c2969681d6bbcf9098046)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:36:54Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:15:38Z):
Reading (locked before any Lean): spec thm_stab, Theorem 3.1, clauses "main; continuous dependence
(3.1); the a priori continuous-dependence estimate; the stability estimate".

Paper content. System 1 (b^1, sigma^1, h^1, f^1, g^1) with xi_0^1 satisfies Assumptions 2.2-2.5
with constants L, alpha, beta1, beta2 and coupling matrix G; system 2 with xi_0^2 satisfies
Assumptions 2.2-2.3 with its own Lipschitz constant; Theta^k in HH solves (1.1) for system k.
Then (3.1):
  E sup|dX|^2 + E sup|dY|^2 + E int_0^T (|dZ|_F^2 + ||dU||^2) dt
  <= C_stab ( E|d xi_0|^2 + E|hat dg_T|^2 + E int_0^T (|(db)(t)|^2 + |(dsigma)(t)|_F^2
     + ||(dh)(t)||^2 + |(df)(t)|^2) dt ),
with d. = .^1 - .^2, (d psi)(t) = psi^1(t,Theta^2_t,mu^2_t) - psi^2(t,Theta^2_t,mu^2_t)
(h at the predictable tuple Theta^{2,-}_t, mu^{2,-}_t), hat dg_T = g^1(X^2_T, Law X^2_T) -
g^2(X^2_T, Law X^2_T). C_stab depends only on T, L, ||G||, c_G, alpha, beta1, beta2, c_BDG:
not on n, m, d, nu(E), system 2.

A faithful formal statement must contain:
- Quantifier order: for all T, L, ||G||-value, c_G-value, alpha, beta1, beta2 there is C_stab
  (or a function C_stab(T, L, ||G||, c_G, alpha, beta1, beta2)), chosen BEFORE n, m, d, nu, the
  basis, G itself (G enters only through ||G|| and c_G), the systems and solutions;
- system 1 satisfying 2.2-2.5 with those constants (and ||G||, c_G of its G equal to the given
  values, or bounded by them if C is monotone - fine either way if the C is a function of the
  actual ||G||, c_G);
- system 2 satisfying 2.2 and 2.3 (own L'); xi_0^k as data; Theta^k in HH solving (1.1)_k with
  genuine integrals and law flows;
- conclusion exactly (3.1), differences along solution 2 as above.
- Arbitrary sigma-finite nu (infinite activity), arbitrary dims.
- Watch: constant depending on G (the matrix) or on dims/nu would be narrower (weaker claim);
  solution class must be HH; system-2 hypotheses not stronger than 2.2-2.3.
Comparison (verdict recorded 2026-10-19T03:29:46Z):
Comparison: spec thm_stab (Sec3.lean:44-88) against my locked reading.

Quantifier order: exists Cstab : R^7 -> R before everything; evaluated at (T, L, ||GX G||
(operator norm of G), (sMin G^2)^{-1} = c_G, alpha, beta1, beta2). Depends only on those (c_BDG
universal); not on n, m, d, nu, the basis, system 2 (L2 does not enter), G except via ||G||, c_G.
Matches "depends only on T, L, ||G||, c_G, alpha, beta1, beta2 and c_BDG; on system 1 alone;
uniform in nu(E)".

Hypotheses: standing setting with arbitrary sigma-finite nu and dims; system 1 (C1, xi1):
JointBorel, Assumptions 2.2, 2.3 (L), 2.4 (G.rank = min m n), 2.5 (G, alpha, beta1, beta2);
system 2 (C2, xi2): JointBorel, Assumptions 2.2 and 2.3 with its own L2; Theta^k Solution of
system k in HH. Matches.

Conclusion: in [0, inf], supSize(Theta^1 - Theta^2) = E sup|dX|^2 + E sup|dY|^2 +
E int (|dZ|_F^2 + ||dU||^2) <= Cstab * dataSize with E|xi1 - xi2|^2, E|g1(X^2_T, Law X^2_T) -
g2(X^2_T, Law X^2_T)|^2 (terminalVal differences along X^2), and the energies of
(db)(t), (dsigma)(t), (df)(t) along (Theta^2_t, lawP2 Theta^2_t) and of (dh)(t) at the predictable
tuple of solution 2 and its law. Exactly (3.1) with the §3 differences along solution 2. Under the
hypotheses both sides are finite, so the [0, inf] reading equals the real one.

Witness thm_stab_hypotheses / thm_stab_nonzero_hypotheses: two systems of Example 5.1(i) with
solutions, right side nonzero. Not vacuous.

Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless:
1. (3.1) is stated in [0, inf] (lintegral energies, ofReal of the constant); under the hypotheses
   all terms are finite, so this is the printed real inequality.
2. C_stab is a function of (T, L, ||G||, c_G, alpha, beta1, beta2) with ||G|| = ||GX G|| (operator
   norm) and c_G = s_min(G)^{-2}; c_BDG is a universal constant, absorbed.
3. The jump difference uses the jointly measurable representative coeffJump of h at the
   predictable tuple of solution 2 (energy independent of the representative); the law flows are
   lawP2 at every time.
4. Solution-notion encodings as in thm_cwp (cadlag versions, vanishing off [0,T], integrability
   fields implied by Assumptions 2.2-2.3 for both systems).
Disagreements with the author's review (shown 2026-10-19T03:36:39Z): none (labelling only: faithful vs my faithful with representation choices, for the same item-by-item analysis)
