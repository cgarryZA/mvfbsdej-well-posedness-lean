### A:thm3.1:companion: Dissertation.PaperSpec.A.thm_stab_data
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba1f26d5949b31ba63f (pl-fp-v1:a2ebce202b2722db050ffc05537cb780d5e9ad8d99a79255a60ddf7effbe9467)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:37:06Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:15:38Z):
Reading (locked before any Lean): spec thm_stab_data, paragraph after Theorem 3.1, clause "(b)
systems sharing b, sigma, h, f: continuous dependence on the initial and terminal data".

Paper content. "When the two systems share the four interior coefficients, the bound gives
continuous dependence on the initial and terminal data." So: under Theorem 3.1's hypotheses
(system 1 under 2.2-2.5 with L, G, alpha, beta1, beta2; system 2 under 2.2-2.3), with
b^1 = b^2, sigma^1 = sigma^2, h^1 = h^2, f^1 = f^2, the interior differences (d psi)(t) vanish
and (3.1) becomes
  E sup|dX|^2 + E sup|dY|^2 + E int (|dZ|^2 + ||dU||^2) <= C_stab (E|d xi_0|^2 +
  E|g^1(X^2_T, Law X^2_T) - g^2(X^2_T, Law X^2_T)|^2),
with C_stab as in Thm 3.1 (depending only on T, L, ||G||, c_G, alpha, beta1, beta2, c_BDG).

A faithful formal statement must contain:
- same quantifier order for C_stab (before dims, nu, basis, systems);
- the shared interior coefficients (b, sigma, h, f) with system 1 = (b,sigma,h,f,g^1) under
  2.2-2.5, system 2 = (b,sigma,h,f,g^2) with xi_0^2 under 2.2-2.3 (i.e. g^2 Lipschitz in the
  sense of (2.6)/ terminal Lipschitz, xi_0^2 in L2);
- Theta^k in HH solving (1.1)_k;
- conclusion: the data-only estimate above (with the terminal difference evaluated along solution
  2, or possibly in another equivalent form); "continuous dependence" could also be expressed as
  a limit statement, but the estimate is the paper's sense.
- If the statement is the general (3.1) with the interior terms present it would not be this
  clause; if it is the data-only estimate, fine.
Comparison (verdict recorded 2026-10-19T03:30:14Z):
Comparison: spec thm_stab_data (Sec3Stability.lean:75-102) against my locked reading.

Quantifier order: exists Cstab as a function of (T, L, ||G||, c_G, alpha, beta1, beta2), before
everything; a constant with the same dependence as Theorem 3.1's (separately quantified, which is
what "the bound gives" requires — the same function works).

Hypotheses: Theorem 3.1's (system 1 under JointBorel and Assumptions 2.2-2.5 with L, G, alpha,
beta1, beta2; system 2 under JointBorel and Assumptions 2.2-2.3 with L2; Theta^k Solutions in HH),
plus C2.b = C1.b, C2.sigma = C1.sigma, C2.h = C1.h, C2.f = C1.f (the two systems share the four
interior coefficients; g and xi may differ). Matches.

Conclusion: supSize(Theta^1 - Theta^2) <= Cstab (E|xi1 - xi2|^2 + E|g1(X^2_T, Law X^2_T) -
g2(X^2_T, Law X^2_T)|^2) in [0, inf] (finite under the hypotheses): continuous dependence on the
initial and terminal data, in the sense of the estimate (3.1) with the interior differences
vanishing. Matches.

Witness thm_stab_nonzero_hypotheses: shared coefficients (the same system twice) with different
initial data; hypotheses met.

Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless:
1. "Continuous dependence on the initial and terminal data" is the data-only form of (3.1); the
   constant is existentially quantified with Theorem 3.1's dependence (T, L, ||G||, c_G, alpha,
   beta1, beta2), c_BDG universal.
2. Stated in [0, inf]; both sides are finite under the hypotheses.
3. Sharing the interior coefficients is equality of the b, sigma, h, f fields of the two Coeffs
   records. Solution-notion encodings as in thm_cwp.
Disagreements with the author's review (shown 2026-10-19T03:36:54Z): none (labelling only: faithful vs my faithful with representation choices)
