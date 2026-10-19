### A:thm3.1:companion: Dissertation.PaperSpec.A.thm_stab_minimal
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba127494e1cb3f498aa (pl-fp-v1:91f29e1752bf9686affa3d43268bcf482a6a79aa39e56dd3f0e382ea9fbc53ff)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:36:39Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:15:38Z):
Reading (locked before any Lean): spec thm_stab_minimal, paragraph after Theorem 3.1, clause
"(c) (3.1) in [0, inf] with only (2.3) on system 2, so whenever the displayed differences are
square-integrable".

Paper content. "More minimally, the hypotheses on system 2 serve only to make the right-hand side
of (3.1) finite: the estimate holds whenever the displayed differences are square-integrable."
So: system 1 (b^1,...,g^1, xi_0^1) satisfies Assumptions 2.2-2.5 with constants L, alpha, beta1,
beta2, G; system 2 (b^2,...,g^2, xi_0^2) satisfies no Assumption 2.2-2.3, only the standing
requirements (deterministic, jointly Borel coefficients - (2.3) is the Borel measurability of h
into L2(nu)); Theta^k in HH solves (1.1) for system k. Then (3.1) holds with the same C_stab
(depending only on T, L, ||G||, c_G, alpha, beta1, beta2, c_BDG), where (3.1) is read in
[0, inf] (trivial when the right side is infinite), equivalently: whenever the differences
(delta psi)(t) along solution 2 and the hat-delta g_T are square-integrable, the estimate holds.

A faithful formal statement must contain:
- the same quantifier order as Theorem 3.1: C_stab chosen from (T, L, ||G||, c_G, alpha, beta1,
  beta2) before dims, nu, basis, systems, solutions;
- system 1 under 2.2-2.5; system 2 under only measurability ((2.3) and standing Borel
  measurability), no Lipschitz, no origin integrability; Theta^k in HH solving (1.1)_k (for system
  2 the solution notion must presuppose whatever integrability makes (1.1)_2 meaningful along
  Theta^2 - that is part of "solves", not an extra assumption);
- conclusion: LHS of (3.1) <= C_stab * RHS in [0, inf] (ENNReal lintegrals), or the real-valued
  version under the hypothesis that the displayed differences are square-integrable;
- differences evaluated along solution 2 exactly as in §3: psi^1(t, Theta^2_t, mu^2_t) -
  psi^2(t, Theta^2_t, mu^2_t), h at the predictable tuple, hat-delta g_T = g^1(X^2_T, Law X^2_T) -
  g^2(X^2_T, Law X^2_T); LHS E sup|dX|^2 + E sup|dY|^2 + E int(|dZ|^2+||dU||^2).
- Narrowing watch: retaining Assumption 2.3 (Lipschitz) or 2.2 on system 2 would lose the
  clause; "(2.3)" in the clause name is the equation (Borel measurability of h), not Assumption
  2.3.
Comparison (verdict recorded 2026-10-19T03:29:22Z):
Comparison: spec thm_stab_minimal (Sec3Stability.lean:104-138) against my locked reading.

Quantifier order: exists Cstab : R^7 -> R first, evaluated at (T, L, ||GX G||, (sMin G^2)^{-1},
alpha, beta1, beta2): a function of T, L, ||G||, c_G, alpha, beta1, beta2 only (c_BDG universal),
fixed before dims, nu, basis, systems and solutions. Matches.

System 1: JointBorel, Assumptions 2.2-2.5 (L, G full rank, alpha, beta1, beta2) with xi1.
System 2: only JointBorel T C2 — the clause's "(2.3)" (standing Borel measurability), no
Lipschitz, no origin integrability; xi2 arbitrary. Matches "with only (2.3) on system 2".

Solutions: Theta^1 Solution of (C1, xi1), Theta^2 Solution of (C2, xi2) in HH. The Lean solution
notion asks the coefficient processes of system 2 along Theta^2 to have finite energy (b_sq,
sigma_sq, f_sq, gamma_sq). A paper solution of system 2 need only have a pathwise drift integral
(and the L2 stochastic integrals). The difference is immaterial for this clause: system 1 satisfies
2.2-2.3 and Theta^2 is in HH, so the system-1 coefficient processes along Theta^2 are square
integrable. If a system-2 process along Theta^2 is not, the corresponding displayed difference is
not square integrable and the [0, inf] estimate is trivial (right side inf). When the displayed
differences are square integrable, the system-2 processes are, and the Lean and paper notions
coincide. The measurability fields follow from JointBorel C2.

Conclusion: supSize(Theta^1 - Theta^2) <= ofReal(Cstab(...)) * dataSize(...) in [0, inf], with
dataSize = E|xi1 - xi2|^2 + E|g1(X^2_T, Law X^2_T) - g2(X^2_T, Law X^2_T)|^2 + sum of energies of
the differences b1 - b2, sigma1 - sigma2, f1 - f2 along Theta^2 (tuple and law lawP2 of Theta^2_s)
and of the jump difference h1 - h2 at the predictable tuple (leftLim X^2, leftLim Y^2, Z^2, U^2)
and its law (coeffJump, a jointly measurable representative; the energy is
representative-independent). This is (3.1) with the differences along solution 2 as in §3, read in
[0, inf], i.e. "the estimate holds whenever the displayed differences are square integrable".

Witness thm_stab_nonzero_hypotheses: a nonzero instance (Example 5.1(i), two initial data) meeting
the hypotheses, with right side 1. Not vacuous.

Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless:
1. The estimate is read in [0, inf] (lintegral energies, ofReal of the constant): this is the
   paper's "holds whenever the displayed differences are square integrable", trivial otherwise.
2. The Lean solution notion for system 2 demands finite energy of its coefficient processes along
   Theta^2. Whenever the displayed differences are square integrable this follows from the
   system-1 bounds, and otherwise the right side is infinite. The clause therefore loses nothing.
3. Constants: C_stab is a function of (T, L, ||G||, c_G, alpha, beta1, beta2) with
   ||G|| = ||GX G|| and c_G = s_min(G)^{-2}; c_BDG is universal.
4. The jump difference uses the jointly measurable representative coeffJump of h at the
   predictable tuple; energies are independent of the representative. The other solution-notion
   encodings are as in thm_cwp (law flow lawP2 at every s, cadlag versions, vanishing off [0,T]).
Disagreements with the author's review (shown 2026-10-19T03:36:24Z): none (labelling only: the review says faithful, I say faithful with representation choices, for the same analysis, including the observation that the finite-energy fields of the system-2 solution lose no case of the printed claim)
