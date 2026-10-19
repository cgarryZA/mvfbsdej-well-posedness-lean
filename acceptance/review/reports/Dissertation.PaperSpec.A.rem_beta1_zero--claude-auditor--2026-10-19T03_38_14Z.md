### A:rem:beta1-dich: Dissertation.PaperSpec.A.rem_beta1_zero
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba10a600b0e388b329d (pl-fp-v1:952cbea350b7e6ce08ab5bae09eab74e30c28585ce8e2c5841a30efc1bd46e3f)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:38:14Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:18:01Z):
Reading of spec:Dissertation.PaperSpec.A.rem_beta1_zero (Remark 2.10, 02-model-assumptions.tex:279-283).

Printed text: "When nu = 0 the fibre L^2(nu) is trivial, dU = 0 identically, and the restriction
disappears: this is the Brownian case of Example 5.2, in which both rank branches remain
available." The restriction (for nu != 0) is: an additive jump coefficient h = h(t,x,e) (no
U-feedback) forces beta1 = 0, hence m >= n with alpha, beta2 > 0.
This unit's clause: "at nu = 0 the restriction disappears: an additive jump coefficient allows
beta1 > 0".

A faithful formal statement must contain:
- Setting: a standing basis with nu = 0 (the zero measure on the mark space), so L^2(nu) = {0}.
- An existence (possibility) claim: there is a coefficient system whose jump coefficient is of the
  additive form h = h(t,x,e) (independent of y, z, u and of the law, or at least independent of
  u), satisfying the interior inequality (2.7) (and ideally all of Assumption 2.5, terminal and
  constant conditions) with beta1 > 0. Stronger and closer to "both rank branches remain
  available": such a system also exists with m < n (where Assumption 2.5 needs beta1 > 0).
- Alternatively the universal form: at nu = 0, for any additive h, the jump channel contributes
  nothing to (2.7) (dU = 0), so the constraint "beta1 <= 0" of the nu != 0 argument is not
  forced. A statement that only proves dU = 0 or only that the jump pairing vanishes is weaker
  than "allows beta1 > 0" unless it exhibits a system with beta1 > 0.
- The inequality must be the paper's (2.7) over diagonal pairs at a.e. t, with beta1 > 0 the
  constant in front of the G^T-weighted (Y,Z,U) block.
Comparison (verdict recorded 2026-10-19T03:34:55Z):
Comparison: spec rem_beta1_zero (PaperSpec/A/Sec2Remarks.lean:182-197).
Lean: for every standing setting with nu = 0 (the zero measure on a countably generated E), n = m
>= 1, any d, T > 0, beta1 > 0, beta2 > 0, sigma_c, h_c: the Example 5.1(i) coefficients
affineCoeffs beta1 beta2 sigma_c h_c have a jump coefficient depending only on (t, x)
(theta.1 = theta'.1 implies h t theta mu = h t theta' mu') AND satisfy Assumption 2.5 (terminal,
interior (2.7) for a.e. t over diagonal pairs, admissible constants) with G = I, alpha = 1,
beta1 > 0, beta2.
Reading: at nu = 0, a coefficient system with an additive jump coefficient h = h(t,x,e)
satisfies (2.7)/Assumption 2.5 with beta1 > 0 (an existence/possibility claim). The m < n branch
is "closer to" the paper's "both rank branches remain available" but is not this clause's
content.
- nu = 0: L^2(0;R^n) = {0}, so every jump coefficient is 0 and the "additive" condition holds. The
  Lean states it explicitly as independence of y, z, u and of the law. Matches the paper's "when
  nu = 0 the fibre is trivial, dU = 0 identically, and the restriction disappears".
- Assumption 2.5 in full, with beta1 > 0. This shows that an additive jump coefficient no longer
  forces beta1 = 0. Matches the clause.
- Universal over the Example 5.1(i) parameters (beta1, beta2 > 0, sigma_c, h_c) and over all
  settings with nu = 0: stronger than the existence the clause needs.
- m = n only. The m < n branch ("both rank branches remain available") is the separate clauses
  ex_brownian / ex_brownian_rank_gt of the same claim (claims.json), so nothing of this clause is
  lost.
- Non-vacuous: LevyDriver.exists for nu = 0 (witness ex_brownian_hypotheses).
- The paper claims it at f598204 (Rem 2.10, last paragraph).
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless:
1. The "additive jump coefficient allows beta1 > 0" possibility is exhibited by the
   Example 5.1(i) system at nu = 0, universally over its parameters beta1, beta2 > 0, sigma_c,
   h_c, and over every setting with nu = 0. This is stronger than the existence the clause needs.
   At nu = 0, h = h_c - beta1 u is identically 0 in L^2(0) = {0}, so it is of the additive form
   h(t,x,e), and the Lean states that explicitly.
2. It is shown at m = n with G = I. The m < n availability (the paper's "both rank branches remain
   available") is carried by the separate clauses ex_brownian / ex_brownian_rank_gt of the same
   claim. It is not part of this clause.
3. Assumption 2.5 is the formal one: expected pairings over diagonal inputs at a.e. t, with
   integrability conjuncts and admissible constants.
Disagreements with the author's review (shown 2026-10-19T03:38:08Z): none
