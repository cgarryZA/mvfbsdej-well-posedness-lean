### A:rem:generalrank: Dissertation.PaperSpec.A.rem_generalrank_wp
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba118d1835a02488a97 (pl-fp-v1:3759c778dd48fa1457637241bbf2a4a8a4ebdde4ee85b7554d5b477cbeebd236)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:37:46Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:15:38Z):
Reading (locked before any Lean): spec rem_generalrank_wp, Remark 3.7, clause "the perturbed
system is well-posed, arbitrary m, n".

Paper content. As cor_robust_wp but for arbitrary m, n with the margin and the perturbation
pairing bound both recorded in the weighted quantities of (2.12): baseline under 2.2-2.5 with
weighted margin c_diss > 0; perturbations with origin integrability, interior diagonal Lipschitz,
weighted (3.4) with c_pert in [0, c_diss). Conclusion ("the identical conclusion"): the perturbed
system satisfies 2.2-2.5 with margin c_diss - c_pert in (2.12) and hence, by Thms 3.1, 3.3, 3.5,
is well-posed: existence and uniqueness of an HH-solution of (1.1) (and stability).

A faithful formal statement must contain:
- arbitrary m, n (no m = n), d, nu, basis, T; G full rank m x n;
- baseline 2.2-2.5 + weighted margin c_diss > 0; perturbations: origin integrability, interior
  diagonal Lipschitz, weighted (3.4) (the notion of def PairingBound34W) with 0 <= c_pert <
  c_diss;
- conclusion: exists unique (HH identification) solution of (1.1) with the perturbed
  coefficients and xi_0 (optionally with stability).
- Same watch on solution notion.
Comparison (verdict recorded 2026-10-19T03:31:05Z):
Comparison: spec rem_generalrank_wp (Sec3GeneralRank.lean:83-142) against my locked reading.

Hypotheses: exactly those of rem_generalrank: arbitrary n, m, d > 0, G in R^{m x n} with
G.rank = min m n; baseline under JointBorel and Assumptions 2.2-2.5 with the weighted margin
Margin212 (cdiss > 0); perturbation with OriginValues, LipInterior (Lp >= 0) and the weighted
pairing bound PairingBound34W (cpert >= 0); JointBorel of the perturbed system; cpert < cdiss.

Conclusion: (i) a Solution in HH of (1.1) for C.perturb p with xi0; (ii) any two WeakSolutions
with the same xi0 equal (indistinguishable X, Y on [0,T], zero energy of Z-, U-differences);
(iii) exists Cstab (chosen first, a function of (T, L, ||G||, c_G, alpha, beta1, beta2)) with (3.1)
for every Lipschitz constant L of the perturbed system, against every system 2 under (2.3) and
Assumptions 2.2-2.3. This is "the identical conclusion" of Corollary 3.6 (well-posedness by
Theorems 3.1, 3.3, 3.5) at arbitrary m, n with both margin and (3.4) in the weighted quantities.

Witness rem_generalrank_hypotheses: the square instance of Cor 3.6 satisfies the weighted
hypotheses; not vacuous.

Verdict: faithful with representation choices (same as cor_robust_wp).
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless (as for cor_robust_wp):
1. Well-posedness is existence of an HH solution, uniqueness in Hweak with the same initial datum,
   and (3.1) with C_stab(T, L, ||G||, c_G, alpha, beta1, beta2) fixed before the data.
2. Standing measurability of the perturbations as JointBorel of the perturbed system; Margin212 and
   PairingBound34W demand integrable pairings (automatic under the Lipschitz bounds); full rank as
   G.rank = min m n.
3. Solution notions and [0, inf] reading as in thm_cwp, thm_uniq, thm_stab.
Disagreements with the author's review (shown 2026-10-19T03:37:29Z): none (labelling only: faithful vs my faithful with representation choices; I add that the witness instance is square, n = m = 1, which shows satisfiability but does not exercise m != n)
