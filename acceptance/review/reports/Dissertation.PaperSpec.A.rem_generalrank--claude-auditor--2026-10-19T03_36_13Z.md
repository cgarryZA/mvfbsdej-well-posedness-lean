### A:rem:generalrank: Dissertation.PaperSpec.A.rem_generalrank
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba1bcd1d82734738c5b (pl-fp-v1:e269f49dfdfbfcc0ec101c99beac867010eebc6017e476e2af7afd4d455f333e)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:36:13Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:15:38Z):
Reading (locked before any Lean): spec rem_generalrank, Remark 3.7, clause "the perturbed system
satisfies Assumptions 2.2-2.5 with margin c_diss - c_pert in (2.12), arbitrary m, n".

Paper content. Same splitting as Cor 3.6, run in the weighted quantities of (2.12): for arbitrary
m, n, if the baseline satisfies Assumptions 2.2-2.5 with margin c_diss > 0 in the weighted form
(2.12) (interior pairing <= -beta1 E[|G^T dY|^2+|G^T dZ|^2+||G^T dU||^2] - beta2 E|G dX|^2 -
c_diss E[|G^T dY|^2 + |G^T dZ|_F^2 + ||G^T dU||^2 + |G dX|^2]) and the perturbations satisfy
origin integrability, interior diagonal Lipschitz, and the weighted version of (3.4):
E[<dp_b,G^T dY> + <dp_sigma,G^T dZ>_F + <-dp_f, G dX> + int <dp_h(e), G^T dU(e)> nu(de)]
<= c_pert E[|G^T dY|^2 + |G^T dZ|_F^2 + ||G^T dU||^2 + |G dX|^2] (a.e. t, all diagonal pairs),
c_pert >= 0, c_pert < c_diss, then the perturbed system satisfies 2.2-2.5 with the same G, alpha,
beta1, beta2 and margin c_diss - c_pert in the weighted form (2.12). "The identical conclusion".

A faithful formal statement must contain:
- arbitrary m, n (no m = n), d, nu, basis, T; G any full-rank m x n matrix (Assumption 2.4 of the
  baseline);
- baseline: 2.2-2.5 plus weighted margin c_diss > 0;
- perturbations: origin integrability, interior diagonal Lipschitz, weighted (3.4) with
  c_pert in [0, c_diss);
- conclusion: perturbed system satisfies 2.2 (same xi_0), 2.3 (some L), 2.4 (same G), 2.5 (same
  constants) and weighted margin c_diss - c_pert.
- The remark is informal ("gives the identical conclusion"), but its content is exactly this
  statement; it is something the paper claims.
Comparison (verdict recorded 2026-10-19T03:27:49Z):
Comparison: spec rem_generalrank (Sec3GeneralRank.lean:53-81) against my locked reading.

Setting: standing basis, arbitrary n, m, d > 0 (no m = n), G in R^{m x n} with G.rank = min m n,
T > 0, arbitrary sigma-finite nu.

Baseline: JointBorel, Assumptions 2.2, 2.3 (L0), 2.4, 2.5 (G, alpha, beta1, beta2), and Margin212
with cdiss > 0: (2.12) for a.e. t and all diagonal pairs, margin term
c E[|G^T dY|^2 + |G^T dZ|_F^2 + ||G^T dU||^2 + |G dX|^2] (integrability included, automatic under
Assumption 2.3). Matches the weighted margin.

Perturbation: OriginValues p, LipInterior p (Lp >= 0), PairingBound34W p with cpert >= 0 —
(3.4) recorded in the weighted quantity: E pairing27 G p <= cpert E[|G^T dY|^2 + |G^T dZ|_F^2 +
||G^T dU||^2 + |G dX|^2] for a.e. t and all diagonal pairs; JointBorel T (C.perturb p) (standing
measurability of p); cpert < cdiss.

Conclusion: perturbed system (b0 + p_b, ..., f0 + p_f, g) with the same xi0 satisfies Assumption
2.2, Assumption 2.3 with some L, 2.4 (same G), 2.5 (same G, alpha, beta1, beta2), and Margin212
with margin cdiss - cpert. This is "the identical conclusion for arbitrary m, n when the margin and
(3.4) are both recorded in those quantities". Matches.

Witness rem_generalrank_hypotheses: the Cor 3.6 instance (n = m = 1, G = 1) meets the weighted
hypotheses with cdiss = 1, cpert = 1/2. The hypotheses are satisfiable (a square instance is an
instance of arbitrary m, n), so not vacuous.

Verdict: faithful with representation choices (same choices as cor_robust).
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless (as for Corollary 3.6):
1. The standing joint Borel measurability of the perturbations is stated as JointBorel of the
   perturbed system, equivalent given JointBorel of the baseline.
2. Margin212, PairingBound34W and Assumption25 require integrable pairings, automatic under the
   diagonal Lipschitz bounds on L2 inputs.
3. The perturbation is a Coeffs record whose g is ignored; the perturbed Lipschitz constant is
   existential, as the remark fixes none; full rank is G.rank = min m n.
Disagreements with the author's review (shown 2026-10-19T03:36:02Z): none
