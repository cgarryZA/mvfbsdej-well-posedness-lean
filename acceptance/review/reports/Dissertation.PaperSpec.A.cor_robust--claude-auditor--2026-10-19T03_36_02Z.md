### A:cor:robust: Dissertation.PaperSpec.A.cor_robust
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba154326c82c977c8bd (pl-fp-v1:ae7d15e4a2037003dde2e3e79b0fe18efd8ad2b28a6932de8bf3a7780731ce94)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:36:02Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:15:38Z):
Reading (locked before any Lean): spec cor_robust, Corollary 3.6, clause "assumptions of the
perturbed system".

Paper content. Let m = n; the baseline (b_0, sigma_0, h_0, f_0, g) with xi_0 satisfies
Assumptions 2.2-2.5 with margin c_diss > 0 in the unweighted form (2.13), i.e. the interior
expected pairing <= -beta1 E[|G^T dY|^2+|G^T dZ|_F^2+||G^T dU||^2] - beta2 E|G dX|^2
- c_diss E[|dY|^2+|dZ|_F^2+||dU||^2+|dX|^2] (a.e. t, all diagonal pairs). The perturbations
p_b, p_sigma, p_h, p_f (deterministic, jointly Borel, same signatures as b, sigma, h, f) satisfy
the origin-integrability (2.2 for the four interior coefficients) and the diagonal Lipschitz
condition of 2.3 (interior part; with some constant L_p'), and, for some c_pert >= 0, (3.4):
for a.e. t and all diagonal pairs,
E[<dp_b, G^T dY> + <dp_sigma, G^T dZ>_F + <-dp_f, G dX> + int_E <dp_h(e), G^T dU(e)> nu(de)]
<= c_pert E[|dX|^2 + |dY|^2 + |dZ|_F^2 + ||dU||^2].
If c_pert < c_diss, the perturbed system (b_0+p_b, sigma_0+p_sigma, h_0+p_h, f_0+p_f, g)
satisfies, with the same xi_0, Assumptions 2.2-2.5 with the same G, alpha, beta1, beta2 and
margin c_diss - c_pert (in the unweighted form (2.13)). (Lipschitz constant: some L, e.g. the sum
of the two; the paper does not fix it in the statement.)

A faithful formal statement must contain:
- m = n (as a hypothesis or by taking the same dimension), arbitrary n, d, nu, basis, T;
- baseline: Assumptions 2.2-2.5 with constants L_0, G, alpha, beta1, beta2, plus the unweighted
  margin inequality with c_diss > 0;
- perturbations: origin integrability (4 interior channels), diagonal interior Lipschitz with
  some constant, and (3.4) with c_pert >= 0 (a.e. t, all diagonal pairs), c_pert < c_diss;
- conclusion: the perturbed system satisfies 2.2 (with the same xi_0), 2.3 (some Lipschitz
  constant, e.g. L_0 + L_p; existence of a constant is what the paper claims), 2.4 (same G), 2.5
  (same G, alpha, beta1, beta2), and the unweighted margin inequality with margin
  c_diss - c_pert.
- The perturbation Lipschitz hypothesis is part of the corollary; joint Borel measurability of
  the perturbations is standing. The second part of the corollary ((3.5) => (3.4) with
  c_pert = ||G|| L_p) is a separate clause, not needed here.
Comparison (verdict recorded 2026-10-19T03:27:08Z):
Comparison: spec cor_robust (Sec3.lean:149-177) against my locked reading.

Setting: standing basis; m = n built in (Coeffs nu n n d, G an n x n matrix); n, d > 0; T > 0;
arbitrary sigma-finite nu.

Baseline hypotheses: JointBorel T C, Assumption22 (xi0, origin values), Assumption23 (L0),
G.rank = min n n (invertible), Assumption25 (G, alpha, beta1, beta2), Margin213 with cdiss > 0:
(2.13) for a.e. t and all diagonal pairs, with the unweighted margin term
c E[|dY|^2 + |dZ|_F^2 + ||dU||^2 + |dX|^2] (integrability of the pairing included, automatic under
Assumption 2.3). Matches.

Perturbation hypotheses: p : Coeffs (its g unused: Coeffs.perturb keeps the baseline g, as printed
"(b0 + p_b, ..., f0 + p_f, g)"); OriginValues T p (origin integrability of p_b, p_sigma, p_h,
p_f); LipInterior with Lp >= 0 (interior diagonal Lipschitz bound of Assumption 2.3, Hilbert-norm
W2); PairingBound34 with cpert >= 0: (3.4) for a.e. t and all diagonal pairs, with the pairing
pairing27 G p (= <dp_b, G^T dY> + <dp_sigma, G^T dZ>_F + <-dp_f, G dX> + int <dp_h(e), G^T dU(e)>)
and the unweighted right side cpert E[|dX|^2 + |dY|^2 + |dZ|^2 + ||dU||^2] (integrability included,
automatic under the Lipschitz bound); cpert < cdiss. JointBorel T (C.perturb p): the standing joint
Borel measurability of the perturbed coefficients, which the paper takes for every coefficient
("all coefficients are jointly Borel measurable"); given JointBorel C it is equivalent to the
measurability of the four perturbations, so it is the standing measurability of p, not an extra
assumption.

Conclusion: the perturbed system with the same xi0 satisfies Assumption22, Assumption23 with some
L (the paper: "Lipschitz constants add", not a fixed constant), G.rank = min n n, Assumption25
with the same G, alpha, beta1, beta2, and Margin213 with margin cdiss - cpert. Exactly the clause.

Witness cor_robust_hypotheses: baseline Example 5.1(i) with beta1 = beta2 = 2 and a feedback
perturbation eps = 1/2 meets all hypotheses. Not vacuous.

Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless:
1. m = n is built into the types (Coeffs nu n n d, G square).
2. The standing joint Borel measurability of the perturbations is stated as JointBorel of the
   perturbed system C.perturb p; with JointBorel C this is equivalent to measurability of
   p_b, p_sigma, p_h, p_f (the paper's standing measurability of every coefficient).
3. Margin213, PairingBound34 and Assumption25 in Lean require the pairings to be integrable;
   under the (baseline / perturbation) diagonal Lipschitz bounds on L2 inputs this is automatic.
4. The perturbation is a Coeffs record whose g-component is ignored (the perturbed g is the
   baseline g).
5. The perturbed Lipschitz constant is existentially quantified, as the paper fixes none.
Disagreements with the author's review (shown 2026-10-19T03:35:50Z): none
