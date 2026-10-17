### A:rem:generalrank: Dissertation.PaperSpec.A.rem_generalrank
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash ed839d34f480cba1bcd1d82734738c5b (pl-fp-v1:e269f49dfdfbfcc0ec101c99beac867010eebc6017e476e2af7afd4d455f333e)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T12:13:00Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:12:24Z):
Reading of Remark 3.7 (rem:generalrank), clause: assumption transfer for arbitrary m, n.

The remark says Corollary 3.6's argument works for arbitrary m, n when the margin and (3.4) are both
recorded in the weighted quantities of (2.12). The clause under review is the first conclusion of
Corollary 3.6 transposed:
Setting: standing setting, T > 0, arbitrary n, m, d >= 1 (no m = n), G in R^{m x n} of full rank.
Hypotheses:
 - baseline (b0, sigma0, h0, f0, g) with xi0 satisfies (2.3)-Borel, Assumptions 2.2, 2.3 (some L0),
   2.4, 2.5 with alpha, beta1, beta2 (admissible constants incl. rank side conditions);
 - the weighted margin (2.12) with c_diss > 0: interior pairing <= -beta1 E[|G^T dY|^2 + |G^T dZ|^2_F +
   ||G^T dU||^2] - beta2 E|G dX|^2 - c_diss E[|G^T dY|^2 + |G^T dZ|^2_F + ||G^T dU||^2 + |G dX|^2],
   a.e. t, all diagonal pairs;
 - perturbations p_b, p_sigma, p_h, p_f with origin integrability (2.2) and diagonal interior
   Lipschitz (2.3) with some constant;
 - (3.4) recorded in the weighted quantity: E[perturbation pairing] <= c_pert E[|G^T dY|^2 +
   |G^T dZ|^2_F + ||G^T dU||^2 + |G dX|^2], c_pert >= 0, a.e. t, all diagonal pairs;
 - c_pert < c_diss.
Conclusion: the perturbed system (b0+p_b, sigma0+p_sigma, h0+p_h, f0+p_f, g) with the same xi0
satisfies Assumptions 2.2-2.5 with the same G, alpha, beta1, beta2 (and some Lipschitz constant,
L0 + L_p), and (2.12) with margin c_diss - c_pert.
(The well-posedness conclusion is a separate clause; the c_pert = ||G|| L_p part is not part of
this clause.)
Comparison (verdict recorded 2026-10-17T12:12:52Z):
Comparison: rem_generalrank vs Remark 3.7 (assumption-transfer clause).
Setting: standing setting, n, m, d > 0 arbitrary (no m = n), T > 0, G : Matrix (Fin m) (Fin n).
Hypotheses: JointBorel C; Assumption22 C xi0; Assumption23 L0 C; G.rank = min m n (full rank);
Assumption25 G alpha beta1 beta2 C (with Constants incl. rank side conditions); Margin212 cdiss C
(weighted margin (2.12): extra -c E[|G^T dY|^2 + |G^T dZ|^2 + ||G^T dU||^2 + |G dX|^2]), cdiss > 0;
OriginValues p; LipInterior Lp p, Lp >= 0; PairingBound34W cpert p ((3.4) with right-hand side
c E[|G^T dY|^2 + |G^T dZ|^2_F + ||G^T dU||^2 + |G dX|^2]), cpert >= 0; JointBorel (C.perturb p);
cpert < cdiss. All match the reading (Margin212 and PairingBound34W checked against (2.12) and the
weighted quantity term by term; integrability of the pairing expectations is required, automatic
under 2.3 + Borel measurability).
Conclusion: Assumption22 (C.perturb p) xi0, exists L with Assumption23 L (C.perturb p), G full rank,
Assumption25 G alpha beta1 beta2 (C.perturb p), Margin212 (cdiss - cpert) (C.perturb p). This is
"Assumptions 2.2-2.5 with the same G, alpha, beta1, beta2 and margin c_diss - c_pert" in the weighted
form. Assumption 2.3 is itself "there is L >= 0", so the existential L is faithful here.
JointBorel (C.perturb p) as hypothesis: equivalent, given JointBorel C, to the standing Borel
measurability of the perturbations; harmless.
Witness rem_generalrank_hypotheses: the cor_robust instance (n = m = 1, G = 1, affine baseline with
beta = 2, margin 1, feedback perturbation cpert = 1/2): hypotheses met. It does not exercise m != n,
but the hypotheses are shown satisfiable at an intended instance.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — 1. The expectations in Assumption 2.5, (2.12) and the weighted (3.4) are Bochner integrals with
   integrability of the pairing required; under Assumption 2.3 and Borel measurability the pairings
   are integrable for L2 inputs, so nothing is lost.
2. Borel measurability of the perturbations is hypothesised as JointBorel of the perturbed system;
   given JointBorel of the baseline the two are equivalent.
3. The common TupleH / w2H / lawP2 encodings (channel-sum norms and Hilbert W2 in the Lipschitz
   bounds; lawP2 a law of finite second moment) as in Assumptions 2.2-2.5.
Disagreements with the author's review (shown 2026-10-17T12:12:52Z): none
