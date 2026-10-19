### A:cor:robust, A:conclusion: Dissertation.PaperSpec.A.cor_robust_wp
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba16dd662e97e677716 (pl-fp-v1:8b30d4c288e009d6fd38c12ae156df445d4f7256e9c5bab9189a26bc90ba6e61)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:37:29Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:15:38Z):
Reading (locked before any Lean): spec cor_robust_wp, Corollary 3.6, clauses "well-posedness;
robustness at m = n below the dissipativity margin".

Paper content. Hypotheses of Cor 3.6 (first part): m = n; baseline (b_0, sigma_0, h_0, f_0, g)
with xi_0 under Assumptions 2.2-2.5 with unweighted margin c_diss > 0 (2.13); perturbations
p_b, p_sigma, p_h, p_f with origin integrability, interior diagonal Lipschitz and (3.4) with some
c_pert >= 0; c_pert < c_diss. Conclusion: the perturbed system is well-posed "by Theorems 3.1,
3.3 and 3.5": existence of a solution Theta in HH of (1.1) for the perturbed coefficients with
initial datum xi_0, its uniqueness (in HH, indeed in Hweak), and continuous dependence in the
sense of (3.1).

A faithful formal statement must contain:
- arbitrary n (= m), d, nu (sigma-finite), basis, T > 0;
- the hypotheses above (margin c_diss > 0 in the unweighted form, (3.4) with c_pert < c_diss);
- conclusion: there exists a unique (in the HH identification) solution in HH of (1.1) with the
  perturbed coefficients (b_0 + p_b, ..., g) and xi_0. Including the stability estimate is
  optional (it is the sense "well-posed" carries via Thm 3.1, but as a property of every system
  under 2.2-2.5 it follows from the "assumptions" clause and Thm 3.1); omitting it is at most a
  minor narrowing of "well-posed" that I would note rather than count against if existence and
  uniqueness are complete.
- Same watch as thm_cwp on the solution notion (genuine integrals, law flows, no junk).
Comparison (verdict recorded 2026-10-19T03:30:52Z):
Comparison: spec cor_robust_wp (Sec3.lean:179-238) against my locked reading.

Hypotheses: exactly those of cor_robust (m = n by types; baseline under JointBorel and Assumptions
2.2-2.5 with unweighted margin Margin213, cdiss > 0; perturbation with OriginValues, LipInterior
(Lp >= 0), PairingBound34 (cpert >= 0); JointBorel of the perturbed system (standing
measurability); cpert < cdiss) — see my comparison for cor_robust, matching Corollary 3.6.

Conclusion ("well-posed by Theorems 3.1, 3.3 and 3.5"):
(i) existence of a Solution in HH of (1.1) for C.perturb p with initial datum xi0 (Thm 3.5);
(ii) uniqueness: any two WeakSolutions (in Hweak, with the same xi0) are equal (X, Y
indistinguishable on [0,T], zero energy of the Z-, U-differences) — Thm 3.3's class, which
contains HH (broader than uniqueness in HH alone, as the paper's citation of Thm 3.3 gives);
(iii) stability: with exists Cstab chosen first as a function of (T, L, ||G||, c_G, alpha, beta1,
beta2), for every L with which the perturbed system satisfies Assumption 2.3, (3.1) for its
solutions against the solutions of every system 2 under (2.3) and Assumptions 2.2-2.3, differences
along solution 2 (Thm 3.1, with the perturbed system as system 1, whose 2.5 constants are the
baseline's). All three senses of "well-posed" are present, with the constant dependence of Thm 3.1.

Solution notions as in thm_cwp / thm_uniq. Witness cor_robust_hypotheses: the hypotheses are met
at Example 5.1(i) with a feedback perturbation.

Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless:
1. "Well-posed by Theorems 3.1, 3.3 and 3.5" is rendered as the conjunction of existence of an
   HH solution, uniqueness among Hweak solutions with the same initial datum (Theorem 3.3's class),
   and the stability estimate (3.1) with a constant C_stab(T, L, ||G||, c_G, alpha, beta1, beta2)
   fixed before the data, for every Lipschitz constant L of the perturbed system.
2. The hypotheses carry the encodings of cor_robust: m = n in the types, standing measurability of
   the perturbations as JointBorel of the perturbed system, integrable pairings in Margin213 and
   PairingBound34 (automatic under the Lipschitz bounds).
3. Solution notions and [0, inf] reading of (3.1) as in thm_cwp, thm_uniq, thm_stab.
Disagreements with the author's review (shown 2026-10-19T03:37:17Z): none (labelling only: faithful vs my faithful with representation choices, for the same analysis)
