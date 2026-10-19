### A:rem:margin: Dissertation.PaperSpec.A.rem_margin_sharp
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba1f5295e520594119c (pl-fp-v1:004d2a6ff2b0fd5a45c28a4cb75483e4dd6d022913b04ab838fcdf5ae83fec7d)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:37:56Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:18:01Z):
Reading of spec:Dissertation.PaperSpec.A.rem_margin_sharp (Remark 2.11, 02-model-assumptions.tex:301-307).

Printed text: "When m=n both G and G^T are injective, so the bounds of Assumption 2.4, applied
channel by channel, give c(|G^T dY|^2+...+|G dX|^2) >= (c/c_G)(|dY|^2+...+|dX|^2). A margin c in
(2.12) therefore yields the margin c/c_G, not c, in the unweighted form (2.13)".
This unit's clause: "the margin c itself does not carry over to (2.13)" -- i.e. the implication
"(2.12) with margin c  =>  (2.13) with margin c" is not valid in general (only margin c/c_G is).

A faithful formal statement must be a counterexample/existence statement:
- Setting: the standing basis (T>0, W, N, nu, filtration), m = n, G in R^{n x n} full rank
  (necessarily with c_G > 1, i.e. s_min(G) < 1, since for c_G <= 1 margin c does carry over).
- There exist G, coefficients (b,sigma,h,f) (Borel, deterministic, ideally satisfying the
  standing assumptions, e.g. affine), constants beta1,beta2 >= 0 and c > 0 such that
  (i) (2.12) holds with margin c: for a.e. t and all diagonal pairs, the expected pairing
      <= -beta1 E[|G^T dY|^2+|G^T dZ|_F^2+||G^T dU||^2] - beta2 E|G dX|^2
         - c E[|G^T dY|^2+|G^T dZ|_F^2+||G^T dU||^2+|G dX|^2];
  (ii) (2.13) with the same beta1, beta2 and the same margin c FAILS: there is a set of t of
      positive measure (or, for a statement "not for a.e. t", at least the a.e.-quantified
      statement is false) and diagonal pairs at which the expected pairing exceeds
      -beta1 E[G-weighted] - beta2 E|G dX|^2 - c E[|dY|^2+|dZ|_F^2+||dU||^2+|dX|^2].
- The negation must be of the full a.e.-in-t, all-diagonal-pairs condition (2.13) (so it suffices
  to exhibit failure on a positive-measure set of times, e.g. all t in (0,T]).
- Quantification over the setting: the paper's basis is fixed but arbitrary; the strongest
  faithful form is "in every standing setting there is such an instance"; "there is a setting"
  is weaker but still expresses "does not carry over" as a general implication failing.
- Optional (not in this clause): sharpness of c/c_G.
Comparison (verdict recorded 2026-10-19T03:34:55Z):
Comparison: spec rem_margin_sharp (PaperSpec/A/Sec2Remarks.lean:248-261).
Lean: for every standing setting with d = 1 (any nu, any G0 independent of the driver) and every
T > 0, there exist G in R^{1x1} of full rank, C : Coeffs nu 1 1 1, beta1, beta2 >= 0, c > 0 with
Margin212 (enlJoint G0 D) P T G beta1 beta2 c C and not Margin213 ... G beta1 beta2 c C.
Reading: existence of a counterexample to "(2.12) with margin c implies (2.13) with margin c":
m = n, G full rank (necessarily c_G > 1), coefficients, beta1, beta2 >= 0, c > 0 with (2.12) and
not (2.13) (same constants, same margin); ideally in every standing setting; the negation of the
full a.e.-t condition.
- Both Margin212 (reviewed in this chunk) and Margin213 (Spec/CorollaryHyps.lean) are the printed
  (2.12) and (2.13): a.e. t, all diagonal pairs, the integrability of the pairing and the
  inequality. They differ only in the margin term (G-weighted vs unweighted). Because both require
  integrability of the same pairing, "not Margin213" given Margin212 can only come from the
  unweighted inequality failing on a set of times of positive measure. That is the negation of
  the full condition, as required.
- Quantified over every setting with d = 1. The remark's "not c" is a statement that the
  implication fails in general, so a counterexample family at n = m = d = 1 in every such
  setting is what is needed. Matches my reading's "every standing setting" form, restricted to
  d = 1.
- C is not required to satisfy Assumptions 2.2-2.5 or (2.3). The remark's claim concerns only the
  implication between the two inequalities, so this is not needed. The proof uses an affine
  system with G = 1/2 (c_G = 4), beta1 = beta2 = 1, c = 1 (Acceptance/A/Sec2Remarks.lean:238-254),
  a legitimate one.
- The paper claims it at f598204: "A margin c in (2.12) therefore yields the margin c/c_G, not c,
  in the unweighted form (2.13)".
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless:
1. The counterexample is sought at n = m = d = 1, in every standing setting with d = 1 and every
   T > 0. The claim is that the implication (2.12, margin c) => (2.13, margin c) fails in
   general, so a counterexample family in these dimensions suffices.
2. The coefficient system is not required to satisfy the standing assumptions. The remark is a
   statement about the two inequalities only, and the system the proof uses is affine (it is
   jointly Borel and Lipschitz) with G = 1/2.
3. Both conditions include the integrability of the pairing (see Margin212). The same pairing is
   involved, so the failure of (2.13) is a failure of the inequality, not of integrability.
Disagreements with the author's review (shown 2026-10-19T03:37:49Z): none
