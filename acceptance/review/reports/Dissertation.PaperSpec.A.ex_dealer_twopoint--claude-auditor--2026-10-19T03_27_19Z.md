### A:ex:dealer: Dissertation.PaperSpec.A.ex_dealer_twopoint
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba10e7a45835d5244c0 (pl-fp-v1:1823ad4947d81894bf45af44cdcf060bce9675d7528682b1df17aa29158a6d51)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:27:19Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:15:07Z):
Reading of spec:Dissertation.PaperSpec.A.ex_dealer_twopoint (Example 5.5, clause "the two-point
laws share their mean, with the printed values").

Paper (05-examples.tex:402-407): for a unit w in L2(nu), lambda_1 = (1/2)(delta_{-w} + delta_w),
lambda_2 = (1/2)(delta_{-2w} + delta_{2w}) "share their mean, yet
A_{lambda_1}(w) = (1/sqrt5) w, A_{lambda_2}(w) = (1/2)(3/sqrt10 - 1/sqrt2) w".
Check: A_{l1}(w) = (1/2)(gradV(2w) + gradV(0)) = (1/2)(2w/sqrt5) = w/sqrt5; A_{l2}(w) =
(1/2)(gradV(3w) + gradV(-w)) = (1/2)(3w/sqrt10 - w/sqrt2).  Correct.

Faithful statement:
- For every w in L2(nu) (fibre of the dealer example, L2(nu; R); general m harmless) with
  ||w|| = 1 (ν arbitrary sigma-finite; if no unit vector exists the statement is vacuous for that
  nu, but the example takes nu != 0);
- with lambda_1, lambda_2 exactly the printed two-point laws (as probability measures, elements of
  P2(L2(nu)) - two-point laws have finite second moment);
- conclusions: mean(lambda_1) = mean(lambda_2) (barycentres; both = 0 - stating "= 0" for both is
  equivalent), A_{lambda_1}(w) = (1/sqrt 5) w, A_{lambda_2}(w) = (1/2)(3/sqrt 10 - 1/sqrt 2) w.
- The crowding correction A must be the paper's, evaluated at u = w.
A statement fixing a particular nu or a particular w is narrower; a statement without the mean
equality is narrower.
Comparison (verdict recorded 2026-10-19T03:21:49Z):
Comparison for spec:Dissertation.PaperSpec.A.ex_dealer_twopoint (Sec5.lean:654-665).

Lean: forall E nu [SigmaFinite] [CountablyGenerated] (w : L2(nu; R^1)), ||w|| = 1 ->
  let L1 := (1/2) . (dirac (-w) + dirac w); L2' := (1/2) . (dirac (-(2 w)) + dirac (2 w));
  (int v dL1 = int v dL2') /\ ex55Crowd L1 w = (1/sqrt 5) . w
    /\ ex55Crowd L2' w = ((1/2) * (3/sqrt 10 - 1/sqrt 2)) . w.

Against my reading:
- For every unit w in the fibre L2(nu; R^1) (any sigma-finite, countably generated nu): matches;
  not a fixed nu or w. Satisfiable when the fibre is nontrivial (witness ex_dealer_unit_hypotheses
  gives a unit w for the dealer mark measure).
- lambda_1, lambda_2 exactly the printed two-point laws (as measures with weights 1/2 in R>=0inf;
  probability measures with finite second moment; the proposition uses them as plain measures,
  which is all that is needed).
- Equal means: Bochner barycentres of finite measures with two atoms (genuine values, both 0).
  Matches "share their mean".
- Printed values: A_{lambda_1}(w) = w/sqrt5 and A_{lambda_2}(w) = (1/2)(3/sqrt10 - 1/sqrt2) w, with
  A = ex55Crowd (the paper's crowding correction). Matches; I rechecked the arithmetic
  (gradV(2w) = 2w/sqrt5, gradV(3w) = 3w/sqrt10, gradV(-w) = -w/sqrt2, gradV(0) = 0).
- Claimed at this revision (05-examples.tex:402-407).
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-19T03:26:58Z): none
