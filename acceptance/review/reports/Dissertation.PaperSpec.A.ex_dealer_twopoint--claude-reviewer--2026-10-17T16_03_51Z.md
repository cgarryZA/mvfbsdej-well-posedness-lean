### A:ex:dealer: Dissertation.PaperSpec.A.ex_dealer_twopoint
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash ed839d34f480cba10e7a45835d5244c0 (pl-fp-v1:1823ad4947d81894bf45af44cdcf060bce9675d7528682b1df17aa29158a6d51)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T16:03:51Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T15:47:46Z):
Reading of spec ex_dealer_twopoint: "for a unit w in L^2(nu), the two-point laws
lambda_1 = (delta_{-w}+delta_w)/2 and lambda_2 = (delta_{-2w}+delta_{2w})/2 share their mean,
yet A_{lambda_1}(w) = w/sqrt5, A_{lambda_2}(w) = (1/2)(3/sqrt10 - 1/sqrt2) w."

Faithful statement: for every sigma-finite nu (countably generated E; an arbitrary real inner
product space would be broader and fine) and every w in L^2(nu;R) with |w| = 1:
 1. lambda_1, lambda_2 are probability measures in P_2 (automatic for two-point laws);
 2. mean(lambda_1) = mean(lambda_2) (both equal 0) - "share their mean";
 3. A_{lambda_1}(w) = (1/sqrt 5) w;
 4. A_{lambda_2}(w) = (1/2)(3/sqrt 10 - 1/sqrt 2) w,
 with A_lambda(u) = int gradV(u-v) lambda(dv), gradV(w) = w/sqrt(1+|w|^2), the Bochner integral
 against the two-point measure. Check: A_{lambda_1}(w) = (gradV(2w)+gradV(0))/2 = w/sqrt5;
 A_{lambda_2}(w) = (gradV(3w)+gradV(-w))/2 = (3w/sqrt10 - w/sqrt2)/2. True.
Hypothesis |w| = 1 is the printed one; it can only be met when L^2(nu) != 0 (the witness, if
any, should exhibit nu != 0 and a unit w). A statement for an arbitrary unit vector of an
arbitrary inner-product space is broader and fine.
The "yet" (the two values differ) may or may not be included; the values themselves imply it.
Comparison (verdict recorded 2026-10-17T16:01:28Z):
Comparison, ex_dealer_twopoint (Sec5.lean:667-678).
forall sigma-finite nu on countably generated E, forall w in L^2(nu;R^1) with |w| = 1 - printed
"unit w".
Lambda_1 = (1/2)(delta_{-w} + delta_w), Lambda_2 = (1/2)(delta_{-2w} + delta_{2w}) as measures
(probability measures; finite second moment automatic - not stated but not needed).
Conclusions: means equal (int v dLambda_1 = int v dLambda_2); ex55Crowd Lambda_1 w =
(1/sqrt5) w; ex55Crowd Lambda_2 w = ((1/2)(3/sqrt10 - 1/sqrt2)) w - the printed values.
The "yet" (difference) follows from the values; the separate non-function-of-mean clause is
ex_dealer_mean_corr.
Witness ex_dealer_unit_hypotheses: a unit vector on the dealer marks - intended instance.
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-17T16:01:35Z): none
