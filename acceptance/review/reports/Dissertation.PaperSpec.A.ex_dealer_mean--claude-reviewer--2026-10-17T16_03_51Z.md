### A:ex:dealer: Dissertation.PaperSpec.A.ex_dealer_mean
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash ed839d34f480cba11a8c2923753a6d10 (pl-fp-v1:54fd3efbdb84240d584a911be3031d55fd6c5c0027cdeda5e08844e4d4fff6e8)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T16:03:51Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T15:47:45Z):
Reading of spec ex_dealer_mean (Example 5.5 "Beyond the mean: The crowding correction is not
a function of E[U]: for a unit w, lambda_1, lambda_2 share their mean, yet A_{lambda_1}(w)
and A_{lambda_2}(w) differ"), the printed reading, every sigma-finite nu.

Objects: fibre L^2(nu;R) (n=m=d=1 of Example 5.1(i)); A_lambda(u) := int gradV(u - v)
lambda(dv) (Bochner integral), lambda in P_2(L^2(nu)); E[U] = mean of the U-law,
m(lambda) := int v lambda(dv).

Printed claim: "A is not a function of the mean": there is no map F with
A_lambda(u) = F(u, m(lambda)) for all u and all lambda in P_2(L^2(nu)); equivalently there are
u and lambda_1, lambda_2 in P_2 with m(lambda_1) = m(lambda_2) and A_{lambda_1}(u) !=
A_{lambda_2}(u). (Either form is faithful; the "for a unit w" witness is the paper's proof.)
Quantification "as printed": for every sigma-finite nu on a countably generated (E,cE) (the
example is posed over the general standing nu; the specific marks come only later). No
nontriviality assumption on nu appears in the printed text.

Expected refutation: at nu = 0 (sigma-finite, on any countably generated E, e.g. a point),
L^2(nu) = {0}, P_2(L^2) = {delta_0}, so every A is trivially a function of the mean; the
negation of the universal statement follows. nu = 0 is covered by the standing setting (the
paper never excludes nu = 0; it treats nu sigma-finite arbitrary). So such a refutation is
valid. The proposition must be no stronger than "for every sigma-finite nu, A is not a
function of (u, mean)": e.g. it must not demand A to differ at a *specific* pair for all u, or
claim more (the printed values are a separate clause, ex_dealer_twopoint).
Comparison (verdict recorded 2026-10-17T16:01:28Z):
Comparison, ex_dealer_mean (Sec5Dealer.lean:135-144), printed reading, refuted.
Lean: forall E, nu sigma-finite, E countably generated: not exists Phi : L^2 -> L^2 -> L^2 with
ex55Crowd Lambda.law u = Phi (int v dLambda.law) u for all Lambda in P2(L^2(nu)), u in L^2(nu).
This is exactly my reading "A is not a function of (u, mean)" (argument order of Phi
irrelevant), over every sigma-finite nu on a countably generated E, with no nontriviality
assumption - the printed quantification. ex55Crowd Lambda u = int (sqrt(1+|u-v|^2))^{-1}.(u-v)
dLambda = int gradV(u - v) dLambda: the printed A_lambda(u). The mean is the Bochner integral of
the identity against a P2 law (genuine: P2 laws have finite first moments; L^2 separable).
Not stronger than printed: it asserts only the non-existence of Phi.
Refutation ex_dealer_mean_false: E = PUnit, nu = 0 (sigma-finite, countably generated), L^2(0)
is a subsingleton, Phi = 0 works. nu = 0 is a sigma-finite measure on a countably generated
space, admitted by the standing setting of Section 2 (never excluded), and the example's
claim is posed for the general nu before the specific marks are introduced. Valid.
Verdict: faithful (refutation valid).
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-17T16:01:35Z): none
