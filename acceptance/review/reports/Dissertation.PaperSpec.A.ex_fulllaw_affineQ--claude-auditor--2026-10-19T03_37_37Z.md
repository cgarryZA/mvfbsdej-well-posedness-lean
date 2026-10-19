### A:ex:fulllaw: Dissertation.PaperSpec.A.ex_fulllaw_affineQ
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba1b7c4d4b7307e74ea (pl-fp-v1:c1c56b7f113beceffc7bfe8c4338c5fe843f308fd8210ce9945992e3b56f615b)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:37:37Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:18:01Z):
Reading of spec:Dissertation.PaperSpec.A.ex_fulllaw_affineQ (Example 5.4, 05-examples.tex:314-318).

Printed claim: "if Q(s) = a + sum_j c_j s_j there [on the attained range of the feature vector
(int phi_1 dmu^U, ..., int phi_J dmu^U)], the Q-term equals int_H (a + sum_j c_j phi_j(u')) mu(dtheta'),
an expectation functional already covered by Example 5.3."

A faithful formal statement must contain:
- Setting: H = R^n x R^m x R^{m x d} x L^2(nu;R^m), P_2(H); J >= 1 (or any J), features
  phi_1..phi_J : L^2(nu;R^m) -> R bounded Lipschitz; Q : R^J -> R (bounded Lipschitz, standing);
  a in R, c in R^J.
- Hypothesis: Q(s) = a + sum c_j s_j for every s in the ATTAINED RANGE
  A = { (int phi_j(u) mu(dtheta))_j : mu in P_2(H) } (not merely somewhere; requiring it on all
  of R^J would be a stronger hypothesis, i.e. a narrower statement).
- Conclusion: for every mu in P_2(H),
  Q(int phi_1 dmu^U, ..., int phi_J dmu^U) = int_H (a + sum_j c_j phi_j(u')) mu(dtheta'),
  and (the "covered by Example 5.3" part) the kernel theta' -> a + sum c_j phi_j(u') is of the
  Example 5.3 class (measurable, Lipschitz in theta' with constant <= sum |c_j| Lip(phi_j), hence
  in the class); the multiplied form eps Q(...) w_1 = int eps(a + sum c_j phi_j(u')) w_1 dmu is
  equivalent.
- The identity holds for all mu in P_2(H) (the integral of bounded phi_j against mu exists).
Comparison (verdict recorded 2026-10-19T03:34:54Z):
Comparison: spec ex_fulllaw_affineQ (PaperSpec/A/Sec5.lean:567-580).
Lean: for every nu, n m d J, Q : R^J -> R, phi : Fin J -> L^2(nu;R^m) -> R, K, a, c:
(phi_j Lipschitz with constant K_j) -> (for all mu in P_2(H),
Q((int phi_j dmu^U)_j) = a + sum_j c_j int phi_j dmu^U) -> for all mu in P_2(H),
Q((int phi_j dmu^U)_j) = int (a + sum_j c_j phi_j(theta'.U)) dmu(theta').
Reading: hypothesis "Q(s) = a + sum c_j s_j on the ATTAINED RANGE" (not on all of R^J); conclusion
the identity for all mu, plus "covered by Example 5.3" (the kernel is of the Example 5.3 class).
- Hypothesis: quantified over mu in P_2(H), i.e. exactly on the attained range
  A = {(int phi_j dmu^U)_j : mu in P_2(H)}. Matches (not the narrower "affine on R^J").
- Conclusion: the identity for every mu in P_2(H). Matches. The kernel theta' -> a +
  sum_j c_j phi_j(u') is Lipschitz with constant sum_j |c_j| K_j (u' is a 1-Lipschitz function of
  theta'), hence measurable and in Example 5.3's class. This is immediate from the stated
  hypothesis and is not restated as a conjunct. I regard it as implicit rather than missing: it
  is a one-line consequence of a hypothesis that appears in the statement.
- The paper's standing data for Ex 5.4 have Q and phi_j bounded and Lipschitz. The Lean drops
  boundedness of phi_j and every condition on Q (only affinity on A is used). The identity
  remains true, since a Lipschitz phi_j has linear growth and is integrable against P_2 laws. So
  the proposition is broader.
- The multiplied term eps Q(...) w1 = int eps (a + sum c_j phi_j(u')) w1 dmu follows by scaling.
- Non-vacuous: witness ex_fulllaw_affineQ_hypotheses.
- The paper claims it at f598204 ("if Q(s) = a + sum_j c_j s_j there, the Q-term equals
  int_H(a + sum_j c_j phi_j(u')) mu(dtheta'), an expectation functional already covered by
  Example 5.3").
Verdict: broader.
Witness: —
Verdict: broader — Broader than the printed claim. The proposition assumes only that the features phi_j are
Lipschitz (constants K_j). It does not assume they are bounded, and it assumes nothing of Q beyond
affinity on the attained range. The paper's Ex 5.4 data have Q and phi_j bounded and Lipschitz.
Instantiation giving the printed claim: take the paper's bounded Lipschitz phi_j with
K_j := Lip(phi_j) and the paper's Q. The hypothesis "Q(s) = a + sum c_j s_j at every
s = (int phi_j dmu^U)_j, mu in P_2(H)" is the printed "on the attained range". The conclusion is
the printed identity Q((int phi_j dmu^U)_j) = int_H (a + sum_j c_j phi_j(u')) mu(dtheta'). The
printed appositive "an expectation functional already covered by Example 5.3" is not restated as
a conjunct, but it follows at once from the Lipschitz hypothesis. The kernel
theta' -> a + sum_j c_j phi_j(u') is Lipschitz on H with constant sum_j |c_j| K_j, because
||u' - u''|| <= |theta' - theta''|_H, and so it is a measurable Lipschitz kernel of Example 5.3.
Disagreements with the author's review (shown 2026-10-19T03:37:27Z): 1. Verdict label. The author's summary verdict is "faithful", with the parenthesis "without the
   bounds: broader". The proposition drops the printed boundedness of phi_j and every condition
   on Q, and the identity stays true for Lipschitz phi_j, so the verdict should be "broader". The
   instantiation is the paper's bounded Lipschitz phi_j (K_j = Lip(phi_j)) and the paper's Q.
2. Small precision. The author says "already covered by Example 5.3" is "the identification of
   the expectation functional with the kernel theta' -> a + sum_j c_j phi_j(u'), Lipschitz in
   theta'". The formal conclusion states only the identity. The Lipschitz membership of the kernel
   (constant sum_j |c_j| K_j) is not a conjunct, though it is an immediate consequence of the
   Lipschitz hypothesis visible in the statement. I accept that, but the review should say it is
   implicit rather than stated.
