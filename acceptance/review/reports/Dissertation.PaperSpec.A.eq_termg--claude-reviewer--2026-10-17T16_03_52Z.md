### A:eq:termg: Dissertation.PaperSpec.A.eq_termg
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash ed839d34f480cba171988e2e6de37794 (pl-fp-v1:15480d57a7b017e059f8cf37ad2705ef42cdc014d87fed09bf3f995b216d4d52)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T16:03:52Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T15:47:46Z):
Reading of spec eq_termg ((4.3): E|g(X_T, Law(X_T))|^2 <= C (E|X_T|^2 + |g(0, delta_0)|^2),
"follows in the same way from (2.? lipT) and (2.couplingT)").

Setting: standing filtered probability space, horizon T > 0, dimensions n, m >= 1 (any nu);
g : R^n x P_2(R^n) -> R^m deterministic, jointly Borel (standing).
Hypothesis: the terminal Lipschitz condition of Assumption 2.4 (eq:lipT) with constant
L >= 0, in its printed diagonal form: for all X_T, X'_T in L^2(Omega, F_T; R^n),
|g(X_T, Law X_T) - g(X'_T, Law X'_T)| <= L (|X_T - X'_T| + W_2(Law X_T, Law X'_T)) a.s.
(A pointwise hypothesis for all x, x', rho, rho' would be stronger than printed => narrower;
the proof uses only the pair (X_T, 0).)
Conclusion: for every X_T in L^2(Omega, F_T; R^n):
   E|g(X_T, Law X_T)|^2 <= C (E|X_T|^2 + |g(0, delta_0)|^2).
Constant: C depends only on L here (C = max(3, 6L^2) works: |g(X_T,rho)| <= |g(0,delta_0)| +
L(|X_T| + (E|X_T|^2)^{1/2})). By the section's convention C may depend on T, L, |G|, c_G,
alpha, beta_1, beta_2, c_BDG; it must be chosen BEFORE g, X_T, the probability space, n, m,
nu (exists C = C(L) for all ...). If C is quantified after g or X_T the statement is
weaker (mismatched with the constant convention).
Edge cases: E as a lintegral (ENNReal) or Bochner integral - if Bochner, need integrability of
|g(X_T, rho)|^2 or else junk 0 would make LHS trivially small (harmless direction: LHS junk 0
makes the bound trivially true, so the proposition would be weaker only in a junk case that
cannot occur here because the bound itself gives integrability... but formally a Bochner
LHS on a non-integrable function is 0, so the statement would hold vacuously there; one
needs the RHS finite: E|X_T|^2 < infinity is given). Law(X_T) must be in P_2(R^n): needs
X_T in L^2.
Comparison (verdict recorded 2026-10-17T16:01:28Z):
Comparison, eq_termg (Sec4Coeff.lean:63-74).
Constant: exists K : R -> R, chosen before the probability space, filtration, dimensions, T, L,
g and X_T; the bound uses K(L): C depends only on L - as in my reading (stricter than the
section's allowed dependence on T, |G|, ...; fine).
Hypothesis: LipTerminal F P T L g, which is (2.6) in the printed diagonal form: for all F_T-
strongly-measurable square-integrable X_T, X'_T, a.s. |g(X_T, Law X_T) - g(X'_T, Law X'_T)|
<= L (|X_T - X'_T| + W_2(Law X_T, Law X'_T)), with W_2 = w2P on P2(R^n) (Euclidean norm).
Not the pointwise form - matches.
Conclusion: for all F_T-strongly-measurable X_T in L^2: lintegral |g(X_T, lawP2 X_T)|^2 <=
ofReal(K L) (lintegral |X_T|^2 + |g(0, delta_0)|^2). lawP2 P X_T is the genuine image law
(MemLp holds). Expectations read in [0, infinity] (lintegrals): no Bochner junk.
No measurability hypothesis on g (broader; the standing Borel measurability is not needed).
n, m in N, T in R, any filtration indexed by R: broader ambient generality.
Witness thm_cwp_hypotheses: a system satisfying the assumptions (Example 5.1(i)); its g
satisfies LipTerminal - fine.
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-17T16:01:35Z): The author's review recorded for this unit is empty (its text is attached to an adjacent review marker of a unit outside this chunk and was not shown), so there is nothing to compare point by point. My verdict: faithful (see comparison); no disagreement can be recorded against an empty review.
