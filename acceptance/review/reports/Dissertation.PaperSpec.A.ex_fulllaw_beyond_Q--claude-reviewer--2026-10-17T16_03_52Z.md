### A:ex:fulllaw: Dissertation.PaperSpec.A.ex_fulllaw_beyond_Q
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash ed839d34f480cba12be9f13eb8df21c1 (pl-fp-v1:77391c424ac867b33c84ccb47f92f2979db03059f85ddcadebf00bcf5fe4dbae)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T16:03:52Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T15:47:46Z):
Reading of spec ex_fulllaw_beyond_Q (Example 5.4 (iii): "the Q-term, a nonlinear cylindrical
functional of the U-marginal: finitely many integrals of arbitrary bounded-Lipschitz features
on the infinite-dimensional fibre L^2(nu), composed through the nonlinear Q. All three lie
beyond the expectation and two-point-kernel jump-integrand interactions"), with the precise
condition "Q not affine on the attained range of the features".

Setting: standing H, any n,m,d, sigma-finite nu (countably generated E); J >= 1; features
phi_1..phi_J : L^2(nu) -> R bounded Lipschitz; Q : R^J -> R bounded Lipschitz; w_1 in R^m.
Feature map F(lambda) := (int phi_1 dlambda, ..., int phi_J dlambda) for lambda in
P_2(L^2(nu)); attained range R := {F(mu^U) : mu in P_2(H)} = {F(lambda): lambda in
P_2(L^2)} (a convex subset of R^J).
Hypothesis: Q is not affine on R (no affine map a + <c, .> agrees with Q on R; equivalently,
since R is convex, Q|_R fails the affine identity on some segment of R).
Conclusion: the cylindrical term mu |-> Q(F(mu^U)) (times epsilon w_1, w_1 != 0) is not an
expectation functional: not int phibar dmu for any kernel phibar (Lipschitz, of the preceding
examples' class), equivalently (here) not affine under mixtures. Quantified over all nu,
features, Q satisfying the hypothesis.
This is exactly the true form: if Q is affine on R, Q(F(mu^U)) = a + sum c_j int phi_j du^U is
an expectation functional; so the condition is necessary and sufficient, and is the faithful
precise reading of "nonlinear Q" (the literal "nonlinear Q, arbitrary features" is false:
constant features). This unit is not flagged as a correction; as a reading of the printed
claim it is the printed claim with "nonlinear" read as "not affine where it is evaluated".
Hypothesis satisfiable when nu != 0 (e.g. J = 1, phi_1 = clipped coordinate functional, Q
non-affine bounded Lipschitz); the witness should show such an instance.
Narrower would be: extra hypotheses (specific J, specific features, nu finite), or a weaker
conclusion (e.g. only non-linearity rather than non-expectation).
Comparison (verdict recorded 2026-10-17T16:01:29Z):
Comparison, ex_fulllaw_beyond_Q (Sec5.lean:623-640), corrected statement ("when Q is not affine
on the attained range of the features").
Setting: sigma-finite nu on countably generated E, n m d J in N; features phi_j : L^2(nu;R^m)
-> R Lipschitz (constants K j) and bounded (B) - printed bounded Lipschitz features; Q : R^J ->
R Lipschitz (LQ). Q is NOT required bounded (the printed Q is bounded Lipschitz): broader.
Hypothesis (the correction): not exists a, c with Q(F(mu^U)) = a + sum c_j F_j(mu^U) for every
mu in P2(H), F_j(mu^U) = int phi_j dmu^U: Q agrees with no affine map on the attained range - my
reading.
Conclusion: every phi' : H -> R integrable against every P2 law has some mu in P2 with
Q(F(mu^U)) != int phi' dmu: the cylindrical term (scalar factor of epsilon w_1) is no
expectation functional - present.
Nothing narrower than printed plus correction; one printed hypothesis (Q bounded) dropped.
Instantiation: add |Q| <= BQ (bounded Q) to obtain the printed claim with the correction.
Witness ex_fulllaw_beyond_Q_hypotheses: nu = delta_0, J = 1, phi_1 = min(|u|,1), Q = min(|s|,1/2),
with Q non-affine on the attained values {0, 1/2, 1} - intended instance.
Verdict: broader.
Witness: —
Verdict: broader — Broader than printed-plus-correction. The Lean requires Q only Lipschitz, not bounded (the
printed Q is bounded and Lipschitz); everything else is the printed claim with exactly the
named correction (Q agrees with no affine map on the attained range of the feature vector).
Instantiation: add |Q| <= B_Q to obtain the printed claim with the correction.
Disagreements with the author's review (shown 2026-10-17T16:01:36Z): The author's review recorded for this unit is empty (its text is attached to an adjacent review marker of a unit outside this chunk and was not shown), so there is nothing to compare point by point. My verdict: broader - the proposition requires Q only Lipschitz (the printed Q is bounded Lipschitz); otherwise it is the printed claim with exactly the named correction (Q not affine on the attained range of the features).
