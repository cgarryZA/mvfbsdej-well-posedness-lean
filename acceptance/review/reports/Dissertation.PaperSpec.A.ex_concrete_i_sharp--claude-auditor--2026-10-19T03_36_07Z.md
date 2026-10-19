### A:ex:concrete: Dissertation.PaperSpec.A.ex_concrete_i_sharp
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba19df1faec1593a821 (pl-fp-v1:53d4773c7a96ad003d755703e3596aa8e67e114500661c002c108bd49106a962)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:36:07Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:16:43Z):
# Reading: spec ex_concrete_i_sharp (Example 5.1(i): "the identity is sharp for beta1, beta2")

Setting of Example 5.1(i): n=m=d=1, G=1, nu sigma-finite (arbitrary), xi0 in L^2(F_0),
sigma_c in R, h_c in L^2(nu), beta1, beta2 > 0; coefficients b=-beta1 y, sigma=sigma_c-beta1 z,
h(e)=h_c(e)-beta1 u(e), f=beta2 x, g(x,rho)=x. The interior pairing equals exactly
-beta1 E[|dY|^2+|dZ|^2+||dU||^2] - beta2 E|dX|^2.
Clause: "(2.7) with beta1', beta2' forces beta1' <= beta1, beta2' <= beta2".

A faithful formal statement: for every standing basis (T>0, any sigma-finite nu), sigma_c, h_c,
beta1, beta2 > 0, and all constants beta1', beta2' (reals, or >= 0): IF for a.e. t in [0,T] and all
diagonal pairs (Theta,Law Theta),(Theta',Law Theta') at t, the interior inequality (2.7) holds for
the Example 5.1(i) coefficients with beta1', beta2' (G = 1), THEN beta1' <= beta1 and
beta2' <= beta2.
* The hypothesis must be the interior (2.7) inequality only (not the whole Assumption 2.5 with
  extra constraints; adding alpha/constraint hypotheses would be harmless for the conclusion but is
  not what is printed; requiring beta' >= 0 is harmless).
* The proof needs diagonal inputs with dY != 0, dX != 0 (constants are F_t-measurable), and a
  non-null set of good times (T>0). The hypothesis is satisfiable (beta' = beta) — non-vacuous.
* The conclusion is both inequalities.
Comparison (verdict recorded 2026-10-19T03:23:12Z):
# Comparison: ex_concrete_i_sharp

Lean (Sec5Sharp.lean): for every standing basis (any sigma-finite nu on countably generated E,
d = 1, G0 independent, filtration enlJoint), T > 0, beta1, beta2 > 0, sigma_c in R^{1x1},
h_c in L^2(nu), and all real beta1', beta2': if for a.e. t in [0,T], Mono27At (the interior
inequality (2.7) at t over all pairs of diagonal inputs, with G = 1 and constants beta1', beta2',
together with integrability of the pairing) holds for affineCoeffs beta1 beta2 sigma_c h_c
(b = -beta1 y, sigma = sigma_c - beta1 z, h = h_c - beta1 u, f = beta2 x, g = x), then
beta1' <= beta1 and beta2' <= beta2.

Against my reading: setting (n = m = d = 1, G = 1, arbitrary nu and basis, T > 0, sigma_c, h_c,
beta1, beta2 > 0): yes. Hypothesis: the interior (2.7) only, for a.e. t, with beta1', beta2'
unrestricted reals (the paper's constants are >= 0; allowing all reals is harmless/stronger):
yes. The integrability conjunct in Mono27At is automatically true for this affine system along
L^2 inputs, so it does not shrink the hypothesis in a way that matters. Conclusion: both
inequalities: yes. The hypothesis is satisfiable (beta' = beta, by the exact identity), so the
statement is not vacuous; xi0 plays no role, as in the printed sentence.
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-19T03:36:03Z): none
