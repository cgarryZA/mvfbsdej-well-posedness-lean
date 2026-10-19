### A:ex:concrete, A:sec5:overview: Dissertation.PaperSpec.A.ex_concrete_ii
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba1cba84bcbe1866633 (pl-fp-v1:750e750ae4a2ad0cd8e6fb10bafbd8ec220649dc0da17a4d14d01d6ecb45b5e6)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:34:14Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:16:14Z):
Reading of spec ex_concrete_ii: Example 5.1(ii) (05-examples.tex:111-194), clause "(ii) the
assumptions; Example 5.1(ii) meets every assumption at arbitrary activity".

Paper claim. n = m = d = 1, G = 1, any sigma-finite nu on a countably generated E (nu(E) = infinity
allowed), xi_0 in L^2(Omega,F_0;R). Coefficients
  b = -2y - m_Y(mu), sigma = -2z - m_Z(mu), h(e) = -2u(e) - m_U(mu)(e), f = 2x + m_X(mu),
  g(x,rho) = 2x + bary(rho),
with m_Psi(mu) = int pi_Psi(theta) mu(dtheta) (m_U(mu) the Bochner mean in L^2(nu)) and bary(rho) =
int x rho(dx). Claims: Assumption 2.2 holds (coefficients vanish at (0,delta_0), plus xi_0 in L^2);
Assumption 2.3 holds with L = 2 (interior bound via |dm_X|+|dm_Y|+|dm_Z|+||dm_U|| <= 2|dm|_H
<= 2 W_2, terminal via |bary(rho)-bary(rho')| <= W_2(rho,rho')); measurability (2.4) of h;
Assumption 2.4 with G = 1 (c_G = 1); Assumption 2.5 with alpha = beta_1 = beta_2 = 2 (interior
pairing equals -2 E[...] - (mean squares) <= -2 E[...]; terminal pairing >= 2 E|dX_T|^2); the
constant conditions (all > 0, m = n).
A faithful formal statement: for every such nu (any sigma-finite measure, any basis of sec. 2) and
xi_0 in L^2(F_0): the system satisfies Assumptions 2.2-2.5 (the Lean predicates that formalise
them) with L = 2, G = 1, alpha = beta_1 = beta_2 = 2. Existential constants (exists L, ...) would lose
the printed values - narrower in conclusion (note). Arbitrary activity: no finiteness of nu as a
hypothesis. It must be the paper's coefficients exactly (signs, factor 2, means).
Comparison (verdict recorded 2026-10-19T03:32:34Z):
Comparison, ex_concrete_ii (Sec5.lean:244-267).

- Setting: every driver with d = 1 and ANY sigma-finite nu on countably generated E (arbitrary
  activity, nu(E) = inf allowed), G0 independent, T > 0, xi_0 strongly F_0-measurable in L^2.
- Coefficients meanFieldCoeffs nu 1 1 (n = m = d = 1): b = -2y - m_Y(mu), sigma = -2z - m_Z(mu),
  h = -2u - m_U(mu) (m_U the Bochner mean in L^2(nu)), f = 2x + m_X(mu), g(x,rho) = 2x + bary(rho);
  tupleMean = int theta dmu, barycentre = int x drho. The paper's coefficients exactly.
- Conclusions: JointBorel (measurability, incl. (2.4) for h); b, sigma, h, f vanish at (t,0,delta_0);
  Assumption 2.2; Assumption 2.3 with L = 2 (printed value); G = 1 has rank 1 (Assumption 2.4);
  Assumption 2.5 with G = 1, alpha = beta_1 = beta_2 = 2 (printed values, incl. admissible
  constants). All of my reading, with the printed constants (no existential loss).
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-19T03:32:45Z): none
