### A:eq:coeffint: Dissertation.PaperSpec.A.eq_coeffint
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash ed839d34f480cba13c4b68e5e50bad34 (pl-fp-v1:b27c90ed9d6d2d473dda6751bc93f67cd4dcad569eb99f1b9bb3fb2d53b5dbe9)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T12:22:13Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:21:28Z):
Reading of (4.2) (eq:coeffint).
Context (Section 4 preamble): "By Assumptions 2.2-2.3, the coefficient processes (2.5) along any
Theta in S are square-integrable: for psi in {b, sigma, h, f}, in the norms of Assumption 2.3,
E int_0^T |psi(s,Theta_s,mu_s)|^2 ds <= C E int_0^T (|X_s|^2 + |Y_s|^2 + |Z_s|_F^2 + ||U_s||^2 +
|psi(s,0,delta_0)|^2) ds, by that Lipschitz bound together with the coupling estimate (2.8) at
mu' = delta_0." Section 4 convention: C depends only on T, L, ||G||, c_G, alpha, beta1, beta2, c_BDG
unless stated; the derivation makes C depend on L alone (e.g. |psi| <= |psi_0| + L(|x|+|y|+|z|+|u| +
W2(mu, delta_0)), squared with Cauchy-Schwarz, E W2(mu_s, delta_0)^2 <= E|Theta_s|^2).
Faithful statement: exists C as a function of (at most) the Section-4 parameters — in fact of L —
chosen before everything; in the standing setting (n, m, d >= 1, T > 0), for coefficients with the
standing Borel measurability and Assumption 2.3 (interior; constant L) (Assumption 2.2 only makes
the right side finite), for every Theta in S (or more generally any tuple with Theta_s in L2 for a.e.
s, e.g. H_weak), with mu_s = Law(Theta_s), for each psi in {b, sigma, h, f} (norm: Euclidean,
Frobenius, L2(nu)), the inequality above, in [0, inf]. The h channel may be evaluated at Theta_s or
at the predictable tuple (equal for a.e. s).
Comparison (verdict recorded 2026-10-17T12:22:03Z):
Comparison: eq_coeffint vs (4.2).
Constant: exists K : R -> R first, the constant K(L) a function of the Lipschitz constant only. The
paper's C (Section 4 convention: depending only on T, L, ||G||, c_G, alpha, beta1, beta2, c_BDG) is
in its derivation a function of L; requiring dependence on L alone is at least as strong. Matches.
Setting: any filtered probability space, nu sigma-finite on countably generated E, any n, m, d, T, L
(broader than the standing setting; the standing basis is an instance).
Hypotheses: LipInterior F P T L C (interior bound of Assumption 2.3 for a.e. t, over diagonal inputs,
with the Hilbert W2). Assumption 2.2 and Borel measurability are not assumed: the inequality does
not need them (2.2 only makes its right side finite), so broader. Theta : R -> Omega -> H with Theta_t
strongly F_t-measurable and square integrable for a.e. t in [0,T]: every Theta in S (and in H_weak)
has this property, so broader than "any Theta in S".
Conclusion: for each psi in {b, sigma, h, f} (Euclidean / Frobenius / L2(nu) norms),
int_[0,T] E|psi(t, Theta_t, lawP2 Theta_t)|^2 dt <= K(L) * int_[0,T] E(|X_t|^2 + |Y_t|^2 + |Z_t|^2 + ||U_t||^2 +
|psi(t, 0, delta_0)|^2) dt, as iterated lower Lebesgue integrals in [0, inf] (time outside, omega inside).
For jointly measurable integrands this equals E int_0^T by Tonelli; without joint measurability the
time-outside order is the meaningful one and the bound holds for a.e. t pointwise. Matches (4.2).
mu_s = Law(Theta_s) is lawP2 of Theta_s (Theta_s in L2 for a.e. s, so it is the true law there).
Witness thm_cwp_hypotheses: Example 5.1(i) satisfies the interior Lipschitz bound; satisfiable.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — 1. The expectation of the time integral is written as the iterated lower integral int dt E[...] in
   [0, inf]; equal to E int dt by Tonelli for jointly measurable integrands, and meaningful without
   measurability assumptions on the family Theta.
2. Stated for any family Theta_t in L2(Omega, F_t; H) for a.e. t (covers every Theta in S and H_weak),
   on any filtered probability space: broader.
3. Only the interior bound of Assumption 2.3 is assumed (the inequality needs nothing else); the
   constant is a function K(L) of the Lipschitz constant, chosen first.
Disagreements with the author's review (shown 2026-10-17T12:22:03Z): none
