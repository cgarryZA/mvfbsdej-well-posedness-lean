### A:cor:robust: Dissertation.PaperSpec.A.cor_robust_lip
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash ed839d34f480cba14b18016daa0b4aac (pl-fp-v1:1c0b2472fa7cc5475eff926b5def78c0b27cea2a6819205588ff76fccf6024ec)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T16:03:52Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T15:47:47Z):
Reading of spec cor_robust_lip (Corollary 3.6, last sentence: "If, in addition, the
perturbations are independent of theta and W_2-Lipschitz, (3.5) |dp_b|+|dp_sigma|_F+
|dp_h|_{L^2(nu)}+|dp_f| <= L_p W_2(mu,mu') for a.e. t and all diagonal pairs, then (3.4) holds
with c_pert = |G| L_p").

Setting: standing basis, horizon T > 0, m = n (the corollary's standing hypothesis; the
implication itself does not need it, so a statement for general m, n is broader and fine),
d >= 1, sigma-finite nu; G in R^{m x n} (full rank in the corollary - not needed for this
implication; broader fine); |G| operator norm.
Perturbations p_b : [0,T] x H x P_2(H) -> R^n, p_sigma -> R^{n x d}, p_h -> L^2(nu;R^n),
p_f -> R^m; "independent of theta": p_psi(t, theta, mu) = p_psi(t, mu) (deterministic
along diagonal inputs). (Dropping independence is broader and still true.)
Hypothesis (3.5): for a.e. t in [0,T] and all diagonal inputs (Theta, mu), (Theta', mu') in
D_t (Theta, Theta' in L^2(Omega, F_t; H), mu = Law Theta, mu' = Law Theta'):
 |dp_b| + |dp_sigma|_F + |dp_h|_{L^2(nu)} + |dp_f| <= L_p W_2(mu, mu') (a.s. / deterministic),
 L_p >= 0.
Conclusion (3.4) with c_pert = |G| L_p: for a.e. t and all such pairs,
 E[<dp_b, G^T dY> + <dp_sigma, G^T dZ>_F + <-dp_f, G dX> + int_E <dp_h(e), G^T dU(e)> nu(de)]
   <= |G| L_p E[|dX|^2 + |dY|^2 + |dZ|_F^2 + |dU|^2_{L^2(nu)}].
Quantifier order: exists null set of times (a.e. t), then all diagonal pairs - in both
hypothesis and conclusion. Also a statement "for each t at which (3.5) holds for all pairs,
(3.4) holds at t for all pairs" is fine (stronger).
Constant: exactly |G| L_p. Inner products: Frobenius for sigma, L^2(nu) for h. W_2 on P_2(H).
Comparison (verdict recorded 2026-10-17T16:01:29Z):
Comparison, cor_robust_lip (Sec3.lean:240-250).
Setting: any probability space and filtration indexed by R (broader than the standing basis),
sigma-finite nu on countably generated E, n d with 0 < n, T > 0, m = n built in (p : Coeffs nu n
n d, G : n x n); G arbitrary (full rank not assumed: broader).
Hypotheses: p.TupleIndep (p_b, p_sigma, p_h, p_f independent of theta - "independent of
theta"); LawLip35 F P T Lp p: for a.e. t in [0,T] and all q, q' in D_t (strongly F_t-measurable,
L^2, law = lawP2), a.s. |dp_b| + |dp_sigma| + |dp_h|_{L^2} + |dp_f| <= Lp w2H(mu, mu') - (3.5) with
the Hilbert W_2. The perturbations' origin-integrability and diagonal-Lipschitz conditions of
Assumptions 2.2-2.3 and the baseline assumptions are not assumed (not needed): broader.
Conclusion: PairingBound34 F P T G (|GX G| Lp) p: for a.e. t, all q, q' in D_t, the pairing is
integrable and E[<dp_b, G^T dY> + <dp_sigma, G^T dZ>_F + <-dp_f, G dX> + int <dp_h(e), G^T
dU(e)> nu(de)] <= |G| Lp E[|dX|^2+|dY|^2+|dZ|^2+|dU|^2] - (3.4) with c_pert = |G| Lp, |G| =
operator norm of x |-> Gx (Euclidean). Quantifier order a.e. t then all pairs - matches.
Instantiation: the Corollary's perturbations (with their Assumption 2.2-2.3 conditions) and
its full-rank G are special cases.
Witness cor_robust_lip_hypotheses: a constant perturbation p_sigma = e_11 with Lp = 1 - fine.
Verdict: broader.
Witness: —
Verdict: broader — Broader than printed. The Lean keeps m = n, tuple-independence of the perturbation and (3.5)
(with the Hilbert-norm W_2, a.e. t, all diagonal pairs, a.s.), and concludes (3.4) with
c_pert = |G| L_p, but drops the context hypotheses: G of full rank, the perturbations' origin-
integrability and diagonal Lipschitz conditions, the baseline's assumptions; and it works over
any filtration. None is used by the implication. Instantiation: the Corollary's perturbations on
the standing basis with its full-rank G.
Disagreements with the author's review (shown 2026-10-17T16:01:36Z): The author's review recorded for this unit is empty (its text is attached to an adjacent review marker of a unit outside this chunk and was not shown), so there is nothing to compare point by point. My verdict: broader - the proposition keeps m = n, tuple independence and (3.5), but drops G of full rank and the perturbations' origin-integrability and diagonal-Lipschitz conditions, which the implication does not use.
