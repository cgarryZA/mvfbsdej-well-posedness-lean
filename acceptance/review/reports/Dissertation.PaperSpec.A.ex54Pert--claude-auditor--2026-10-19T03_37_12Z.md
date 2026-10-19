### A:ex:fulllaw, A:rem:regimes: Dissertation.PaperSpec.A.ex54Pert
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash a358f11639418d450e7e870df0a64a0c (pl-fp-v1:b8ce5a059094cc38fc3923a0137340c5cbfb4a5888c9733bb2e8ea4ec978aeca)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:37:12Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:18:00Z):
Reading of def:Dissertation.PaperSpec.A.ex54Pert (Example 5.4, 05-examples.tex:292-297).

Paper notion: the perturbation added to the baseline in Example 5.4:
  p_f(t,theta,mu) = eps q(W_2(mu,mu_0)) w_0 + eps Q(int phi_1 dmu^U, ..., int phi_J dmu^U) w_1,
  p_b(t,theta,mu) = eps q~(W_2(mu^U,Lambda_0)) v_0,
  p_h(t,theta,e,mu) = eps q^(W_2(mu^U,Lambda_0)) h^(e),
  p_sigma = 0, and g unchanged (no terminal perturbation);
with mu_0 in P_2(H), Lambda_0 in P_2(L^2(nu)), eps > 0, q,q~,q^ : R_+ -> R, Q : R^J -> R,
phi_j : L^2(nu) -> R (bounded Lipschitz), w_0,w_1 in R^m, v_0 in R^n, h^ in L^2(nu;R^n);
mu^U the U-marginal of mu (pushforward under theta -> u), int phi_j dmu^U = int phi_j(u) mu(dtheta).
The perturbations are independent of theta and of t.

A faithful Lean definition must reproduce each channel exactly: which statistic enters which
channel (full-law radial in f; U-marginal radial in b with v_0 and in h with h^; the cylindrical
Q-term in f with w_1), the W_2 distances on the right spaces (P_2(H) for the first, P_2(L^2(nu;R^m))
for the U-marginal ones), sigma-perturbation 0, terminal perturbation 0 (or absent). Junk values:
W_2 for measures outside P_2 (only arguments in P_2 occur on diagonal inputs), the integral of
phi_j against a measure (bounded phi_j, so integrable for probability measures).
Comparison (verdict recorded 2026-10-19T03:34:54Z):
Comparison: def ex54Pert nu n d J eps q qb qh Q phi mu0 Lambda0 w0 w1 v0 hhat
(PaperSpec/A/Sec5.lean:430-448) =
Coeffs.ofLaw (p_b := eps qb(W_2(mu^U,Lambda0)) v0) (p_sigma := 0)
  (p_h := eps qh(W_2(mu^U,Lambda0)) hhat)
  (p_f := eps q(W_2(mu,mu0)) w0 + eps Q((int phi_j dmu^U)_j) w1) : Coeffs nu n n d.
Reading: p_f = eps q(W2(mu,mu0)) w0 + eps Q(int phi_1 dmu^U, ..., int phi_J dmu^U) w1;
p_b = eps q~(W2(mu^U,Lambda0)) v0; p_h = eps q^(W2(mu^U,Lambda0)) h^; p_sigma = 0; g unchanged;
mu0 in P_2(H), Lambda0 in P_2(L^2(nu)), w0, w1 in R^m, v0 in R^n, h^ in L^2(nu;R^n); m = n;
theta- and t-independent.
- Channels: q (full law, W_2 = w2H, Hilbert norm of H) in f with w0; qb in b with v0 and qh in h with
  hhat, both at w2P(mu.margU, Lambda0), the W_2 of the norm of L^2(nu;R^n); the Q-term in f
  with w1; sigma-perturbation 0. Matches channel by channel, with qb = q~, qh = q^.
- mu.margU = pushforward of mu under the projection onto the U-channel (Law/TupleMarginal.lean),
  so int phi_j u d(mu.margU.law) = int phi_j(u) mu(dtheta). Matches.
- m = n (Coeffs nu n n d) as in Example 5.4 (baseline of Cor 3.6), so L^2(nu;R^m) = L^2(nu;R^n)
  and w0, w1, v0 in R^n. Matches.
- Independent of t and theta: the ofLaw arguments ignore time, and ofLaw ignores theta. The
  terminal component is 0 and is not used by perturb, so g is unchanged. Matches.
- Junk values: the Bochner integral of phi_j would be 0 if phi_j were not integrable, but in every
  use phi_j is Lipschitz (hence integrable against P_2 laws). Profiles q : R -> R are evaluated
  only at W_2 >= 0. Harmless.
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-19T03:37:07Z): none
