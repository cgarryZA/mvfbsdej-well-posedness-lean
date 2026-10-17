### A:ex:concrete: Dissertation.PaperSpec.A.ex_concrete_ii_mean
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash ed839d34f480cba1adb40add6e4f8112 (pl-fp-v1:34ddf4bc033fa61ac98044ebade2bbc057a9826cd7affde3bad67b959eea9ea6)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T12:19:08Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:18:49Z):
# Reading: ex_concrete_ii_mean, clause "(ii) the mean and the barycentre"

Paper (Ex 5.1(ii)): m_Psi(mu) = int pi_Psi(theta) mu(dtheta), dm = (dm_X, dm_Y, dm_Z, dm_U) =
int theta dmu - int theta dmu' in H; b(rho) = int x rho(dx). "Both dm and b(rho) are integrals of
the identity map, which is 1-Lipschitz, so (2.10) applies on P_2(H) and on P_2(R^n).
Cauchy-Schwarz across the four coordinates of H then splits the first bound":
  |dm|_H <= W_2(mu, mu'),   |b(rho) - b(rho')| <= W_2(rho, rho'),
  |dm_X| + |dm_Y| + |dm_Z|_F + ||dm_U|| <= 2 |dm|_H <= 2 W_2(mu, mu').
Faithful statement: for all mu, mu' in P_2(H) (H with its Hilbert norm |theta|_H^2 = |x|^2 +
|y|^2 + |z|_F^2 + ||u||^2; W_2 the Hilbert-norm Wasserstein distance), the three inequalities
above, with |.|_H the Hilbert norm (not a max norm -- with the max norm the constant 2 would be
4 and the first bound would be a different statement); and for all rho, rho' in P_2(R^n) the
barycentre bound. Setting: n = m = d = 1 as in the example (general n, m, d is a harmless
generalisation), any sigma-finite nu (the U-mean is a Bochner mean in L^2(nu)).
No probabilistic basis needed (deterministic statement about laws).
Comparison (verdict recorded 2026-10-17T12:19:03Z):
# Comparison: ex_concrete_ii_mean

Lean (Sec5.lean:228): for every sigma-finite nu on a countably generated E: for all mu, mu' in
P_2(H) (n = m = d = 1): tupleMean mu has the marginal means as channels; ||toL2 (dm)|| <= w2H mu mu'
(toL2 into the Hilbert-norm tuple space, ||toL2 theta||^2 = |x|^2 + |y|^2 + |z|^2 + ||u||^2, w2H the
Hilbert-norm W_2); |dm_X| + |dm_Y| + |dm_Z| + ||dm_U|| <= 2 ||toL2 dm||; and for rho, rho' in
P_2(R^1): |b(rho) - b(rho')| <= w2P rho rho'.

Against my reading: all three printed inequalities (the final "<= 2 W_2" is the composition of
the first two), with the Hilbert norm as required; plus the identification of the channels of
the mean with m_Psi (printed: "dm = (dm_X, ..., dm_U) = int theta dmu - int theta dmu'"). Setting
n = m = d = 1 as in the example. No hypotheses to witness.

Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-17T12:19:03Z): none
