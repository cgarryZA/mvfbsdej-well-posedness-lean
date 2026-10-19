### A:eq:termg: Dissertation.PaperSpec.A.eq_termg
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba171988e2e6de37794 (pl-fp-v1:15480d57a7b017e059f8cf37ad2705ef42cdc014d87fed09bf3f995b216d4d52)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:31:22Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:16:08Z):
Reading of spec eq_termg, clause (4.3): E|g(X_T,Law X_T)|^2 <= C(E|X_T|^2 + |g(0,delta_0)|^2).
Setting: standing basis, g: R^n x P_2(R^n) -> R^m deterministic (Borel), satisfying the terminal Lipschitz
bound (eq:lipT) of Assumption 2.3 with constant L: for all X_T, X'_T in L^2(Omega,F_T;R^n),
|g(X_T,Law X_T) - g(X'_T,Law X'_T)| <= L(|X_T - X'_T| + W_2(Law X_T, Law X'_T)) a.s.
Conclusion: for every X_T in L^2(Omega,F_T;R^n), E|g(X_T,Law X_T)|^2 <= C(E|X_T|^2 + |g(0,delta_0)|^2), where
C depends only on L (follows from lipT at X'_T=0 and couplingT: C = max(8L^2, 2) suffices). Quantifier
order: C chosen as a function of L (or of the §4 parameters T,L,||G||,c_G,alpha,beta's,c_BDG) BEFORE g and X_T.
A statement with C depending on g or X_T would be weaker/unfaithful. Hypothesis on g: only lipT (the
interior Assumptions are not needed); requiring the full Assumption 2.3 or 2.2-2.5 would be narrower but
harmless if they can be met; g(0,delta_0) is the value at x=0, rho = Dirac at 0.
Note Law X_T in P_2(R^n) requires X_T in L^2. Witness: g(x,rho)=x (Example 5.1(i)).
Comparison (verdict recorded 2026-10-19T03:29:18Z):
Comparison, eq_termg (Sec4Coeff.lean:63-74) vs reading.
- ∃ K : ℝ → ℝ chosen first, then ∀ filtered probability space, n, m, T, L, g: C = K(L) depends on L only,
  chosen before g and X_T. Matches the quantifier order (the paper allows dependence on more parameters;
  dependence on L alone is stronger, as in the reading).
- Hypothesis LipTerminal ℱ P T L g: for all ℱ_T-measurable square-integrable X_T, X'_T, a.s.
  |g(X_T, Law X_T) - g(X'_T, Law X'_T)| ≤ L(|X_T - X'_T| + W2(Law X_T, Law X'_T)) -- exactly (2.6).
  No measurability of g is assumed (paper: g Borel); interior assumptions not needed. Broader.
- ∀ X_T strongly ℱ_T-measurable, MemLp 2: ∫⁻ |g(X_T, Law X_T)|² ≤ K(L)(∫⁻|X_T|² + |g(0, δ_0)|²), integrals
  in [0,∞]. For Borel g the left side is E|g(X_T,Law X_T)|². Matches (4.3); lawP2 junk irrelevant
  (X_T ∈ L²).
- Witness thm_cwp_hypotheses supplies Assumption 2.3 (hence LipTerminal) for an instance.
Verdict: broader.
Witness: —
Verdict: broader — Broader: g is not required to be Borel (the paper's g is), and the statement holds on every filtered
probability space and horizon. The printed (4.3) is the instance: the standing basis and filtration,
T the horizon, g the Borel terminal function satisfying (2.6) with constant L, C := K(L); for Borel g the
lintegral on the left is E|g(X_T,Law X_T)|^2.
Disagreements with the author's review (shown 2026-10-19T03:29:28Z): Label only. The review records "faithful" while noting itself that no measurability of g is assumed and
that the filtration/T are arbitrary ("broader; ... broader ambient generality"). Under the review rules a
proposition that drops a printed hypothesis (g Borel) is "broader", with the instantiation g Borel on the
standing basis, C := K(L); that is my verdict. No disagreement on content (C depends on L only, chosen
first; lintegrals avoid Bochner junk).
