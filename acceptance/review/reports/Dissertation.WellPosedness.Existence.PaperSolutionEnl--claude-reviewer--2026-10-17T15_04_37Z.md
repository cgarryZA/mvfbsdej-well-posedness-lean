### A:cor:robust, A:eq:mvfbsdej, A:ex:concrete, A:intro:mvfbsdej, A:rem:cwp-class, A:rem:generalrank, A:thm3.1:companion, A:thm:cwp, A:thm:stab: Dissertation.WellPosedness.Existence.PaperSolutionEnl
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash a03b8b3d0b5b5f35c55bf194cd675c69 (pl-fp-v1:e90daacb5dd10dffd4538881ebc758b73033ec52679da3aa37db7705ea74e8df)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:04:37Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:34:00Z):
Unit: def Existence.PaperSolutionEnl (used by Cor 3.6 and 8 more claims: the well-posedness
statements). Paper notion (§3, "Solution space" and the definition of a solution):
A solution of (1.1) is a tuple Theta = (X, Y, Z, U) in the space S:
  X in S^2(0,T;R^n), Y in S^2(0,T;R^m): cadlag adapted, E sup_t |.|^2 < inf;
  Z in H^2_W(0,T;R^{m x d}): predictable, E int |Z|_F^2 < inf;
  U in H^2_N(0,T;L^2(nu;R^m)): predictable (P x E-measurable representative), E int ||U||^2 < inf;
satisfying, almost surely for every t in [0,T] (null set may be taken independent of t),
  X_t = xi_0 + int_0^t b(s,Theta_s,mu_s) ds + int_0^t sigma(s,Theta_s,mu_s) dW_s
        + int_0^t int_E h(s,Theta_s^-,e,mu_s^-) Ntilde(ds,de),
  Y_t = g(X_T, Law(X_T)) + int_t^T f(s,Theta_s,mu_s) ds - int_t^T Z dW - int_t^T int_E U Ntilde,
with mu_s = Law(Theta_s), mu_s^- = Law(Theta_s^-) (Borel representatives, a.e. equal to the
laws), h evaluated at the predictable tuple, everything over the standing filtration (usual
augmentation of W, N and the independent F_0; "Enl" = the initially enlarged filtration), xi_0
F_0-measurable square integrable (Assumption 2.2). Elements are equivalence classes
(indistinguishable / a.e.), so existence is "there is a representative" and uniqueness is
"any two coincide as classes".

A faithful Lean predicate: parameters (G0, driver, coefficients, xi_0, T), the filtration
enlJoint G0 D; fields: X, Y adapted cadlag (or right-continuous with the equation forcing
cadlag), E sup |X|^2, E sup |Y|^2 finite (S^2 membership, not only L^2(dt x dP)), Z, U
(predictable or progressive with the library integral) of finite energy; the forward and
backward identities a.s. at each t (or for all t a.s.) with the coefficient processes evaluated
along Theta with its own law at each time; the stochastic integrals the genuine ones of that
filtration; the jump coefficient through an L^2(nu) representative evaluated at Theta_s (equal
to Theta_{s-} dt x dP-a.e.). Must not require more than the paper (e.g. no extra integrability
beyond S), and must not allow less (e.g. not only H-weak integrability if it is called the
solution in S; Theorem 3.3 uses the weak class separately).
Comparison (verdict recorded 2026-10-17T12:38:49Z):
PaperSolutionEnl D hG0 hind0 T C xi0 X Y Z U gamma := PaperSolution D (enlJoint G0 D hG0)
(Brownian/Poisson filtration proofs from hind0) T C xi0 X Y Z U gamma (GlobalEnl.lean:39).
The unit fixes the filtration to the standing one (enlJoint, reviewed: usual augmentation of
W, N, G0) with G0 independent of the driver, and the rest is PaperSolution
(System/PaperSolution.lean:201), which I read to judge the meaning:
* X, Y in S^2: adapted at each t in [0,T], every path right-continuous on [0,T), a.e. path with
  left limits on (0,T], E sup_{[0,T]} |X|^2, |Y|^2 < inf (lintegral of a sup of squared norms).
  Matches (cadlag up to indistinguishability; the PaperSpec Solution adds everywhere left limits).
* Z in H^2_W, U in H^2_N: coordinates predictable / marked predictable, finite (marked) energy,
  vanishing off [0,T] (normalisation). Matches.
* Laws: mu_s = lawP2 P Theta_s (true law at every s), mu_s^- = lawP2 of the predictable tuple
  (leftLimProc X, leftLimProc Y, Z, U); the paper uses Borel representatives agreeing a.e.
* h at the predictable tuple: gamma represents e |-> h(s, Theta_s^-, e, mu_s^-) nu-a.e. for a.e. s,
  a.s.; gamma jointly measurable and marked progressive (the paper's representative is
  predictable; the library integral needs only marked progressive and the dt x dP x nu class).
  leftLim at s = 0 reads values at negative times, which are unconstrained, but s = 0 is a
  Lebesgue-null time and jump_rep is a.e. in s.
* Identities: on one full-measure set, for every t in [0,T],
  X_t = xi0 + int_{[0,t]} b(s,Theta_s,mu_s) ds + M_t + int_0^t int_E gamma dNtilde, and
  Y_t = g(X_T, Law X_T) + int_{[t,T]} f ds - (M'_T - M'_t) - (J^U_T - J^U_t), with M, M' a.s.-cadlag
  versions of the library Brownian integrals (diffusion row i against the d-dim W; Z row k). This is
  the paper's "a.s. for every t, null set independent of t".
* Extra fields: joint/progressive measurability and finite energy of the drift, diffusion,
  driver processes along Theta and of gamma. The paper's definition presupposes that the integrals
  exist; under the standing measurability (2.5) and Assumptions 2.2-2.3 these hold for every
  tuple of S (paper (4.3)), so in the statements that use this predicate (existence /
  well-posedness under 2.2-2.5 and JointBorel) they are automatic. Without those assumptions the
  finite-energy fields are stronger than mere existence of the integrals (a.s. local
  integrability), but no statement using PaperSolutionEnl is posed there (the weak class of
  Thm 3.3 has its own predicate).
* xi0's L^2(F_0) membership is part of Assumption 2.2, not of the solution; fine.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — 1. Filtration fixed to enlJoint G0 D (the standing usual augmentation), independence of G0 as an
   argument; faithful.
2. S^2 paths: right-continuous everywhere on [0,T), left limits only a.s. (indistinguishability-
   invariant form of cadlag); Z, U predictable with finite energy, vanishing off [0,T].
3. Laws are the true laws lawP2 at every time instead of Borel representatives (a.e. equal).
4. The Poisson integral of the forward equation uses a jointly measurable, marked progressive
   representative gamma of h at the predictable tuple (nu-a.e., a.e. s, a.s.), instead of a
   predictable one; the library integral depends only on the dt x dP x nu class.
5. Brownian integrals are taken through a.s.-cadlag versions agreeing a.s. at each time with the
   library's per-time integral, so the identities can hold on one full-measure set for all t.
6. Finite energy (and measurability) of the coefficient processes along Theta are fields; the
   paper derives them from (2.5) and Assumptions 2.2-2.3 for every tuple of S, under which all
   statements using this predicate are posed.
Disagreements with the author's review (shown 2026-10-17T15:04:20Z): No disagreement on substance. The author's review is an empty marker with no recorded
comparison; the representation choices listed in my detail are not recorded there.
