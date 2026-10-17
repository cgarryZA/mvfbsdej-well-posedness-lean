### A:cor:robust, A:eq:mvfbsdej, A:ex:concrete, A:intro:mvfbsdej, A:rem:cwp-class, A:rem:generalrank, A:thm3.1:companion, A:thm:cwp, A:thm:stab: Dissertation.WellPosedness.System.PaperSolution
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 0dd47e8a79576bf20000000000000000 (pl-fp-v1:548810fe1944bd5aaa604f0ac1624282d93688676d2b2723c2d83a963efbd173)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:06:15Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:33:34Z):
Reading for PaperSolution (paper: §3 "A solution of (1.1)").
Setting: (Omega, F, (F_t), P) usual conditions, T>0, n,m,d>=1; W d-dim BM; N independent PRM on
R_+ x E, intensity dt nu(de), nu sigma-finite, E countably generated; Ntilde = N - dt nu; filtration
= usual augmentation of sigma(W, N, F_0). Coefficients (b, sigma, h, f, g) deterministic, Borel; initial
datum xi_0 (in L^2(F_0) under Ass 2.2; but the notion of solution itself just needs xi_0 F_0-meas.).
A solution is Theta = (X,Y,Z,U) in HH:
 - X in S^2(R^n): cadlag adapted, E sup_{t<=T}|X_t|^2 < inf; Y in S^2(R^m) likewise;
 - Z in H^2_W(R^{m x d}): predictable, E int_0^T |Z_t|_F^2 dt < inf;
 - U in H^2_N(L^2(nu;R^m)): predictable (P (x) calE-measurable representative),
   E int_0^T ||U_t||^2_{L^2(nu)} dt < inf;
satisfying, for every t in [0,T], almost surely,
 X_t = xi_0 + int_0^t b(s,Theta_s,mu_s) ds + int_0^t sigma(s,Theta_s,mu_s) dW_s
       + int_0^t int_E h(s,Theta^-_s,e,mu^-_s) Ntilde(ds,de),
 Y_t = g(X_T, Law(X_T)) + int_t^T f(s,Theta_s,mu_s) ds - int_t^T Z_s dW_s
       - int_t^T int_E U_s(e) Ntilde(ds,de),
where mu_t = Law(Theta_t), mu^-_t = Law(Theta^-_t) (Borel representatives, equal to the true laws a.e. t),
Theta^-_t = (X_{t-}, Y_{t-}, Z_t, U_t). Law(X_T) in P_2(R^n) (X_T in L^2 since X in S^2). The
integrals: Lebesgue ds-integral pathwise, the Ito integral of the n x d (resp. m x d) matrix
integrand against the d-dim W (sum over Brownian components), the compensated-Poisson integral of
the predictable integrand. "For every t a.s." (equivalently, by cadlag, a.s. for all t).
Faithful Lean: the class conditions above (S^2 for X,Y, not merely Hweak), the integral identities at
every t in [0,T] a.s. (or a.s. simultaneously for all t), the right law arguments (law of the full
tuple at time s under P, left-limit tuple for h), the right integrals (no junk: the integrals must
be shown/required to be defined, e.g. via an admissibility condition), the same initial datum.
Using a representative gamma of the jump coefficient is acceptable if it is required to represent
h(s,Theta^-_s,.,mu^-_s) in L^2(nu) for a.e. (s,omega). The backward equation must use the given Z,U
(the same as the tuple's components), and the terminal value g(X_T, Law X_T) must use the
tuple's X at T.
Comparison (verdict recorded 2026-10-17T12:39:11Z):
Comparison for PaperSolution (System/PaperSolution.lean:201). Read with Solves.lean (coefficient
processes, terminalVal), Tuple.lean (tupleAt, uLift, TupleH), LawP2 (lawP2), LawFlow (leftLimProc),
PairDiff (esq), LevyStochCalc (energy, markedEnergy, Predictable/MarkedPredictable sigma-algebras,
Multidim Ito integral = sum over j of 1-d L^2 integrals against W^j, compensated Poisson L^2 integral
as cadlag modification). Also checked its uses in PaperSpec/A/Setting.lean (Solution wraps it and
adds every-path left limits) and Sec3.lean (thm_stab, thm_cwp, cor_robust_wp all assume
JointBorel + Ass 2.2 + Ass 2.3 for every system whose solutions are quantified).

Against my reading:
- Theta in HH: X_adapted (each coordinate F_t-measurable for t in [0,T]), every path right-continuous
  on [0,T), a.s. left limits on (0,T], X_sup: E sup_{t in [0,T]} sum_i X_{i,t}^2 < inf (esq is the
  squared Euclidean norm). Same for Y. Z: each coordinate predictable (predictableSigma), finite
  energy on [0,T], vanishes off [0,T]. U: each coordinate marked predictable (sigma-algebra generated
  by F x (r,q] x B, F in F_r, nu(B) < inf; equal to P (x) calE on times > 0 for sigma-finite nu),
  finite marked energy, vanishes off [0,T]. Matches S^2 x S^2 x H^2_W x H^2_N (with
  representation choices below).
- Integrals exist: joint/progressive measurability and finite energy of drift, diffusion, driver
  processes, and of the jump representative gamma (cut to [0,T]); jump_rep: gamma = h(s, Theta^-_s, ., mu^-_s)
  nu-a.e. for a.e. s, a.s.
- Forward identity: exists M, a version (a.s. at each t in [0,T]) of the multidim Ito integral of
  row i of sigma(s,Theta_s,mu_s), a.s. cadlag on [0,T], with a.s. for all t in [0,T]:
  X_t = xi0 + int_{[0,t]} b ds + M_t + int_0^t int_E gamma Ntilde. Matches (1.1) first line.
- Backward identity: a.s. for all t in [0,T]: Y_t = g(X_T, Law X_T) + int_{[t,T]} f ds - (M_T - M_t)
  - (int_0^T int U Ntilde - int_0^t int U Ntilde), with M a cadlag version of int Z dW. terminalVal is
  g(X_T(omega), lawP2 P X_T): X_T in L^2 by X_sup, so the true law. Matches (1.1) second line.
- Law arguments: mu_s = lawP2 P Theta_s (full tuple, time s, under P), mu^-_s = lawP2 P Theta^-_s with
  Theta^- = (X_-, Y_-, Z, U). Matches with exact laws in place of Borel representatives.
- "for every t a.s." vs "a.s. for all t": Lean states the latter, which the paper says is
  equivalent (both sides cadlag); with every path of X right-continuous and M, the Poisson integral
  and the Lebesgue integral a.s. right-continuous, the two are equivalent.
- Extra requirements vs. my reading: finite energy of b and f (more than existence of the
  Lebesgue integrals) and measurability of the coefficient processes as fields. Every claim
  using PaperSolution assumes JointBorel and Ass 2.2-2.3 for the system concerned, under which a
  paper solution in HH satisfies these ((2.5), (4.2)), so they are harmless there.
- Initial datum xi0 is any function (Ass 2.2 supplies F_0-measurability and L^2 in the claims).
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices (harmless):
1. Coordinate encoding: X, Y, Z, U as families of real processes indexed by R; Z's rows give the
   m x d channel (Frobenius norm via EuclideanSpace on pairs); U a real function of (s, omega, e).
2. Cadlag: every path right-continuous on [0,T), left limits only a.s. on (0,T] (invariant under
   indistinguishability; the PaperSpec wrapper Solution adds every-path left limits). Nothing is
   asked of X, Y off [0,T].
3. Z, U vanish off [0,T] (normalisation); the marked-predictable sigma-algebra has no time-0 cells,
   forcing U_0 = 0 (and predictability forces Z_0 = 0): a Lebesgue-null time.
4. Finite energy of the drift and driver processes and joint/progressive measurability of all
   coefficient processes are fields; every claim using the unit assumes JointBorel and Ass 2.2-2.3,
   under which every paper solution in HH has them ((2.5), (4.2)).
5. Exact laws lawP2 P Theta_s at every time (Dirac 0 off L^2) instead of Lemma A.1's Borel
   representatives; equal for a.e. s, so integrals unchanged. uLift junk 0 on a dt dP-null set.
6. Poisson integrand through a marked-progressive representative gamma equal to the predictable-tuple
   evaluation nu-a.e. for a.e. s, a.s.; same L^2 integral.
7. Identities stated a.s. simultaneously for all t in [0,T], with a cadlag version M of the per-time
   Brownian L^2 integral: equivalent to the paper's "a.s. for every t" (paper says so).
8. xi0 is an arbitrary function here; its F_0-measurability and square integrability come from
   Ass 2.2 in the claims.
Disagreements with the author's review (shown 2026-10-17T15:05:44Z): none (the author's excerpt shown for this unit is a marker and at most a section heading, with no
item-level reading to compare against; my comparison file records the representation choices in
detail).
