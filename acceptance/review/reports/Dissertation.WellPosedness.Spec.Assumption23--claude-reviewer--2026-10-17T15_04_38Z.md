### A:ass:lip, A:cor:robust, A:ex:brownian, A:ex:concrete, A:lem:cont, A:lem:pert, A:lem:small, A:rem:cwp-class, A:rem:diag-mono, A:rem:generalrank, A:rem:intrinsic, A:sec4:horizon-not-contractive, A:sec:examples, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: Dissertation.WellPosedness.Spec.Assumption23
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 0d5048c72ef913b60000000000000000 (pl-fp-v1:dd9ab5ae5b841cdac1967ed31635366e7a453e9e614d1a9613856912df00d46d)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:04:38Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:35:27Z):
Unit: def Spec.Assumption23 (Assumption 2.3, Lipschitz coefficients; 16 more claims).
Paper: there is L >= 0 such that
 (interior) for a.e. t in [0,T] and all (Theta,mu), (Theta',mu') in D_t (Theta, Theta' in
   L^2(Omega, F_t; H), mu = Law(Theta), mu' = Law(Theta')), almost surely
   |delta b| + |delta sigma|_F + ||delta h||_{L^2(nu)} + |delta f|
       <= L (|delta X| + |delta Y| + |delta Z|_F + ||delta U||_{L^2(nu)} + W_2(mu, mu')),
   delta psi = psi(t, Theta, mu) - psi(t, Theta', mu');
 (terminal) for all X_T, X'_T in L^2(Omega, F_T; R^n), almost surely
   |g(X_T, rho) - g(X'_T, rho')| <= L (|X_T - X'_T| + W_2(rho, rho')), rho = Law(X_T),
   rho' = Law(X'_T).
Quantifier order: L is fixed first (exists L, or L a parameter of the predicate with L >= 0
required or harmless), then "for a.e. t" (one null set of times for all pairs), then all pairs of
F_t-measurable square-integrable H-valued inputs on the standing space, then a.s. The measure
argument is always the law of the input (diagonal). The norms: Euclidean on R^n, R^m,
Frobenius on R^{m x d} (and n x d for sigma), L^2(nu) norms for U and h. W_2 on P_2(H) with the
H-norm |x|^2 + |y|^2 + |z|_F^2 + ||u||^2, and on P_2(R^n) for the terminal part.
Faithful Lean: a predicate over (F, P, T, L, C) with those two clauses; the inputs ranging over
all strongly F_t-measurable (or a.e.) square-integrable random elements of H; the a.e. t set
chosen before the inputs; no extra condition (e.g. not pointwise Lipschitz in free (theta,mu)).
"for a.e. t, for all inputs" vs "for all inputs, for a.e. t" matters: the former is the paper's.
Comparison (verdict recorded 2026-10-17T15:01:23Z):
Assumption23 F P T L C (Spec/Assumptions.lean): fields nonneg : 0 <= L; interior : LipInterior F P T L C
(= for a.e. t in [0,T] (volume.restrict (Icc 0 T)), LipInteriorAt F P t L C); terminal :
LipTerminal F P T L C.g.
LipInteriorAt: for all p, p' in diagonalInputs F P t (Theta strongly F_t-measurable, MemLp 2, and
p.2 = lawP2 P Theta, its law), a.s.
 ||db|| + ||dsigma|| + ||dh|| + ||df|| <= L (||dx|| + ||dy|| + ||dz|| + ||du|| + w2H mu mu'),
with Euclidean norms on R^n, R^m, the EuclideanSpace (Fin _ x Fin d) norm = Frobenius for sigma
and z, the L^2(nu) norm for h and u, and w2H the W_2 distance of the Hilbert norm of H.
LipTerminal: for all strongly F_T-measurable square-integrable X_T, X'_T, a.s.
 ||g(X_T, lawP2 X_T) - g(X'_T, lawP2 X'_T)|| <= L (||X_T - X'_T|| + w2P(lawP2 X_T, lawP2 X'_T)).
Comparison with the reading: L fixed first (a parameter, L >= 0 required as printed "there is
L >= 0"; the statements quantify it in the right place); the a.e.-t quantifier precedes the inputs
(one exceptional time set); inputs are the diagonal (own laws, genuine since MemLp); a.s.
conclusion; norms and W_2 as in the paper. Strong F_t-measurability of the representative instead
of an a.e. class is harmless: every element of L^2(Omega, F_t; H) has a strongly F_t-measurable
representative, and modifying an input on a null set changes neither its law nor the a.s.
inequality. Nothing added, nothing missing.
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-17T15:04:21Z): none
