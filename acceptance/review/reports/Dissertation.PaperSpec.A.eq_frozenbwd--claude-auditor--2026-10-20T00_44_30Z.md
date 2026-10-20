### A:eq:frozenbwd: Dissertation.PaperSpec.A.eq_frozenbwd
Pins: manuscript A None; project 6d403c197bfb10fe8808933c6e525ee0ae544fb1; hash ed839d34f480cba178b77fba8e33d01f (pl-fp-v1:5fca5bf624f3b2d8ef37924d6e351591a603294616df002528fce4ca58097e63)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-20T00:44:30Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-20T00:30:26Z):
Reading of (4.8) (eq:frozenbwd, manuscript/paper/sections/04-proof-wellposedness.tex,
lines 287-310, inside the proof of Lemma 4.2 = lem:small).

Setting and hypotheses: as for (4.7): the standing setting of Section 2 (Brownian motion W,
independent Poisson random measure N with sigma-finite intensity on a countably generated mark
space, usual augmentation of the filtration of W, N, F_0), deterministic jointly Borel
coefficients, Assumptions 2.2 (ass:integ) and 2.3 (ass:lip) only, lambda in [0,1], a forcing q
(q^b, q^sigma, q^f progressive and L^2; q^h predictable, L^2(dP dt nu); q^g_T in
L^2(Omega,F_T;R^m)), xi_0 in L^2(F_0), a trial Theta in S (the solution space \HH), and Xbar
the solution of (4.7) (in S^2(0,T;R^n)). Laws: mu^Theta_s the Borel law flow of Theta;
Law(Xbar_T) the law of Xbar_T under P, in P_2(R^n).

Assertions of the passage:
 (a) Xi := lambda g(Xbar_T, Law(Xbar_T)) + q^g_T + int_0^T (lambda f(s,Theta_s,mu^Theta_s)
     + q^f_s) ds lies in L^2(Omega, F_T; R^m) (by (4.3), (4.2) for f, and the integrability of
     q). Here F_T-measurability is part of the claim.
 (b) Intermediate construction: M_t := E[Xi | F_t]; by the PRP there are unique Zbar in H^2_W,
     Ubar in H^2_N with M_t = M_0 + int_0^t Zbar dW + int_0^t int_E Ubar Ntilde; Ybar_t :=
     M_t - int_0^t (lambda f + q^f) ds; M in S^2 (Doob), Ybar in S^2 (Cauchy-Schwarz).
 (c) (Ybar, Zbar, Ubar) solves the frozen linear BSDE (4.8):
     Ybar_t = lambda g(Xbar_T, Law(Xbar_T)) + q^g_T + int_t^T (lambda f(s,Theta_s,mu^Theta_s)
     + q^f_s) ds - int_t^T Zbar dW - int_t^T int_E Ubar(e) Ntilde(ds,de), a.s. for every t in
     [0,T].
 (d) Hence Thetabar = (Xbar, Ybar, Zbar, Ubar) in S, and Phi_lambda : S -> S is well defined
     (the image is determined by Theta as an element of S).

A faithful formal statement: for every basis, coefficient system satisfying Assumptions 2.2-2.3,
lambda in [0,1], forcing q, xi_0, Theta in S, and every solution Xbar of (4.7) (with whatever
regularity (4.7) gives), (a) holds; there exist Ybar cadlag adapted with E sup|Ybar|^2 <
infinity, Zbar predictable in H^2_W, Ubar predictable in H^2_N such that (4.8) holds a.s. for
each t (so Thetabar in S); and well-definedness: Thetabar is unique in S (any two tuples
(Xbar, Ybar, Zbar, Ubar) with Xbar solving (4.7) and (Ybar, Zbar, Ubar) solving (4.8) in S agree:
Xbar, Ybar indistinguishable, Zbar dt x dP-a.e., Ubar dt x dP x nu-a.e.). The uniqueness of the
solution of the linear BSDE is not literally printed at (4.8) (the paper says "Phi_lambda well
defined" and proves uniqueness of BSDE solutions in the "Conversely" paragraph by the same PRP
argument); stating it is a faithful reading of "well defined". The intermediate objects (b) are
proof devices; their omission is harmless only if the existence of (Ybar, Zbar, Ubar) and the
membership in S are stated. The terminal law must be the law of the actual Xbar_T (not of a
representative or of X_T of the trial), and g, f must enter with the factor lambda; f is
evaluated at (Theta_s, mu^Theta_s) of the trial, not at Thetabar. Extra hypotheses (monotonicity,
lambda small, finite nu, more regularity of Theta) would make it narrower.
Comparison (verdict recorded 2026-10-20T00:43:39Z):
Comparison of Dissertation.PaperSpec.A.eq_frozenbwd (Dissertation/PaperSpec/A/Sec4Frozen.lean)
with (4.8) and its surrounding text (manuscript/paper/sections/04-proof-wellposedness.tex,
lines 287-310, proof of Lemma 4.2).

Setting and hypotheses: identical to eq_frozenfwd (standing setting; JointBorel, Assumption22,
Assumption23 with L; lam in [0,1]; PredForcing; trial Theta with HTuple). These are the
hypotheses in force in Lemma 4.2. Matches (see the comparison for (4.7) for the conventions).

Conclusion 1 (Xi in L^2(Omega, F_T; R^m)): for every X' with FrozenForward and every coordinate k,
the function omega -> lam g(X'_T, Law X'_T)_k + q^g_k + int_[0,T] (lam f_k(s, Theta_s, Law
Theta_s) + q^f_k) ds is strongly measurable for F_T of the augmented filtration and in L^2(P).
terminalVal is g at X'_T and the law (lawP2) of X'_T, the new forward process, as printed; the
driver is f along the trial Theta and its law; lambda multiplies g and f only. The quantifier is
over all solutions of (4.7) in the FrozenForward sense (no S^2 requirement): broader than "every
solution in S^2", harmless. The s-integral is a pathwise Bochner integral (0 on the omega's whose
section is not integrable, a P-null set under the hypotheses); the claim of strong F_T-measurability
of this specific function is at least the paper's (class) statement.

Conclusion 2 (existence): there are X', Y', Z', U' with FrozenStep: X' solves (4.7)
(FrozenForward), each coordinate of (Y', Z', U') solves the linear BSDE (4.8) with terminal value
lam g(X'_T, Law X'_T) + q^g and driver lam f(s, Theta_s, mu_s) + q^f, a.s. at each t in [0,T]
(LinearBSDEJ), and (X', Y', Z', U') satisfies HTuple (Thetabar in S: cadlag paths, E sup finite,
Z' predictable, U' marked predictable, finite energies). This is "there is Thetabar = (Xbar, Ybar,
Zbar, Ubar) in S with Xbar solving (4.7) and (Ybar, Zbar, Ubar) solving (4.8)". The X-component is
chosen with the rest instead of being the given Xbar; by the uniqueness clause of (4.7) it is
indistinguishable from any given solution, so the two readings agree in S.

Conclusion 3 (uniqueness): two FrozenStep tuples have indistinguishable X' and Y' on [0,T] and
differences of Z' and U' of zero energy (dt x dP and dt x dP x nu), i.e. they are equal in S under
the identification of Section 3. This is the reading of "Phi_lambda : S -> S is well defined",
with the uniqueness of (Zbar, Ubar) asserted by the PRP and proved for solutions of (4.8) in the
"Conversely" paragraph by the same argument. Not more than the passage claims.

Representation choices (each harmless): coordinatewise equations; "for each t a.s." with
right-continuous paths; integral over [t,T] for (t,T]; stochastic integrals over (t,T] as
differences of the library's integral processes; expectations in [0, infinity]; the pointwise law
flow of the trial in place of the Borel representative (differs on a Lebesgue-null set of times,
inside ds-integrals); "equal in S" as indistinguishability / zero energy; Phi_lambda encoded as the
relation FrozenStep rather than a function (equivalent given conclusions 2-3).

Witness: Dissertation.Acceptance.A.frozen_hypotheses exhibits the hypotheses (lam = 1, zero
forcing, the zero trial) at the affine instance of Example 5.1(i) with nu a Dirac mass. Non-vacuous.

Coverage (claim A:eq:frozenbwd in acceptance/claims.json, one clause). The clause states the
L^2(F_T) membership of Xi, the existence of Thetabar in S solving (4.7)-(4.8), and its uniqueness
in S. Not stated: the intermediate objects of the construction (M_t = E[Xi | F_t] and M in S^2,
its predictable representation with Zbar, Ubar, and Ybar = M - int_0^. (lam f + q^f) ds), which the
authors record as not stated. That is right, and it does not matter: they are proof devices whose
outputs (existence of a solution in S and uniqueness of (Zbar, Ubar)) are stated; the explicit
formula Ybar_t = E[Xi | F_t] - int_0^t (...) is a consequence of any solution in S and is re-derived
by the paper where it is needed ("Conversely"). One further implicit assertion of "Phi_lambda : S
-> S well defined" is not stated: that the image does not depend on the representative of the
trial in S (Lemma A.1, last assertion); it is minor and belongs to Lemma A.1's claims. No clause
states something the passage does not claim (the uniqueness is the content of "well defined").
The hypotheses are exactly those in force at that point of the printed proof (standing setting,
Assumptions 2.2-2.3, lambda in [0,1], a forcing of the class of (4.1), Theta in S); the "for every
solution Xbar of (4.7)" is the printed quantifier, here over the larger FrozenForward class.
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless:
(1) Xi in L^2(Omega,F_T;R^m) is stated per coordinate: the given function is strongly
F_T-measurable for the augmented filtration and lies in L^2(P). The ds-integral is a pathwise
Bochner integral, junk only on a P-null set. This states at least the class statement.
(2) "Every solution of (4.7)" ranges over all FrozenForward solutions, which need only be
right-continuous. That is broader than the printed quantifier.
(3) The existence clause chooses the X-component together with (Ybar, Zbar, Ubar). By the
uniqueness in (4.7) it is indistinguishable from any given solution, so it agrees with the given
Xbar in S.
(4) "Thetabar in S" is HTuple, a predicate on representatives (every path cadlag on [0,T]; Z, U
predictable and vanishing off [0,T]). "Equal in S" is indistinguishability of X and Y plus zero
energy of the Z and U differences, which is the paper's identification.
(5) The uniqueness clause is the reading of "Phi_lambda : S -> S is well defined". The PRP
uniqueness supports it, and so does the paper's own "Conversely" argument.
(6) The law flow of the trial is the pointwise law, not the Borel representative. The two differ
only on a Lebesgue-null set of times, inside ds-integrals.
(7) The BSDE holds for each t a.s., over [t,T]. The stochastic integrals are written as
differences of the library integral processes.
Disagreements with the author's review (shown 2026-10-20T00:43:45Z): On eq_frozenbwd itself I agree with the review, with no substantive disagreement. My verdict is
"faithful with representation choices": the review's readings are those choices (coordinatewise
L^2(F_T), the pathwise Bochner drift integral, FrozenStep as a relation, "equal in S" as
indistinguishability and zero energy, existence with the X-component re-chosen). The joint
verdict line, "faithful (both true as printed ...)", also covers (4.7), where I disagree (see that
unit): the existence part of (4.7) does not state that Xbar has left limits.

Two small points.
(1) "Phi_lambda : S -> S is well defined" also contains independence from the representative of
the trial in S. Neither clause states it; it is Lemma A.1's last assertion and minor.
(2) The witness's "two trials", the zero tuple and the solution of Theorem 3.5, coincide in S at
that instance (homogeneous system with zero data). This does not affect non-vacuity.
