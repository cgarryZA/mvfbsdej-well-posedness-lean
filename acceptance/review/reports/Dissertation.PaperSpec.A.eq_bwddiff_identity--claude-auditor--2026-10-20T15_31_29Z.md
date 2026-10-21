### A:eq:bwddiff: Dissertation.PaperSpec.A.eq_bwddiff_identity
Pins: manuscript A None; project 53a4ee4fc8767ba8884b5732431dded9772b47df; hash ed839d34f480cba1d4d84f3b5a301248 (pl-fp-v1:1ecec6f76851c79b6ce6b8ce3480b07430828740018500a91b413bd1a6f65ecd)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-20T15:31:29Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-20T15:21:24Z):
Reading of the clause "the backward difference before (4.12)" of claim A:eq:bwddiff
(manuscript/paper/sections/04-proof-wellposedness.tex, proof of Lemma lem:small, Step 4,
lines 391-397).

Setting: standing basis of Section 2; dimensions n, m, d >= 1; lambda in [0,1]; a fixed
square-integrable forcing q = (q^b, q^sigma, q^h, q^f, q^g_T) (q^f progressively measurable in
L^2(Omega x [0,T]; R^m), q^g_T in L^2(F_T; R^m)); coefficients b, sigma, h, f, g deterministic,
jointly Borel, with Assumptions ass:integ and ass:lip in force (Lemma lem:small).

Objects: two trial tuples Theta^1, Theta^2 in S; their images Phibar^k = Phi_lambda(Theta^k)
= (Xbar^k, Ybar^k, Zbar^k, Ubar^k), where Xbar^k is the frozen forward process (4.7) and
(Ybar^k, Zbar^k, Ubar^k) solves the frozen linear BSDE (4.8):
  Ybar^k_t = lambda g(Xbar^k_T, Law(Xbar^k_T)) + q^g_T
             + int_t^T (lambda f(s, Theta^k_s, mu^{Theta^k}_s) + q^f_s) ds
             - int_t^T Zbar^k_s dW_s - int_t^T int_E Ubar^k_s(e) Ntilde(ds,de),
for every t, a.s., with Zbar^k in H^2_W, Ubar^k in H^2_N (constructed by the predictable
representation of E[Xi^k | F_t]).
Differences: deltaYbar = Ybar^1 - Ybar^2, deltaZbar, deltaUbar likewise,
deltaxibar = lambda [g(Xbar^1_T, Law Xbar^1_T) - g(Xbar^2_T, Law Xbar^2_T)],
delta f_s = f(s, Theta^1_s, mu^{Theta^1}_s) - f(s, Theta^2_s, mu^{Theta^2}_s).

Conclusion: for every t in [0,T], almost surely,
  deltaYbar_t = deltaxibar + int_t^T lambda delta f_s ds - int_t^T deltaZbar_s dW_s
                - int_t^T int_E deltaUbar_s(e) Ntilde(ds,de),
i.e. (4.4) with deltaxi = deltaxibar and phi = lambda delta f: the forcing terms q^g_T and q^f
cancel. The stochastic integrals are the genuine Ito and compensated Poisson integrals, and
the identity is their linearity applied to the two frozen BSDEs (with the dt-integrals finite
a.s.).

Faithful formal statement: for lambda, q, Theta^1, Theta^2 as above and the Phi_lambda images
(either defined by the construction, or characterised as any tuples in S solving (4.7)-(4.8),
which is broader and harmless since the frozen BSDE solution is unique), the difference
identity holds for every t a.s. The difference must be taken with the SAME lambda and the SAME
forcing q for both k. A statement that merely assumes the difference identity, or in which the
integrals are abstract operators unrelated to the real ones, would be mismatched/vacuous. The
companion assertions of the passage (deltaYbar cadlag adapted, (deltaZbar, deltaUbar) in
H^2_W x H^2_N, deltaxibar in L^2(F_T), lambda delta f in L^2) are other parts of the passage;
whether they appear is a coverage question. A witness should exhibit nonconstant data
(lambda > 0, Theta^1 != Theta^2 with nonzero delta f or nonzero g difference).
Comparison (verdict recorded 2026-10-20T15:25:42Z):
Comparison of Dissertation.PaperSpec.A.eq_bwddiff_identity (Dissertation/PaperSpec/A/Sec4ProofSteps.lean)
with the locked reading (Step 4 of the proof of Lemma lem:small, lines 391-407).

Setting: the standing basis (Levy driver D, sigma-finite nu, countably generated E, G0
independent, enlJoint), n, m, d > 0, T > 0. Match.

Hypotheses in force.
- JointBorel T C, Assumption22 (xi_0), Assumption23 with L: Assumptions ass:integ-ass:lip of
  Lemma lem:small and the standing (2.3). Match.
- lam in [0,1]: "Fix lambda in [0,1]". Match.
- PredForcing for (q^b, q^sigma, q^h, q^f, q^g): the forcing class of (4.1) (defined elsewhere;
  progressive square-integrable q^b, q^sigma, q^f, predictable q^h, F_T-measurable square-integrable
  q^g). Match.
- Two trials of S (HTuple). Match.
- FrozenStep for each trial, with the SAME T, lam, C, xi_0 and q: (X_k', Y_k', Z_k', U_k') with
  X_k' solving the frozen forward equation (4.7) (b, sigma at (Theta_s, Law Theta_s), h through a
  representative of h(s, Theta^-_s, ., Law Theta^-_s)), each coordinate of (Y_k', Z_k', U_k')
  solving (4.8) as a LinearBSDEJ with terminal lam g(X_k'_T, Law X_k'_T) + q^g and driver
  lam f(s, Theta_k s, Law Theta_k s) + q^f (terminalVal, driverProc), and Theta_k-bar in S. This
  characterises Phi_lam(Theta^k) relationally (any tuple of S solving (4.7)-(4.8)) instead of by
  the predictable-representation construction; since the construction produces such a tuple and
  the frozen step is unique in S (clause eq_frozenbwd), the two readings coincide, and the
  relational one is at least as broad. Match.

Conclusion. For every coordinate k, LinearBSDEJ D enlJoint T with
  xi  = lam (g(X_1'_T, Law X_1'_T)_k - g(X_2'_T, Law X_2'_T)_k)  (= deltaxibar_k),
  phi = lam (f(s, Theta_1 s, Law Theta_1 s)_k - f(s, Theta_2 s, Law Theta_2 s)_k) cut to [0,T]
        (= lam delta f_s),
  Y = Y_1' k - Y_2' k, Z = Z_1' k - Z_2' k, U = U_1' k - U_2' k.
LinearBSDEJ's equation field is: for every t in [0,T], a.s.,
  Y_t = xi + int_{[t,T]} phi ds - (I^W_T(Z) - I^W_t(Z)) - (I^N_T(U) - I^N_t(U)),
with the canonical Ito and compensated Poisson integrals of the DIFFERENCE integrands: exactly
deltaYbar_t = deltaxibar + int_t^T lam delta f_s ds - int_t^T deltaZbar dW - int_t^T int deltaUbar dNtilde,
"for every t, a.s." as in the paper's convention. q^g and q^f do not appear: they cancel, as
printed. Match.
The structure also asserts the side conditions of (4.4): Z, U, phi jointly and progressively
measurable, zero off [0,T], of finite energy; xi square integrable; Y adapted with
right-continuous paths. These are the passage's own assertions (lines 398-407: deltaYbar cadlag
adapted, the remaining hypotheses hold), stated slightly differently: progressive measurability
of deltaZbar, deltaUbar instead of predictability (weaker than the printed H^2_W x H^2_N, but
predictability of the differences follows at once from the HTuple hypotheses on both images),
progressive measurability of lam delta f (stronger than the printed phi in L^2(Omega x [0,T]),
and true), and no explicit left limits of deltaYbar nor F_T-measurability of deltaxibar (both
immediate from the hypotheses and the equation at t = T). None of this changes the identity the
clause is about.

Representation choices (harmless): coordinates; relational characterisation of Phi_lam by
FrozenStep (equivalent by uniqueness); integrands extended by zero off [0,T]; the identity
packaged with the side conditions of (4.4) in LinearBSDEJ.

Witness. Dissertation.Acceptance.A.frozen_pair_window_hypotheses: Example 5.1(i) with b = -y,
sigma = -z, h = -u, f = x, g(x, rho) = x, n = m = d = 1, nu = Dirac mass at 0, T = 1, L = 1, xi_0 = 0,
lam = 1, zero forcing, trials 0 and (1, 1, 1_{(0,1]}, 1_{(0,1]}), with FrozenStep tuples for both
(obtained from eq_frozenbwd). All hypotheses of the proposition are supplied. The instance is
not degenerate: lam = 1, delta f = f(Theta^1) - f(Theta^2) = 0 - 1 = -1 on [0,1], and the frozen
forward images differ (Xbar^2 carries the drift -1 and the noise terms of -1_{(0,1]}), so
deltaxibar = Xbar^1_1 - Xbar^2_1 is nonzero. It is an instance the paper intends.

Coverage. Claim A:eq:bwddiff has two clauses: eq_bwddiff ((4.12), the chain with C_BP, C_g,
L_*, C_X, C_Y, for every c_BDG >= c_0) and this identity clause (lines 391-397). With the side
conditions carried by LinearBSDEJ, the two clauses state every mathematical assertion of lines
391-422, up to the small differences in the side conditions noted above (predictability of the
differences stated as progressive measurability; left limits and F_T-measurability implicit).
Neither clause states something the passage does not claim, and the hypotheses are those in
force. The clause reads lines outside the pinned source region (409-422), so a change to lines
391-397 would not by itself reopen the review.
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless: (1) Phi_lam(Theta^k) is characterised relationally by
FrozenStep (any tuple of S solving (4.7)-(4.8) with the same lam, xi_0 and forcing q) rather than
by the predictable-representation construction; the construction yields such a tuple and the
frozen step is unique in S, so the readings coincide; (2) coordinates, with integrands extended
by zero off [0,T]; (3) the identity is stated as LinearBSDEJ, i.e. the equation "for every t in
[0,T], a.s." with the canonical Ito and compensated Poisson integrals of the difference
integrands, together with the side conditions of (4.4); among those, deltaZbar, deltaUbar are
asserted progressive rather than predictable (predictability follows at once from the
hypotheses), and the left limits of deltaYbar and the F_T-measurability of deltaxibar are left
implicit (immediate from the hypotheses and the equation at t = T). The identity itself, with
deltaxibar = lam [g(Xbar^1_T, Law Xbar^1_T) - g(Xbar^2_T, Law Xbar^2_T)] and phi = lam delta f,
matches the printed step.
Disagreements with the author's review (shown 2026-10-20T15:30:33Z): Agreement on the identity, its "every t, a.s." reading, the objects (deltaxibar through
terminalVal, lam outside delta f, q^g and q^f cancelling) and the witness. One point of
disagreement on the review's description of the side conditions: it says the regularity that
LinearBSDEJ carries "is what the next sentence lists" as the hypotheses of Lemma lem:bpbsde for the
difference. Not exactly: lines 398-407 assert (deltaZbar, deltaUbar) in H^2_W x H^2_N, i.e.
predictable, whereas LinearBSDEJ asserts only progressive (marked progressive) measurability of
deltaZbar, deltaUbar; it also asserts progressive measurability of lam delta f, which the passage
does not ask for (stronger, and true), and leaves the left limits of deltaYbar and the
F_T-measurability of deltaxibar implicit. Predictability of the differences follows at once from the
HTuple hypotheses on both images, so this does not affect the identity the clause states, but the
clause does not literally carry the printed membership in H^2_W x H^2_N. Verdict label: I record
"faithful with representation choices" (relational Phi_lam via FrozenStep, equivalent by
uniqueness; coordinates; integrands extended by zero off [0,T]; the identity packaged with the side
conditions of (4.4)). Procedural remark: the clause reads lines 391-397, outside the pinned region
(409-422).
