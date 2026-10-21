### A:eq:frozenbwd: Dissertation.PaperSpec.A.FrozenStep
Pins: manuscript A None; project 6d403c197bfb10fe8808933c6e525ee0ae544fb1; hash 4c12ec59e5b0c0624baf69ddef5e32bc (pl-fp-v1:82e1108bde071f19f72c24fc6c510d315481af8f1f78ded9fb563fb3702de6ce)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-20T00:44:30Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-20T00:30:26Z):
Reading of the notion behind FrozenStep: the frozen step Theta -> Thetabar = Phi_lambda(Theta)
of the proof of Lemma 4.2, i.e. "Xbar solves (4.7) and (Ybar, Zbar, Ubar) solves (4.8)"
(manuscript/paper/sections/04-proof-wellposedness.tex, lines 258-310; (4.8) = eq:frozenbwd at
lines 305-310).

Paper's notion: for a trial Theta in S, lambda in [0,1], forcing q, initial datum xi_0, the
tuple Thetabar = (Xbar, Ybar, Zbar, Ubar) with
 - Xbar solving the frozen forward dynamics (4.7) (see FrozenForward);
 - (Ybar, Zbar, Ubar) solving the frozen linear BSDE, for every t in [0,T], a.s.,
     Ybar_t = lambda g(Xbar_T, Law(Xbar_T)) + q^g_T
            + int_t^T (lambda f(s, Theta_s, mu^Theta_s) + q^f_s) ds
            - int_t^T Zbar_s dW_s - int_t^T int_E Ubar_s(e) Ntilde(ds, de),
   with g evaluated at the terminal value of the NEW forward process Xbar and its law under P,
   f evaluated along the TRIAL Theta and its Borel law flow (not Thetabar), the factor lambda on
   g and f only, the forcing q^g_T, q^f added unscaled;
 - in the paper's construction Thetabar in S (Zbar in H^2_W, Ubar in H^2_N, Ybar, Xbar in S^2);
   Phi_lambda(Theta) := Thetabar.

What a faithful Lean definition must be: a predicate on (basis, coefficients, lambda, q, xi_0,
Theta, Thetabar) consisting of the FrozenForward predicate for the X-component and the displayed
backward identity (each t in [0,T], a.s.) for the other three components, with the stochastic
integrals those of the standing basis; possibly including the membership Thetabar in S (else the
statements using it must add it). Law(Xbar_T) must be the push-forward of P under Xbar_T as an
element of P_2(R^n) (junk if Xbar_T not in L^2; harmless where Xbar_T in L^2 is guaranteed). The
integrals int_t^T must be over (t, T] with t in [0,T]; the Ntilde integral of Ubar must be the
compensated-Poisson L^2 integral (Ubar predictable). Edge cases as for FrozenForward (junk values
of non-integrable integrals).
Comparison (verdict recorded 2026-10-20T00:43:40Z):
Comparison of Dissertation.PaperSpec.A.FrozenStep (Dissertation/PaperSpec/A/Sec4Frozen.lean)
with the frozen step Theta -> Phi_lambda(Theta) = Thetabar of the proof of Lemma 4.2
(manuscript/paper/sections/04-proof-wellposedness.tex, lines 258-310: Phi_lambda defined at
lines 258-263, (4.7) at 265-275, (4.8) at 305-310). That passage defines the notion.

FrozenStep ... X Y Z U X' Y' Z' U' := FrozenForward (X' solves (4.7) for the trial) and, for each
coordinate k, LinearBSDEJ over the augmented filtration with terminal value
lam * g(X'_T, lawP2 P X'_T)_k + qg_k, driver lam * driverProc_k + qf_k (f along the trial Theta and
its law, cut to [0,T]), solution (Y'_k, Z'_k, U'_k); and HTuple (X', Y', Z', U').

Item by item against (4.8): g at the terminal value of the new forward process X' and its law, as
printed; f along the trial (Theta_s, mu^Theta_s), not along Thetabar, as printed; lambda on g and f
only, q^g_T and q^f unscaled, as printed; Ybar_t = xi + int_[t,T] phi ds - (I^W_T - I^W_t) -
(I^N_T - I^N_t), a.s. for each t in [0,T] (LinearBSDEJ), which is (4.8) with int_t^T read over
[t,T] (Lebesgue, same) and the stochastic integrals over (t,T] as differences of the library's
processes; Zbar, Ubar progressive with finite energy in LinearBSDEJ and predictable via HTuple;
Thetabar in S via HTuple, as printed ("so Thetabar in S").

Phi_lambda is printed as a map defined by a construction (conditional expectation, PRP); FrozenStep
is the relation "Thetabar is a tuple of S solving (4.7)-(4.8) for the trial". By the existence and
uniqueness in S (the content of A:eq:frozenbwd) the relation holds exactly for the tuples equal in
S to the constructed Phi_lambda(Theta), so it means the same object. Terminal law: lawP2 of X'_T is
its law (X'_T is square integrable for a tuple of S). Junk values: the driver integral is a Bochner
integral over [t,T], 0 only on a P-null set of omega under the hypotheses; the identity is a.s.

Representation choices (harmless): relation instead of function; coordinatewise equations; "for
each t a.s." with right-continuous paths; stochastic integrals over (t,T] as differences;
[t,T] for (t,T] in the Lebesgue integral; the pointwise law flow of the trial; integrands
extended by 0 off [0,T]; membership in S as the representative-level HTuple.
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless:
(1) Phi_lambda is encoded as the relation "Thetabar is a tuple of S solving (4.7)-(4.8) for the
trial", not as the constructed map. By existence and uniqueness in S, the content of
A:eq:frozenbwd, the relation holds exactly for the tuples equal in S to the paper's
Phi_lambda(Theta).
(2) The BSDE holds coordinatewise, for each t a.s. The Lebesgue integral runs over [t,T], and the
stochastic integrals over (t,T] are written as differences of the library integral processes.
(3) The trial's law flow is the pointwise law, which agrees with the Borel representative for
a.e. s.
(4) Membership in S is the representative-level HTuple, and integrands are extended by 0 off
[0,T].
The evaluation points are as printed: g at the new X'_T and its law, f along the trial. lambda
multiplies g and f only.
Disagreements with the author's review (shown 2026-10-20T00:43:45Z): No disagreement. I did not examine the remark relating FrozenStep to BrownianFrozenStep at nu = 0,
which lies outside this unit's reading, and I take no position on it.
