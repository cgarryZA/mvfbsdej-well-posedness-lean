### A:abstract, A:conclusion, A:cor:robust, A:eq:coefmeas, A:eq:forced, A:eq:mvfbsdej, A:ex:brownian, A:ex:concrete, A:ex:dealer, A:ex:fulllaw, A:intro:limin-comparison, A:intro:mvfbsdej, A:lem:cont, A:lem:pert, A:lem:small, A:rem:cwp-class, A:rem:generalrank, A:rem:regimes, A:rem:uniq-no-integ, A:sec3:one-null-set, A:sec4:WP-def, A:sec5:overview, A:sec:examples, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: Dissertation.WellPosedness.System.jumpProc
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash bfa4317d32adaf7b2cab0921e18838d1 (pl-fp-v1:ed914efee604e15d0baf2ec38b4116df10bf7093d55985d2256a986172d53f57)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:50:56Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T15:41:48Z):
Reading for def:Dissertation.WellPosedness.System.jumpProc.

Paper notion: the jump channel of the forward equation along a tuple Theta: either (a) the
predictable jump-integrand field (s, omega, e) |-> h(s, Theta_{s-}(omega), e, mu_s^-) (an L^2(nu;R^n)-
valued predictable process, (2.5)), or (b) the compensated Poisson integral
t |-> int_0^t int_E h(s, Theta_s^-, e, mu_s^-) Ntilde(ds, de) built from it. (The name does not
determine which; it is "the jump process" of the system.)

Faithful Lean: if (a): the process (t,omega) |-> h(t, Theta^-_t(omega), mu^-_t) in L^2(nu;R^n) with
Theta^-_t = (X_{t-}, Y_{t-}, Z_t, U_t) (left limits in X, Y only; Z, U untouched) and the measure
argument the law of Theta^-_t (the Borel representative of Lemma A.1, equal to Law(Theta^-_t) for a.e.
t). If (b): the L^2 compensated-Poisson stochastic integral of that integrand w.r.t.
Ntilde = N - dt nu(de) (the Ito-isometry extension, for predictable square-integrable integrands,
with a cadlag version), evaluated at t. Edge cases: evaluation at Theta_t instead of Theta_{t-} is
harmless inside dt-integrals and stochastic integrals (they agree dt x dP a.e.), so either is
acceptable; the integral's junk value for non-square-integrable integrands must not be relied on.
Comparison (verdict recorded 2026-10-17T15:50:03Z):
Comparison for def:Dissertation.WellPosedness.System.jumpProc (System/Solves.lean:122-126):
jumpProc T gamma i s omega e = indicator_{[0,T]}(s) * gamma i s omega e.

It is my alternative (a): the jump integrand field of the forward equation, coordinatewise and
pointwise in the mark, cut off to [0,T]. The link with the coefficient is made in SolvesForced:
jump_rep says gamma represents e |-> h(s, Theta_s(omega), e, mu_s) in L^2(nu) for a.e. s in [0,T] and
a.e. omega; the forward equation uses lam * jumpProc T gamma + q^h as the Poisson integrand.
Representation choices: (1) a pointwise representative gamma of the L^2(nu)-valued h, which is the
paper's own reading via (2.4); (2) evaluation at (Theta_s, mu_s) rather than (Theta_{s-}, mu^-_s),
which agree dt x dP-a.e. (paper, §4 opening and Lemma A.1), so the L^2 Poisson integral is
unchanged; (3) extension by 0 off [0,T], the convention for all integrands of LinearFSDEJ.
The definition itself is only the cut-off; no junk value is involved. Verdict: faithful with
representation choices.
Witness: —
Verdict: faithful with representation choices — Choices: (1) the L^2(nu;R^n)-valued jump coefficient is carried by a pointwise representative gamma
(coordinates i, mark e), tied to h by SolvesForced.jump_rep (a.e. s, a.e. omega, nu-a.e. e), which
is the paper's reading of L^2(nu)-valued integrands through representatives (2.4); (2) the
representative is of h at (Theta_s, mu_s), not at the predictable (Theta_{s-}, mu^-_s), harmless
because they agree dt x dP-a.e. and the L^2 compensated Poisson integral only sees the
dt x dP x nu class; (3) the process is extended by 0 off [0,T], consistent with all integrands of the
linear equations.
Disagreements with the author's review (shown 2026-10-17T15:50:11Z): No disagreement with a stated position (the author's entry shown is empty). For the record: faithful
with representation choices -- pointwise representative gamma of the L^2(nu)-valued jump
coefficient, evaluation at (Theta_s, mu_s) instead of the predictable (Theta_{s-}, mu^-_s) (equal
dt x dP-a.e.), extension by 0 off [0,T].
