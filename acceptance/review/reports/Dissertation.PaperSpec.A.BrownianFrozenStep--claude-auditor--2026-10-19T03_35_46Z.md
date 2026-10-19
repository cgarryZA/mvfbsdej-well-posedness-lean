### A:sec4:horizon-not-contractive: Dissertation.PaperSpec.A.BrownianFrozenStep
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash 98bd6b9787534217c971d1dc13a30cc3 (pl-fp-v1:fe89adcadd9aa07bdfafda0dd6fc08aca936251cbc5fa8afc1fb7ceb7a96ec36)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:35:46Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:16:43Z):
# Reading: def BrownianFrozenStep (used by sec4_horizon_not_contractive)

Paper notion: the frozen-coefficient map Phi_lambda of the proof of Lemma 4.2 (eqs. frozenfwd and
frozenbwd), the map whose (non-)contractivity the §4 intro discusses. Given a trial tuple
Theta = (X,Y,Z,U) in HH and its law flow mu^Theta_s = Law(Theta_s), mu^{Theta,-}_s = Law(Theta^-_s):
* forward: Xbar_t = xi0 + lambda int_0^t b(s,Theta_s,mu^Theta_s) ds + lambda int_0^t
  sigma(s,Theta_s,mu^Theta_s) dW_s + lambda int_0^t int_E h(s,Theta^-_s,e,mu^{Theta,-}_s) Ntilde(ds,de)
  (+ forcing terms; zero forcing for the unforced map);
* backward: Xi = lambda g(Xbar_T, Law(Xbar_T)) + q^g_T + int_0^T (lambda f(s,Theta_s,mu^Theta_s)+q^f_s) ds,
  M_t = E[Xi | F_t] = M_0 + int Zbar dW + int int Ubar dNtilde (PRP), Ybar_t = M_t - int_0^t (lambda f + q^f) ds.
The name "Brownian frozen step" suggests the Brownian-channel part of this map (no Poisson channel,
e.g. nu = 0 or the forward Brownian integral only). A faithful Lean definition must:
* evaluate the coefficients at the TRIAL tuple and the TRIAL tuple's law (pushforward of P under
  Theta_s), not at the output;
* use the Ito integral against the standing Brownian motion W on the standing filtration, with the
  forward output Xbar_t = xi0 + int b ds + int sigma dW (+ jump term if present);
* if it includes the backward part, evaluate g at the OUTPUT Xbar_T and its law, and obtain
  (Ybar,Zbar,Ubar) by conditional expectation + martingale representation;
* if it is only the forward Brownian part, then any statement using it must still compare it with
  the full HH distance of the inputs; and the coefficient class must be the paper's (a system
  satisfying the assumptions), or a recorded specialisation (nu = 0 / Brownian reduction).
Edge cases: Lean's stochastic integral of a non-integrable integrand returns a junk value (0); the
definition must be used only where the integrand is square-integrable (which holds along HH by
(4.2)); the law argument must be the law under P; the time domain [0,T].
Comparison (verdict recorded 2026-10-19T03:21:10Z):
# Comparison: def BrownianFrozenStep

Lean: a relation between a trial (X,Y,Z,U) and an output (X',Y',Z',U'), all scalar
(n = m = d = 1), over a Levy driver with E = Unit, nu = 0, on the §2 filtration enlJoint G0 D:
  * for each i: LinearFSDEJ with initial value 0, drift driftProc P T C X Y Z U i, diffusion
    diffusionProc P T C X Y Z U i, jump integrand 0, solution X' i:
    X'_t = 0 + int_0^t b(s, Theta_s, Law Theta_s) ds + int_0^t sigma(s, Theta_s, Law Theta_s) dW_s
    a.s. at each t in [0,T];
  * for each k: LinearBSDEJ with terminal value terminalVal P T C X' k = g(X'_T, Law X'_T) and
    driver driverProc P T C X Y Z U k = f(s, Theta_s, Law Theta_s), solution (Y' k, Z' k, U' k).
Against my reading:
* Coefficients evaluated at the TRIAL tuple tupleAt ... s omega and its law lawP2 P (tupleAt ... s)
  (pushforward of P; Dirac junk only when Theta_s is not in L^2, a null set of times along HH):
  yes.
* Terminal at the OUTPUT X'_T and its law: yes (terminalVal ... X').
* Backward part via the linear BSDEJ (whose solution is the PRP construction, unique up to the HH
  identification): yes.
* Ito integral against the standing W over the §2 filtration: yes.
Specialisations / representation choices:
1. n = m = d = 1, E = Unit, nu = 0: a Brownian specialisation; the jump integrand of the forward
   equation is 0, exact since the compensated Poisson integral vanishes at nu = 0; Ubar is the
   trivial jump integrand. The definition is used only by the horizon remark, where this
   specialisation is the recorded instance.
2. lambda = 1, zero forcing, initial datum 0 (as in the docstring) — the unforced frozen map of
   the instance used.
3. The map is a relation (outputs unique up to modification), not a function.
4. The conventions of LinearFSDEJ/LinearBSDEJ (progressive integrands, right-continuous paths,
   identities a.s. at each t) — harmless (see LinearBSDEJ).
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless:
1. Specialised to n = m = d = 1 and a mark space E = Unit with nu = 0 (Brownian, no jumps); the
   forward jump integrand is 0, which is exact at nu = 0, and the definition is only used for the
   horizon remark's Brownian instance.
2. lambda = 1, zero forcing and initial datum 0: the unforced frozen map Phi_1 of Lemma 4.2 for the
   instance used.
3. The map is encoded as a relation trial -> output via LinearFSDEJ (forward, coefficients along the
   trial and the trial's law) and LinearBSDEJ (terminal g at the output X'_T and its law, driver f
   along the trial); its outputs are unique up to the HH identification, so it determines the map.
4. LinearFSDEJ/LinearBSDEJ conventions (progressive integrands, right-continuous paths, identity a.s.
   at each t) are equivalent up to modification to the paper's.
Disagreements with the author's review (shown 2026-10-19T03:35:41Z): none
