### A:eq:forced, A:lem:cont, A:lem:small, A:sec4:WP-def: Dissertation.PaperSpec.A.ForcedSolution
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 6d8e8f373c5e26da1ce1add2f80b1ed8 (pl-fp-v1:46144dc6e903689616ed6e62223ff8a89a779b1b5a45d97d6cb37b51fdcd66c0)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T16:02:16Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T15:42:32Z):
Reading for def:Dissertation.PaperSpec.A.ForcedSolution (locked before seeing Lean).

Paper notion: a solution in HH of the lambda-scaled forced system (4.1) with initial datum xi_0
and forcing q = (q^b, q^sigma, q^h, q^f, q^g_T): Theta = (X,Y,Z,U) in HH (X, Y cadlag adapted
with E sup < inf, Z in H^2_W, U in H^2_N) such that a.s. for every t in [0,T]:
 X_t = xi_0 + lambda int_0^t b(s,Theta_s,mu_s) ds + lambda int_0^t sigma(s,Theta_s,mu_s) dW_s
       + lambda int_0^t int_E h(s,Theta^-_s,e,mu^-_s) Ntilde(ds,de)
       + int_0^t q^b ds + int_0^t q^sigma dW + int_0^t int_E q^h(e) Ntilde(ds,de),
 Y_t = lambda g(X_T, Law X_T) + lambda int_t^T f(s,Theta_s,mu_s) ds + q^g_T + int_t^T q^f ds
       - int_t^T Z dW - int_t^T int_E U(e) Ntilde(ds,de).
Faithful: lambda multiplies b, sigma, h, f and g (all four interior coefficients and terminal);
forcings enter additively, unscaled; mu_s = Law Theta_s, mu^-_s = Law Theta^-_s (a.e. equal);
library L^2 stochastic integrals; HH membership. Linear combination of integrals vs integral of
combination is equivalent under the L^2 integrability present.
Comparison (verdict recorded 2026-10-17T15:57:22Z):
Comparison for def:Dissertation.PaperSpec.A.ForcedSolution.

Lean (PaperSpec/A/Setting.lean): ForcedSolution ... T lam C xi0 qb qsigma qh qf qg X Y Z U :=
(∃ gamma, PaperSolutionForced over enlJoint ...) ∧ every path of X and Y has left limits on (0,T].
PaperSolutionForced: q is a Forcing; X, Y adapted on [0,T], every path right-continuous on [0,T), a.s.
left limits, E sup < inf; Z predictable, U marked predictable, finite energies, 0 off [0,T]; the forced
integrands lam*b(..)+q^b, lam*sigma(..)+q^sigma, lam*gamma+q^h, lam*f(..)+q^f measurable, progressive,
finite energy; gamma represents h(s, Theta^-_s, ., mu^-_s) in L^2(nu) for a.e. s a.s.; fwd: a.s. for all t,
X_t = xi0 + int_{[0,t]} (lam b + q^b) ds + M_t + I^N(lam gamma + q^h)_t (M cadlag version of
int (lam sigma + q^sigma) dW); bwd: a.s. for all t, Y_t = lam g(X_T, Law X_T) + q^g + int_{[t,T]} (lam f + q^f) ds
- (M_T - M_t) - (I^N(U)_T - I^N(U)_t).

Item by item:
- lambda multiplies b, sigma, h, f and g; forcings additive and unscaled: yes.
- h at (Theta^-, mu^-) via representative; b, sigma, f at (Theta_s, mu_s) with mu_s = Law Theta_s: yes.
- Theta in HH, standing filtration: yes (as in Solution).
- one integral of the combined integrand instead of the sum of two integrals: equal a.s. by
  linearity of the L^2 integrals and of the Bochner integral under the square integrability
  present (q finite energy; the combined integrand finite energy); at lambda = 0 the coefficient
  processes are rightly not required integrable.
- q required to be a Forcing (square-integrable, progressive, q^h marked progressive; WP adds
  predictability of q^h): yes.
- extra conditions (measurability and finite energy of the forced integrands): (2.5) plus (4.2),
  automatic for HH tuples under Assumptions 2.2-2.3 with a square-integrable forcing.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices: (1) the integrals of lambda*psi and of q^psi combined into the integral of
lambda*psi + q^psi (equal by linearity under the square integrability present); (2) the Poisson
integral of lambda h(Theta^-, mu^-) + q^h read through a marked progressive representative gamma
of h(Theta^-, mu^-); (3) measurability and finite energy of the forced integrands required
explicitly ((2.5) and (4.2), automatic for HH tuples under Assumptions 2.2-2.3); (4) coordinates,
cadlag as every path right-continuous on [0,T) with left limits on (0,T], cadlag versions of the Ito
integrals, identities on one null set, integrands extended by 0 off [0,T]; (5) laws at each time
with Dirac-0 junk on a null set of times.
Disagreements with the author's review (shown 2026-10-17T16:02:09Z): The author's review entry is empty (no recorded reading). It should record: lambda multiplies b,
sigma, h, f and g with additive unscaled forcings; the integrals of lambda*psi + q^psi taken as one
integral of the combined integrand; the forcing only required to be a Forcing (q^h marked
progressive; WP adds predictability); and the extra measurability/finite-energy requirements on the
forced integrands, automatic for HH tuples under Assumptions 2.2-2.3.
