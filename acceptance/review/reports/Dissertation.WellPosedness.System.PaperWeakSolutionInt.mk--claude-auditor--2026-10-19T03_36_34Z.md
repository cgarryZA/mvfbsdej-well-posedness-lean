### A:abstract, A:conclusion, A:cor:robust, A:ex:brownian, A:rem:cwp-class, A:rem:generalrank, A:rem:uniq-no-integ, A:sec:examples, A:thm:uniq: Dissertation.WellPosedness.System.PaperWeakSolutionInt.mk
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash 88d41182691dfcb90000000000000000 (pl-fp-v1:b2c5d23e54a3eeaac27cf895a0d2f462cc8c7bf03356ee7852820ea404be81c4)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:36:34Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:18:00Z):
Reading of def:Dissertation.WellPosedness.System.PaperWeakSolutionInt.mk (the constructor of the structure PaperWeakSolutionInt; its type lists the fields, so the reading is that of the structure).

Paper notion: a solution of (1.1) in the weak class H^2 (Thm 3.3: "Theta^1,Theta^2 in H^2 satisfy
(1.1)"; Rem 3.2; Rem 3.4), in integral form: Theta=(X,Y,Z,U) with
- X, Y cadlag adapted to the standing filtration (augmentation of F0 v sigma(W) v sigma(N)),
  E int_0^T|X_t|^2 dt < oo, E int_0^T|Y_t|^2 dt < oo; Z predictable, E int|Z|_F^2 < oo;
  U predictable (P x E-measurable), E int ||U_t||^2_{L^2(nu)} dt < oo;
- for every t in [0,T], a.s.:
  X_t = xi0 + int_0^t b(s,Theta_s,mu_s)ds + int_0^t sigma(s,Theta_s,mu_s)dW_s
        + int_0^t int_E h(s,Theta_s^-,e,mu_s^-) Ntilde(ds,de),
  Y_t = g(X_T,Law(X_T)) + int_t^T f(s,Theta_s,mu_s)ds - int_t^T Z_s dW_s
        - int_t^T int_E U_s(e) Ntilde(ds,de);
- mu_t = Law(Theta_t), mu_t^- = Law(Theta_t^-) (or a.e.-equal Borel representatives), the law of
  X_T exactly in g; the jump coefficient at the left-limit tuple Theta_t^- = (X_{t-},Y_{t-},Z_t,U_t).

A faithful Lean definition must contain: the weak-class membership (not S), the two identities
for all t a.s., the diagonal law arguments, xi0 the given initial datum, the backward terminal
value g(X_T, Law(X_T)) (not a free terminal variable), the correct signs. It may carry
admissibility conditions (measurability and integrability of the coefficient processes so that the
integrals exist); L^2-integrability of those processes is automatic under Assumptions 2.2-2.3 but
restricts the class when 2.2 is dropped (Thm 3.3, Rem 3.4).
Comparison (verdict recorded 2026-10-19T03:34:53Z):
Comparison: constructor PaperWeakSolutionInt.mk (its type lists the fields of PaperWeakSolutionInt:
toPaperWeakTuple, toPaperAdmissibleInt, XT_sq, fwd, bwd; same content as the structure).
Reading: weak class (not S); both identities for all t a.s.; diagonal laws; xi0 the given datum;
terminal value g(X_T, Law X_T); correct signs; admissibility with only the needed integrability.
- Weak class: PaperWeakTuple (adapted on [0,T]; every path right-continuous on [0,T); a.e. path
  has left limits on (0,T]; finite E int_0^T |X_i|^2, |Y_k|^2; Z predictable, U marked predictable,
  finite energies; Z, U vanish off [0,T]). Matches H^2_weak.
- fwd: exists M with M_t = sum_j int_0^t sigma_ij dW^j a.s. for each t, M cadlag a.s., and a.s.
  for all t in [0,T]: X_i t = xi0_i + int_[0,t] driftProc + M_t + (compensated integral of gamma_i)_t.
  Matches the forward line of (1.1).
- bwd: a.s. for all t: Y_k t = terminalVal k + int_[t,T] driverProc - (M_T - M_t)
  - (int U_k dNtilde)_T + (int U_k dNtilde)_t, where M is the Brownian integral of the row Z_k,
  terminalVal = g(X_T, lawP2 P X_T). Matches the backward line of (1.1), signs included.
- XT_sq: X_T in L^2 (presupposed by the paper), making Law(X_T) the genuine law.
- The filtration F is a parameter carrying the driver (Brownian and Poisson filtration
  properties). The paper's filtration is supplied by PaperWeakSolutionIntEnl (enlJoint). As a
  def over a general F this is the right abstraction.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices of the solution notion (shared by WeakSolution, PaperWeakSolutionIntEnl,
PaperWeakSolutionInt(.mk), PaperAdmissibleInt(.mk), PaperWeakTuple(.mk)), each harmless:
1. Coordinate families (X : Fin n -> R -> Omega -> R etc.) in place of vector-valued processes;
   U as a mark-indexed function, marked predictable, i.e. the P x E-measurable representative the
   paper itself uses ((2.4)).
2. Z and U are required to vanish off [0,T]; adaptedness and the path conditions are imposed on
   [0,T] only. Values off the horizon play no role in the paper.
3. The law flow is the exact law lawP2 P Theta_s at every s, with the junk value delta_0 where
   Theta_s is not in L^2. On a weak tuple that happens only on a Lebesgue-null set of times, so
   this agrees with the paper's Borel representatives (Lemma A.1) up to null sets, which the paper
   shows do not affect any integral.
4. The jump integrand is an exists-quantified representative gamma of h(s,Theta_{s-},.,mu^-_s)
   for a.e. s, a.s., required to be marked progressive (not predictable) with finite energy. The L^2
   compensated integral does not distinguish an integrand from its predictable version.
5. "The integrals of (1.1) exist" is spelled out: the drift and driver need only a.e. path
   integrable (pathwise Lebesgue integrals, as in the paper, so no L^2 requirement on b, f without
   Assumption 2.2). The diffusion and jump integrand need finite energy (L^2 stochastic
   integrals). Under Assumption 2.3, the setting of every use, finite energy is equivalent to
   the a.s. local square integrability that the stochastic integrals need, since both reduce to
   square integrability in time of the deterministic origin values. The measurability fields are
   (2.5).
6. Both identities hold on one null set for all t in [0,T]. The paper allows this because both
   sides are cadlag, and the library integrals are cadlag versions (the Brownian one through an
   explicit cadlag version M).
7. X_T in L^2 is a field. The paper presupposes it ("the terminal conditions presuppose
   Law(X_T) in P_2").
8. Cadlag: PaperWeakTuple asks every path to be right-continuous and almost every path to have
   left limits. WeakSolution/Solution also ask every path to have left limits. The filtration is
   augmented, so this is a choice of version.
Disagreements with the author's review (shown 2026-10-19T03:36:34Z): none
