### A:abstract, A:conclusion, A:cor:robust, A:ex:brownian, A:rem:cwp-class, A:rem:generalrank, A:rem:uniq-no-integ, A:sec3:one-null-set, A:sec:examples, A:thm:uniq: Dissertation.WellPosedness.System.PaperAdmissibleInt
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash 6be52fa0d3961fab0000000000000000 (pl-fp-v1:8b5b404dde66cea59aa1793b4f082f1804bf693a17a204f24fadd42e0e048f8d)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:36:34Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:18:00Z):
Reading of def:Dissertation.WellPosedness.System.PaperAdmissibleInt (structure).

From the name ("admissible", "Int" = integral form) and its users (Thm 3.3, Rem 3.2, Rem 3.4,
Cor 3.6, Sec. 3 "one null set", examples): the conditions on a tuple Theta and a coefficient system
under which the two identities of (1.1) are meaningful, i.e. the standing requirements of a
solution before the identities are imposed. In the paper these are:
- Theta in the weak class H^2 (or S): X, Y cadlag adapted, E int|X|^2, E int|Y|^2 < oo;
  Z predictable in H^2_W; U predictable (P x E-measurable) in H^2_N;
- X_T in L^2(F_T) so that Law(X_T) in P_2(R^n) and g(X_T,Law(X_T)) is defined (Thm 3.3 proof:
  "the terminal conditions presuppose Law(X_T) in P_2");
- the law flows mu_t, mu_t^- (Borel representatives; Lemma A.1);
- the coefficient processes (2.5): b,sigma,f along (Theta_s,mu_s) progressively measurable,
  h along (Theta_{s-},mu_s^-) predictable, with the integrability that makes
  int b ds (pathwise L^1 suffices), int sigma dW (L^2 for the L^2 Ito integral),
  int int h dNtilde (L^2(dt x dP x nu) for the L^2 Poisson integral) and int f ds defined;
  in the paper's L^2 theory these are in L^2(dt x dP) by (4.2) under Assumptions 2.2-2.3.
- (Sec. 3) both sides of each identity cadlag in t, so one null set for all t.

A faithful Lean definition must contain these and nothing that changes the class in the
paper's intended uses: requiring L^2 integrability of the coefficient processes is harmless
under Assumptions 2.2-2.3 (it follows from them by (4.2)) but is an added hypothesis when 2.2 is
not assumed (Thm 3.3 as printed needs only 2.3-2.5; Rem 3.4's singular drift is not L^2 in time).
The measure argument must be the law of the tuple (diagonal), not a free measure.
Comparison (verdict recorded 2026-10-19T03:34:53Z):
Comparison: structure PaperAdmissibleInt F P T C X Y Z U gamma
(System/PaperWeakSolutionInt.lean:58-103).
Fields: b_meas, b_prog, b_int (a.e. path of the drift process integrable on [0,T]); sigma_meas,
sigma_prog, sigma_sq (finite energy); gamma_meas, gamma_prog (marked progressive), gamma_sq
(finite marked energy); f_meas, f_prog, f_int (a.e. path integrable); jump_rep: for a.e.
s in [0,T], a.s., e -> gamma(.,s,omega,e) equals h(s, tupleAt(leftLim X, leftLim Y, Z, U) s omega,
lawP2 P of that tuple) nu-a.e.
Reading: the conditions under which the identities of (1.1) are meaningful: measurability (2.5)
(progressive for b, sigma, f; predictable for h along (Theta_{s-}, mu^-_s)), the integrability
needed for int b ds, int sigma dW, int int h dNtilde, int f ds, diagonal law arguments; L^2 for
b, f would be an added hypothesis without Assumption 2.2.
- Drift and driver: pathwise integrability only. That is exactly what the dt-integrals of (1.1)
  need, so there is no narrowing without Assumption 2.2 (Thm 3.3, Rem 3.4).
- Diffusion and jump: finite energy (the L^2 Ito / compensated Poisson integrals). Under
  Assumption 2.3 this is equivalent to the a.s. local square integrability these integrals need,
  since both reduce to sigma(.,0,delta_0), h(.,0,.,delta_0) in L^2(0,T). So nothing a paper
  solution has is lost in the settings where the class is used.
- The jump coefficient at the left-limit tuple and the law of the left-limit tuple: matches
  (Theta^-_t, mu^-_t). The representative gamma is marked progressive rather than predictable;
  the L^2 compensated integral is the same for both.
- The drift, diffusion and driver processes are at (Theta_s, Law Theta_s) (driftProc etc.,
  Solves.lean), with the exact law (delta_0 junk only at times where Theta_s is not L^2).
- X_T in L^2 is not here but in PaperWeakSolutionInt (XT_sq). Fine.
- The measure argument is always the law of the tuple (diagonal), never a free measure. Matches.
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
Disagreements with the author's review (shown 2026-10-19T03:36:17Z): none
