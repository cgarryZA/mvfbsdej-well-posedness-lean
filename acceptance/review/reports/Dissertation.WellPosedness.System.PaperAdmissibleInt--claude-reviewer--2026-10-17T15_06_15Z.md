### A:cor:robust, A:rem:cwp-class, A:rem:generalrank, A:sec3:one-null-set, A:sec:examples, A:thm:uniq: Dissertation.WellPosedness.System.PaperAdmissibleInt
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 6be52fa0d3961fab0000000000000000 (pl-fp-v1:8b5b404dde66cea59aa1793b4f082f1804bf693a17a204f24fadd42e0e048f8d)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:06:15Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:28:47Z):
Reading for def PaperAdmissibleInt (paper notion: the admissible candidate tuple on which the
integral form of (1.1)/(4.1) is posed; used by Thm 3.3 (Hweak tuples), Rem 3.2, Cor 3.6, §3 solution
definition).

Paper notion (§2 standing setting, §3 "Solution space", Lemma A.1):
- Setting: filtered prob. space with usual conditions, horizon T>0, dims n,m,d>=1; W d-dim BM,
  N independent PRM on R_+ x E with intensity dt nu(de), nu sigma-finite on a countably generated
  (E, calE); filtration = usual augmentation of sigma(W, N, F_0).
- A candidate tuple Theta=(X,Y,Z,U):
  * X: R^n-valued cadlag adapted, Y: R^m-valued cadlag adapted, with E int_0^T |X_t|^2 dt < inf,
    E int_0^T |Y_t|^2 dt < inf (Hweak) [for HH: E sup|X|^2, E sup|Y|^2 < inf];
  * Z: R^{m x d}-valued predictable with E int |Z|_F^2 dt < inf;
  * U: predictable L^2(nu;R^m)-valued (via a P (x) calE-measurable representative) with
    E int ||U_t||^2 dt < inf.
  * Identification: cadlag components up to indistinguishability, Z up to dt x dP null sets,
    U up to dt x dP x nu null sets.
- Law flows: mu_t = Law(Theta_t), mu_t^- = Law(Theta_t^-) with Theta^- = (X_-, Y_-, Z, U);
  Borel representatives agreeing with the true laws a.e. t; mu_t^- = mu_t a.e.
- Coefficient processes along Theta: psi(s,Theta_s,mu_s) (psi in b,sigma,f) progressively
  measurable; h(s,Theta_{s-},e,mu_s^-) predictable; for the integrals in (1.1) to be defined one
  needs (at least) integrability: E int |b| ds < inf (or a.s. finite), sigma, h square-integrable
  (or locally) so that the Ito and compensated-Poisson integrals exist; the terminal value
  g(X_T, Law(X_T)) needs X_T in L^2 so that Law(X_T) in P_2.

A faithful Lean definition "admissible for the integral form" must therefore record:
the measurability (adapted/cadlag for X,Y; predictable for Z,U on the right filtration and
predictable sigma-field), the square integrabilities (Hweak level, not more), the X_T in L^2
condition (needed for the terminal law; the paper's Thm 3.3 proof says terminal conditions
presuppose Law(X_T) in P_2), and whatever integrability of the coefficient processes makes the
stochastic integrals defined. Any extra requirement (e.g. square-integrability of coefficient
processes along Theta) must either be implied by the paper's assumptions (Lip + integ, eq. (4.2)),
or be one the paper itself imposes (in Thm 3.3 without Ass 3.1 the paper derives only that the
coefficient DIFFERENCES are square-integrable, so requiring each coefficient process to be
square-integrable individually would be an extra hypothesis in uniqueness without origin
integrability -- Remark 3.4). Junk: Lean total integrals returning 0 for non-integrable
integrands must not make non-admissible tuples count as admissible.
Comparison (verdict recorded 2026-10-17T12:37:45Z):
Comparison for PaperAdmissibleInt (Dissertation/WellPosedness/System/PaperWeakSolutionInt.lean:58).
Definitions read: driftProc/diffusionProc/driverProc/jumpProc/terminalVal (System/Solves.lean),
tupleAt/uLift/TupleH (System/Tuple.lean), lawP2 (Law/LawP2.lean), leftLimProc (System/LawFlow.lean),
Coeffs (System/Coefficients.lean), LevyStochCalc energy / markedEnergy / ProgressivelyMeasurable /
MarkedProgressivelyMeasurable / Predictable / MarkedPredictable.

Item by item against my reading ("the integrals of (1.1) along Theta exist"):
- drift b(s,Theta_s,mu_s): driftProc = indicator_[0,T] of C.b s (tupleAt X Y Z U s omega)
  (lawP2 P (tupleAt ... s)) i. Tuple at time s (no left limits), law of the full tuple at time s
  under P. Fields: joint measurability, progressive measurability (b_prog), a.s. integrable paths on
  [0,T] (b_int) -- exactly the existence of the pathwise Lebesgue integral int_0^t b ds, no L^2
  requirement (consistent with Thm 3.3 / Rem 3.4 where Ass 2.2 is absent). Matches.
- diffusion: joint + progressive measurability and finite energy E int_0^T |sigma_ij|^2 < inf. The
  paper's Ito integral is the L^2 one; moreover for deterministic coefficients Lipschitz along the
  diagonal and an Hweak tuple, local square integrability of s -> sigma(s,Theta_s,mu_s) forces
  int_0^T |sigma(s,0,delta_0)|^2 ds < inf and hence finite energy, so this is no restriction in the
  claims where the definition is used (all assume Ass 2.3). Matches.
- driver f: as drift. Matches.
- jump: a representative gamma, cut to [0,T] (jumpProc), jointly measurable, marked progressively
  measurable, finite marked energy (E int int |gamma|^2 nu ds < inf), and jump_rep: for a.e. s in
  [0,T], a.s., e -> gamma(s,omega,e) equals h(s, Theta^-_s(omega), ., mu^-_s) nu-a.e., with
  Theta^-_s = tupleAt (leftLimProc X) (leftLimProc Y) Z U s and mu^-_s = lawP2 P Theta^-_s. This is the
  paper's (2.4)/(2.5) reading of the Poisson integrand through a representative; the paper's is
  predictable, the Lean one marked progressive, but since it equals the predictable-tuple
  evaluation dP dt nu-a.e. the L^2 compensated integral (defined through the dP dt nu energy) is the
  same. Matches.
- Law flows: Lean uses the exact law lawP2 P Theta_s at every s (Dirac 0 when Theta_s is not in L^2)
  rather than a Borel representative; for an Hweak tuple Theta_s in L^2 for a.e. s, so it agrees
  with the paper's Borel representative for a.e. s (Lemma A.1), and the coefficient processes agree
  dt dP-a.e.
- U channel: uLift gives 0 when e -> U_s(omega,e) is not square integrable -- only on a dt dP-null set
  for U in H^2_N.
- Left limits: Function.leftLim over R; at s = 0 it reads X at negative times (junk) and where a left
  limit fails to exist it is a limUnder junk value; both only on null sets (a single time; a null set
  of omega) and irrelevant to the a.e.-s representation and to the integrals.
- Nothing about X_T in L^2 here: that is in PaperWeakSolutionInt (XT_sq). Fine for this unit.
- No junk-integral issue: integrability fields guarantee the Bochner/stochastic integrals are the
  genuine ones.
No mismatch found. Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices (all harmless):
1. Coefficient processes are extended by 0 off [0,T] (indicator); only [0,T] enters (1.1).
2. mu_s, mu^-_s are the exact laws lawP2 P Theta_s at every time (Dirac 0 when Theta_s is not in L^2)
   instead of Lemma A.1's Borel representatives; they agree for a.e. s, so coefficient processes
   agree dt dP-a.e. and every integral is unchanged.
3. The L^2(nu) channel uLift is 0 where U_s(omega,.) is not square integrable: a dt dP-null set.
4. The Poisson integrand is a representative gamma required marked progressively measurable and
   equal nu-a.e. to h(s,Theta^-_s,.,mu^-_s) for a.e. s, a.s. (the paper's is predictable); the L^2
   compensated integral depends only on the dP dt nu class, so it is the paper's integral.
5. Finite energy of sigma and gamma (L^2 stochastic integrals) rather than mere existence; under
   Ass 2.3 (assumed wherever the unit is used) any Hweak tuple along which these integrals exist
   satisfies it. Drift/driver only need a.s. integrable paths, matching the Lebesgue integrals.
6. Joint measurability is asked besides progressive measurability (implied).
7. leftLimProc at s = 0 / where no left limit exists takes junk values: a single time and a null set
   of paths, irrelevant to the a.e.-s representation.
Disagreements with the author's review (shown 2026-10-17T15:05:44Z): none (the author's excerpt shown for this unit is a marker and at most a section heading, with no
item-level reading to compare against; my comparison file records the representation choices in
detail).
