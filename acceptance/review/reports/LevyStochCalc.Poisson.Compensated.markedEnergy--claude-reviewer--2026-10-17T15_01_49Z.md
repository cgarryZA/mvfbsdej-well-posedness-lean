### A:cor:robust, A:eq:coefmeas, A:eq:forced, A:eq:mvfbsdej, A:ex:brownian, A:ex:concrete, A:intro:mvfbsdej, A:lem:bpbsde, A:lem:cont, A:lem:lawflow, A:lem:pert, A:lem:small, A:rem:cwp-class, A:rem:generalrank, A:sec2:coefmeas, A:sec2:prp, A:sec3:HH-banach, A:sec3:one-null-set, A:sec4:WP-def, A:sec4:horizon-not-contractive, A:sec:examples, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: LevyStochCalc.Poisson.Compensated.markedEnergy
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 2cb843d4d0d59f2db65e60392e647c8a (pl-fp-v1:ee56f20b3228540bce8abb7e1b147d9fa5d5c918d2a2b446386794f74530cd40)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:01:49Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:35:34Z):
Unit: def:LevyStochCalc.Poisson.Compensated.markedEnergy (reading locked before any Lean is seen)

Paper notion. The squared norm of a marked integrand in the space H^2_N of Section 3 (line ~560):
   E int_0^T ||U_t||_{L^2(nu)}^2 dt = E int_0^T int_E |U_t(e)|^2 nu(de) dt
(the right side of the Ito-Levy isometry E|int int U dNtilde|^2 = E int int |U|^2 nu ds and of the
compensation formula (2.1)). For an elementary marked integrand (unit 17) with disjoint B_j it equals
sum_{k,j} E|xi_{k,j}|^2 (t_{k+1}-t_k) nu(B_j).

What a faithful Lean definition must be.
- For an integrand psi(t, omega, e) (real or R^m), the triple integral of |psi|^2 against
  dt on [0,T] (x) dP (x) nu, either as an R>=0oo-valued lintegral (natural: finiteness is then the
  H^2_N membership condition) or as a real integral.
- Edge case: if real-valued via Bochner integrals, the junk value 0 for non-integrable psi would make
  "markedEnergy psi < oo" or "markedEnergy psi = 0" vacuous/wrong statements; a real-valued version is
  harmless only if every use also requires integrability. Also the order of integration: Tonelli makes all
  orders agree for the lintegral; for Bochner integrals iterated junk can differ, so only the lintegral (or
  integrability hypotheses) is safe.
- Integration over [0,T] (or the stated time range) and over all of E with the paper's nu.
Comparison (verdict recorded 2026-10-17T15:01:17Z):
Comparison: def:LevyStochCalc.Poisson.Compensated.markedEnergy
(Poisson/CompensatedIntegrandComplete.lean:34-37; uses e.g. PaperSolution.U_sq (markedEnergy ... != oo) and
WP uniqueness (markedEnergy of differences = 0).)

- Reading: E int_0^T int_E |psi_t(e)|^2 nu(de) dt, either as an R>=0oo lintegral (preferred: finiteness is
  the H^2_N condition) or real; Bochner junk would be dangerous; integration over [0,T] and all of E with
  the paper's nu.
- Lean: markedEnergy P nu T phi = lintegral over omega of lintegral over s in Icc 0 T of lintegral over e
  of ||phi omega s e||_+^2, in R>=0oo. Exactly the H^2_N squared norm for a real (scalar) integrand
  phi : Omega -> R -> E -> R. ENNReal-valued, so "!= oo" means finite energy and "= 0" means phi = 0
  dt (x) dP (x) nu-a.e. on [0,T] for measurable phi; no Bochner junk.
- Measurability: for measurable phi, Tonelli makes the iterated lintegral the product-measure integral
  (any order). For non-measurable phi the iterated lintegral is still defined (lower integral), but every
  use pairs it with marked predictability/measurability of the integrand (PaperSolution.U_pred, gamma_meas),
  so the case does not arise in the propositions.
- Vector integrands: the paper's ||U||_{L^2(nu; R^m)}^2 = sum_k |U^k|^2 is handled by applying markedEnergy
  per component (PaperSolution.U_sq for every k; WP for every k), equivalent to the total.
- Interval Icc 0 T vs (0,T]: differ by a Lebesgue-null set.

Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless:
1. The integrand is scalar (phi : Omega -> R -> E -> R); the paper's L^2(nu; R^m)-valued U is handled by
   applying the definition to each component (the PaperSpec requires finiteness, resp. vanishing, for every
   component), which is equivalent to finiteness, resp. vanishing, of the sum of the components' energies.
2. The value is an iterated R>=0oo lintegral in the order omega, s, e over Icc 0 T x E; for the measurable
   integrands to which the propositions apply it, Tonelli identifies it with the dt (x) dP (x) nu integral
   of |phi|^2 over [0,T] x Omega x E, i.e. the H^2_N squared norm; the endpoints of the time interval are a
   Lebesgue-null set.
Disagreements with the author's review (shown 2026-10-17T15:01:28Z): No disagreement about the meaning. The author's entry is a bare def-review marker with no recorded comparison, so it does not record the representation choices this review lists (each judged harmless):
1. The integrand is scalar (phi : Omega -> R -> E -> R); the paper's L^2(nu; R^m)-valued U is handled by
   applying the definition to each component (the PaperSpec requires finiteness, resp. vanishing, for every
   component), which is equivalent to finiteness, resp. vanishing, of the sum of the components' energies.
2. The value is an iterated R>=0oo lintegral in the order omega, s, e over Icc 0 T x E; for the measurable
   integrands to which the propositions apply it, Tonelli identifies it with the dt (x) dP (x) nu integral
   of |phi|^2 over [0,T] x Omega x E, i.e. the H^2_N squared norm; the endpoints of the time interval are a
   Lebesgue-null set.
