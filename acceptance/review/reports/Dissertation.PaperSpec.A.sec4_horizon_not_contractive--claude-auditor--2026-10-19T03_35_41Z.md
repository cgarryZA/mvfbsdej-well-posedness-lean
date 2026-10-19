### A:sec4:horizon-not-contractive: Dissertation.PaperSpec.A.sec4_horizon_not_contractive
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba1fc081d81965ca7e6 (pl-fp-v1:0f2eca89e394f3acb7be38f17fc0b66a08a91f950a8b0f02b75f579f883c5b85)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:35:41Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:16:43Z):
# Reading: spec sec4_horizon_not_contractive (§4 intro, line 13)

Paper text: "The continuation is in the coupling strength, not the horizon: shortening the horizon
does not make the frozen-coefficient map contractive, since the (z,u)-dependence of sigma,h and the
full-tuple law coupling enter the contraction constant with no T-factor."
Clause: "on every horizon a system satisfying the assumptions has a frozen map that does not
decrease distances".

The frozen-coefficient map is the map Phi_lambda of Lemma 4.2 (eqs. frozenfwd/frozenbwd), taken at
the unscaled coupling lambda = 1 (the point of the remark is that Picard iteration of the original
system, lambda = 1, is not a contraction however short T is): for a trial Theta in HH,
Xbar = xi0 + int b(s,Theta_s,mu^Theta_s) ds + int sigma(...) dW + int int h(s,Theta^-_s,e,mu^{Theta,-}_s) dNtilde,
(Ybar,Zbar,Ubar) from the PRP of E[Xi | F_t], Xi = g(Xbar_T, Law(Xbar_T)) + int_0^T f(s,Theta_s,mu^Theta_s) ds,
Ybar_t = M_t - int_0^t f ds.

A faithful formal statement must contain:
* Setting: the standing Brownian-Poisson basis of §2 (usual conditions, d-dim BM W, independent PRM
  with sigma-finite nu); the horizon T > 0 is ARBITRARY (universally quantified, in particular
  arbitrarily small). Ideally the basis is arbitrary (universally quantified) too: the claim is
  about the fixed standing basis. An existential choice of basis would be a weaker reading.
* Quantifiers: for every T > 0 there EXISTS a coefficient system (b,sigma,h,f,g, xi0) satisfying
  Assumptions 2.2-2.5 on [0,T] (with some G, alpha, beta1, beta2 obeying the constant
  constraints), such that the frozen map Phi of that system on HH(0,T) is not a contraction.
* Conclusion "does not decrease distances": there exist Theta^1, Theta^2 in HH with
  ||Theta^1 - Theta^2||_HH > 0 and ||Phi(Theta^1) - Phi(Theta^2)||_HH >= ||Theta^1 - Theta^2||_HH
  (one pair suffices to refute contractivity with any constant k<1; a statement for all pairs is
  stronger and also acceptable). The norm must be the HH norm (E sup|X|^2 + E sup|Y|^2 +
  E int(|Z|^2+||U||^2)) on both sides; it may be acceptable to bound only the forward component of
  the output from below, since the output norm dominates E sup|dXbar|^2, but the INPUT distance
  must be the full HH distance.
* The pair must be a genuine non-trivial pair (nonzero distance), else ">= " is trivial (0 >= 0).
* The system must genuinely satisfy all assumptions (non-vacuity): e.g. Example 5.1(i) with
  beta1 >= 1 (sigma = sigma_c - beta1 z gives dXbar_T = -beta1 int dZ dW, so the output distance is
  at least beta1^2 * input distance when the input differs only in Z), which works on every T.
* What the "(z,u)-dependence ... no T-factor" explanation adds is motivation; it need not be
  formalized.
* If the Lean frozen map is only the Brownian part (no Poisson channel), it must still be the
  frozen map of a system satisfying the paper's assumptions on the paper's basis (or a recorded
  specialisation such as nu = 0); otherwise it is narrower / a different object.
Comparison (verdict recorded 2026-10-19T03:20:40Z):
# Comparison: sec4_horizon_not_contractive

Lean (PaperSpec/A/Sec4Horizon.lean): for every probability space, every Levy driver D with d = 1,
E = Unit, nu = 0 (a scalar Brownian basis, a point of the §2 setting since nu = 0 is sigma-finite),
every initial sigma-field G0 independent of the driver (filtration enlJoint = usual augmentation of
the driver filtration joined with G0, as in §2), every T > 0, beta1 >= 1, beta2 > 0:
  - the Example 5.1(i) system with sigma_c = h_c = 0 satisfies (2.3), Assumption 2.2 (xi0 = 0),
    2.3 (L = beta1 + beta2), 2.4 (G = 1 full rank), 2.5 (alpha = 1, beta1, beta2) — all asserted
    as conclusions, constants independent of T;
  - BrownianFrozenStep (the frozen step of Lemma 4.2 at lambda = 1, no forcing, xi0 = 0) relates
    the trial 0 to the output 0;
  - there is a trial Theta = (0,0,Z,0), Z = 1 on [0,T], in H_weak, and an output
    (X',Y',Z',U') in H_weak with BrownianFrozenStep Theta -> output, X' = Y' = -beta1 W a.s.,
    Z' = -beta1, U' = 0, and 0 < supSize(Theta) <= supSize(output) < oo.
supSize is E sup|X|^2 + E sup|Y|^2 + E int |Z|^2 + E int ||U||^2 in [0,oo] (the squared HH norm).
So ||Phi(Theta) - Phi(0)||_HH >= ||Theta - 0||_HH > 0 on every horizon: the frozen map is not a
contraction for any T.

Item by item against my reading:
* Horizon arbitrary (forall T > 0): yes; the same system (coefficients and constants independent of
  T) on every horizon — the strongest natural reading.
* System satisfying Assumptions 2.2-2.5 (and Borel measurability): asserted as conclusions, not
  hypotheses — no vacuity. The witness Acceptance.A.sec4_horizon_hypotheses shows a driver exists.
* Frozen map: BrownianFrozenStep is the frozen step (4.10)-(4.11) at lambda = 1: forward
  LinearFSDEJ with integrands driftProc/diffusionProc evaluated along the TRIAL tuple and its law
  lawP2 P (tupleAt ...); backward LinearBSDEJ with terminal terminalVal at the OUTPUT X' and its law
  and driver driverProc along the trial. Matches. The jump integrand of the forward equation is 0,
  which is exact at nu = 0 (the compensated integral against a zero-intensity N vanishes).
* Non-contraction: one pair (Theta, 0) with output distance >= input distance > 0, distances in
  the full HH norm on both sides. Matches my reading ("one pair suffices").
* The frozen map is a relation; outputs are unique up to the HH identification (linear SDE solution
  determined a.s. at each t with right-continuous paths; BSDE by the PRP), so the exhibited output
  pins down the distance.

Representation choices / differences:
1. The basis is restricted to d = 1 and nu = 0 (scalar Brownian, no jumps), universally over such
   bases; bases with nu != 0 or d > 1 are not covered. The claim is a non-contractivity
   observation, i.e. the negation of "the assumptions make the frozen map contractive on short
   horizons"; one system class satisfying all assumptions in the standing setting refutes that,
   and nu = 0 is a point of the setting (Remark 2.10 treats it). The explanation via the
   (z,u)-dependence is realised through the z-dependence of sigma only. Harmless for the claim.
2. The instance (sigma_c = h_c = 0, xi0 = 0, beta1 >= 1) is a recorded instance of Example 5.1(i).
3. Trial and output are stated in H_weak plus finiteness of supSize, which is HH membership.
4. LinearBSDEJ / LinearFSDEJ use right-continuous paths, progressive integrands and the identity
   a.s. at each t (see the reviews of those definitions); harmless here.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless:
1. The claim is witnessed on every Brownian basis with d = 1, E = Unit, nu = 0 (a point of the §2
   setting: nu = 0 is sigma-finite), not on bases with jumps or d > 1. The paper's remark is the
   negation of "under the assumptions the frozen map becomes contractive on short horizons"; one
   system satisfying all of Assumptions 2.2-2.5 whose frozen map is non-contractive on every
   horizon refutes it, and the Lean gives exactly that (same coefficients and constants for all T).
2. The system is the instance sigma_c = h_c = 0, xi0 = 0, beta1 >= 1 of Example 5.1(i); the
   assumptions are asserted as conclusions, so nothing is assumed.
3. Non-contractivity is shown at the pair (Theta, 0), Theta = (0,0,1,0): the squared HH distances
   satisfy 0 < supSize(Theta) <= supSize(Phi Theta) < oo with Phi(0) = 0; one pair with ratio >= 1
   rules out every contraction constant k < 1.
4. The frozen map is the relation BrownianFrozenStep (outputs unique up to the HH identification);
   its forward jump integrand is 0, exact at nu = 0.
5. Trial and output are in H_weak with finite supSize, i.e. in HH.
Disagreements with the author's review (shown 2026-10-19T03:35:31Z): none
