### A:ex:brownian: Dissertation.WellPosedness.Spec.BrownianPaperWeakSolution
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 022ed18f831241360000000000000000 (pl-fp-v1:07199fadc2fdd6630ecc12c86d995ed5b2a512f18d5a4adc953aa711ad5fbb8f)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T16:01:05Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T15:42:31Z):
Reading for def:Dissertation.WellPosedness.Spec.BrownianPaperWeakSolution (locked before Lean).

Paper notion: the Brownian analogue of a tuple in Hweak satisfying (1.1): (X,Y,Z) with X,Y cadlag
adapted (Brownian filtration W, F_0) and E int_0^T |X_t|^2 dt < inf, E int_0^T |Y_t|^2 dt < inf
(L^2(0,T;R^j), not S^2), Z in H^2_W, satisfying a.s. for every t in [0,T] the Brownian forward
and backward identities with mu_s = Law(Theta_s) (a.e. t). The terminal condition
g(X_T, Law X_T) presupposes Law X_T in P2(R^n), i.e. X_T in L^2 (Thm 3.3's proof says so);
a faithful def includes X_T in L^2 or equivalent. Same faithfulness checks as for the strong
version but with the weak integrability; it must not require E sup.
Comparison (verdict recorded 2026-10-17T15:53:12Z):
Comparison for def:Dissertation.WellPosedness.Spec.BrownianPaperWeakSolution.

Lean (Spec/BrownianForms.lean): as BrownianPaperSolution but with: X, Y finite energy
E int_0^T |X_t|^2 dt < inf, E int_0^T |Y_t|^2 dt < inf per coordinate (no E sup); drift and driver
processes jointly measurable, progressive, a.s. pathwise integrable on [0,T] (not finite energy);
diffusion process jointly measurable, progressive, finite energy; X_T in L^2 (XT_sq); Z predictable,
0 off [0,T], finite energy; identities a.s. for all t in [0,T] with cadlag versions of the Ito
integrals; coefficients at Theta_s = (X_s, Y_s, Z_s, 0) and the tuple's own law.

Against my reading:
- Hweak membership (cadlag adapted, L^2(dt(x)dP), Z in H^2_W), no E sup: yes.
- X_T in L^2 (presupposed by the terminal law): yes, explicit.
- identities a.s. for every t, own laws, terminal law of X_T: yes.
- Brownian basis / nu = 0: yes (filtration parameter; PaperSpec wrapper instantiates enlBrownian).
- extra conditions: measurability of the coefficient processes ((2.5)); pathwise integrability of
  drift and driver (what the ds-integrals need, no junk-0 Bochner values); finite energy of the
  diffusion process (what the L^2 Ito integral needs; the paper's stochastic integrals are L^2
  integrals throughout). These make the notion well defined rather than narrowing it in the
  paper's setting; with Assumption 2.2 and Lipschitz coefficients they hold for Hweak tuples.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices: (1) Brownian reduction at nu = 0; (2) coordinatewise processes;
(3) cadlag as every path right-continuous on [0,T) plus a.s. left limits; (4) the identities with
cadlag versions of the library L^2 Ito integrals on one full-measure set for all t in [0,T];
(5) the coefficient processes along the tuple are required jointly and progressively measurable,
the drift and driver a.s. pathwise integrable on [0,T] (so the ds-integrals are genuine) and the
diffusion of finite energy (so the L^2 Ito integral exists), which the paper's identities
presuppose; (6) X_T in L^2 stated explicitly, as the paper's terminal law presupposes.
Disagreements with the author's review (shown 2026-10-17T16:01:01Z): none
