### A:ex:brownian: Dissertation.WellPosedness.Spec.BrownianPaperSolution
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 022ed18f831241360000000000000000 (pl-fp-v1:07199fadc2fdd6630ecc12c86d995ed5b2a512f18d5a4adc953aa711ad5fbb8f)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T16:01:01Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T15:42:31Z):
Reading for def:Dissertation.WellPosedness.Spec.BrownianPaperSolution (locked before seeing Lean).

Paper notion: a solution of the Brownian reduction (Ex 5.2) of (1.1) in the space
S^2(R^n) x S^2(R^m) x H^2_W(R^{m x d}): a triple (X,Y,Z), X,Y cadlag (here continuous suffices)
adapted to the Brownian filtration (W, F_0), E sup |X|^2 < inf, E sup |Y|^2 < inf, Z predictable
(or progressively measurable) with E int_0^T |Z|_F^2 dt < inf, such that a.s. for every
t in [0,T]:
 X_t = xi_0 + int_0^t b(s,Theta_s,mu_s) ds + int_0^t sigma(s,Theta_s,mu_s) dW_s,
 Y_t = g(X_T, Law X_T) + int_t^T f(s,Theta_s,mu_s) ds - int_t^T Z_s dW_s,
with Theta = (X,Y,Z) and mu_s = Law(Theta_s) (Borel representative, a.e. equal).
Faithful: Brownian filtration (no Poisson), H_B-valued tuple (no U), the Ito integral, the
correct law arguments (full-tuple law of (X,Y,Z), terminal law of X_T), the S^2/H^2 integrability.
A structure with fields for the components and the conditions is fine. Using "for each t a.s."
is equivalent by cadlag paths.
Comparison (verdict recorded 2026-10-17T15:52:52Z):
Comparison for def:Dissertation.WellPosedness.Spec.BrownianPaperSolution.

Lean (Spec/BrownianForms.lean): structure BrownianPaperSolution W F hFW T C xi0 X Y Z, C : Coeffs (0) n m d,
coordinates X i, Y k, Z k (Fin d -> R):
 X, Y: adapted on [0,T], every path right-continuous on [0,T), a.s. left limits on (0,T],
   E sup_{[0,T]} |X|^2 < inf, E sup |Y|^2 < inf;
 Z: each coordinate predictable, 0 off [0,T], finite energy;
 drift/diffusion/driver processes along Theta_s = (X_s, Y_s, Z_s, 0) with law lawP2 P (tupleAt .. s):
   jointly measurable, progressive, finite energy E int_0^T |.|^2 < inf;
 fwd: exists a version M of the Ito integral of the diffusion process, a.s. cadlag on [0,T], and a.s.
   for all t in [0,T]: X_t = xi0 + int_{[0,t]} b(s,Theta_s,mu_s) ds + M_t;
 bwd: exists a cadlag version M of int Z dW and a.s. for all t in [0,T]:
   Y_t = g(X_T, law X_T) + int_{[t,T]} f(s,Theta_s,mu_s) ds - (M_T - M_t).

Against my reading:
- Brownian basis: filtration F a parameter with each W^j a Brownian motion for it; the PaperSpec
  wrapper BrownianSolution instantiates F = enlBrownian (W, F_0). nu = 0: no U, no Poisson
  integral. Yes.
- X, Y in S^2 (cadlag adapted, E sup < inf): yes (right-continuity for every path, left limits a.s.;
  the PaperSpec wrapper adds left limits for every path).
- Z in H^2_W predictable: yes.
- identities a.s. for every t on one null set, with the Ito integral (cadlag version), the
  full-tuple law of (X,Y,Z) and the terminal law of X_T: yes (terminalVal uses lawP2 of X_T, the true
  law since X_T in L^2).
- extra conditions: the coefficient processes along Theta are required jointly/progressively
  measurable with finite energy. Measurability is (2.5) (the paper's standing joint Borel
  measurability gives it); finite energy of b, sigma, f along Theta in HH follows from Assumptions
  2.2-2.3 by (4.2) (eq:coeffint), the setting of Ex 5.2's claims; the diffusion's finite energy is
  what the L^2 Ito integral needs. For a system without Assumption 2.2 the drift requirement would
  narrow the notion (the weak "Int" variants exist for that), but Ex 5.2 is under 2.2-2.5. Mild.
- xi0 measurability/integrability not part of the notion: hypotheses of the propositions. Fine.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices: (1) Brownian reduction at nu = 0 (tuple (X,Y,Z,0), no Poisson integral);
(2) coordinatewise processes; (3) cadlag as: every path right-continuous on [0,T) and a.s. left
limits (versions); (4) the identities via a cadlag version of the library L^2 Ito integral, on one
full-measure set for all t in [0,T]; (5) the coefficient processes along the solution are required
jointly and progressively measurable with finite energy: measurability is (2.5) under the standing
joint Borel measurability, and the energies are finite for Theta in HH under Assumptions 2.2-2.3
((4.2)), so this restricts nothing where the paper uses the notion (systems satisfying 2.2-2.5);
(6) Z and the coefficient processes extended by 0 off [0,T]; (7) the filtration is a parameter,
instantiated by the PaperSpec wrapper with the usual augmentation of the (W, F_0) filtration.
Disagreements with the author's review (shown 2026-10-17T16:00:55Z): No disagreement on the description. The review describes the Lean by its diff from PaperSolution
but does not compare it with the paper: it should record that the required measurability and
finite energy of the drift, diffusion and driver processes along the solution are not part of the
printed solution notion and are harmless only because they follow from (2.5) and (4.2) under
Assumptions 2.2-2.3 for HH tuples (the setting of Ex 5.2), and that every path is required
right-continuous on [0,T) (a version choice).
