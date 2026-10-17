### A:ex:brownian: Dissertation.WellPosedness.Spec.BrownianPaperSolution.mk
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash d9e9d3d34768f9080000000000000000 (pl-fp-v1:495c4cca674452fcec0e9396a90f456928fc5905ca1d5ccc77131e667d6ab83e)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T16:02:47Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T15:42:32Z):
Reading for def:Dissertation.WellPosedness.Spec.BrownianPaperSolution.mk (locked before Lean).

Constructor of BrownianPaperSolution: fields must be the components (X, Y, Z) on the Brownian
basis and the conditions: X, Y cadlag adapted (Brownian filtration W, F_0), E sup|X|^2 < inf,
E sup|Y|^2 < inf, Z predictable/progressive with E int |Z|_F^2 < inf, the forward identity
X_t = xi_0 + int_0^t b ds + int_0^t sigma dW and the backward identity
Y_t = g(X_T, Law X_T) + int_t^T f ds - int_t^T Z dW, a.s. for every t in [0,T], with
mu_s = Law(X_s,Y_s,Z_s). Faithful iff the fields are exactly these (no extra restrictive field,
none missing).
Comparison (verdict recorded 2026-10-17T15:58:46Z):
Comparison for def:Dissertation.WellPosedness.Spec.BrownianPaperSolution.mk (constructor).

The constructor's fields are exactly those of BrownianPaperSolution (Spec/BrownianForms.lean:150-238),
compared in that unit: X, Y adapted on [0,T] (Measurable[F t]; the printed signature elides the
sigma-algebra argument, the source has it), every path right-continuous on [0,T), a.s. left limits,
E sup |.|^2 < inf; Z predictable, 0 off [0,T], finite energy; drift/diffusion/driver processes along
(X, Y, Z, 0) jointly and progressively measurable with finite energy; forward and backward identities
a.s. for all t in [0,T] with cadlag versions of the Ito integrals and the terminal law of X_T.

Against my reading: components (X, Y, Z) on the Brownian basis, S^2 x S^2 x H^2_W, the two Brownian
identities with own laws: present; nothing missing; the only additional fields are the measurability
and finite-energy conditions on the coefficient processes (automatic under Assumptions 2.2-2.3 for HH
tuples, needed for the L^2 Ito integral) and version conventions.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices (those of BrownianPaperSolution): Brownian reduction at nu = 0; coordinates;
cadlag as every path right-continuous on [0,T) plus a.s. left limits; cadlag versions of the library
Ito integrals with the identities on one null set; coefficient processes along the solution
required jointly and progressively measurable with finite energy ((2.5) and (4.2), automatic under
Assumptions 2.2-2.3 for HH tuples); Z extended by 0 off [0,T]; the filtration a parameter.
Disagreements with the author's review (shown 2026-10-17T16:02:38Z): none (the author's entry for the constructor is empty, but the review of BrownianPaperSolution
just above it names this constructor and describes its fields; my remarks there apply).
