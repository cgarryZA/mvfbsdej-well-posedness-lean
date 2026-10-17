### A:ex:brownian: Dissertation.PaperSpec.A.BrownianWeakSolution
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash ad5f899adde540f582430c5fbb5efc55 (pl-fp-v1:90bb9a29f8dd89b4f17dfaef61ab09da22a7a6b5535cce0528d7f4cbffd0d0e9)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T16:02:01Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T15:42:32Z):
Reading for def:Dissertation.PaperSpec.A.BrownianWeakSolution (locked before seeing Lean).

Same notion as BrownianPaperWeakSolution: (X,Y,Z) on the Brownian basis with X, Y cadlag adapted,
E int_0^T |X|^2 dt < inf, E int_0^T |Y|^2 dt < inf, X_T in L^2 (presupposed by the terminal law),
Z in H^2_W, satisfying the Brownian forward and backward identities a.s. for every t in [0,T],
with mu_s = Law Theta_s for a.e. s and terminal g(X_T, Law X_T). No E sup requirement.
A Prop wrapper of the structure is fine.
Comparison (verdict recorded 2026-10-17T15:56:38Z):
Comparison for def:Dissertation.PaperSpec.A.BrownianWeakSolution.

Lean: BrownianWeakSolution W hG0 hW T C xi0 X Y Z := BrownianPaperWeakSolution W (enlBrownian G0 W hG0) hW T C
xi0 X Y Z ∧ every path of X and Y has left limits on (0,T].

Against my reading: the Hweak Brownian notion over the usual augmentation of the (W, G0)
filtration: X, Y cadlag adapted with E int |.|^2 dt < inf, X_T in L^2, Z in H^2_W, identities a.s. for
every t with own laws and terminal law, no E sup: yes, via BrownianPaperWeakSolution (unit 15) whose
representation choices carry over; the extra clause makes every path cadlag on [0,T].
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices (inherited from BrownianPaperWeakSolution): Brownian reduction at nu = 0;
coordinatewise processes; every path cadlag on [0,T]; cadlag versions of the Ito integrals and the
identities on one null set; the integrals made explicit (drift and driver pathwise integrable,
diffusion of finite energy, measurability of the coefficient processes); X_T in L^2 explicit;
filtration enlBrownian.
Disagreements with the author's review (shown 2026-10-17T16:01:54Z): none
