### A:ex:brownian: Dissertation.PaperSpec.A.BrownianSolution
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash ad5f899adde540f54a42ffaf2a183700 (pl-fp-v1:b6f008aeca3701b5df167846c3307f862efecf18ea2d9f339d1c59c3cb9cf663)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T16:01:53Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T15:42:32Z):
Reading for def:Dissertation.PaperSpec.A.BrownianSolution (locked before seeing Lean).

Same paper notion as BrownianPaperSolution: a solution in S^2 x S^2 x H^2_W of the Brownian
reduction (Ex 5.2) of (1.1) on the Brownian filtration (W, F_0):
 X_t = xi_0 + int_0^t b(s,Theta_s,mu_s) ds + int_0^t sigma(s,Theta_s,mu_s) dW_s,
 Y_t = g(X_T, Law X_T) + int_t^T f(s,Theta_s,mu_s) ds - int_t^T Z_s dW_s,
a.s. for every t in [0,T], Theta = (X,Y,Z), mu_s = Law Theta_s (a.e. t), with X, Y cadlag adapted,
E sup|X|^2, E sup|Y|^2 < inf, Z predictable/progressive with E int |Z|_F^2 < inf. The PaperSpec
def may be a Prop wrapper (e.g. Nonempty of the structure, or existence of the components); it
must express exactly this, over the Brownian basis with no Poisson channel and no U-coordinate.
Comparison (verdict recorded 2026-10-17T15:56:30Z):
Comparison for def:Dissertation.PaperSpec.A.BrownianSolution.

Lean (PaperSpec/A/Sec5BrownianReduction.lean): BrownianSolution W hG0 hW T C xi0 X Y Z :=
BrownianPaperSolution W (enlBrownian G0 W hG0) hW T C xi0 X Y Z ∧ every path of X and Y has left limits
on (0,T]; C : Coeffs (0) n m d.

Against my reading: the Brownian solution notion over the usual augmentation of the (W, G0)
filtration: yes (enlBrownian, unit 5); in S^2 x S^2 x H^2_W with the Brownian forward and backward
identities a.s. for every t, own laws, terminal law: yes, via BrownianPaperSolution (unit 14),
whose representation choices carry over (nu = 0, coordinates, versions, explicit measurability and
energy of the coefficient processes). The added left-limit clause makes every path cadlag on
[0,T], matching the full Solution notion so that ex_brownian_reduction compares like with like.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices (inherited from BrownianPaperSolution): Brownian reduction at nu = 0;
coordinatewise processes; every path cadlag on [0,T] (right-continuous on [0,T), and, by the extra
clause, left limits on (0,T]); cadlag versions of the Ito integrals with the identities on one null
set; coefficient processes required measurable with finite energy (automatic under Assumptions
2.2-2.3 for HH tuples); integrands extended by 0 off [0,T]; the filtration is enlBrownian, the usual
augmentation (by the null sets of the ambient sigma-algebra) of the (W, G0) filtration.
Disagreements with the author's review (shown 2026-10-17T16:01:48Z): none
