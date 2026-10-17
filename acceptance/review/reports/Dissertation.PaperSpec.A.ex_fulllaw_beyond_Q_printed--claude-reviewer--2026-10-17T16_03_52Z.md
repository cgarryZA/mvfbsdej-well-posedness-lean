### A:ex:fulllaw: Dissertation.PaperSpec.A.ex_fulllaw_beyond_Q_printed
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash ed839d34f480cba1ef10ddd1a845cbd2 (pl-fp-v1:6c15473a14199e99c7f796ff7631320c2cb734020ef57e4ce79877cab02a0848)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T16:03:52Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T15:47:47Z):
Reading of spec ex_fulllaw_beyond_Q_printed, as printed (arbitrary bounded Lipschitz features):
"the Q-term, a nonlinear cylindrical functional of the U-marginal: finitely many integrals of
arbitrary bounded-Lipschitz features on the fibre, composed through the nonlinear Q ... lies
beyond the expectation ... interactions".

Printed proposition: for every sigma-finite nu (countably generated E), all n,m,d, J >= 1,
all bounded Lipschitz features phi_j : L^2(nu) -> R, and every bounded Lipschitz Q : R^J -> R
that is nonlinear (= not affine on R^J), the cylindrical term mu |-> Q(int phi_1 dmu^U, ...,
int phi_J dmu^U) (times w_1 != 0) is not an expectation functional.
"Arbitrary" features: universal; "nonlinear Q": not affine on R^J (globally). 
Expected refutation: constant features (phi_j = const; bounded Lipschitz), with any non-affine
bounded Lipschitz Q (e.g. Q = sin(r_1) or a clipped |r|), make the term constant, hence an
expectation functional; also nu = 0 works. The counterexample is covered by the printed claim
("arbitrary bounded-Lipschitz features" includes constants). Valid.
The proposition must be no stronger than printed: its "nonlinear" must be global non-affinity
of Q on R^J (the weakest reading of "nonlinear Q"); if it used "Q not linear" (allowing affine
non-linear Q = a + c.r), refuting it would be easier but still within printed text? "Nonlinear
Q" could be read as "not linear" - but an affine non-constant Q with constant features also
gives an expectation functional, so either reading is refuted by the same counterexample.
Comparison (verdict recorded 2026-10-17T16:01:29Z):
Comparison, ex_fulllaw_beyond_Q_printed (AsPrinted.lean:128-141), printed reading, refuted.
Setting: sigma-finite nu on countably generated E, any n m d J; features bounded Lipschitz
("arbitrary bounded-Lipschitz features"), Q bounded Lipschitz and not affine on R^J (no a, c
with Q s = a + sum c_j s_j for all s) - the weakest reading of "the nonlinear Q" (global
non-affinity). Conclusion: the cylindrical term is no expectation functional (as in the
corrected clause). Not stronger than printed.
Refutation ex_fulllaw_beyond_Q_printed_false: nu = delta_0 on R (a genuine nonzero instance),
n = m = d = J = 1, the bounded Lipschitz feature phi = 0, Q(s) = min(1, |s_1|) bounded,
1-Lipschitz, not affine; the term is Q(0) = 0 = int 0 dmu. Constant features are bounded
Lipschitz, so "arbitrary bounded-Lipschitz features" covers them. Valid.
Verdict: faithful (refutation valid).
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-17T16:01:36Z): The author's review recorded for this unit is empty (its text is attached to an adjacent review marker of a unit outside this chunk and was not shown), so there is nothing to compare point by point. My verdict: faithful (see comparison); no disagreement can be recorded against an empty review.
