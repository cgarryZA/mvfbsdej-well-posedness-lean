### A:ass:mono, A:cor:robust, A:ex:brownian, A:ex:concrete, A:lem:cont, A:lem:pert, A:rem:diag-mono, A:rem:generalrank, A:rem:intrinsic, A:sec4:horizon-not-contractive, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: Dissertation.WellPosedness.Spec.Assumption25.mk
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 0f5949362ae546510000000000000000 (pl-fp-v1:861a2bc3bed1c760eb259ca5cfa0f71033467350fd6dd6e03286f89a85c27864)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:04:37Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:36:07Z):
Unit: Assumption25.mk, the constructor of Assumption25 (Assumption 2.5). Its type must take
exactly: the terminal inequality E<dg_T, G dX_T> >= alpha E|G dX_T|^2 for all square-integrable
F_T-measurable X_T, X'_T (laws induced); the interior inequality (2.7) in expectation for a.e. t
and all pairs of diagonal inputs at t; the constant pattern alpha, beta1, beta2 >= 0,
alpha+beta1 > 0, beta1+beta2 > 0, m<n -> beta1>0, m>n -> alpha, beta2 > 0; and return
Assumption25 F P T G alpha beta1 beta2 C. Nothing else (no full-rank or Lipschitz premise).
Comparison (verdict recorded 2026-10-17T15:02:18Z):
Assumption25.mk takes: the terminal clause (for strongly F_T-measurable square-integrable X_T, X'_T,
integrability of the pairing and E<dg_T, G dX_T> >= alpha E|G dX_T|^2; the printer drops the
sigma-algebra of StronglyMeasurable, the source field is StronglyMeasurable[F T]); the interior
clause (for a.e. t in [0,T], Mono27At F P t G beta1 beta2 C); Constants n m alpha beta1 beta2; and
returns Assumption25. Exactly my reading, with the same representation choices as Assumption25
(existence of the expectations of the pairings required; strongly measurable representatives).
No full-rank or Lipschitz premise.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — As for Assumption25: the expectations of the two pairings are required to exist (automatic under
Assumption 2.3 and (2.3), always assumed with 2.5); inputs are strongly measurable
representatives of the L^2 classes; Bochner expectations of integrable functions.
Disagreements with the author's review (shown 2026-10-17T15:04:21Z): No disagreement on substance. The author's review is an empty marker with no recorded
comparison; the representation choices listed in my detail are not recorded there.
