### A:cor:robust, A:rem:cwp-class, A:rem:generalrank, A:sec:examples, A:thm:uniq: Dissertation.WellPosedness.System.PaperWeakSolutionInt.mk
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 88d41182691dfcb90000000000000000 (pl-fp-v1:b2c5d23e54a3eeaac27cf895a0d2f462cc8c7bf03356ee7852820ea404be81c4)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:06:16Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:33:34Z):
Reading for PaperWeakSolutionInt.mk (constructor of the structure PaperWeakSolutionInt).
Same notion as PaperWeakSolutionInt (Theta in Hweak, X_T in L^2, integrals of (1.1) existing, both
identities of (1.1) for every t a.s.). The constructor takes exactly the structure's fields;
faithful iff the structure is.
Comparison (verdict recorded 2026-10-17T12:41:29Z):
Comparison for PaperWeakSolutionInt.mk: the auto-generated constructor; it takes the two parents
(toPaperWeakTuple, toPaperAdmissibleInt), XT_sq, fwd and bwd -- exactly the structure's fields -- and
returns PaperWeakSolutionInt D F hFW hFN T C xi0 X Y Z U gamma. Nothing added or dropped; meaning as
reviewed under PaperWeakSolutionInt (faithful with the representation choices listed there).
Witness: —
Verdict: faithful with representation choices — Representation choices (harmless): those of PaperWeakTuple and PaperAdmissibleInt (coordinate
encoding; every-path right continuity, a.s. left limits; Z, U vanishing off [0,T]; exact laws at every
time with Dirac-0 junk off L^2; uLift junk on a null set; marked-progressive representative gamma of
the predictable jump integrand; L^2 existence conditions for the stochastic integrals, pathwise for
the Lebesgue ones; junk left limits at time 0) and of PaperSolution's identities (one null set for all
t in [0,T], cadlag versions M of the per-time Brownian L^2 integrals). xi0 is an arbitrary function
(no L^2, as Thm 3.3 has no Ass 2.2).
Disagreements with the author's review (shown 2026-10-17T15:05:45Z): none (the author's excerpt shown for this unit is a marker and at most a section heading, with no
item-level reading to compare against; my comparison file records the representation choices in
detail).
