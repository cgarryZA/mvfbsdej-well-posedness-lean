### A:eq:forced, A:lem:cont, A:lem:small, A:sec4:WP-def: Dissertation.WellPosedness.System.PaperSolutionForced.mk
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash f826ed5f5757258c0000000000000000 (pl-fp-v1:dda3ae4f0835b38f6e958f4e207b7de638a04c05017df8ddb665c5c310aad2cc)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:06:15Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:33:34Z):
Reading for PaperSolutionForced.mk (constructor of the structure PaperSolutionForced).
Same notion as PaperSolutionForced (solution in HH of (4.1) at lambda with forcing q and initial
datum xi_0). The constructor takes exactly the structure's fields; faithful iff the structure is.
Comparison (verdict recorded 2026-10-17T12:40:42Z):
Comparison for PaperSolutionForced.mk: the auto-generated constructor of PaperSolutionForced; its type
takes exactly the structure's fields (forcing, X_adapted, ..., bwd, dependent fields as in the
structure) and returns PaperSolutionForced D F hFW hFN T lam C xi0 qb qsigma qh qf qg X Y Z U gamma. It
adds and drops nothing; its meaning is the structure's, reviewed under PaperSolutionForced: faithful
to the paper's solution in HH of (4.1), with the representation choices listed there.
Witness: —
Verdict: faithful with representation choices — Representation choices (harmless), in addition to those of PaperSolution (coordinate encoding,
every-path right continuity with a.s. left limits, Z/U and forcings vanishing off [0,T], exact laws
at every time, uLift junk on a null set, marked-progressive representative gamma, identities on one
null set with cadlag versions of the Brownian integrals):
1. Measurability and finite energy are asked of the forced integrands lam*psi + q^psi rather than of
   psi and q^psi separately; given q square integrable and progressive these are equivalent for
   lam /= 0, and the single integral of the sum equals the paper's sum of integrals by linearity.
2. The forcing field is Forcing (q^h marked progressively measurable, all components vanishing off
   [0,T], q^g_T strongly F_T-measurable): implied by the paper's class (PredForcing, which WP
   quantifies over); the larger class only enlarges what may be plugged in.
3. Finite energy of the forced drift and driver is more than existence of the Lebesgue integrals;
   implied under Ass 2.2-2.3, which every claim using the unit assumes.
Disagreements with the author's review (shown 2026-10-17T15:05:45Z): none (the author's excerpt shown for this unit is a marker and at most a section heading, with no
item-level reading to compare against; my comparison file records the representation choices in
detail).
