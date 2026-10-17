### A:cor:robust, A:eq:mvfbsdej, A:ex:concrete, A:intro:mvfbsdej, A:rem:cwp-class, A:rem:generalrank, A:thm3.1:companion, A:thm:cwp, A:thm:stab: Dissertation.WellPosedness.System.PaperSolution.mk
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 07f48ea7fa37d0240000000000000000 (pl-fp-v1:1b6b3045e165f5e70edc04ea705e83944be66c061956fea7b36abfec03828b60)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:06:15Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:33:34Z):
Reading for PaperSolution.mk (constructor of the structure PaperSolution).
Paper notion: same as PaperSolution (a solution of (1.1) in HH, §3). The constructor must take
exactly the fields of the structure and return the structure; its faithfulness reduces to that of
PaperSolution: the fields jointly must say Theta in HH (cadlag adapted X, Y with E sup |.|^2 < inf;
predictable Z, U with finite energies), both identities of (1.1) a.s. for every t in [0,T], h at the
predictable tuple and law flows mu, mu^-; no extra hypotheses and no missing ones.
Comparison (verdict recorded 2026-10-17T12:39:20Z):
Comparison for PaperSolution.mk: the auto-generated constructor of the structure PaperSolution; its
type takes exactly the structure's fields (X_adapted ... bwd, the later fields depending on the
earlier ones as in the structure) and returns PaperSolution D F hFW hFN T C xi0 X Y Z U gamma. It
adds and drops nothing, so its meaning is the structure's, reviewed under PaperSolution: faithful to
the paper's solution in HH of (1.1) with the representation choices listed there.
Witness: —
Verdict: faithful with representation choices — Representation choices (harmless):
1. Coordinate encoding: X, Y, Z, U as families of real processes indexed by R; Z's rows give the
   m x d channel (Frobenius norm via EuclideanSpace on pairs); U a real function of (s, omega, e).
2. Cadlag: every path right-continuous on [0,T), left limits only a.s. on (0,T] (invariant under
   indistinguishability; the PaperSpec wrapper Solution adds every-path left limits). Nothing is
   asked of X, Y off [0,T].
3. Z, U vanish off [0,T] (normalisation); the marked-predictable sigma-algebra has no time-0 cells,
   forcing U_0 = 0 (and predictability forces Z_0 = 0): a Lebesgue-null time.
4. Finite energy of the drift and driver processes and joint/progressive measurability of all
   coefficient processes are fields; every claim using the unit assumes JointBorel and Ass 2.2-2.3,
   under which every paper solution in HH has them ((2.5), (4.2)).
5. Exact laws lawP2 P Theta_s at every time (Dirac 0 off L^2) instead of Lemma A.1's Borel
   representatives; equal for a.e. s, so integrals unchanged. uLift junk 0 on a dt dP-null set.
6. Poisson integrand through a marked-progressive representative gamma equal to the predictable-tuple
   evaluation nu-a.e. for a.e. s, a.s.; same L^2 integral.
7. Identities stated a.s. simultaneously for all t in [0,T], with a cadlag version M of the per-time
   Brownian L^2 integral: equivalent to the paper's "a.s. for every t" (paper says so).
8. xi0 is an arbitrary function here; its F_0-measurability and square integrability come from
   Ass 2.2 in the claims.
Disagreements with the author's review (shown 2026-10-17T15:05:44Z): none (the author's excerpt shown for this unit is a marker and at most a section heading, with no
item-level reading to compare against; my comparison file records the representation choices in
detail).
