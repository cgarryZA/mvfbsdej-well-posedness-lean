### A:lem:cont, A:lem:pert, A:lem:small, A:sec4:WP-def: Dissertation.WellPosedness.System.PredForcing.mk
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 72571516b42bad8d0000000000000000 (pl-fp-v1:28aa56fd208183b2889cce407bf67882b0603543e6ad6c0016ba12dadfcd6c0f)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:06:17Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:33:34Z):
Reading for PredForcing.mk (constructor of the structure PredForcing).
Same notion as PredForcing (square-integrable forcing: progressive q^b, q^sigma, q^f in L^2(Omega x [0,T]),
predictable q^h in L^2(dP dt nu), q^g_T in L^2(F_T)). The constructor takes exactly the structure's
fields; faithful iff the structure is.
Comparison (verdict recorded 2026-10-17T12:42:30Z):
Comparison for PredForcing.mk: the constructor takes the parent Forcing F P nu T q and qh_pred (each
coordinate of q^h marked predictable) and returns PredForcing F P nu T q -- exactly the structure's
fields. Meaning as reviewed under PredForcing (faithful with the representation choices there).
Witness: —
Verdict: faithful with representation choices — Representation choices (harmless):
1. Forcing components are processes on R vanishing off [0,T] (encoding of processes on [0,T]).
2. Joint measurability is required besides progressive / marked predictable measurability (implied).
3. The marked predictable sigma-algebra lacks the paper's time-0 cells, forcing q^h(0) = 0; time 0 is
   Lebesgue-null and every paper q^h has an a.e.-equal version in the class.
4. q^g_T is required strongly F_T-measurable (an exact representative of its L^2(F_T) class).
5. q^h is required both marked progressive (inherited from Forcing) and marked predictable; the
   former follows from the latter.
Under WP's "for every forcing", each paper forcing is represented by one in this class with the
same integrals in (4.1), so the quantifier is equivalent to the paper's.
Disagreements with the author's review (shown 2026-10-17T15:05:46Z): none (the author's excerpt shown for this unit is a marker and at most a section heading, with no
item-level reading to compare against; my comparison file records the representation choices in
detail).
