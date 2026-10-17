### A:cor:robust, A:eq:forced, A:eq:mvfbsdej, A:ex:brownian, A:ex:concrete, A:intro:mvfbsdej, A:lem:bpbsde, A:lem:cont, A:lem:pert, A:lem:small, A:rem:cwp-class, A:rem:generalrank, A:sec2:prp, A:sec3:one-null-set, A:sec4:WP-def, A:sec4:horizon-not-contractive, A:sec:examples, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: LevyStochCalc.Poisson.Compensated.TimeGrid.N₀
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 96a3829b277b5ce438918b7312dbff61 (pl-fp-v1:e6ef2b887f951f78019572d712bd980d1ef3c9fa9b0b0a2498f8c5b8147255a8)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:01:48Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:35:34Z):
Unit: def:LevyStochCalc.Poisson.Compensated.TimeGrid.N₀ (reading locked before any Lean is seen)

Paper notion. The number of steps (slabs) of the time grid (unit 25).

What a faithful Lean definition must be.
- A natural-number field of TimeGrid indexing the grid points / slabs; no further content.
Comparison (verdict recorded 2026-10-17T15:01:17Z):
Comparison: def:LevyStochCalc.Poisson.Compensated.TimeGrid.N₀
(Poisson/MarkStepIsometry.lean:32-33.)

- Reading: natural-number number of slabs; no content.
- Lean: N_0 : N, "Number of pieces"; the slabs are (p_i, p_{i+1}], i < N_0.

Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-17T15:01:28Z): none
