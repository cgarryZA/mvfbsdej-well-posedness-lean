### A:cor:robust, A:eq:forced, A:eq:mvfbsdej, A:ex:brownian, A:ex:concrete, A:intro:mvfbsdej, A:lem:bpbsde, A:lem:cont, A:lem:pert, A:lem:small, A:rem:cwp-class, A:rem:generalrank, A:sec2:prp, A:sec3:one-null-set, A:sec4:WP-def, A:sec4:horizon-not-contractive, A:sec:examples, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: LevyStochCalc.Poisson.Compensated.MarkStep.eval
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 29db58ad6d1eaba10f37be13a59482ea (pl-fp-v1:6503e2ccdda261d071ec8cbbaa6758dbb8c4c00172f5bdd0d20c4aa7a48a69be)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:01:48Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:35:33Z):
Unit: def:LevyStochCalc.Poisson.Compensated.MarkStep.eval (reading locked before any Lean is seen)

Paper notion. The pointwise value of the elementary marked integrand (unit 17):
   phi(t, omega, e) = sum_{k,j} xi_{k,j}(omega) 1_{(t_k, t_{k+1}]}(t) 1_{B_j}(e).

What a faithful Lean definition must be.
- A function (t, omega, e) |-> that sum, with LEFT-OPEN, right-closed time slabs (t_k, t_{k+1}] (so that
  the process is predictable / left-continuous in t). A half-open [t_k, t_{k+1}) convention differs only
  on the grid times, a dt-null set, so is harmless for every integral (dt (x) dP (x) nu)-norm and for the
  integral formula, but would make the pointwise process cadlag-adapted rather than left-continuous; harmless
  if the uses are only through integrals and the slab coefficient is still F_{t_k}-measurable.
- Overlapping mark sets add; outside the grid the value is 0.
Comparison (verdict recorded 2026-10-17T15:01:15Z):
Comparison: def:LevyStochCalc.Poisson.Compensated.MarkStep.eval
(Poisson/MarkStepIsometry.lean:102-105.)

- Reading: (t, omega, e) |-> sum_{k,j} xi_{k,j}(omega) 1_{(t_k,t_{k+1}]}(t) 1_{B_j}(e), left-open
  right-closed slabs, overlapping mark sets add, 0 off the grid.
- Lean: eval G s e omega = sum_{i < N_0} 1_{Ioc (p_i) (p_{i+1})}(s) * sum_k xi i k omega * 1_{B k}(e).
  Exactly the reading, with the slabs (p_i, p_{i+1}] (predictable convention); 0 for s outside (0, p_{N_0}].
  Argument order (s, e, omega) is a presentation choice.

Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-17T15:01:27Z): none
