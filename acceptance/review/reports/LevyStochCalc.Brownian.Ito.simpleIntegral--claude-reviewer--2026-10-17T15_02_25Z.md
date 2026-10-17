### A:cor:robust, A:eq:forced, A:eq:mvfbsdej, A:ex:brownian, A:ex:concrete, A:intro:mvfbsdej, A:lem:bpbsde, A:lem:cont, A:lem:pert, A:lem:small, A:rem:cwp-class, A:rem:generalrank, A:sec2:prp, A:sec4:WP-def, A:sec4:horizon-not-contractive, A:sec:examples, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: LevyStochCalc.Brownian.Ito.simpleIntegral
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 1a897ae182e91c2d9e8ab5364d5848bb (pl-fp-v1:bcbbe0c34c29bb96eac6ec690aa95946ba1f5656ea727589b116017db20b278a)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:02:25Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:34:25Z):
Reading for def:LevyStochCalc.Brownian.Ito.simpleIntegral (written before seeing any Lean).

Paper notion. The Ito integral of a simple predictable integrand
Z = sum_{i<N} xi_i 1_{(t_i,t_{i+1}]}: (int_0^t Z dW)(omega) = sum_{i<N} xi_i(omega)
(W_{t_{i+1} wedge t}(omega) - W_{t_i wedge t}(omega)), forward (Ito) increments with xi_i at the
left endpoint. At t = T (or t >= t_N) it is sum xi_i (W_{t_{i+1}} - W_{t_i}).

A faithful Lean definition must:
- use forward increments W_{t_{i+1}} - W_{t_i} multiplied by the coefficient xi_i of the
  interval (t_i, t_{i+1}] (not the right-endpoint coefficient, not the midpoint — Stratonovich);
- cut off at the evaluation time t via min (t_{i+1} wedge t, t_i wedge t), if it is a process in
  t; a terminal-only version (no t) must be used with integrands supported in [0,T] or with the
  partition truncated at t;
- be linear in xi and satisfy the isometry E|int Z dW|^2 = E int |Z|^2 dt for adapted
  square-integrable xi_i.
Comparison (verdict recorded 2026-10-17T15:01:16Z):
Comparison for Ito.simpleIntegral.
Lean: simpleIntegral W H t ω = Σ_i ξ_i(ω) (W_{t_{i+1} ∧ t}(ω) − W_{t_i ∧ t}(ω)).
- Forward (Itô) increments, with the left-endpoint coefficient ξ_i of the piece (t_i, t_{i+1}],
  cut off at t by min. This is exactly the formula of my reading (not Stratonovich, not the
  right-endpoint coefficient).
- Linear in ξ. The isometry is proved under the adaptedness hypothesis (consumers supply it).
  For t < 0 every increment is W_t − W_t = 0.
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-17T15:01:53Z): No disagreement on the substance. The author's entry (acceptance/review/definitions.md) records only the review marker, or a section heading, and no comparison with the paper. It does not state the points I relied on: the formula uses forward increments with the left-endpoint coefficient, cut off at t. The isometry holds only under the adaptedness hypothesis that consumers supply.
