### A:cor:robust, A:eq:forced, A:eq:mvfbsdej, A:ex:brownian, A:ex:concrete, A:intro:mvfbsdej, A:lem:bpbsde, A:lem:cont, A:lem:pert, A:lem:small, A:rem:cwp-class, A:rem:generalrank, A:sec2:prp, A:sec3:one-null-set, A:sec4:WP-def, A:sec4:horizon-not-contractive, A:sec:examples, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: LevyStochCalc.Poisson.Compensated.stageHorizon
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash c8740e4d49db17c3a53710c3133d9af0 (pl-fp-v1:c578433722693e1388cef9f775ba23bf58ca68bf88988d8f8109a492b37a5bea)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:16:41Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T15:06:20Z):
Reading (locked before any Lean is shown) — def LevyStochCalc.Poisson.Compensated.stageHorizon

Paper notion. None of its own: an internal quantity of the construction of the
compensated-Poisson stochastic integral. From the name, the time horizon used at stage k
(e.g. k, or k+1, so that stages exhaust ℝ_+), or the horizon on which a stage approximant
is controlled. The paper works on [0,T] only; any construction on growing horizons is
faithful iff for every T the stages eventually cover [0,T] (horizon → ∞ or ≥ T) and the
resulting process restricted to [0,T] is the paper's integral. A fixed horizon would be fine
if it is the T of the statement; a horizon that does not reach T would make the integral on
part of [0,T] junk.
Comparison (verdict recorded 2026-10-17T15:15:52Z):
Comparison — stageHorizon (CompensatedApprox.lean:281-282)

Lean: stageHorizon n = 2^n (real). Positive, monotone, unbounded.
Against my reading: the horizons of the stages exhaust [0,∞): for every t there is N₀ with
t ≤ 2^{N₀} (used in stageLp_cauchySeq), so every [0,T] is eventually covered and the limit at
each time t is the genuine integral.
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-17T15:15:58Z): The author's review, as shown by rv.py author, consists of the review marker only (no reading text, no item-by-item comparison), so there is no stated position of the author to disagree with on substance.
I agree with the implicit verdict (reviewed as faithful); my comparison finds no representation choice that needs recording.
