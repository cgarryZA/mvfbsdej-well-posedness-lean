### A:cor:robust, A:eq:forced, A:eq:mvfbsdej, A:ex:brownian, A:ex:concrete, A:intro:mvfbsdej, A:lem:bpbsde, A:lem:cont, A:lem:pert, A:lem:small, A:rem:cwp-class, A:rem:generalrank, A:sec2:prp, A:sec3:one-null-set, A:sec4:WP-def, A:sec4:horizon-not-contractive, A:sec:examples, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: LevyStochCalc.Poisson.PoissonRandomMeasure.compensated
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 98b57d8ea9507e8faf4b33861dc8f3a1 (pl-fp-v1:c09772a16baf1ae70c55e2fb927e8e567cbe5dc278b0b269b673a0e207a91a6f)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:16:41Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T15:06:21Z):
Reading (locked before any Lean is shown) — def LevyStochCalc.Poisson.PoissonRandomMeasure.compensated

Paper notion (§2): Ñ(dt, de) := N(dt, de) − dt ν(de), the compensated measure. As a set
function it is defined on sets B of finite intensity (dt⊗ν)(B) < ∞:
Ñ(ω)(B) = N(ω)(B) − (dt⊗ν)(B) ∈ ℝ (N(B) < ∞ a.s. on such sets). It is not a (signed) measure
on all of ℝ_+ × E when ν is infinite.

Faithful Lean definition: for each ω and measurable B, a real number equal to
(N ω B).toReal − (dt⊗ν)(B).toReal; the junk values on sets of infinite intensity (where
toReal gives 0, so the formula gives N(B).toReal − 0 or 0 − 0) and on the null event
{N(B) = ∞} for a finite-intensity B are harmless provided all uses are on finite-intensity
sets (elementary integrands with ν(A) < ∞ and bounded time intervals). The intensity
subtracted must be the PRM's reference intensity dt⊗ν (not something else).
Comparison (verdict recorded 2026-10-17T15:15:53Z):
Comparison — PoissonRandomMeasure.compensated (RandomMeasure.lean:151-157)

Lean: compensated N B ω = (N.N ω B).toReal − (referenceIntensity ν B).toReal.
Against my reading: exactly Ñ(B) = N(B) − (dt⊗ν)(B) on finite-intensity B, with the PRM's own
reference intensity subtracted. Junk values: on infinite-intensity B the formula gives
N(B).toReal − 0 (= 0 a.s., since N(B) = ∞ a.s. there) — never a meaningful Ñ(B), and the
library only uses it on rectangles (a,b] × B_k with ν(B_k) < ∞ (MarkStep.integral); on the
null event {N(B) = ∞} for finite-intensity B, toReal gives 0 — a.e. irrelevant.
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-17T15:16:02Z): The author's review, as shown by rv.py author, consists of the review marker only (no reading text, no item-by-item comparison), so there is no stated position of the author to disagree with on substance.
I agree with the implicit verdict (reviewed as faithful); my comparison finds no representation choice that needs recording.
