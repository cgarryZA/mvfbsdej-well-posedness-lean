### A:sec2:infinite-activity-atoms: Dissertation.PaperSpec.A.sec2_infinite_activity
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash ed839d34f480cba13a9f48f6bc72d40f (pl-fp-v1:2fcdef13ef168d5751a9482b352ed8ec2e89c36142390eef6d6b8cf243c8588e)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T12:21:04Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:20:31Z):
# Reading of §2 ¶1, infinite activity (sec2_infinite_activity)

Passage: "We do not require ν to be finite: the infinite-activity regime, in which N has
infinitely many atoms on every nondegenerate time interval, is admitted throughout".

Claim: for a Poisson random measure N on ℝ₊ × E with intensity dt ⊗ ν, ν σ-finite, if
ν(E) = ∞ then N has infinitely many atoms on every nondegenerate time interval.

A faithful formal statement must contain:
- Setting: a Poisson random measure N with intensity Leb ⊗ ν on a probability space (no
  filtration needed); ν σ-finite (countably generated E standing).
- Hypothesis: ν(E) = ∞.
- Conclusion: almost surely, for every s < t (in ℝ₊), N(ω) has infinitely many atoms in
  (s,t] × E. Strongest reading: one null set for all intervals (follows from rational
  intervals); the weaker "for each interval, a.s." is an acceptable reading of the prose
  but weaker. "Infinitely many atoms" may be represented by N(ω)((s,t] × E) = ∞, which for an
  integer-valued measure finite on sets of finite intensity is equivalent (a countable union
  of finite-intensity pieces with finitely many atoms each), but a representation by infinite
  mass alone should be noted.
- Intervals: nondegenerate means s < t; open/closed endpoints immaterial.
Comparison (verdict recorded 2026-10-17T12:20:55Z):
# Comparison for sec2_infinite_activity

Lean: ∀ Ω, P, E, ν σ-finite, d, D : LevyDriver P d ν, ν univ = ⊤ →
∀ᵐ ω ∂P, ∀ s t, 0 ≤ s → s < t → N ω ((s,t] × E) = ⊤.

- Setting: a Lévy driver (Brownian motion and PRM with intensity Leb|[0,∞) ⊗ ν): the standing
  noise; E not required countably generated (harmless broadening). Match.
- Hypothesis ν(E) = ∞: `ν Set.univ = ⊤`. Match.
- Quantifiers: a.s., simultaneously for all 0 ≤ s < t (one null set) — the strongest reading.
  Match.
- "Infinitely many atoms" is represented by infinite mass N(ω)((s,t] × E) = ∞. For a Poisson
  random measure (integer valued on finite-intensity sets, a.s. simple because the time
  intensity is diffuse), infinite mass on (s,t] × E is the same as infinitely many atoms there;
  the LevyStochCalc PRM structure does not carry atomicity as a field, so the formal content is
  the infinite-mass form. Representation choice, harmless (and it is the property the paper
  uses: infinite total jump intensity on every interval).
- Non-vacuity: witness sec2_infinite_activity_hypotheses: Lebesgue measure on ℝ is σ-finite of
  infinite mass and a Lévy driver with that intensity exists.

Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — 1. "Infinitely many atoms on (s,t]" is stated as N(ω)((s,t] × E) = ∞ (infinite mass). For a
   Poisson random measure with diffuse time intensity the two agree almost surely (integer-valued
   on finite-intensity pieces, simple atoms), so nothing of the printed meaning is lost; the
   formal statement is the mass form since the PRM structure has no atomicity field.
2. The countable generation of E is not assumed (broader). The noise is the standing Lévy driver
   (W and N); the Brownian part plays no role.
Disagreements with the author's review (shown 2026-10-17T12:20:55Z): The author's review shown for this unit (A.md:885) is empty, so it does not record that
"infinitely many atoms" is formalised as infinite mass, nor the witness. No content to disagree
with; my verdict is faithful with representation choices.
