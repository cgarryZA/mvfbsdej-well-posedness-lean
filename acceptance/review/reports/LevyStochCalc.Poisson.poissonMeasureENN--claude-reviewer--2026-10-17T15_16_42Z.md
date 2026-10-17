### A:cor:robust, A:eq:compid, A:eq:forced, A:eq:mvfbsdej, A:eq:zeromean, A:ex:brownian, A:ex:concrete, A:intro:mvfbsdej, A:lem:bpbsde, A:lem:cont, A:lem:pert, A:lem:small, A:rem:cwp-class, A:rem:diag-mono, A:rem:generalrank, A:rem:intrinsic, A:sec2:infinite-activity-atoms, A:sec2:prp, A:sec3:HH-banach, A:sec3:one-null-set, A:sec4:WP-def, A:sec4:horizon-not-contractive, A:sec:examples, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: LevyStochCalc.Poisson.poissonMeasureENN
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 599fddfd2c12e9e4b502f9d73d19721c (pl-fp-v1:cffb430a5e473f6e8433a0ce01a00ad4219d613a1005b669ab592ca92277e681)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:16:42Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T15:06:21Z):
Reading (locked before any Lean is shown) — def LevyStochCalc.Poisson.poissonMeasureENN

Paper notion: the law of N(B), the Poisson distribution with mean λ = (dt⊗ν)(B), as a
law on ℕ ∪ {∞} ⊆ ℝ≥0∞ (the values of a measure). Faithful Lean definition: a probability
measure on ℝ≥0∞ which, for λ < ∞, is Σ_k e^{−λ} λ^k / k! δ_(k : ℝ≥0∞) (λ = 0 gives δ_0);
and for λ = ∞ it must be δ_∞ (the only law compatible with σ-finite intensity: a set of
infinite intensity is a countable disjoint union of finite-intensity sets with independent
Poisson counts whose sum diverges a.s.). Any other value at λ = ∞ (zero measure, δ_0, junk)
matters if the PRM axioms require Law(N(B)) = poissonMeasureENN((dt⊗ν)(B)) for ALL
measurable B: then the junk value would either be unsatisfiable (zero measure / δ_0 ⇒
vacuous structure for infinite ν) or wrong. If the PRM axiom is only on finite-intensity
sets, the λ = ∞ value is irrelevant. It must be a probability measure (total mass 1) for
finite λ.
Comparison (verdict recorded 2026-10-17T15:15:53Z):
Comparison — poissonMeasureENN (RandomMeasure.lean:59-63)

Lean: poissonMeasureENN μ = (ProbabilityTheory.poissonMeasure μ).map (ℕ → ℝ≥0∞ cast), μ : ℝ≥0;
Mathlib's poissonMeasure r = Measure.sum (n ↦ ofReal(e^{−r} r^n / n!) • δ_n).
Against my reading: for finite mean λ it is Σ_k e^{−λ} λ^k/k! δ_k on ℝ≥0∞ (λ = 0 gives δ_0,
since 0^0 = 1); a probability measure; the cast is measurable (ℕ has ⊤). The λ = ∞ case is not
in the domain (μ : ℝ≥0): PoissonRandomMeasure.poisson_law only applies it to sets of finite
intensity (via toNNReal), and infinite-intensity sets are handled by the separate field
N(B) = ∞ a.s. — so no junk value at λ = ∞ is ever imposed (the vacuity risk I flagged does not
arise).
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-17T15:16:03Z): The author's review, as shown by rv.py author, consists of the review marker only (no reading text, no item-by-item comparison), so there is no stated position of the author to disagree with on substance.
I agree with the implicit verdict (reviewed as faithful); my comparison finds no representation choice that needs recording.
