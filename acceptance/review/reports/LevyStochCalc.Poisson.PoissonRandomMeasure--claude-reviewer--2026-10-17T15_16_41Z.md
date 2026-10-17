### A:cor:robust, A:eq:compid, A:eq:forced, A:eq:mvfbsdej, A:eq:zeromean, A:ex:brownian, A:ex:concrete, A:intro:mvfbsdej, A:lem:bpbsde, A:lem:cont, A:lem:pert, A:lem:small, A:rem:cwp-class, A:rem:diag-mono, A:rem:generalrank, A:rem:intrinsic, A:sec2:infinite-activity-atoms, A:sec2:prp, A:sec3:HH-banach, A:sec3:one-null-set, A:sec4:WP-def, A:sec4:horizon-not-contractive, A:sec:examples, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: LevyStochCalc.Poisson.PoissonRandomMeasure
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 351b24f2cb8b3f890000000000000000 (pl-fp-v1:0fb613dcd4f42e6dccefe749bfbc81f2574c58d46c6abef9b66cb7ea4da3a8d4)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:16:41Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T15:06:21Z):
Reading (locked before any Lean is shown) — def LevyStochCalc.Poisson.PoissonRandomMeasure

Paper notion (§2): "a Poisson random measure N on ℝ_+ × E with intensity dt ν(de), where ν
is a σ-finite measure on a countably generated (E, E)". Standard definition: a map
ω ↦ N(ω) into the measures on ℝ_+ × E (with values in ℕ ∪ {∞}, a counting measure a.s.),
measurable in the sense that ω ↦ N(ω)(B) is a random variable for each measurable B, such
that (a) for each measurable B with (dt⊗ν)(B) < ∞, N(B) ~ Poisson((dt⊗ν)(B)) (and N(B) = ∞
a.s. if (dt⊗ν)(B) = ∞, by convention / consequence of σ-finiteness and independence);
(b) for pairwise disjoint B_1,…,B_k, the variables N(B_1),…,N(B_k) are independent.
Independence from W (and F_0) is a separate hypothesis in the paper.

Faithful Lean definition: a structure with such a random measure field N, its measurability,
the Poisson law with mean the reference intensity dt⊗ν on each measurable set (with the ∞
convention, or only for finite-intensity sets), and mutual independence on disjoint finite
families. Time domain: ℝ_+ (ℝ restricted to [0,∞), ℝ≥0, or all of ℝ with Lebesgue — the
last is a broader object that restricts to the paper's). Problems: a law requirement that
is impossible at infinite-intensity sets (vacuity, since ν may be infinite), missing
independence, intensity not dt⊗ν, measure values not integer (if law forces Poisson on
every finite-intensity set, integer-valuedness a.s. follows on those sets; that suffices).
Satisfiability: a witness PRM must exist for σ-finite ν (with infinite ν(E)).
Comparison (verdict recorded 2026-10-17T15:15:53Z):
Comparison — PoissonRandomMeasure (LevyStochCalc/Poisson/RandomMeasure.lean:71-149)

Lean: a structure over (Ω, P) probability and σ-finite ν, with
N : Ω → Measure (ℝ × E) (a measure for every ω);
measurable_eval: ω ↦ N ω B measurable for measurable B;
integer_valued: for finite-intensity B, a.s. N ω B ∈ ℕ;
infinite_at_infinite_intensity: for infinite-intensity B, a.s. N ω B = ∞;
poisson_law: for finite-intensity B, Law(N(·,B)) = poissonMeasureENN((dt⊗ν)(B));
independent_disjoint: for every countable pairwise-disjoint measurable family, the counts are
iIndepFun;
joint_past_future_independent: σ(N(B) : B ⊆ (−∞,s]×E) ⊥ σ(N((s,t]×A)) for 0 ≤ s < t,
ν(A) < ∞.
Intensity = referenceIntensity ν = Lebesgue on [0,∞) ⊗ ν.

Against my reading:
- Random measure, measurable evaluations: matches.
- Poisson law with mean dt⊗ν(B) on finite-intensity sets: matches; the infinite-intensity
  case is the separate field N(B) = ∞ a.s. — the correct convention (not a junk law), so no
  vacuity from infinite ν (poissonMeasureENN is only applied to finite means).
- Independence on disjoint sets: countable families (stronger in form than finite families but
  equivalent, iIndepFun being defined through finite subfamilies).
- joint_past_future_independent: a consequence of the standard axioms (refine finitely many past
  sets into disjoint atoms; additivity of N(ω) expresses past counts through the atoms;
  independence on disjoint families) — adds no restriction.
- infinite_at_infinite_intensity: also a consequence for σ-finite intensity (countable disjoint
  finite-intensity pieces, independent Poisson counts with divergent mean sum ⇒ sum = ∞ a.s.).
- Integer-valuedness: only per set a.s., no atomicity field. The standard definition asks
  N(ω) to be a counting measure. Every standard PRM is a Lean PRM; a Lean PRM has, on each
  set, the same law and joint laws as a standard one, and (docstring) the library proves a.s.
  integer-valuedness / atomicity on finite-intensity windows for countably generated E (the
  paper's E is countably generated). All paper uses are a.e. statements, so this is harmless.
- Time domain ℝ × E with intensity Lebesgue restricted to [0,∞): counts on negative-time sets
  are Poisson(0) = 0 a.s.; the restriction to [0,∞) × E is the paper's PRM.
- Satisfiable: PoissonRandomMeasure.exists_of_sigmaFinite (every σ-finite ν, infinite ν(E)
  included) and LevyDriver.exists.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices of PoissonRandomMeasure, and why each is harmless:
1. Time axis ℝ with intensity Lebesgue on [0,∞) ⊗ ν: the counts at negative times vanish a.s.,
   and the restriction to [0,∞) × E is the paper's PRM.
2. "Integer-valued atomic measure" recorded only as a.s. integrality on each finite-intensity
   set (no atomicity field): laws and joint laws of counts are those of a standard PRM, every
   standard PRM satisfies the structure, and all uses are almost sure.
3. Extra fields (N(B) = ∞ a.s. on infinite-intensity sets; past/future independence;
   countable instead of finite disjoint families): each follows from the standard definition for
   σ-finite ν, so they do not narrow the notion. Existence for every σ-finite ν is a theorem
   (exists_of_sigmaFinite).
Disagreements with the author's review (shown 2026-10-17T15:16:02Z): The author's review, as shown by rv.py author, consists of the review marker only (no reading text, no item-by-item comparison), so there is no stated position of the author to disagree with on substance.
Not recorded there: integer-valuedness is only per set almost surely, with no atomicity field;
two fields (N(B) = ∞ a.s. on infinite-intensity sets, past/future independence) are derived
properties of the standard definition added as axioms of the structure; time is ℝ with intensity
restricted to [0,∞). All harmless (existence theorem exists_of_sigmaFinite; standard PRMs satisfy
the structure), but these are the points an independent reader must check.
