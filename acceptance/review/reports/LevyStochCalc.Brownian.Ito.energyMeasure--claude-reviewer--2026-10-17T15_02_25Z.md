### A:lem:lawflow, A:sec3:HH-banach: LevyStochCalc.Brownian.Ito.energyMeasure
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 8bb90a671c0f63eba6329d346b422bc3 (pl-fp-v1:44daab3706e079af5d0ff371170231e0f8f609a1bf7142b8c20cd86b9e8482fd)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:02:25Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:34:24Z):
Reading for def:LevyStochCalc.Brownian.Ito.energyMeasure (written before seeing any Lean).

Paper notion. The product measure dt (x) dP on [0,T] x Omega (or Omega x [0,T]), with Lebesgue
measure restricted to the horizon [0,T]: Section 3 identifies Z-components "when they agree
dt (x) dP-a.e.", the U-components dt (x) dP (x) nu-a.e.; Lemma A.1 works in
L^2([0,T] x Omega; H). The "energy" of a process is its squared L^2 norm for this measure.

A faithful Lean definition must be the product of Lebesgue measure restricted to [0,T] (the
horizon, closed or half-open interval: endpoints are null) and the reference probability P,
in either order of factors. Not Lebesgue on all of R_+ (infinite mass would change "energy finite"
for processes not cut off at T), and not a normalised time measure (dt / T would rescale the
energy). The sigma-algebra on which it is used (product, progressive or predictable) is a matter
for the spaces built on it.
Comparison (verdict recorded 2026-10-17T15:01:16Z):
Comparison for Ito.energyMeasure.
Lean: energyMeasure P T = P.prod (volume.restrict (Icc 0 T)) on Ω × ℝ.
- The product of P and Lebesgue measure restricted to the horizon [0,T]. Factors are in the order
  Ω × time. Lebesgue is not on all of ℝ_+ and not normalised. Matches my reading.
- Measure.prod with a σ-finite second factor (restricted Lebesgue) is the usual product measure.
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-17T15:01:53Z): None. The author's description, P ⊗ (Lebesgue on [0,T]) on Ω × ℝ (the measure dP ⊗ dt of the L²
classes of the integrands), agrees with my comparison.
