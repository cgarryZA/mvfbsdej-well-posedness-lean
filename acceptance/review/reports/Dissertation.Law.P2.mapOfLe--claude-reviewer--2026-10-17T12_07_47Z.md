### A:cor:robust, A:eq:coefmeas, A:eq:hborel, A:ex:brownian, A:ex:concrete, A:lem:cont, A:lem:lawflow, A:lem:pert, A:lem:small, A:rem:cwp-class, A:rem:diag-mono, A:rem:generalrank, A:rem:intrinsic, A:sec2:coefmeas, A:sec2:hborel-derivation, A:sec4:horizon-not-contractive, A:sec:examples, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: Dissertation.Law.P2.mapOfLe
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash eacf22aaa85ca476d2e3ad477d111a93 (pl-fp-v1:a2a3b0660a16c0401c0ec2e4063b63e570652896490c1632946e3722cd2fc646)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T12:07:47Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:07:24Z):
# Reading: (presumably) pushforward of a P_2 law under a norm-dominated map
# (def:Dissertation.Law.P2.mapOfLe)

Paper's notion. The claims that use this unit (Ass. 2.3, 2.5, Cor. 3.6, ...) involve laws
obtained from a tuple law by image under a map: the X-marginal rho = Law(X_T) of the tuple, the
U-marginal mu^U, laws of components of Theta, and the induced terminal law. In each case the
notion is the image measure mu ∘ P^{-1} of a law mu in P_2(E) under a measurable map P : E -> F
whose growth makes the image again a law of finite second moment (e.g. |P x| <= C |x| or
|P x| <= |x|, or a bound of the image's second moment by that of mu).

A faithful Lean definition: the element of `P2 F` whose underlying measure is `μ.law.map P`
for measurable P (genuine pushforward, no junk), with whatever hypothesis guarantees finite
second moment (a "≤" hypothesis, e.g. on norms or on second moments). The measure must not be
altered. If instead the hypothesis is a bound on the second moment of the image (`secondMoment
(μ.law.map P) ≤ ...`), that is a sufficient condition too, harmless.
Comparison (verdict recorded 2026-10-17T12:07:39Z):
# Comparison: P2.mapOfLe

Lean: for `μ : P2 E`, measurable `φ : E → F` and `c : ℝ` with `‖φ x‖ ≤ c ‖x‖`,
`P2.mapOfLe` is the element of `P2 F` with `law := μ.law.map φ`.

- Underlying measure: the genuine pushforward (φ measurable). Matches mu ∘ φ^{-1}.
- Probability: preserved. Second moment: ≤ c^2 · secondMoment μ < ⊤. Correct proof
  obligation, nothing hidden.
- Hypothesis `‖φ x‖ ≤ c‖x‖` is a sufficient condition for the image to lie in P_2; it
  restricts where the operation is defined, not its value. It covers the uses in the
  repository (an isometric/linear embedding `toL2` into an L^2 space in
  WellPosedness/System/HilbertW2Space.lean, coordinate projections in Examples/Brownian.lean),
  all of linear growth. A negative c only makes the hypothesis unsatisfiable unless E is
  trivial; no junk value arises.
- Same as `P2.map` with c = 1 up to the form of the bound.

Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-17T12:07:39Z): No disagreement on meaning. The author's entry shown for this unit (definitions.md:159) is empty: it records no reading of P2.mapOfLe (pushforward along a measurable map of linear growth; the bound is only a sufficient condition for finite second moment).
