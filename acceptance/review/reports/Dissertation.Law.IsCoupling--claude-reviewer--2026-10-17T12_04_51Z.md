### A:ass:lip, A:cor:robust, A:eq:coeffint, A:eq:coefmeas, A:eq:hborel, A:eq:termg, A:ex:brownian, A:ex:concrete, A:ex:expfunc, A:lem:cont, A:lem:lawflow, A:lem:pert, A:lem:small, A:prop:strict, A:rem:cwp-class, A:rem:diag-mono, A:rem:generalrank, A:rem:intrinsic, A:remark-2.6, A:sec2:coefmeas, A:sec2:hborel-derivation, A:sec4:horizon-not-contractive, A:sec:examples, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: Dissertation.Law.IsCoupling
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash b0bdef6c32a05af44418b437fabafbee (pl-fp-v1:e6a1e6bb253d9930cfc2b6712183dfa8c3ebfa603de4488656e0c71bb769dd87)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T12:04:51Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:04:30Z):
# Reading: coupling (def:Dissertation.Law.IsCoupling)

Paper's notion. The paper uses "coupling" in the standard optimal-transport sense
(Villani 2009, Def. 6.1, cited in the Wasserstein-bounds remark after Ass. 2.5, and in
Rem. 2.9 "every coupling of two laws in P_2(H) is the joint law of a pair of F_t-measurable
inputs"): a coupling of mu, mu' (probability measures on a space E, here H or R^n or L^2(nu))
is a probability measure pi on E x E whose first marginal is mu and whose second marginal is
mu'. W_2(mu,mu')^2 = inf over couplings pi of the integral of |theta - theta'|^2 d pi.
The paper also uses "the pair (Theta, Theta') realises a coupling" = Law(Theta,Theta') is a
coupling, and "the image of pi under (theta,theta') -> (u,u') is a coupling of the marginals".

A faithful Lean definition: a predicate on (mu, mu', pi) with pi a measure on the product
(Borel product sigma-algebra), saying pi.map Prod.fst = mu and pi.map Prod.snd = mu'
(equivalently, pi(A x E) = mu(A), pi(E x B) = mu'(B) for measurable A, B). If pi ranges over
general measures (not ProbabilityMeasure), the marginal equalities with probability measures
mu, mu' force pi to have total mass 1, so this is harmless. It must not add extra
conditions (e.g. finite second moment of pi), nor drop one of the marginal conditions.
Measurability of Prod.fst/Prod.snd w.r.t. the product sigma-algebra means Measure.map has no
junk-value issue. If the space's sigma-algebra on the product is the product sigma-algebra
(and for separable metric spaces equals the Borel sigma-algebra of the product), fine.
Comparison (verdict recorded 2026-10-17T12:04:45Z):
# Comparison: IsCoupling

Lean: `IsCoupling μ ν γ := γ.fst = μ ∧ γ.snd = ν` for measures on a measurable space E,
γ a measure on E × E with the product σ-algebra; `Measure.fst γ = γ.map Prod.fst`,
`Measure.snd γ = γ.map Prod.snd` (Mathlib).

- Both marginal conditions present: yes (first = μ, second = ν). Matches Villani Def. 6.1.
- γ is a general measure, not a probability measure: when μ (or ν) is a probability measure,
  γ.fst = μ forces γ(univ) = μ(univ) = 1, so γ is a probability measure. For non-probability
  μ, ν the predicate is the usual marginal condition for measures of equal mass; the paper
  only uses it for laws (probability measures). Harmless.
- No extra conditions (no moment condition on γ). Good.
- Measure.map of the measurable projections: no junk-value issue.
- σ-algebra on E × E: the product σ-algebra. For the separable spaces of the paper (H, R^n,
  L^2(nu)) this equals the Borel σ-algebra of the product; in any case a coupling in the
  paper is a measure on the product σ-algebra with the given marginals. Fine.

Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-17T12:04:45Z): none
