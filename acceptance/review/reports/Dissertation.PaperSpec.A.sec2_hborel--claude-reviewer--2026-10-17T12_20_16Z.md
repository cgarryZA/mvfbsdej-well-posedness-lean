### A:sec2:hborel-derivation: Dissertation.PaperSpec.A.sec2_hborel
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash ed839d34f480cba1c7bf6ee7f1e38851 (pl-fp-v1:b1e4d726d3b3b991de9f5512ca4f3545c5196ffe05e90dd05535db981e2b5e9a)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T12:20:16Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:19:57Z):
# Reading of the paragraph after (2.3) (sec2_hborel)

Passage: "Since L²(ν;ℝⁿ) is separable, (2.3) follows from joint pointwise measurability of
(t,θ,e,μ) ↦ h(t,θ,e,μ): the latter makes h weakly measurable by Tonelli, and the Pettis
measurability theorem then upgrades weak to strong measurability."
(2.3): (t,θ,μ) ↦ h(t,θ,·,μ), [0,T] × H × P₂(H) → L²(ν;ℝⁿ), Borel measurable.

A faithful formal statement must contain:
- Setting: ν σ-finite on countably generated (E, 𝓔) (L²(ν) separable); n, m, d; T.
- Hypotheses: a jump coefficient with values in L²(ν;ℝⁿ), h(t,θ,μ), and a pointwise version
  h̃ : [0,T] × H × E × P₂(H) → ℝⁿ that is jointly measurable — for B([0,T] × H × P₂(H)) ⊗ 𝓔
  (Borel σ-algebras of [0,T], H, and (P₂(H), W₂), product with 𝓔) — and represents h:
  for every (t,θ,μ), e ↦ h̃(t,θ,e,μ) is (square integrable and) a representative of the class
  h(t,θ,μ) (ν-a.e. equality).
- Conclusion: (t,θ,μ) ↦ h(t,θ,·,μ) is Borel measurable from [0,T] × H × P₂(H) into L²(ν;ℝⁿ)
  (strong measurability equivalent, L² separable).
- The representation must hold at every (t,θ,μ) (not a.e.), since (2.3) is an everywhere
  statement. The domain σ-algebra should be the Borel σ-algebra with W₂ on P₂(H) (another
  σ-algebra on P₂(H), e.g. the evaluation σ-algebra, would change the claim).
Comparison (verdict recorded 2026-10-17T12:20:11Z):
# Comparison for sec2_hborel

Lean: ∀ E, ν σ-finite, E countably generated, n m d T, C, H : ([0,T] × H × P₂(H)) × E → ℝⁿ,
Measurable for borel([0,T] × H × P2WH) ⊗ 𝓔 → (∀ p, C.h p = H(p, ·) ν-a.e.) →
p ↦ C.h p is measurable from borel([0,T] × H × P2WH) to borel(L²(ν; ℝⁿ)).

- Setting: as in §2 (L²(ν) separable via countable generation and σ-finiteness). Match.
- Joint pointwise measurability: H measurable for the product of the Borel σ-algebra of
  [0,T] × H × P₂(H) (W₂ of the Hilbert norm on P₂(H), P2WH) and 𝓔. Grouping (t,θ,μ) first is a
  harmless reordering of (t,θ,e,μ). Match.
- Representation: at every p, the class C.h p equals H(p,·) ν-a.e. Match (everywhere in p).
  Square integrability of the sections is implied since C.h p ∈ L².
- Conclusion: (2.3) for h: Borel measurability into L²(ν;ℝⁿ), the same form as
  JointBorel.h_meas. Match.
- Non-vacuity: witness sec2_hborel_nonzero_hypotheses: the jump coefficient h = −u of the affine
  example with ν = δ₀ has a continuous (hence measurable) nonzero pointwise representative.

Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-17T12:20:11Z): The author's review shown for this unit (A.md:889) is empty: no correspondence, verdict or
witness is recorded there. No disagreement on content can be stated; my review is faithful.
