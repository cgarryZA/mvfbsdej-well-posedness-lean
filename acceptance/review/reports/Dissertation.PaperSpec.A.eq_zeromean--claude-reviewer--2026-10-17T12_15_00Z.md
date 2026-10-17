### A:eq:zeromean: Dissertation.PaperSpec.A.eq_zeromean
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash ed839d34f480cba1ca027a9d4d1614c9 (pl-fp-v1:e314aa964749e23c86495ea27e32e48d154c51e2f09e3d1fc5ced7502708b61a)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T12:15:00Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:14:33Z):
# Reading of (2.2), the zero-mean property (eq_zeromean)

Passage: "the zero-mean property of the compensated integral reads
E ∫_0^T ∫_E ψ_s(e) Ñ(ds,de) = 0 whenever E ∫_0^T ∫_E |ψ_s(e)| ν(de) ds < ∞."
Context: right after (2.1) "for predictable ψ ≥ 0"; here ψ is a real (or vector) predictable
integrand, not necessarily nonnegative (|ψ| appears). Setting as in (2.1): standing filtration
(usual augmentation of F^W ∨ F^N ∨ independent F₀), N Poisson random measure with intensity
dt ⊗ ν, Ñ = N − dt ν, T > 0, ν σ-finite.

A faithful formal statement must contain:
- Hypotheses: ψ : Ω × [0,T] × E → ℝ (or ℝʲ) 𝒫⊗𝓔-measurable (predictable), with
  E ∫_0^T ∫_E |ψ| ν(de) ds < ∞ (an L¹ condition only — no square integrability).
- The integral against Ñ under only L¹ integrability is the pathwise one:
  ∫∫ ψ dÑ := ∫_{(0,T]×E} ψ dN(ω) − ∫_0^T ∫_E ψ ν(de) ds, a.s. well defined (both terms
  absolutely convergent a.s. by (2.1) applied to |ψ|) and integrable.
- Conclusion: E[∫∫ ψ dÑ] = 0.
- A version requiring E∫∫|ψ|² ν ds < ∞ and using the L² (Itô) compensated integral would be
  narrower (adds a hypothesis, loses the L¹-only case). A version over an arbitrary filtration
  would be false; over any filtration for which N is Poisson, broader and fine.
Comparison (verdict recorded 2026-10-17T12:14:54Z):
# Comparison for eq_zeromean

Lean: same setting as eq_compid (LevyDriver D, 𝒢₀ ⊥ driver, filtration enlJoint), ∀ T,
ψ : Ω × ℝ × E → ℝ measurable for markedPredictableSigma (enlJoint 𝒢₀ D h𝒢₀) ν,
∫⁻ω ∫⁻_{(0,T]} ∫⁻_E ‖ψ‖ₑ dν ds dP < ⊤ →
∫ ω, (∫_{(0,T]×E} ψ(ω,·) d(N ω) − ∫_{(0,T]} ∫_E ψ(ω,s,e) dν ds) dP = 0.

- Setting: the standing filtration and driver, as in (2.1). Match (E not required countably
  generated: harmless broadening).
- ψ predictable real-valued: marked predictable σ-algebra, same representation as in (2.1):
  𝒫 ⊗ 𝓔 on times > 0, times ≤ 0 unsplit; harmless since all integrals run over (0,T] (use
  ψ·1_{s>0} for a paper-predictable ψ).
- Hypothesis: E ∫_0^T ∫_E |ψ| ν(de) ds < ∞ as a lintegral of the extended norm. Match; L¹ only,
  no square integrability. Match.
- Compensated integral: pathwise ∫ψ dN(ω) − ∫∫ψ ν ds, as in my reading. Match.
- Junk values: Bochner integrals return 0 for non-integrable functions. Under the hypothesis,
  (2.1) applied to |ψ| gives E∫|ψ| dN < ∞, so for a.e. ω both inner integrals are absolutely
  convergent, and the outer integrand is integrable (bounded by ∫|ψ|dN + ∫∫|ψ|ν ds). Hence the
  junk branch is not reached on a non-null set, and the conclusion is the true expectation = 0,
  not a vacuous 0 = 0.
- Non-vacuity: witness sec2_compensation_nonzero_hypotheses (ν = δ₀, ψ = 1_{(0,1]}, predictable,
  with E∫∫|ψ| ν ds = 1 < ∞).

Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — 1. Predictability is measurability for `markedPredictableSigma` (𝒫 ⊗ 𝓔 on times > 0 since ν is
   σ-finite; times ≤ 0 unsplit, so ψ is constant there). Harmless: all integrals run over (0,T];
   for a paper-predictable ψ apply the statement to ψ·1_{s>0}.
2. The compensated integral is read pathwise, ∫_{(0,T]×E} ψ dN − ∫_0^T∫_E ψ dν ds, which is the
   meaning of Ñ-integration under the printed L¹ condition.
3. The expectations are Bochner integrals; under the L¹ hypothesis the integrands are integrable
   (by (2.1) for |ψ|), so the junk value 0 is never what makes the identity hold.
4. Broadenings: E need not be countably generated; any T and d.
Disagreements with the author's review (shown 2026-10-17T12:14:54Z): The author's review shown by `rv.py author` is empty (marker at A.md:887, adjacent to the
eq_compid marker at A.md:886, with no review text displayed for either), so it records no
correspondence, no discussion of the Bochner junk value 0 (which matters for this statement:
the identity must not hold merely because the outer integrand fails to be integrable) and no
witness. My review: faithful with representation choices; the integrands are integrable under
the L¹ hypothesis, so the junk branch is not what makes the identity hold.
