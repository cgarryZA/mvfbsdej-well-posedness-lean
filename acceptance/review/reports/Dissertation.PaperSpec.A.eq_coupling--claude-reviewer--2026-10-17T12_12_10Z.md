### A:remark-2.6: Dissertation.PaperSpec.A.eq_coupling
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash ed839d34f480cba17af7c36ae6c33114 (pl-fp-v1:c06c57a8182b802f4febab5ebac000d011c3ca6dba4ea3d8ef4bffca45217da2)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T12:12:10Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:11:42Z):
# Reading of (2.8), the coupling bound (eq_coupling)

Passage (Remark 2.6): for two diagonal inputs (Θ, μ), (Θ', μ') at the same time t on the same
probability space (Difference notation, §2), "the pair (Θ, Θ') realises a coupling of (μ, μ')
... W₂(μ, μ')² ≤ E[|δX|² + |δY|² + |δZ|_F² + ‖δU‖²_{L²(ν)}]".

A faithful formal statement must contain:
- Setting: ν σ-finite on countably generated E (so H separable), n, m, d; H = ℝⁿ × ℝᵐ ×
  ℝ^{m×d} × L²(ν;ℝᵐ) with the Hilbert norm |θ|²_H = |x|² + |y|² + |z|²_F + ‖u‖²; a probability
  space (with filtration, time t: the F_t-measurability of the inputs is irrelevant and may be
  dropped, giving a broader statement).
- Hypotheses: Θ, Θ' : Ω → H measurable (strongly measurable / F_t-measurable) and square
  integrable; μ = Law(Θ), μ' = Law(Θ') ∈ P₂(H).
- Conclusion: W₂(μ, μ')² ≤ E[|δX|² + |δY|² + |δZ|²_F + ‖δU‖²], with W₂ the quadratic
  Wasserstein distance of the Hilbert norm |·|_H (infimum over couplings of ∫|θ−θ'|²_H dπ).
  The right side is E|Θ − Θ'|²_H. If H is represented with a different (e.g. max) norm, the
  W₂ must still be the Hilbert-norm one and the right side the sum of the four squared
  channel norms.
Comparison (verdict recorded 2026-10-17T12:12:05Z):
# Comparison for eq_coupling

Lean: ∀ Ω, P probability, E, ν σ-finite, E countably generated, n m d,
Θ Θ' : Ω → TupleH ν n m d, MemLp Θ 2 P → MemLp Θ' 2 P →
w2H (lawP2 P Θ) (lawP2 P Θ')² ≤ ∫ (‖δX‖² + ‖δY‖² + ‖δZ‖² + ‖δU‖²) dP.

Item by item:
- Setting: ν σ-finite, E countably generated (standing). n, m, d arbitrary (paper n,m,d ≥ 1;
  the d = 0 etc. cases are harmless broadenings).
- Inputs: any two square-integrable random tuples on one probability space. The paper's inputs
  are diagonal inputs at a time t (F_t-measurable); dropping F_t-measurability is a harmless
  broadening (the bound does not involve the filtration). MemLp for the max-of-channels norm of
  `TupleH` is equivalent to square integrability for the Hilbert norm (norms within factor 2)
  and includes a.e. strong measurability.
- Laws: `lawP2 P Θ` = P.map Θ as a P₂ law (MemLp holds, so the junk branch is not used).
- W₂: `w2H` = w2 of the images under `toL2` into `TupleL2` (iterated L² product), i.e. the
  quadratic Wasserstein distance of the Hilbert norm |θ|²_H = |x|²+|y|²+|z|²_F+‖u‖²; w2 is the
  square root of the infimum over couplings (measures on the product with the two marginals) of
  ∫‖p₁−p₂‖². Matches Villani Def 6.1.
- Right side: explicit sum of the four squared channel norms of the differences, Bochner
  integral (integrable since Θ, Θ' ∈ L²). ‖δZ‖ is the Euclidean norm on Fin m × Fin d =
  Frobenius; ‖δU‖ the L²(ν) norm. Match.
- Non-vacuity: no witness is listed, but the hypotheses are met by any square-integrable pair
  (e.g. Θ = Θ' = 0, or any diagonal input); the proposition is a plain inequality with only
  satisfiable integrability premises.

Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — 1. The inputs are any two square-integrable random tuples on one probability space; the paper's
   diagonal inputs additionally are F_t-measurable, which the bound does not use (a harmless
   broadening; the printed claim is the instance of F_t-measurable inputs).
2. `TupleH` carries the max of the channel norms; W₂ is nevertheless that of the Hilbert norm,
   `w2H` (images under `toL2`), and the right side is written as the sum of the four squared
   channel norms, so the printed quantities are used exactly. MemLp for the max norm is
   equivalent to Hilbert-norm square integrability.
3. No witness is recorded; none is needed beyond the obvious one (any square-integrable pair),
   since the only premises are integrability.
Disagreements with the author's review (shown 2026-10-17T12:12:05Z): none
