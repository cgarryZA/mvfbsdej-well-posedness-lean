### A:cor:robust: Dissertation.PaperSpec.A.cor_robust
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash ed839d34f480cba154326c82c977c8bd (pl-fp-v1:ae7d15e4a2037003dde2e3e79b0fe18efd8ad2b28a6932de8bf3a7780731ce94)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T12:24:23Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:23:18Z):
# Reading of Corollary 3.6, clause "assumptions of the perturbed system" (cor_robust)

Setting: standing basis (filtration (F_t), W, N, ν), T > 0, n = m, d; G ∈ ℝ^{n×n}.

Hypotheses (all must appear):
 (H1) m = n.
 (H2) Baseline C₀ = (b₀, σ₀, h₀, f₀, g) with ξ₀ satisfies Assumptions 2.2–2.5: ξ₀ ∈ L²(F₀),
      origin values in L²(0,T); Assumption 2.3 with some L₀ (interior diagonal Lipschitz and
      terminal (2.6)); G of full rank (2.4); Assumption 2.5 with α, β₁, β₂ (terminal monotonicity,
      interior (2.7), admissible constants) — and moreover the interior inequality with margin
      c_diss > 0 in the unweighted form (2.13).
 (H3) Perturbations p_b, p_σ, p_h, p_f (same signatures as b, σ, h, f; deterministic,
      standing measurability) with origin values in L²(0,T) (the origin part of 2.2) and the
      interior diagonal Lipschitz condition of 2.3 with some constant.
 (H4) c_pert ≥ 0 with (3.4): for a.e. t and all diagonal inputs, E[perturbation pairing]
      ≤ c_pert E[|δX|² + |δY|² + |δZ|²_F + ‖δU‖²].
 (H5) c_pert < c_diss.
Conclusion: the perturbed system C = (b₀+p_b, σ₀+p_σ, h₀+p_h, f₀+p_f, g) with the same ξ₀ satisfies
 Assumptions 2.2–2.5 with the same G, α, β₁, β₂ (2.2: ξ₀ and origin values; 2.3 with some
 Lipschitz constant, e.g. L₀ + L_p; 2.4 for G; 2.5 terminal and interior with admissible
 constants), and the interior inequality with margin c_diss − c_pert in the unweighted form
 (2.13).
Notes: the Lipschitz constant of the perturbed system is existential (sum of constants);
the well-posedness sentence ("By Theorems 3.1, 3.3, 3.5 it is well-posed") and the θ-independent
case (3.5) are other clauses. Expectations in (3.4) and (2.13) are of integrable pairings
(under the Lipschitz hypotheses). The margin in the conclusion must be exactly c_diss − c_pert
(or at least that), and the constants G, α, β₁, β₂ the same.
Comparison (verdict recorded 2026-10-17T12:24:15Z):
# Comparison for cor_robust

Lean hypotheses: standing basis, 0 < n (= m), 0 < d, T > 0; baseline C, ξ₀ with JointBorel,
Assumption22, Assumption23 (L₀), G.rank = min n n, Assumption25 (G, α, β₁, β₂), Margin213 with
c_diss and 0 < c_diss; perturbation p : Coeffs with OriginValues, LipInterior (Lₚ ≥ 0),
PairingBound34 (c_pert ≥ 0); JointBorel (C.perturb p); c_pert < c_diss.
Conclusion: Assumption22 (perturbed, ξ₀) ∧ ∃ L, Assumption23 (perturbed) ∧ G.rank = min n n ∧
Assumption25 (perturbed, same G α β₁ β₂) ∧ Margin213 (perturbed, c_diss − c_pert).

Item by item against my reading:
- (H1) m = n: Coeffs ν n n d, G : Matrix (Fin n) (Fin n). Match.
- (H2) baseline Assumptions 2.2–2.5 with margin c_diss > 0 in the unweighted form (2.13):
  Margin213 = for a.e. t, all diagonal inputs, integrable pairing and pairing ≤ −β₁E[…] −
  β₂E|GδX|² − c E[|δY|² + |δZ|² + ‖δU‖² + |δX|²], with the same β₁, β₂. Match. (2.3) for C:
  standing. Match.
- (H3) perturbations: OriginValues (origin part of 2.2) and LipInterior (interior diagonal
  Lipschitz of 2.3) with Lₚ ≥ 0; p.g unused (Coeffs.perturb keeps C.g). Match. The standing
  measurability of the perturbations is expressed as JointBorel of the perturbed system; given
  JointBorel C this is equivalent to the joint Borel measurability of p (difference / sum of
  Borel maps into separable normed spaces). Representation choice.
- (H4) PairingBound34: (3.4) for a.e. t and all diagonal inputs, pairing of the perturbation
  differences with integrable pairing ≤ c_pert E[|δX|² + |δY|² + |δZ|² + ‖δU‖²], c_pert ≥ 0.
  Match.
- (H5) c_pert < c_diss. Match.
- Conclusion: perturbed system (b₀+p_b, …, g) (Coeffs.perturb) with ξ₀: 2.2; 2.3 with some L
  (existential, as the paper does not name it); 2.4 (G unchanged); 2.5 with the same
  G, α, β₁, β₂; and (2.13) with margin c_diss − c_pert. Match. The well-posedness sentence and
  the θ-independent case are other clauses.
- Non-vacuity: witness cor_robust_hypotheses: Example 5.1(i) with β₁ = β₂ = 2 as baseline
  (c_diss = 1) and a nonzero feedback perturbation with c_pert = 1/2: all hypotheses met.

Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — 1. The perturbations' standing joint Borel measurability is expressed as `JointBorel T
   (C.perturb p)`; with `JointBorel T C` among the hypotheses this is equivalent to joint Borel
   measurability of p_b, p_σ, p_h, p_f (sums and differences of Borel maps into separable normed
   spaces are Borel).
2. The perturbation is packaged as a coefficient record p : Coeffs whose terminal component is
   unused (`Coeffs.perturb` keeps the baseline g), as printed.
3. The expectations in (2.13) and (3.4) are required to exist (integrable pairings), the formal
   reading used throughout; under the Lipschitz hypotheses they do.
Disagreements with the author's review (shown 2026-10-17T12:24:15Z): none on cor_robust (the author's reading of the perturbed system's measurability is the one I
recorded as a representation choice; both note its equivalence with (2.3) for p given (2.3) for
the baseline).
Process note: this joint review also describes cor_robust_lip (a later unit of my chunk:
TupleIndep and LawLip35 imply PairingBound34 with ‖GX G‖·L_p, other hypotheses dropped). I saw
it before locking that unit and disclose it there.
