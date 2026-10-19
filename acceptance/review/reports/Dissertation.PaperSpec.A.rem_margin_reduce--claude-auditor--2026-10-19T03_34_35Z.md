### A:rem:margin: Dissertation.PaperSpec.A.rem_margin_reduce
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba15843e0ffe4756126 (pl-fp-v1:06376446ea6c52f808cb95f81e4a08000ee9375a67c1ee52d32b2eb68afe740f)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:34:35Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:17:16Z):
Reading (spec rem_margin_reduce; Remark 2.11, 02-model-assumptions.tex:298-301). See COMMON.md.
Claim: if the interior pairing has been bounded as in (2.6) with constants β̄1, β̄2, then for
every 0 < c < min{β̄1, β̄2} the same bound is (2.12) with constants β_i := β̄_i − c and margin c.
A faithful statement must contain:
- setting: standing basis, any m, n, d, any G (full rank not needed), any coefficients.
- quantifiers: ∀ β̄1 β̄2 c with 0 < c < min{β̄1,β̄2}.
- hypothesis: (2.6) with β̄1, β̄2 (for a.e. t, all diagonal pairs).
- conclusion: (2.12) with β_i = β̄_i − c and margin c (same quantifier), i.e. the identity
  −β̄1 A − β̄2 B = −(β̄1−c) A − (β̄2−c) B − c(A + B) read inside the bound. Optionally the
  reduced constants are > 0 (they are, by c < min). Since the identity is exact, an iff, or a
  version without the restriction on c, is broader and acceptable.

----
Common setting (paper §1–§2), used by every reading below:
- filtered probability space (Ω,F,(F_t),P), usual conditions; horizon T>0; dims n,m,d ≥ 1;
  d-dim Brownian motion W; independent Poisson random measure N on R_+×E with intensity dt⊗ν,
  ν σ-finite on a countably generated (E,𝓔); filtration = usual augmentation of σ(W,N,F_0).
- H = R^n × R^m × R^{m×d} × L²(ν;R^m) with |θ|² = |x|² + |y|² + |z|_F² + ‖u‖²_{L²(ν)}
  (Euclidean norms on R^j, Frobenius on matrices; NOT sup norms).
- Coefficients b,σ,h,f : [0,T]×H×P_2(H) → R^n, R^{n×d}, L²(ν;R^n), R^m; g : R^n×P_2(R^n) → R^m,
  deterministic. W_2 the quadratic Wasserstein distance.
- Diagonal input at time t: (Θ, Law Θ) with Θ ∈ L²(Ω,F_t;H) (F_t-measurable, square-integrable).
- Interior pairing P(Θ,Θ') := E[⟨δb,GᵀδY⟩ + ⟨δσ,GᵀδZ⟩_F + ⟨−δf,GδX⟩ + ∫_E⟨δh(e),GᵀδU(e)⟩ν(de)].
- (2.6): for a.e. t, all diagonal pairs: P ≤ −β1 E[|GᵀδY|²+|GᵀδZ|²_F+‖GᵀδU‖²] − β2 E|GδX|².
- (2.12) weighted margin c: (2.6) RHS minus c E[|GᵀδY|²+|GᵀδZ|²_F+‖GᵀδU‖²+|GδX|²].
- (2.13) unweighted margin c: (2.6) RHS minus c E[|δY|²+|δZ|²_F+‖δU‖²+|δX|²].
- Solution: Θ=(X,Y,Z,U) ∈ 𝕊 (X,Y càdlàg adapted with E sup|·|²<∞, Z predictable in H²_W,
  U predictable in H²_N) satisfying both identities of (1.1) a.s. for every t, h evaluated at the
  predictable tuple Θ^-_t=(X_{t-},Y_{t-},Z_t,U_t) and μ^-_t = Law(Θ^-_t).
Comparison (verdict recorded 2026-10-19T03:32:32Z):
Comparison: spec rem_margin_reduce (Sec2Remarks.lean:220-232).
- Setting: standing basis, any n, m, d, any G, any coefficients C — as in my reading.
- Hypothesis: ∀ᵐ t ∈ [0,T], Mono27At (2.6/2.7 at time t: for all diagonal pairs, integrable
  pairing and pairing ≤ −β̄1 E[...] − β̄2 E|GδX|²) with the constants named β₁, β₂ (= β̄₁, β̄₂).
- Quantifier: ∀ c, 0 < c, c < min β̄₁ β̄₂ — after the hypothesis, as printed ("for every 0<c<min").
- Conclusion: Margin212 with constants β̄₁ − c, β̄₂ − c and margin c — exactly (2.12) with the
  reduced constants. Matches the identity −β̄A − β̄'B = −(β̄−c)A − (β̄'−c)B − c(A+B).
- Witness rem_affine_hypotheses: Ex 5.1(i) at ν = δ0 satisfies Assumption 2.5 with β = 1 and
  c = 1/2 < min{1,1} — an intended instance.
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-19T03:32:39Z): none
