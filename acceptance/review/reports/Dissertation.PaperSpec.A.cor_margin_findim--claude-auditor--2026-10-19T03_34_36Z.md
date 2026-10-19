### A:sec3:margin-paragraph: Dissertation.PaperSpec.A.cor_margin_findim
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba153b1b629e759bb45 (pl-fp-v1:53a7e83fe0a0b90a756441a31bb3d618edd1c4a1ddd523d8eb7111c9e23c34f9)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:34:36Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:17:17Z):
Reading (spec cor_margin_findim; ¶ after Corollary 3.6, 03-main-results.tex:286-288).
Claim: if L²(ν) is finite-dimensional (as when ν is carried by finitely many atoms), finitely many
functionals can determine u and the second obstruction (cor_margin_finite) disappears.
A faithful statement must contain, for a standing basis with dim L²(ν;R^m) < ∞:
- (a) there are finitely many continuous (linear) functionals φ_1,…,φ_J on L²(ν;R^m) that
  determine u (u ↦ (φ_j(u))_j injective);
- (b) "the obstruction disappears": there is a jump feedback entering only through finitely many
  such functionals that carries a margin, i.e. a baseline (m = n, G full rank) with
  h0(t,θ,μ) = H(t,x,y,z,φ(u)) satisfying (2.13) with some margin c > 0 (e.g. Example 5.1(i),
  h = h_c − β1 u written through coordinates). Whether the baseline must satisfy all of
  Assumptions 2.2–2.5 is not said; (2.13) with a margin is the content. An existence statement is
  the right shape. Stating only (a) would be narrower (it omits "the obstruction disappears").
- the claim is for every such ν (finite-dimensional L²(ν)), not just one example ν, although
  the existential (b) may use any convenient feedback.

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
Comparison: spec cor_margin_findim (Sec3Margin.lean:124-147).
- Setting: standing basis, m = n ≥ 1, T > 0, L²(ν;ℝⁿ) finite-dimensional; for all β₁, β₂ ≥ 0,
  c > 0, σ_c, h_c.
- Conclusion: ∃ k and a linear ℓ : L²(ν) → ℝ^k, injective (finitely many functionals determine
  u — (a) of my reading; linear maps on a finite-dimensional space are continuous); the Ex 5.1(i)
  system with constants β₁+c, β₂+c has h = h_c − (β₁+c)u depending on u only through ℓu (indeed
  on nothing else), and it satisfies (2.13) at G = I with β₁, β₂ and margin c — a jump feedback
  through finitely many functionals carrying a margin: "the second obstruction disappears", (b).
- Exactly the existential shape of my reading, for every such ν.
- Witness cor_margin_findim_hypotheses: ν = δ0, finite-dimensional L².
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-19T03:32:39Z): none
