### A:rem:wasserstein-bounds: Dissertation.PaperSpec.A.eq_margproj
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba1c19abbad6d02050c (pl-fp-v1:add2ab479c715c283f0abfd1c91ccd82e4d32f1549b9881808c8e64365d6745b)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:34:37Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:17:18Z):
Reading (spec eq_margproj; (2.11) in Remark 2.6, 02-model-assumptions.tex:222-231).
Claim: marginal projection P_2(H) → P_2(L²(ν)), μ ↦ μ^U = (θ ↦ u)_#μ, is 1-Lipschitz for W_2:
W_2(μ^U, μ'^U)² ≤ W_2(μ,μ')² (the display's chain ≤ ∫‖u−u'‖²dπ ≤ ∫|θ−θ'|²dπ ≤ W_2² for an
optimal π is the proof).
A faithful statement: ∀ μ, μ' ∈ P_2(H) (arbitrary, not only laws of diagonal inputs):
W_2(μ^U,μ'^U)² ≤ W_2(μ,μ')² (or the unsquared version), with H the Hilbert product (u-norm the
L²(ν;R^m) norm, |θ|² the sum of squares) and W_2 the quadratic Wasserstein distance on each space.
Restricting to laws of random tuples on the standing basis would be narrower unless every
μ ∈ P_2(H) arises (it does for F_t, t > 0, by Remark 2.8).

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
Comparison (verdict recorded 2026-10-19T03:32:33Z):
Comparison: spec eq_margproj (Sec2.lean:45-51).
- ∀ ν σ-finite on a countably generated E, ∀ n, m, d, ∀ μ, μ' ∈ P₂(H):
  w2P μ^U μ'^U ≤ w2H μ μ', μ^U = pushforward under θ ↦ u, w2P on P₂(L²(ν;ℝ^m)) for the L² norm,
  w2H = W₂ of the pushforwards to the nested WithLp-2 product, i.e. the Hilbert norm
  (|x|²+|y|²+|z|²_F+‖u‖²)^{1/2} of H. Unsquared form of (2.11), for arbitrary laws. Matches.
- Witness: two Dirac laws with distinct U-marginals.
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-19T03:32:41Z): none
