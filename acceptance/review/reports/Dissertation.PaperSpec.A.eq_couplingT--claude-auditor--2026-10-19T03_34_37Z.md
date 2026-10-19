### A:rem:wasserstein-bounds: Dissertation.PaperSpec.A.eq_couplingT
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba1b0b3c75b14edd5d3 (pl-fp-v1:1a693cb2c3538754b4113a944316473dbc55b8b812343163a2d2c5be76e92385)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:34:37Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:17:18Z):
Reading (spec eq_couplingT; (2.9) in Remark 2.6, 02-model-assumptions.tex:207-209).
Claim: W_2(ρ,ρ')² ≤ E|δX|² with ρ = Law(X_T), ρ' = Law(X'_T), δX = X_T − X'_T, for
X_T, X'_T ∈ L²(Ω,F_T;R^n) on a common probability space (the synchronous coupling bound, the
X-marginal case of (2.8)).
A faithful statement: ∀ X, X' square-integrable R^n-valued random variables (on the standing basis
or on any probability space — broader is fine): W_2(Law X, Law X')² ≤ E|X − X'|², with W_2 the
quadratic Wasserstein distance on P_2(R^n) for the EUCLIDEAN norm and | · | Euclidean (a sup-norm
R^n would be a different statement). Edge: if W_2 is ℝ≥0∞-valued or a toReal of it, the
inequality must still be the real one (finite for L² laws). F_T-measurability is part of the
setting but not essential.

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
Comparison: spec eq_couplingT (Sec2.lean:86-91).
- ∀ probability space, n, X, X' : Ω → EuclideanSpace ℝ (Fin n) in L²:
  w2P(Law X, Law X')² ≤ E‖X − X'‖², with w2P the quadratic Wasserstein distance (inf over
  couplings of ∫‖x−y‖²) for the Euclidean norm, real-valued; for L² laws the squared distance is
  finite (w2sq_ne_top), so the real square root is not the junk value. Matches (2.9); any
  probability space (ambient generality).
- Witness: two L² vectors on a two-point space, not a.s. equal.
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-19T03:32:40Z): none
