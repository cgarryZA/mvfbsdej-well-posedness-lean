### A:ex:dealer: Dissertation.PaperSpec.A.ex_dealer_inert
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba141c76d0c8dddc879 (pl-fp-v1:838045c7d87fddde3031c3696d762220ebb32694d1742f0fdb184c0426935597)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:34:36Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:17:17Z):
Reading (spec ex_dealer_inert; Example 5.5, 05-examples.tex:474-482).
Setting: dealer system with h_x = 0, general parameters β1, β2 > 0, σ_c ∈ R, h_c ∈ L²(ν),
ξ0 ∈ L²(F_0), n = m = d = 1, G = 1, standing basis, T > 0. p : [0,T] → (0,∞) the positive
solution of p' = β1 p² − β2, p(T) = 1 (exists on [0,T]).
Conclusion: the tuple
Y_t = p(t)X_t, Z_t = p(t)σ_c/(1+β1p(t)), U_t = p(t)h_c/(1+β1p(t)),
with X the state (solution of the closed-loop forward equation
dX = −β1pX dt + σ_c/(1+β1p) dW + ∫ h_c/(1+β1p) dÑ, X_0 = ξ0), solves the dealer system (it is in
𝕊 and satisfies both identities); Law(U_t) is a Dirac mass (U_t deterministic) for every t;
A_{Law(U_t)}(U_t) = ∇V(0) = 0; and the same tuple solves the system for every ε ≥ 0.
Faithful forms: either ∃ X such that (X, pX, Z, U) solves the system at every ε, or for the X
solving the closed-loop equation; p may be quantified as any positive solution of the Riccati
problem (hypothesis) provided such a p exists (witness). Must not assume the tuple solves.

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
Comparison: spec ex_dealer_inert (Sec5DealerActive.lean:78-116).
- Setting: standing basis with d = 1, ν arbitrary σ-finite (ν = 0 allowed), T > 0, β1, β2 > 0,
  σ_c ∈ ℝ, h_c ∈ L²(ν), h_x = 0, ε ≥ 0, ξ₀ ∈ L²(ℱ_0); p with p' = β1p² − β2 on [0,T], p(T) = 1,
  p > 0 on [0,T] taken as a hypothesis (existence and uniqueness of such p is ex_dealer_riccati;
  the witness exhibits it).
- Conclusions: the h_x = 0 system at ε has a solution; every solution has Y_t = p(t)X_t a.s. at
  each t ∈ [0,T], Z = pσ_c/(1+β1p) (zero energy of the difference), U_s = p(s)h_c/(1+β1p(s)) for
  a.e. s a.s.; for a.e. s the law of U_s (U-marginal of Law Θ⁻_s) is the Dirac mass at
  p h_c/(1+β1p) and A_{Law(U_s)}(U_s) = 0 a.s.; and the solution solves the system at every
  ε' ≥ 0. Together: the explicit tuple (with X the state) solves, Law(U_t) is Dirac, the
  correction vanishes, the same tuple solves at every ε — the printed content. "a.e. t" for the law
  statements is the natural reading for a predictable class U.
- Nothing about the tuple is assumed (existence is concluded).
- Witness ex_dealer_inert_hypotheses: dealer marks with ν(E) = ∞, ξ₀ = 0, and a Riccati p.
Verdict: broader (instantiation ν ≠ 0, as the paper takes in Example 5.5).
Witness: —
Verdict: broader — Broader: ν is any σ-finite measure, ν = 0 included (the paper takes ν ≠ 0 in Example 5.5); the
Riccati p is a hypothesis (any p with p' = β₁p² − β₂, p(T) = 1, p > 0), which exists and is
unique (ex_dealer_riccati). Instantiation: ν ≠ 0 and p the positive Riccati solution.
Disagreements with the author's review (shown 2026-10-19T03:32:40Z): none
