### A:ex:dealer, A:rem:regimes, A:abstract, A:sec5:overview: Dissertation.PaperSpec.A.ex_dealer_mono
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba17aa9ad92a733a79a (pl-fp-v1:f4134380585412cc10565fa2896f0c0f7cf415b16ba44f5d256d2a777a7a9500)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:34:36Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:17:17Z):
Reading (spec ex_dealer_mono; Example 5.5 "Monotonicity at arbitrary ε", 05-examples.tex:410-448;
abstract "monotone at every interaction strength").
Setting: as in ex_dealer (general parameters β1, β2 > 0, σ_c, h_c, h_x, ε ≥ 0; n=m=d=1, G = 1).
Content:
(a) crowding monotonicity along diagonal pairs: for (Θ,μ),(Θ',μ') ∈ D_t (μ^U = Law(U),
    μ'^U = Law(U')): E⟨A_{μ^U}(U) − A_{μ'^U}(U'), U − U'⟩_{L²(ν)} ≥ 0;
(b) consequently Assumption 2.5 holds for the dealer system with G = 1 and the constants
    α = 1, β1, β2 of Ex 5.1(i) (independent of ε), for EVERY ε ≥ 0: terminal
    E⟨δg_T, δX_T⟩ ≥ 1·E|δX_T|² for all X_T, X'_T ∈ L²(F_T); interior (2.6) for a.e. t and all
    diagonal pairs; constants α,β1,β2 ≥ 0, α+β1 > 0, β1+β2 > 0 (m = n, so no branch condition).
"Monotone at every interaction strength" is (b) with ε-independent constants (no smallness, no
margin); (a) is its key ingredient. A statement of (b) for all ε ≥ 0 is faithful; a statement of
(a) alone is a faithful reading of "the crowding interaction is monotone" but omits that (2.6)
holds with the Ex 5.1(i) constants; I would call (a)-only acceptable for the clause label but
narrower than the example's monotonicity conclusion. The pairs must be diagonal (μ = Law Θ); the
monotonicity is false/meaningless for free measure arguments.

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
Comparison: spec ex_dealer_mono (Sec5Dealer.lean:104-135).
- Setting/parameters as ex_dealer (ν arbitrary σ-finite, ν = 0 allowed; T > 0, β1, β2 > 0,
  σ_c, h_c, h_x, ε ≥ 0).
- (a) for EVERY t and all diagonal pairs (μ = Law Θ): 0 ≤ E⟨A_{μ^U}(U) − A_{μ'^U}(U'), U − U'⟩.
  The integrand is integrable (A bounded by 1, U − U' ∈ L²), so the Bochner integral is the true
  expectation, not a junk 0. Matches (a).
- the exposure identity ⟨δx h_x, δu⟩ − ⟨h_x, δu⟩δx = 0 and the jump+driver bound
  E[∫⟨δh,δU⟩ν + ⟨−δf,δX⟩] ≤ −β1 E‖δU‖² − β2 E|δX|² along diagonal pairs (printed steps).
- (b) Assumption25 with G = 1, α = 1, β1, β2 (terminal, interior a.e. t with integrability,
  admissible constants) for every ε ≥ 0 — constants independent of ε. Matches (b).
- Diagonal pairs throughout, as required.
- Witness ex_dealer_hypotheses.
Verdict: broader (instantiation ν ≠ 0, as the paper takes in Example 5.5).
Witness: —
Verdict: broader — Broader: ν is any σ-finite measure, ν = 0 included (the paper takes ν ≠ 0 in Example 5.5).
Instantiation: ν ≠ 0; then the statement is the printed crowding monotonicity along diagonal
pairs and Assumption 2.5 with G = 1, α = 1, β₁, β₂ for every ε ≥ 0.
Disagreements with the author's review (shown 2026-10-19T03:32:40Z): none
