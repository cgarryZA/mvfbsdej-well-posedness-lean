### A:ex:dealer, A:rem:regimes, A:abstract, A:sec5:overview: Dissertation.PaperSpec.A.ex_dealer_active
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba11684a792fea39139 (pl-fp-v1:5005e72fb9e6a5cdddb7ef7bdf2abe22c38698cc04223e4ecfa23e7ce9554593)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:34:35Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:17:16Z):
Reading (spec ex_dealer_active; Example 5.5 "The interaction is active", 05-examples.tex:482-524).
See COMMON.md. Setting: the explicit specialisation n = m = d = 1, G = 1, β1 = 1, β2 = 1/2,
σ_c = 1, ξ0 = 0, E = {−1,+1} × (0,1], ν(dς,dq) = c_ς q^{−1−ϱ} dq with 0 < ϱ < 2 and
c_{±1} = (2−ϱ)/2, h_c(ς,q) = ςq, h_x(ς,q) = q (so ‖h_c‖ = ‖h_x‖ = 1, ⟨h_c,h_x⟩ = 0, ν(E) = ∞).
Dealer coefficients: b = −β1 y, σ = σ_c − β1 z, h = h_c + h_x x − β1 u − ε A_{μ^U}(u),
f = β2 x + ⟨h_x,u⟩, g(x,ρ) = x; A_λ(u) = ∫ ∇V(u−v) λ(dv), ∇V(w) = w/√(1+‖w‖²); μ^U the U-marginal
of the measure argument (for h, of μ^-_t, i.e. Law(U_t)).
Conclusion must contain both:
(a) with Θ⁰ = (X⁰, X⁰, 1/2, U⁰), U⁰_t = ½(h_c + h_x X⁰_{t−}), X⁰ the solution of the linear SDE,
    for every t ∈ (0,T]: P( A_{Law(U⁰_t)}(U⁰_t) ≠ 0 ) > 0.
(b) for every ε > 0 and the solution Θ^ε ∈ 𝕊 of the dealer system at strength ε (given by
    Theorem 3.5; unique): E ∫_0^T ‖ε A_{Law(U^ε_t)}(U^ε_t)‖²_{L²(ν)} dt > 0.
    Faithful forms: "for every solution Θ^ε in 𝕊 …" (with existence elsewhere/also), or
    "∃ a solution and every solution satisfies …". A form that only says "there exists a solution
    with the property" is weaker (fine only if uniqueness is also in the statement or proved for
    this system). A form where the property is assumed rather than concluded is wrong.
- The law in A must be the law of the solution's own U-component at time t (the diagonal law),
  not a free measure; ‖·‖ the L²(ν) norm; integral over [0,T].
- Hypotheses on the standing basis only (W, N as above, T > 0); no extra hypothesis such as an
  assumed solution property. The PRM must have exactly this ν on this E.

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
Comparison: spec ex_dealer_active (Sec5DealerActive.lean:185-216).
- Setting: Ω, 𝒢₀ independent of the driver, LevyDriver P 1 (ex55Marks ϱ) (d = 1), 0 < ϱ < 2,
  T > 0. ex55Marks ϱ = dealerMarks (c ≡ (2−ϱ)/2) ϱ = (count ⊗ Leb(0,1]).withDensity
  (c_ς q^{−1−ϱ}) on E = Bool × (0,1] (Bool true = side +1) — the paper's ν with c_{±1} = (2−ϱ)/2.
- h_c, h_x: Lp classes with representatives ς q and q a.e. — as printed.
- Coefficients ex55Coeffs ν 1 (1/2) (σ_c = single (0,0) 1 = 1) hc hx ε: b = −y, σ = σ_c − z,
  h = h_c + x h_x − u − ε A_{μ^U}(u), f = x/2 + ⟨h_x,u⟩, g = x; ex55Crowd Λ u = ∫ ∇V(u−v) Λ(dv)
  with ∇V(w) = w/√(1+‖w‖²); μ^U = margU (pushforward under θ ↦ u). β1 = 1, β2 = 1/2, σ_c = 1,
  ξ0 = 0 (Solution with ξ₀ = 0). Matches the specialisation.
- (a): ∀ X0 solving ex55Linear (the printed linear SDE from 0, adapted, right-continuous) with left
  limits on every path on (0,T], ∀ t ∈ (0,T], with U0 = ½(h_c + X0_{t−} h_x):
  0 < P{ω : A_{P∘U0⁻¹}(U0 ω) ≠ 0}. Law = P.map U0 = Law(U⁰_t). Matches (a); quantifying over
  every solution is at least as strong as the paper's "the" solution (existence is in
  ex_dealer_zero).
- (b): ∀ ε > 0, ∀ Solution (X,Y,Z,U) of the ε-system from 0:
  0 < ∫⁻ω ∫⁻_{[0,T]} ‖ε A_{Law(U_s)}(U_s)‖² ds, where the law is the U-marginal of
  lawP2 P Θ⁻_s (Θ⁻_s = (X_{s−},Y_{s−},Z_s,U_s)), whose U-channel is U_s itself, so it is
  Law(U_s). Matches (b) in the "for every solution" form; existence of a solution for every
  ε ≥ 0 is ex_dealer_wp, so (b) is not vacuous.
- Nothing about the solution is assumed beyond being a solution.
- Witness ex_dealer_spec_hypotheses: ϱ = 1, the classes h_c, h_x exist, a driver exists.
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-19T03:32:39Z): Classification only, no disagreement about meaning. The author lists "for every solution at ε" in
the second clause as a broadening; I record the unit as faithful, since with existence
(ex_dealer_wp) and uniqueness in ℍ (Theorem 3.3) "for every solution" is the printed "the solution
given by Theorem 3.5". Otherwise none.
