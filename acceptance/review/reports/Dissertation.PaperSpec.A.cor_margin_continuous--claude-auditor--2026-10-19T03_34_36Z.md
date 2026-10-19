### A:sec3:margin-paragraph: Dissertation.PaperSpec.A.cor_margin_continuous
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba1bd840ffee2f6a13b (pl-fp-v1:9358cce2e07cb46aa3e2ee596ce0932e3293dada6bff269a06c2a31e33b8d4d3)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:34:36Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:17:17Z):
Reading (spec cor_margin_continuous; ¶ after Corollary 3.6, 03-main-results.tex:281-286).
Same sentence as cor_margin_finite, in its general reading: when L²(ν;R^m) is
infinite-dimensional, jump feedback entering through finitely many continuous (possibly
nonlinear) functionals of u, with any dependence on the law, supplies no margin.
Is it claimed? The sentence restricts only how u enters h0 ("through finitely many functionals of
u") and justifies it by "finitely many continuous functionals cannot separate the points"; it does
not restrict linearity nor the law dependence, so this general reading is a legitimate reading of
the printed claim (and is true: Borsuk–Ulam gives u ≠ u' with φ(u) = φ(u'); a fair-coin swap in
F_t, t > 0, gives diagonal pairs with equal laws, δX=δY=δZ=0, δh0 = 0, δU ≠ 0).
A faithful statement must contain:
- setting: standing basis, T > 0, dim L²(ν;R^m) = ∞; m = n, G full rank (general broader, fine).
- class: h0(t,(x,y,z,u),μ) = H(t,x,y,z,φ_1(u),…,φ_J(u),μ) with φ_j : L²(ν;R^m) → R continuous
  (not necessarily linear) and H arbitrary (any law dependence); b0, σ0, f0 arbitrary.
- conclusion: for every β1, β2 ≥ 0 and c > 0, (2.13) with margin c fails.
- the refuting diagonal pairs must live on the standing basis (F_t-measurable), so the basis must
  be the paper's (W present, F_t rich for t > 0).

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
Comparison: spec cor_margin_continuous (Sec3Margin.lean:156-175).
- Is it claimed? Yes, by my locked reading: the sentence restricts only how u enters h0; it does
  not restrict linearity nor law dependence.
- Setting: standing basis, d ≥ 1 (standing), T > 0, L²(ν;ℝ^m) infinite-dimensional; n, m, G
  arbitrary.
- Class: F : ℝ → L²(ν;ℝ^m) → ℝ^k with every F t continuous (possibly nonlinear; may vary with t),
  and h(t,θ,μ) = h(t,θ',μ) whenever θ, θ' share (x,y,z) and F_t u = F_t u' — the same law on both
  sides, so h = H(t,x,y,z,F_t(u),μ) with arbitrary law dependence. b, σ, f arbitrary. Matches.
- Constants β₁ ≥ 0, β₂ arbitrary, c > 0; conclusion ¬Margin213 — no margin. Matches.
- Broader than the printed context in: m, n, G general (Cor 3.6 has m = n, G full rank) and
  t-dependent functionals.
- Witness cor_margin_continuous_hypotheses: ν = Lebesgue, rank-one feedback through ⟨φ,u⟩.
Verdict: broader (instantiation m = n, G of full rank, β₁, β₂ ≥ 0, F_t = F independent of t).
Witness: —
Verdict: broader — Broader: m, n, G arbitrary (Corollary 3.6 has m = n, G of full rank), β₂ of any sign, and the
continuous functionals F_t may depend on t. Instantiation: m = n, G of full rank, β₁, β₂ ≥ 0,
F_t = (φ_1,…,φ_k) independent of t; then a jump coefficient depending on u only through these
continuous functionals, with any law dependence, carries no margin when L²(ν) is
infinite-dimensional.
Disagreements with the author's review (shown 2026-10-19T03:32:40Z): Classification only. The author records faithful; I record broader because m, n and G are general
(Corollary 3.6: m = n, G of full rank), β₂ has any sign and the functionals may depend on t. We
agree that the clause is claimed by the paper (the general reading of the sentence) and on its
meaning.
