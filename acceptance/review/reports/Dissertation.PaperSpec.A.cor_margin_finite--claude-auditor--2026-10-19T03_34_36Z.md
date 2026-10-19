### A:sec3:margin-paragraph: Dissertation.PaperSpec.A.cor_margin_finite
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba15e05ed8a37017606 (pl-fp-v1:eb820c1f1c871b1099803e7e8e1724d8a0ad6a6270e8836a9d3319570a2a4865)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:34:36Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:17:16Z):
Reading (spec cor_margin_finite; ¶ after Corollary 3.6, 03-main-results.tex:281-286).
Claim: when L²(ν) is infinite-dimensional, jump feedback entering through finitely many
functionals of u supplies no margin, since finitely many continuous functionals cannot separate
the points of an infinite-dimensional space; a margin then needs feedback dissipative on the whole
of L²(ν).
A faithful statement must contain:
- setting: standing basis, T > 0, dim L²(ν;R^m) = ∞ (or at least > J); m = n (Cor 3.6) with G
  full rank (general m,n broader and fine).
- the class: h0(t,θ,μ) depends on u only through finitely many continuous functionals
  φ_1,…,φ_J : L²(ν;R^m) → R, i.e. h0(t,(x,y,z,u),μ) = H(t,x,y,z,φ_1(u),…,φ_J(u)[,μ]).
  "Functionals" can be read as continuous linear functionals (the minimal reading, standard in a
  Hilbert space) or as continuous possibly nonlinear ones (also true, via Borsuk–Ulam). A version
  with continuous linear functionals is an acceptable reading of this sentence; the law
  dependence of h0 is not restricted by the sentence, so the most faithful form leaves it
  arbitrary, but a law-free h0 version captures the stated mechanism (separation of points) and I
  would accept it only if the clause is explicitly the law-free/linear case and another clause
  carries the general one. b0, σ0, f0 arbitrary.
- conclusion: for every β1, β2 ≥ 0 and c > 0, (2.13) fails (no margin), i.e. the baseline with such
  h0 does not satisfy (2.13) with any margin c > 0.
- refuting pairs must be genuine diagonal inputs at a.e. t (deterministic u ≠ u' in the common
  kernel of the φ_j suffice in the linear law-free case).

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
Comparison: spec cor_margin_finite (Sec3Margin.lean:104-122).
- Setting: standing basis, T > 0, ¬FiniteDimensional L²(ν;ℝ^m) (infinite-dimensional fibre);
  n, m, d, G arbitrary (m = n and full rank not required).
- Class: ℓ : L²(ν;ℝ^m) →ₗ ℝ^k linear (continuity not required), and h along deterministic diagonal
  inputs depends on u only through ℓ u: h(t,(x,y,z,u),δ_{(x,y,z,u)}) = h(t,(x,y,z,u'),δ_{(x,y,z,u')})
  whenever ℓu = ℓu'. Every law-free h0 = H(t,x,y,z,ℓu) satisfies it; so do some law-dependent
  ones. b, σ, f arbitrary.
- Constants: β₁ ≥ 0, β₂ arbitrary, c > 0. Conclusion ¬Margin213: no margin. Matches.
- Reading of "functionals": my lock accepted the linear reading for this clause provided another
  clause carries the general (nonlinear, law-dependent) reading; cor_margin_continuous does.
  Relative to the linear, law-free reading the Lean is broader (no continuity, condition only at
  deterministic inputs, general m, n, G, β₂).
- Witness cor_margin_finite_hypotheses: ν = Lebesgue (infinite-dimensional L²), a rank-one
  feedback h = −⟨φ,u⟩φ through ℓu = ⟨φ,u⟩ — an intended instance.
Verdict: broader (instantiation: m = n, G full rank, β₁, β₂ ≥ 0, ℓ = (φ_1,…,φ_k) continuous
linear functionals and h0 = H(t,x,y,z,ℓu) law-free; the nonlinear/law-dependent reading is the
separate clause cor_margin_continuous).
Witness: —
Verdict: broader — Broader than the linear reading: ℓ any linear map L²(ν) → ℝ^k (continuity not needed), the
factorisation through ℓ required only at deterministic inputs with their Dirac laws, and m, n, G,
β₂ general. Instantiation: m = n, G of full rank, β₁, β₂ ≥ 0, ℓ = (φ_1,…,φ_k) continuous linear
functionals and a law-free h0 = H(t,x,y,z,ℓ(u)). The nonlinear, law-dependent reading of the same
sentence is the separate clause cor_margin_continuous.
Disagreements with the author's review (shown 2026-10-19T03:32:39Z): Classification only. The author calls cor_margin_finite narrower than the printed sentence in
isolation (linear functionals, Dirac-input condition), the general reading being carried by
cor_margin_continuous; I locked the linear reading as acceptable for this clause on exactly that
condition and, relative to it, record broader (continuity not needed, condition only at
deterministic inputs, general m, n, G). Both reviews agree that the two clauses together cover the
sentence. The author's remark that the Dirac-input condition also admits coefficients
H(t,x,y,z,ℓu,π_#μ) is correct and matches my note that some law-dependent coefficients qualify.
