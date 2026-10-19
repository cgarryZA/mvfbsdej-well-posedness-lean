### A:sec3:margin-paragraph: Dissertation.PaperSpec.A.cor_margin_additive
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba19075028a95edf84d (pl-fp-v1:b73e058908da190df52e8ee42186266e119383b4a9479d6ec61efd78518efa20)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:34:35Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:17:16Z):
Reading (spec cor_margin_additive; ¶ after Corollary 3.6, 03-main-results.tex:278-281).
Claim: by the reduction of Remark 2.10 a margin in (2.13) forces every baseline channel to be
strictly dissipative; therefore, when ν ≠ 0, an additive jump coefficient h0 = h0(t,x,e) cannot
serve as a baseline of Corollary 3.6.
A faithful statement must contain:
- setting: standing basis with ν ≠ 0 (ν(E) > 0, so L²(ν;R^m) ≠ {0}), T > 0; m = n (Cor 3.6
  setting; general m,n would be broader and fine); G full rank.
- h0 additive: h0(t,θ,μ) = k(t,x) (an L²(ν;R^n)-valued function of (t,x) only: no dependence on
  y, z, u or on the law). Allowing also y,z-dependence is broader and fine. b0, σ0, f0 arbitrary.
- conclusion: for every β1, β2 ≥ 0 (nonnegativity is needed: with β1 < 0 the claim can fail) and
  every c > 0, the unweighted margin inequality (2.13) does NOT hold (for a.e. t and all diagonal
  pairs). Equivalently: the baseline does not satisfy the hypotheses of Corollary 3.6 (Assumptions
  2.2–2.5 with a margin c_diss > 0 in (2.13)). The negation of (2.13) alone is the stronger and
  preferred form; the negation of the whole Cor 3.6 hypothesis is weaker but is literally "cannot
  serve as a baseline" and acceptable.
- The refuting pairs must be genuine diagonal inputs on the standing basis (deterministic
  (0,0,0,u),(0,0,0,u') with u ≠ u' suffice), and T > 0 is needed so "a.e. t" is not vacuous.

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
Comparison: spec cor_margin_additive (Sec3Margin.lean:90-102).
- Setting: standing basis, T > 0, ν ≠ 0, m ≥ 1 (so L²(ν;ℝ^m) ≠ {0}); n, d arbitrary; G an
  arbitrary m×n matrix (full rank not required); m = n not required.
- Additive h: ∀ t θ θ' μ μ', θ.1 = θ'.1 → h(t,θ,μ) = h(t,θ',μ') — h depends on (t,x) only (no y,
  z, u, law), the paper's h0 = h0(t,x,e). b, σ, f arbitrary. Matches.
- Constants: β₁ ≥ 0 (needed), β₂ arbitrary, c > 0.
- Conclusion: ¬ Margin213 — the unweighted margin inequality (2.13) fails. As noted in my
  reading this is the strong form; it implies that the baseline hypotheses of Corollary 3.6 fail
  (under Assumption 2.3 the pairing integrability in Margin213 is automatic, so Margin213 is the
  printed (2.13) there).
- The paper's claim concerns Corollary 3.6 baselines (m = n, G full rank, β1, β2 ≥ 0); the Lean
  drops m = n, full rank and β₂ ≥ 0. Broader.
- Witness cor_margin_additive_hypotheses: ν = δ0 ≠ 0, Ex 5.1(i) with β1 = 0 has an additive h.
Verdict: broader (instantiation m = n, G of full rank, β₁, β₂ ≥ 0: then ¬(2.13) for every
c > 0 means the additive h0 is no Corollary 3.6 baseline).
Witness: —
Verdict: broader — Broader: m, n, G arbitrary (no m = n, no full rank) and β₂ of any sign. Instantiation: m = n,
G of full rank, β₁, β₂ ≥ 0 (the Corollary 3.6 baseline setting); then ¬(2.13) for every c > 0
says an additive h0(t,x) cannot carry a margin, i.e. cannot serve as a Corollary 3.6 baseline
(when ν ≠ 0).
Disagreements with the author's review (shown 2026-10-19T03:32:39Z): Classification only. The author records faithful while noting that the dimensions are general
(Corollary 3.6 has m = n); the proposition also allows any G (not only full rank) and any sign of
β₂. I record broader, with the instantiation m = n, G of full rank, β₁, β₂ ≥ 0. No disagreement
about meaning.
