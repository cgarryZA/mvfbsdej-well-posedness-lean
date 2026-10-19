### A:rem:uniq-no-integ: Dissertation.PaperSpec.A.rem_uniq_initial
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba1fa628ed6b5f5989d (pl-fp-v1:d16d93ab938552f1255a8a7c20185ed36e03a7b3fc6c7bfce7ce993aa86f1a8a)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:34:35Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:17:16Z):
Reading (spec rem_uniq_initial; Remark 3.4, 03-main-results.tex:186-187). See COMMON.md.
Claim: the initial-data condition ξ0 ∈ L² (part of Assumption 2.2) is necessary for a solution in
𝕊, since X_0 = ξ0 and E sup_t |X_t|² < ∞.
A faithful statement: on the standing basis, for arbitrary coefficients (b,σ,h,f,g) (no
assumption needed; Assumptions 2.3–2.5 as context would be a harmless narrowing) and an
F_0-measurable ξ0 : Ω → R^n, if there is a solution Θ ∈ 𝕊 of (1.1) with initial datum ξ0, then
E|ξ0|² < ∞ (ξ0 ∈ L²(Ω,F_0;R^n)). The solution notion must be the paper's (both identities a.s. for
every t, in particular at t = 0 giving X_0 = ξ0 a.s.; X ∈ S²). It must not assume ξ0 ∈ L² nor
assume Assumption 2.2 (that would make it trivial).

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
Comparison: spec rem_uniq_initial (Sec3Rem34.lean:41-54).
- Setting: standing basis, any n, m, d, T ≥ 0, arbitrary coefficients C (no assumption) and an
  arbitrary ξ₀ : Ω → ℝⁿ — as in my reading (no assumption needed).
- Hypotheses: WeakSolution (a tuple of ℍ_weak satisfying (1.1) with initial datum ξ₀, integrals
  existing, h at the predictable tuple) AND E sup_{t≤T}|X_t|² < ∞. The paper's hypothesis is "a
  solution in ℍ". PaperSolution.toWeakInt (PaperWeakSolutionInt.lean:211, T ≥ 0) turns a
  Solution into the WeakSolution data with the same γ (left limits are part of both), and
  Solution contains X_sup. So every solution in ℍ meets the Lean hypotheses; the Lean also covers
  ℍ_weak tuples whose X merely has a finite sup moment. Broader.
- Conclusion: ∀ i, MemLp (ξ₀ · i) 2 P, i.e. ξ₀ ∈ L² (coordinatewise = vector-valued in finite
  dimension). F_0-measurability is not concluded; it is part of what an initial datum is, and the
  remark's content is the L² condition. Matches.
- Not trivial: ξ₀ ∈ L² is not assumed; the solution notion fixes X_0 = ξ₀ a.s. through the
  forward identity at t = 0.
- Witness rem_uniq_hypotheses: the singular-drift system has a WeakSolution from 0 with finite
  sup moments — the hypotheses can be met.
Verdict: broader (instantiation: a Solution in ℍ gives the WeakSolution hypothesis by
PaperSolution.toWeakInt and the sup bound by its X_sup field).
Witness: —
Verdict: broader — Broader: the hypothesis is "a WeakSolution (ℍ_weak tuple satisfying (1.1)) whose X has finite
E sup|X|²" instead of "a Solution in ℍ". Instantiation giving the printed claim: for a Solution
(T ≥ 0), PaperSolution.toWeakInt yields the WeakSolution data with the same γ (left limits are in
both predicates) and the Solution's X_sup field gives the sup bound; the conclusion ξ₀ ∈ L² then
is the printed necessity of the initial-data condition.
Disagreements with the author's review (shown 2026-10-19T03:32:39Z): Classification only. The author records faithful; I record broader: the hypothesis is a
WeakSolution with a finite sup moment of X, which every Solution in ℍ provides
(PaperSolution.toWeakInt and the X_sup field), but which also covers ℍ_weak tuples that are not
Solutions. The author's own correspondence states this ("a solution in ℍ is such a tuple"); we
agree on the meaning.
