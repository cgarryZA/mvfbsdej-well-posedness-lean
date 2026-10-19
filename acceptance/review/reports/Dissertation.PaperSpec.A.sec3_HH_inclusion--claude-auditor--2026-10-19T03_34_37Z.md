### A:sec3:HH-banach: Dissertation.PaperSpec.A.sec3_HH_inclusion
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba130514b735af5f227 (pl-fp-v1:4e8f72443b121a3726cd0f49b21bb90f6c2115b3679c2ef8ddbb770d66d76acc)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:34:37Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:17:17Z):
Reading (spec sec3_HH_inclusion; §3 "Solution space", 03-main-results.tex:31-32).
Claim: E∫_0^T|V_t|²dt ≤ T E sup_{t≤T}|V_t|², hence 𝕊 ⊂ ℍ².
A faithful statement: on the standing filtered space, T > 0 (T ≥ 0 fine):
(a) for every (càdlàg adapted, or merely jointly measurable) process V : [0,T]×Ω → R^j,
    E∫_0^T |V_t|² dt ≤ T · E sup_{0≤t≤T} |V_t|² (in [0,∞] or with finiteness hypotheses);
(b) consequently every Θ = (X,Y,Z,U) ∈ 𝕊 (X ∈ S²(0,T;R^n), Y ∈ S²(0,T;R^m), Z ∈ H²_W, U ∈ H²_N)
    belongs to ℍ² (X, Y ∈ L²(0,T;·): càdlàg adapted with E∫_0^T|·|² < ∞; Z, U unchanged).
The sup must be over all t ∈ [0,T] (not essential sup in t unless equal for càdlàg paths), the
time integral over [0,T] with Lebesgue measure.

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
Comparison: spec sec3_HH_inclusion (Sec3Space.lean:99-108).
- ∀ measure P, n, T ≥ 0, any V : Fin n → ℝ → Ω → ℝ (no regularity needed; lower integrals):
  ∫⁻ω ∫⁻_{[0,T]} |V_s|² ds ≤ T · ∫⁻ω sup_{t∈[0,T]} |V_t|² (esq = Euclidean squared norm, sup over
  every t of [0,T]). That is E∫_0^T|V|² ≤ T E sup|V|². Matches (a).
- and E sup|V|² < ∞ ⇒ every coordinate has finite energy E∫_0^T|V_i|² < ∞: for X, Y ∈ S²
  (already càdlàg adapted) this is membership in L²(0,T;·), so 𝕊 ⊂ ℍ² (Z, U channels identical).
  Matches (b).
- Generality in P and V is ambient, not a dropped hypothesis.
- Witness: the forward component of the Ex 5.1(i) solution, nonzero.
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-19T03:32:40Z): The shown review gives only a verdict ("faithful with representation choices") and a pointer to a
report I may not open. I record faithful: the bound is stated with lower integrals in [0,∞] for any
process and the inclusion as finiteness of the energy of each coordinate; I see no choice that
changes the meaning. The difference is one of classification.
