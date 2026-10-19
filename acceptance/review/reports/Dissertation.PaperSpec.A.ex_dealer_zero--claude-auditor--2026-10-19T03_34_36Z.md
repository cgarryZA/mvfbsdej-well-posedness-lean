### A:ex:dealer: Dissertation.PaperSpec.A.ex_dealer_zero
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba1fbee3842d146d0f8 (pl-fp-v1:74fc22dd8bbb997ca8742bc9d4a9bc8e1ddeec0b2a9ac397cc2898afb2ee1607)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:34:36Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:17:16Z):
Reading (spec ex_dealer_zero; Example 5.5, 05-examples.tex:483-505).
Setting: the explicit specialisation (as in ex_dealer_active): n = m = d = 1, G = 1, β1 = 1,
β2 = 1/2, σ_c = 1, ξ0 = 0, E = {−1,+1}×(0,1], ν = c_ς q^{−1−ϱ}dq, 0 < ϱ < 2, c_{±1} = (2−ϱ)/2,
h_c = ςq, h_x = q; standing basis with this N, T > 0. Dealer coefficients at ε = 0:
b = −y, σ = 1 − z, h = h_c + h_x x − u, f = x/2 + ⟨h_x,u⟩, g = x.
Conclusions that must all be present:
(a) the linear SDE X⁰_t = ∫_0^t(−X⁰_s ds + ½ dW_s) + ½∫_0^t∫_E (h_c(e) + h_x(e)X⁰_{s−}) Ñ(ds,de)
    has a unique solution X⁰ ∈ S²(0,T;R) (càdlàg adapted, E sup|X⁰|² < ∞; uniqueness up to
    indistinguishability within S²);
(b) Θ⁰ = (X⁰, X⁰, 1/2, U⁰) with U⁰_t = ½(h_c + h_x X⁰_{t−}) is in 𝕊 and solves the dealer system
    at ε = 0 in the paper's sense;
(c) E X⁰_t = 0 for every t; v(t) := E|X⁰_t|² satisfies v' = −(7/4)v + 1/2 (v(0) = 0), hence
    v(t) = (2/7)(1 − e^{−7t/4}) on [0,T];
(d) E‖U⁰_t − E U⁰_t‖²_{L²(ν)} = v(t)/4 = (1/14)(1 − e^{−7t/4}), and Law(U⁰_t) is not a Dirac mass
    for every t ∈ (0,T].
Formal shape: these are conclusions about the specific system, with no hypothesis beyond the
standing basis. The ODE can be stated by its closed-form solution plus the derivative identity.

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
Comparison: spec ex_dealer_zero (Sec5DealerActive.lean:130-172).
- Setting: the specialisation exactly (as in ex_dealer_active): d = 1, ex55Marks ϱ, 0<ϱ<2, T > 0,
  h_c, h_x with representatives ς q, q; coefficients ex55Coeffs with β1 = 1, β2 = 1/2, σ_c = 1,
  ε = 0, ξ0 = 0.
- (a) existence: ∃ X0 solving ex55Linear (LinearFSDEJ: X0_t = 0 + ∫_0^t (−X0) ds + ∫ ½ dW
  + ∫∫ ½(ς q + q X0_{s−}) Ñ, a.s. at each t ∈ [0,T], X0 adapted, right-continuous) with
  E sup_{[0,T]} X0² < ∞ and left limits on every path: X0 ∈ S². Uniqueness: any two solutions of
  ex55Linear are indistinguishable on [0,T] (uniqueness among all solutions — at least the
  printed uniqueness in S²). Matches.
- (b) ∀ such X0: Solution of the ε = 0 system from 0 with X = Y = X0, Z = ½ on [0,T],
  U = ½(ς q + q X0_{s−}) on (0,T] (value at s = 0 irrelevant). Matches "Θ⁰ solves at ε = 0".
- (c) E X0_t = 0 on [0,T]; v(t) = E|X0_t|² = (2/7)(1 − e^{−7t/4}) on [0,T]; v' = −(7/4)v + 1/2 on
  (0,T) (derivative at interior points). Matches.
- (d) ∀ t ∈ (0,T]: E‖U⁰_t − E U⁰_t‖² = v(t)/4 = (1/14)(1 − e^{−7t/4}) and P.map U⁰_t is no Dirac
  mass. Matches.
- No hypotheses beyond the specialisation. Witness ex_dealer_spec_hypotheses: it can be met.
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-19T03:32:39Z): none
