### A:sec3:margin-paragraph: Dissertation.PaperSpec.A.cor_margin_channels
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba14127298d8cc156d9 (pl-fp-v1:862db66b011634d6483b8589a7a62eac7b1844ace37da177882e55340383bc33)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:34:36Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:17:17Z):
Reading (spec cor_margin_channels; ¶ after Corollary 3.6, 03-main-results.tex:278-280).
Claim: by the reduction of Remark 2.10, a margin c > 0 in (2.13) forces every channel of the
baseline to be strictly dissipative.
A faithful statement: m = n (Cor 3.6 context; general m,n fine), G full rank, β1, β2 ≥ 0, c > 0,
coefficients satisfying (2.13) with margin c. Then for a.e. t and all diagonal pairs:
- δX = δY = δZ = 0: E∫⟨δh,GᵀδU⟩ν ≤ −β1 E‖GᵀδU‖² − c E‖δU‖² (≤ −c E‖δU‖²: h strictly
  U-dissipative);
- δX = δY = δU = 0: E⟨δσ,GᵀδZ⟩_F ≤ −β1E|GᵀδZ|² − cE|δZ|² (σ strictly Z-dissipative);
- δX = δZ = δU = 0: E⟨δb,GᵀδY⟩ ≤ −β1E|GᵀδY|² − cE|δY|² (b strictly Y-dissipative);
- δY = δZ = δU = 0: E⟨−δf,GδX⟩ ≤ −β2E|GδX|² − cE|δX|² (−f strictly X-dissipative).
All four channels must be present ("every channel"); each with a strictly positive rate (c, or the
full RHS). The other coordinates' differences vanish but the laws of the two inputs may differ.

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
Comparison: spec cor_margin_channels (Sec3Margin.lean:47-88).
- Setting: standing basis, any n, m, d, G, T, β₁, β₂, c (no sign conditions, no m = n).
- Hypothesis Margin213 (2.13) with (β₁, β₂, c).
- Conclusion for a.e. t and all diagonal pairs, all four channels:
  f: δY=δZ=δU=0 ⇒ E⟨−δf,GδX⟩ ≤ −β₂E|GδX|² − cE|δX|²;
  b: δX=δZ=δU=0 ⇒ E⟨δb,GᵀδY⟩ ≤ −β₁E|GᵀδY|² − cE|δY|²;
  σ: δX=δY=δU=0 ⇒ E⟨δσ,GᵀδZ⟩_F ≤ −β₁E|GᵀδZ|²_F − cE|δZ|²_F;
  h: δX=δY=δZ=0 ⇒ E∫⟨δh,GᵀδU⟩ν ≤ −β₁E‖GᵀδU‖² − cE‖δU‖².
  Matches my reading (every channel, each with the full right-hand side; with β ≥ 0 and c > 0 this
  is strict dissipativity at rate ≥ c). Laws of the two inputs may differ, as required.
- Equalities of the other channels required at every ω (not a.s.): harmless, as for
  rem_beta1_dich.
- Broader: c, β₁, β₂ of any sign and m, n, G general; the printed claim is at c > 0 (and the
  Corollary 3.6 baseline, m = n, β ≥ 0).
- Witness cor_robust_hypotheses: Ex 5.1(i) baseline with (2.13), margin 1.
Verdict: broader (instantiation c > 0, β₁, β₂ ≥ 0, m = n, G of full rank).
Witness: —
Verdict: broader — Broader: no sign conditions on β₁, β₂, c and general m, n, G. Instantiation: c > 0, β₁, β₂ ≥ 0
(m = n, G of full rank in the Corollary 3.6 context); then each of the four channel inequalities
gives strict dissipativity at rate at least c, i.e. every channel of the baseline is strictly
dissipative.
Disagreements with the author's review (shown 2026-10-19T03:32:40Z): Classification only. The author notes that the proposition assumes neither c > 0 nor β₁, β₂ ≥ 0
("the reduction, valid for any constants") and records faithful; I record broader with the
instantiation c > 0, β₁, β₂ ≥ 0 (and the m = n, full-rank context), under which each channel
inequality is strict dissipativity. No disagreement about meaning.
