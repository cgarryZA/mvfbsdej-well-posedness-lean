### A:lem:lawflow, A:sec3:HH-banach: LevyStochCalc.Brownian.Ito.energyMeasure
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash 8bb90a671c0f63eba6329d346b422bc3 (pl-fp-v1:44daab3706e079af5d0ff371170231e0f8f609a1bf7142b8c20cd86b9e8482fd)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:34:37Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:17:17Z):
Reading (def LevyStochCalc.Brownian.Ito.energyMeasure; used for H²_W in §3 "Solution space" and in
Lemma A.1; 03-main-results.tex:10, 09-appendix.tex).
Paper notion: the measure dt ⊗ dP on [0,T] × Ω (Lebesgue measure on the time interval [0,T]
times P), with respect to which H²_W is the space of predictable Z with
E∫_0^T|Z_t|²_F dt = ∫|Z|² d(dt⊗dP) < ∞; the paper's "dt⊗dP-a.e." identifications and the Fubini
isometry (2.4) refer to it (on the predictable σ-field 𝒫 or the product σ-field; restricted to
𝒫 for the jump integrand).
A faithful Lean definition: the product measure (Lebesgue restricted to [0,T], or to (0,T],
[0,T), — endpoints are null) ⊗ P on time × Ω (either order), possibly as a measure on the product
σ-algebra (predictability then imposed by a separate measurability requirement), so that
∫⁻ ‖Z‖² d(energyMeasure) = E∫_0^T ‖Z_t‖² dt. Edge cases to check: the horizon must be T (not all
of [0,∞), unless every use truncates); the measure in ω must be P (a probability measure), not a
different measure; total mass T (finite); no density or weight (e.g. no e^{-t} or 1/T
normalisation); the time measure Lebesgue (not counting). If it is a measure on a predictable
σ-algebra it must be the restriction of the product measure.

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
Comparison: def LevyStochCalc.Brownian.Ito.energyMeasure.
- Lean: energyMeasure P T = P.prod (volume.restrict (Icc 0 T)) on Ω × ℝ.
- Paper: dt ⊗ dP on [0,T] × Ω. Lebesgue on [0,T] (closed interval; endpoints null), P the sample
  measure, product in the order Ω × time (immaterial). No weight, no normalisation, total mass T
  for a probability P; defined on the product σ-algebra mΩ ⊗ Borel, predictability imposed
  separately (e.g. Z_pred in PaperSolution), as allowed in my reading. For T < 0 it is the zero
  measure (no paper meaning). energy P T H = ∫⁻ω ∫⁻_{[0,T]} |H|², the integral of |H|² against it.
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-19T03:32:40Z): none
