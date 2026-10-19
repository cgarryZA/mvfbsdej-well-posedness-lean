### A:lem:lawflow, A:sec3:HH-banach: LevyStochCalc.Poisson.Compensated.markedEnergyMeasure
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash 6a70d753259c930a27f458a6e2a44d87 (pl-fp-v1:690e02d5578bab6254df09c5c161210ce770644fd680d3f7a0dea95a3b5f09f1)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:34:37Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:17:18Z):
Reading (def LevyStochCalc.Poisson.Compensated.markedEnergyMeasure; used for H²_N in §3 and in
Lemma A.1, (2.4)).
Paper notion: the measure dt ⊗ dP ⊗ ν on [0,T] × Ω × E (the compensator measure of N times P on
the horizon), with respect to which H²_N is the space of predictable U with
E∫_0^T∫_E|U_t(e)|²ν(de)dt < ∞, and the identification "U = U' dt⊗dP⊗ν-a.e."; (2.4) identifies
L²(𝒫;L²(ν)) with L²(𝒫⊗𝓔) under this measure.
A faithful Lean definition: the product of Lebesgue on [0,T] (endpoints irrelevant), P, and the
intensity ν of the PRM (the same ν as the compensator dt⊗ν), in any bracketing/order, so that
∫⁻ |U|² d(markedEnergyMeasure) = E∫_0^T∫_E |U_t(e)|² ν(de) dt. Edge cases: ν must be the PRM's
intensity (σ-finite, possibly infinite), not normalised; the horizon T; no weights; if defined
via energyMeasure ⊗ ν it inherits that definition's checks; measure on the product σ-algebra
(predictable restriction allowed).

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
Comparison: def LevyStochCalc.Poisson.Compensated.markedEnergyMeasure.
- Lean: markedEnergyMeasure P ν T = P.prod ((volume.restrict (Icc 0 T)).prod ν) on Ω × ℝ × E.
- Paper: dt ⊗ dP ⊗ ν on [0,T] × Ω × E, ν the intensity of N. Lebesgue restricted to [0,T], P,
  and the mark measure ν passed as argument (in every use the driver's ν), no weights; product
  σ-algebra, predictability imposed separately (U_pred). markedEnergy = ∫⁻ω∫⁻_{[0,T]}∫⁻_E |φ|² dν,
  its integral of |φ|². Matches.
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-19T03:32:40Z): none
