### A:sec2:infinite-activity-atoms: Dissertation.PaperSpec.A.sec2_infinite_activity
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba13a9f48f6bc72d40f (pl-fp-v1:2fcdef13ef168d5751a9482b352ed8ec2e89c36142390eef6d6b8cf243c8588e)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:34:37Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:17:18Z):
Reading (spec sec2_infinite_activity; §2 ¶1, 02-model-assumptions.tex:9-11).
Claim: in the infinite-activity regime ν(E) = ∞, the Poisson random measure N has infinitely many
atoms on every nondegenerate time interval (almost surely).
A faithful statement: for N a PRM on R_+ × E with intensity dt ⊗ ν (the standing N), ν σ-finite
with ν(E) = ∞: almost surely, for every a < b (in R_+, or in [0,T]), N((a,b) × E) = ∞ (infinitely
many atoms). "∀ interval, a.s." and "a.s., ∀ interval" are equivalent here (rational intervals),
so either order is fine. The hypothesis must be ν(E) = ∞ (and σ-finiteness), not a stronger one;
the conclusion is about N itself (its atoms / counting values), not about the compensator.

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
Comparison: spec sec2_infinite_activity (Sec2Basics.lean:45-52).
- ∀ probability space, ν σ-finite, d, ∀ Lévy driver D (its PRM N with intensity
  Leb|[0,∞) ⊗ ν), ν(E) = ∞ ⇒ a.s., for all 0 ≤ s < t, N(ω)((s,t] × E) = ∞. Every nondegenerate
  time interval in ℝ_+ contains such a (s,t]; "a.s., for all intervals" (the stronger order).
  N(B) = ∞ is the count of atoms being infinite. Matches.
- Witness: Lebesgue intensity (infinite mass) with an existing driver.
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-19T03:32:41Z): The shown review gives only a verdict ("faithful with representation choices") and a pointer to a
report I may not open. I record faithful: "infinitely many atoms on every nondegenerate time
interval" is stated as N((s,t] × E) = ∞ for all 0 ≤ s < t simultaneously, almost surely, which I
read as the claim itself (every nondegenerate interval contains such an (s,t]). The difference is
one of classification.
