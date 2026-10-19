### A:rem:margin: Dissertation.PaperSpec.A.rem_margin_unweighted
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba1ba4163c9b3d796bd (pl-fp-v1:604c2f8d9a4cd6515bd432ddbef03bd8d40f767692a90ae2016bccf0a124b152)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:34:35Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:17:16Z):
Reading (spec rem_margin_unweighted; Remark 2.11, 02-model-assumptions.tex:302-307). See COMMON.md.
Claim: when m = n, a margin c in the weighted form (2.12) yields the margin c/c_G in the
unweighted form (2.13), with the same β1, β2 and the same coefficients and G.
A faithful statement must contain:
- setting: standing basis, m = n, G ∈ R^{n×n} of full rank (hence invertible), c_G = s_min(G)^{-2}
  (equivalently the best constant with |x|² ≤ c_G|Gx|², |y|² ≤ c_G|Gᵀy|²);
  arbitrary coefficients b,σ,h,f; arbitrary real β1, β2 (signs not needed); c > 0.
- hypothesis: (2.12) with margin c holds (for a.e. t, all diagonal pairs (Θ,LawΘ),(Θ',LawΘ')
  of F_t-measurable L² tuples).
- conclusion: (2.13) holds with margin c/c_G and the same β1, β2 (same a.e.-t / all-pairs
  quantifier). The mechanism is the channel-wise pointwise bound
  c(|Gᵀy|²+|Gᵀz|²_F+‖Gᵀu‖²+|Gx|²) ≥ (c/c_G)(|y|²+|z|²_F+‖u‖²+|x|²); stating that bound as well
  is fine but the implication between the margin forms is the claim.
- c_G must be s_min(G)^{-2} (not e.g. ‖G⁻¹‖ with another norm, nor an arbitrary constant). The
  words "not c" are emphasis; a formal refutation of margin c is not required.
- Broader is fine (e.g. any constant c' ≤ c/c_G, or a pointwise version); requiring extra
  hypotheses on the coefficients (Assumptions 2.2–2.5) would be a harmless narrowing only if it
  does not exclude the general case — it should not be needed.

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
Comparison (verdict recorded 2026-10-19T03:32:31Z):
Comparison: spec rem_margin_unweighted (Sec2Remarks.lean:234-246) vs locked reading.
- Setting: standing basis (LevyDriver D with d-dim W and PRM N of intensity dt⊗ν, ν σ-finite on a
  countably generated E, 𝒢₀ independent of the driver, filtration enlJoint = usual augmentation of
  σ(W,N) ∨ 𝒢₀) — matches §2. d = 0 and T ≤ 0 are not excluded (harmless: T ≤ 0 makes the a.e.
  quantifier vacuous; d is not used).
- m = n: Coeffs ν n n d and G : Matrix (Fin n) (Fin n) — yes. 0 < n.
- G full rank: G.rank = min n n — yes. c_G = s_min(G)^{-2}: the conclusion uses
  c / (sMin G ^ 2)⁻¹ = c · s_min(G)², i.e. c / c_G, with sMin the square root of the least
  eigenvalue of GᵀG (FullRank.lean) — the smallest singular value. Correct.
- β1, β2 arbitrary reals, c > 0 — as in my reading (no sign needed).
- Hypothesis Margin212 = (2.12): for a.e. t ∈ [0,T] (Lebesgue on Icc), all p, p' ∈ diagonalInputs
  (strongly ℱ_t-measurable, L², μ = lawP2 P Θ), integrable pairing27 and the weighted bound with
  −β1 E[|GᵀδY|²+|GᵀδZ|²+‖GᵀδU‖²] − β2 E|GδX|² − c E[...weighted sum...]. pairing27 is
  ⟨δb,GᵀδY⟩ + ⟨δσ,GᵀδZ⟩_F + ⟨−δf,GδX⟩ + ∫⟨δh(e),Gᵀ δU(e)⟩ν(de) with GZ the Kronecker G⊗I_d
  and GU the mark-wise action. Matches.
- Conclusion Margin213 = (2.13) with the same β1, β2 and margin c/c_G, same quantifiers,
  unweighted sum |δY|²+|δZ|²_F+‖δU‖²+|δX|² with the channel norms (Euclidean, Frobenius, L²(ν)).
  Matches.
- The project's TupleH carries the max norm, but no norm of H enters this statement (only the
  channel norms), so the representation does not matter here.
- Witness rem_margin_hypotheses: Ex 5.1(i) (β1=β2=1) at ν = δ0, G = 1 satisfies (2.12) with
  constants 1/2 and margin 1/2 — an intended instance.
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-19T03:32:39Z): none
