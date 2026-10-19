### A:ex:concrete: Dissertation.PaperSpec.A.ex_concrete_i_ham
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba1cf9f26355b828c6a (pl-fp-v1:8c80bbaef3cfa4fe088b7cd654058531ed81cc400b41b4e80c26d9e363b80ede)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:31:21Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:16:08Z):
Reading of spec ex_concrete_i_ham, clause "(i) the Hamiltonian and its minimiser" (Example 5.1(i)).
Setting: n=m=d=1, nu sigma-finite, sigma_c in R, h_c in L2(nu), beta1, beta2 > 0.
H(x,y,z,u; a^b,a^sigma,a^h) = a^b y + (sigma_c + a^sigma) z + int_E (h_c(e)+a^h(e)) u(e) nu(de)
   + (beta2/2)|x|^2 + (1/(2 beta1)) (|a^b|^2 + |a^sigma|^2 + ||a^h||^2_{L2(nu)}),
controls (a^b,a^sigma,a^h) in R x R x L2(nu), (x,y,z,u) in R x R x R x L2(nu) (z real since d=m=1).
Claims:
 (a) for every (x,y,z,u), H is strictly convex in the controls a=(a^b,a^sigma,a^h) on R x R x L2(nu);
 (b) the pointwise minimiser is a* = (-beta1 y, -beta1 z, -beta1 u): H(a*) <= H(a) for all a (and, by strict
     convexity, the unique minimiser: H(a*) < H(a) for a != a*).
The jump pairing is the L2(nu) inner product <h_c + a^h, u>. Quantifiers: for all beta1>0, beta2 (>0),
sigma_c, h_c, all points (x,y,z,u). The consequence via the maximum principle [TangLi] (closed-loop system
= (1.1) with the affine coefficients) is a cited argument, not part of this clause. A statement giving only
"a* minimises" without strict convexity/uniqueness would be narrower than "(strictly convex) with pointwise
minimiser"; I would accept minimiser + uniqueness (strict minimality) as capturing strict convexity's role
only if strict convexity is also stated or implied; strict convexity is the printed claim.
Comparison (verdict recorded 2026-10-19T03:29:17Z):
Comparison, ex_concrete_i_ham (Sec5.lean:73-88) vs reading.
- ∀ E, ν (any measure), β1 > 0, β2 ∈ ℝ, σc ∈ R^{1×1}, hc ∈ L²(ν;R), (x,y,z,u) ∈ R×R×R^{1×1}×L²(ν).
  The paper has β2 > 0, ν σ-finite: the Lean drops two unused hypotheses (broader).
- H(a) = ⟨a^b, y⟩ + ⟨σc + a^σ, z⟩ + ∫ ⟨hc(e) + a^h(e), u(e)⟩ dν + β2/2 |x|² + 1/(2β1)(|a^b|² + |a^σ|²
  + ‖a^h‖²): the printed Hamiltonian (the jump pairing as a Bochner integral of representatives; the
  integrand is integrable as a product of L² functions, so it equals ⟨hc + a^h, u⟩_{L²}).
- StrictConvexOn ℝ univ H: strict convexity in the controls on R × R^{1×1} × L²(ν). Matches (a).
- ∀ a, H(-β1 y, -β1 z, -β1 u) ≤ H a: the minimiser. Matches (b); uniqueness follows from strict
  convexity, which is stated.
Verdict: broader (β2 arbitrary real, ν arbitrary).
Witness: —
Verdict: broader — Broader: the hypotheses β2 > 0 and ν σ-finite are dropped (neither is used for convexity or the
minimiser). The printed clause is the instance ν σ-finite, β2 > 0 (with σc ∈ R read as the 1×1 matrix
EuclideanSpace ℝ (Fin 1 × Fin 1), and R as EuclideanSpace ℝ (Fin 1)).
Disagreements with the author's review (shown 2026-10-19T03:29:28Z): none
