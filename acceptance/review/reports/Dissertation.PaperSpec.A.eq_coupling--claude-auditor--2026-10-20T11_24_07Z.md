### A:rem:wasserstein-bounds, A:rem:freelaw, A:lemA1:polish: Dissertation.PaperSpec.A.eq_coupling
Pins: manuscript A None; project d3e594defeeeb94a6d05c33c666bcb870d584302; hash ed839d34f480cba17af7c36ae6c33114 (pl-fp-v1:c06c57a8182b802f4febab5ebac000d011c3ca6dba4ea3d8ef4bffca45217da2)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-20T11:24:07Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-20T11:09:24Z):
# Reading: eq_coupling — (2.8) of Remark 2.6 (also used by Remark 5.6 and Lemma A.1 step 2)

Passage (02-model-assumptions.tex, Remark 2.6; 05-examples.tex Remark 5.6; 09-appendix.tex Lemma A.1 step 2).

Setting. A probability space (Omega, F, P) (the standing one; F_t-measurability is irrelevant to
the bound, so a statement over any probability space and any sigma-algebra is a harmless
broadening). H = R^n x R^m x R^{m x d} x L^2(nu; R^m) with the HILBERT (sum of squares) norm
|theta|_H^2 = |x|^2 + |y|^2 + |z|_F^2 + ||u||_{L^2(nu)}^2, where |.| is Euclidean on R^j,
|.|_F is Frobenius on matrices and the L^2(nu) norm uses the Euclidean norm on R^m pointwise.
W_2 on P_2(H) is the Kantorovich infimum over couplings of the squared H-distance, square-rooted
(Villani Def. 6.1).

Hypotheses. Theta, Theta' : Omega -> H two (strongly) measurable, square-integrable random
tuples (Theta in L^2(Omega, F_t; H)); mu = Law(Theta), mu' = Law(Theta') (both in P_2(H)).

Conclusion. W_2(mu, mu')^2 <= E[ |dX|^2 + |dY|^2 + |dZ|_F^2 + ||dU||^2 ] = E |Theta - Theta'|_H^2.
Equivalently (Lemma A.1 / Remark 5.6 clause): the law map L^2(Omega; H) -> (P_2(H), W_2) is
1-Lipschitz.

No constants. Quantifiers: for all Theta, Theta' (in L^2), the inequality.

What a faithful Lean statement must get right:
- the norm on H must be the l2-product norm (Lean's default product norm is the sup norm; a sup
  norm would change W_2 and the right-hand side), the matrix norm Frobenius, R^m Euclidean
  inside L^2(nu);
- the expectation must not be a Bochner integral that collapses to 0 when not integrable unless
  square-integrability is a hypothesis; Law = pushforward needs (AE-)measurability of Theta;
- W_2 must be the genuine coupling infimum on P_2(H) (any junk value of a total W_2 for
  measures outside P_2 must not be reachable under the hypotheses).
A broader statement (any probability space, any measurable square-integrable pair, no
F_t-measurability) is acceptable: the printed claim is the instance at the standing space.
Comparison (verdict recorded 2026-10-20T11:23:00Z):
# Decision: spec:Dissertation.PaperSpec.A.eq_coupling (Dissertation/PaperSpec/A/Sec2.lean)

Verdict: broader.

Comparison with the locked reading, item by item.
- Space H. `TupleH ν n m d` (Dissertation/WellPosedness/System/Tuple.lean) is
  `EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m × Fin d) ×
  Lp (EuclideanSpace ℝ (Fin m)) 2 ν`: Euclidean norms on R^n, R^m, the Frobenius norm on R^{m x d}
  (Euclidean on the index pairs), and L^2(ν; R^m) with the Euclidean norm on R^m pointwise, as in
  the paper. The product carries Lean's sup norm, but `w2H` (Dissertation/WellPosedness/System/
  HilbertW2.lean) is the Kantorovich distance of the images under `toL2`, the iterated `WithLp 2`
  product, whose squared norm is |x|^2+|y|^2+|z|_F^2+||u||^2 (`norm_toL2_sq`). So W_2 is the
  paper's W_2 for the Hilbert norm. `P2` membership (finite second moment for the sup norm) is
  equivalent to finite second moment for the Hilbert norm (norms within a factor 2).
- W_2. `w2sq` (Dissertation/Law/Wasserstein.lean) is the infimum over all measures on H x H
  with the two marginals of the lintegral of the squared distance; `w2` is the square root of its
  real part. The junk value (0 when w2sq = infinity) cannot occur on `P2` laws (`w2sq_map_toL2_ne_top`).
- Law. `lawP2 P Θ` (Dissertation/Law/LawP2.lean) is the image measure `P.map Θ` when
  `MemLp Θ 2 P` and a Dirac mass otherwise; the hypotheses `MemLp Θ 2 P`, `MemLp Θ' 2 P` select
  the genuine image laws. MemLp includes a.e.-strong measurability.
- Right-hand side. The Bochner integral of
  ‖δX‖^2 + ‖δY‖^2 + ‖δZ‖^2 + ‖δU‖^2 is genuine: the integrand is integrable under the two MemLp
  hypotheses, so no junk 0 is possible. It is E[|δX|^2+|δY|^2+|δZ|_F^2+||δU||^2] as printed.
- Quantifiers and setting. For every probability space (Ω, P), every σ-finite ν on a countably
  generated mark space (the paper's standing hypotheses on ν), every n, m, d and every pair of
  square-integrable random tuples: W_2(Law Θ, Law Θ')^2 <= E|Θ - Θ'|_H^2. No constants.
This is broader than the printed claim in two harmless ways: the probability space is arbitrary
(not the standing filtered space), and Θ, Θ' need only be square integrable (not F_t-measurable
diagonal inputs). The printed claim is the instance in the detail file. The Lemma A.1 clause
(the law map is 1-Lipschitz from L^2(Ω; H) to (P_2(H), W_2)) is exactly this inequality, since
the L^2(Ω; H) distance is (E|Θ - Θ'|_H^2)^{1/2}. The Remark 5.6 clause ("the W_2 term is dominated
by the synchronous coupling bound (2.8)") is the same inequality.

Current text. The passage read is the one at revision 1f67672 in manuscript/paper (Remark 2.6,
Remark 5.6, Lemma A.1 step 2). I have not seen the earlier text (the brief forbids reading
history), so I cannot say what changed; the proposition states (2.8) as the current Remark 2.6
prints it, and the current Remark 5.6 and Lemma A.1 step 2 use it in exactly this form. Nothing
in the current wording (the synchronous coupling bounding the W_2 infimum of Villani Def. 6.1)
asks for more than this proposition.

Witness. `Dissertation.Acceptance.A.eq_coupling_hypotheses` (Dissertation/Acceptance/A/
WitnessHyp.lean): ν = δ_0 on R (nonzero, σ-finite, countably generated), n = m = d = 1,
Ω = Bool with the uniform law, Θ = 1_{true} θ₁ and Θ' = 1_{false} θ₁ with θ₁ = (1,1,1,1) whose
U-channel is the nonzero constant of L^2(δ_0). Both are in L^2 and not a.s. equal. A genuine
instance with every channel nonzero; it does not live on the paper's Brownian-Poisson basis, which
is irrelevant for this clause.

Coverage (claim A:rem:wasserstein-bounds, clauses (2.8)-(2.11); also A:rem:freelaw and
A:lemA1:polish, which use this proposition). Remark 2.6 asserts (2.8), (2.9) (with the remark
that it is the X-marginal case of (2.8)), the W_2-Lipschitz property of mu |-> int phibar dmu with
the same constant (2.10), and the 1-Lipschitz property of marginal projection onto the U-marginal
(2.11) including that mu^U is in P_2(L^2(ν)); the four clauses state all of these. The only
further mathematical content is the existence of an optimal coupling used inside the printed
chains of (2.10) and (2.11), a cited proof device (Villani) rather than a claim of the remark; no
clause states anything the passage does not claim. The hypotheses in force (ν σ-finite on a
countably generated space, square-integrable tuples on one probability space) are the ones used.
Witness: —
Verdict: broader — Broader than the printed claim: the proposition holds over every probability space and every
pair of square-integrable random tuples. The printed (2.8) is the instance Ω = the standing
space with P, ν the standing intensity, and Θ, Θ' two diagonal inputs at time t (strongly
F_t-measurable, square integrable, hence MemLp Θ 2 P); then lawP2 P Θ = Law(Θ) = μ,
lawP2 P Θ' = μ', and w2H is the paper's W_2 on P_2(H), so the conclusion reads
W_2(μ, μ')^2 <= E[|δX|^2 + |δY|^2 + |δZ|_F^2 + ||δU||^2]. The Lemma A.1 / Remark 5.6 clauses are
the same inequality (the law map is 1-Lipschitz from L^2(Ω; H)).
Disagreements with the author's review (shown 2026-10-20T11:23:13Z): Disagreement in the verdict label only. The earlier review (against the earlier text) records
"faithful with representation choices"; I record "broader", because the proposition quantifies
over every probability space and every pair of square-integrable random tuples, not only over
pairs of F_t-measurable diagonal inputs on the standing basis, and the printed (2.8) is an
instance of it. I see no substantive disagreement: both readings find that the norms on H, the
W_2 of the Hilbert norm (`w2H`), the laws (`lawP2` under MemLp) and the genuine Bochner expectation
match the current Remark 2.6, and that the Lemma A.1 and Remark 5.6 clauses are this inequality.
