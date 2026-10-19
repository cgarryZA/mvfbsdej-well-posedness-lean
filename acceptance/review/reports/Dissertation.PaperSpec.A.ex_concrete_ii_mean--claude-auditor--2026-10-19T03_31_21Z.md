### A:ex:concrete: Dissertation.PaperSpec.A.ex_concrete_ii_mean
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba1adb40add6e4f8112 (pl-fp-v1:34ddf4bc033fa61ac98044ebade2bbc057a9826cd7affde3bad67b959eea9ea6)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:31:21Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:16:07Z):
Reading of spec ex_concrete_ii_mean (Example 5.1(ii), clause "the mean and the barycentre"), sections/05-examples.tex:112-148.

Setting: n=m=d=1, so H = R x R x R^{1x1} x L^2(nu;R), with the Hilbert (l2-product) norm
|theta|_H^2 = |x|^2+|y|^2+|z|_F^2+||u||^2_{L2(nu)}; nu sigma-finite on a countably generated (E,calE),
arbitrary activity (nu(E)=infinity allowed). P_2(H), P_2(R) with W_2 built from those Euclidean/Hilbert norms.

Notions: m_Psi(mu) = int_H pi_Psi(theta) mu(dtheta) (Bochner, Psi in {X,Y,Z,U}; m_U(mu) in L2(nu));
b(rho) = int_{R^n} x rho(dx); delta m = int theta dmu - int theta dmu' = (delta m_X,...,delta m_U) in H.

What the clause claims (the mean and barycentre part of (ii)):
 (a) for all mu,mu' in P_2(H): |delta m|_H <= W_2(mu,mu')  (lipfun with the identity map);
 (b) for all rho,rho' in P_2(R^n) (n=1): |b(rho)-b(rho')| <= W_2(rho,rho');
 (c) |delta m_X|+|delta m_Y|+|delta m_Z|_F+||delta m_U|| <= 2|delta m|_H <= 2 W_2(mu,mu')
     (Cauchy-Schwarz over four coordinates).
 Possibly also (d) along a diagonal input, m_Psi(Law Theta) = E Psi (Bochner expectation), delta m_Psi = E delta Psi.
A faithful statement must contain at least (a)/(c) and (b), universally quantified over the measures (free
measures in P_2, no diagonal restriction needed), with the paper's norms (l2 product on H, Frobenius on z,
L2(nu) on u), for arbitrary sigma-finite nu. Constants are the absolute 1 and 2. A version with only part of
(a)-(c) would be narrower than the clause; a version over arbitrary dimensions n,m,d would be broader (fine,
instantiate n=m=d=1).
Hypotheses: none beyond the setting (no Lipschitz / monotonicity hypotheses). No witness needed.
Comparison (verdict recorded 2026-10-19T03:29:17Z):
Comparison, ex_concrete_ii_mean (Sec5.lean:226-242) against my locked reading.
- Setting: ∀ E, ν σ-finite, E countably generated; H = TupleH ν 1 1 1 (n=m=d=1). Matches.
- tupleMean μ = ∫ θ ∂μ.law (Bochner in TupleH); first conjunct states its four channels are the marginal
  means ∫θ.1, ∫θ.2.1, ∫θ.2.2.1, ∫θ.2.2.2 (m_X, m_Y, m_Z, m_U; m_U a Bochner mean in L2(ν)). This is the
  paper's identification δm = (δm_X,...,δm_U) = ∫θdμ - ∫θdμ'. Matches (d) partly (law-level identity).
- ‖toL2(tupleMean μ - tupleMean μ')‖ ≤ w2H μ μ': |δm|_H ≤ W2(μ,μ') with toL2 the Hilbert norm
  (norm_toL2_sq: |toL2 θ|^2 = sum of channel squares) and w2H the W2 of the Hilbert norm. Matches (a).
- sum of channel norms of δm ≤ 2 |δm|_H: matches the first inequality of (c); combined with (a) gives
  ≤ 2 W2. Channel norms: Euclidean on R^1, Euclidean on Fin 1 × Fin 1 (= Frobenius), L2(ν) norm. Matches.
- ∀ ρ ρ' ∈ P2(EuclideanSpace ℝ (Fin 1)): ‖b(ρ) - b(ρ')‖ ≤ w2P ρ ρ' (Euclidean W2 on R^1). Matches (b).
- Free measures, no hypotheses: matches. Constants 1, 2: match.
- Not covered: the diagonal identity m_Ψ(Law Θ) = E Ψ (my optional (d)); the clause title "the mean and
  the barycentre" is adequately covered by the Lipschitz bounds and the channel identification; the
  diagonal identity is used in the pairing clause, not this one.
Definitions checked: P2 (probability measure with finite second moment), w2/w2sq (inf over couplings of
∫‖x-y‖^2, sqrt of toReal; finite on P2), w2H (w2 of the images under toL2), TupleH (max-norm product;
Hilbert norm only via toL2), barycentre, tupleMean: all as the paper's notions.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices: (1) H is realised as the product TupleH with the max of the channel norms; the
paper's Hilbert norm |.|_H enters explicitly through toL2 (|toL2 θ|^2 = |x|^2+|y|^2+|z|_F^2+||u||^2), and
the paper's W2 on P2(H) is w2H (the W2 of the toL2 images); the statement uses exactly those, so the
inequalities are the paper's. (2) R and R^{1x1} are EuclideanSpace ℝ (Fin 1) and EuclideanSpace ℝ
(Fin 1 × Fin 1) (Euclidean/Frobenius norms). (3) The mean is a Bochner integral in TupleH, equal to the
tuple of marginal Bochner means (stated as the first conjunct); Bochner junk is irrelevant on P2.
Disagreements with the author's review (shown 2026-10-19T03:29:27Z): No disagreement on substance. Label only: the review records "faithful"; I record "faithful with
representation choices", because the statement realises H as the max-norm product TupleH and obtains the
paper's Hilbert norm and W2 only through toL2 and w2H (and R as EuclideanSpace ℝ (Fin 1)). The
statement uses exactly those, so the inequalities are the paper's.
