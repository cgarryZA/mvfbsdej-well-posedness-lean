### A:cor:robust: Dissertation.PaperSpec.A.cor_robust_lip
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba14b18016daa0b4aac (pl-fp-v1:1c0b2472fa7cc5475eff926b5def78c0b27cea2a6819205588ff76fccf6024ec)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:34:13Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:16:14Z):
Reading of spec cor_robust_lip: Corollary 3.6, last paragraph and its proof (03-main-results.tex:
227-233, 259-276): "(3.5) gives (3.4) with c_pert = ||G|| L_p".

Paper claim. Setting of Corollary 3.6: m = n, G in R^{m x n} full rank with operator norm ||G||,
perturbations p_b, p_sigma, p_h, p_f : [0,T] x H x P_2(H) -> R^n, R^{n x d}, L^2(nu;R^n), R^m,
independent of theta (p_psi(t,theta,mu) = p_psi(t,mu)). Hypothesis (3.5): for a.e. t in [0,T] and
all diagonal inputs (Theta,mu),(Theta',mu') in D_t,
 |delta p_b| + |delta p_sigma|_F + ||delta p_h||_{L^2(nu)} + |delta p_f| <= L_p W_2(mu,mu')
(deterministic, since independent of theta). Conclusion (3.4) with c_pert = ||G|| L_p: for a.e. t
and all diagonal inputs,
 E[<delta p_b, G^T dY> + <delta p_sigma, G^T dZ>_F + <-delta p_f, G dX>
   + int_E <delta p_h(e), G^T dU(e)> nu(de)] <= ||G|| L_p E[|dX|^2 + |dY|^2 + |dZ|_F^2 + ||dU||^2].
A faithful formal statement must contain: theta-independence; (3.5) along diagonal inputs a.e. t;
conclusion (3.4) a.e. t for all diagonal inputs with the exact constant ||G|| L_p, ||G|| the
operator (spectral) norm (a Frobenius norm would weaken the constant - a different claim);
L_p >= 0. m = n may be dropped (broader; the instantiation m = n gives the printed claim). The
other hypotheses of Corollary 3.6 (baseline assumptions, origin-integrability, diagonal Lipschitz of
the perturbations) are not needed; including them makes it narrower only formally (they are the
corollary's standing hypotheses, so including them is still faithful to the printed clause).
The stochastic setting: the sec. 2 basis, D_t over F_t-measurable L^2 tuples, U-component in
L^2(nu;R^m), the h-pairing int_E <., G^T .> nu(de) = L^2(nu) inner product.
Comparison (verdict recorded 2026-10-19T03:32:34Z):
Comparison, cor_robust_lip (Sec3.lean:240-250).

- Setting: any probability space with any filtration F (the sec. 2 one is an instance), nu
  sigma-finite on countably generated E, n >= 1, T > 0, m = n (p : Coeffs nu n n d, G : n x n),
  any G (full rank not required), any L_p.
- p.TupleIndep: p_b, p_sigma, p_h, p_f independent of theta. OK.
- LawLip35 F P T L_p p: for a.e. t in [0,T], for all diagonal inputs, a.s.
  |dp_b| + |dp_sigma|_F + ||dp_h||_{L^2(nu)} + |dp_f| <= L_p w2H(mu,mu') - (3.5) with the Hilbert-norm
  W_2. (a.s. is harmless: the differences are deterministic.)
- Conclusion PairingBound34 F P T G (||GX G|| * L_p) p: for a.e. t, all diagonal inputs, the
  pairing27 of p (<dp_b, G^T dY> + <dp_sigma, G^T dZ>_F + <-dp_f, G dX> + int_E <dp_h(e), G^T dU(e)>
  nu(de)) is integrable and its expectation is <= c E[|dX|^2 + |dY|^2 + |dZ|_F^2 + ||dU||^2] with
  c = ||GX G|| L_p; ||GX G|| is the operator norm of the continuous linear map x |-> Gx on Euclidean
  space = the spectral norm ||G|| of the paper. (3.4) exactly, with the printed constant.
- The other hypotheses of Corollary 3.6 (baseline assumptions, perturbation origin integrability and
  Lipschitz) are not needed and absent: broader.
- Witness cor_robust_lip_hypotheses: constant p_sigma (so dp = 0) with L_p = 1 - satisfiable,
  though a degenerate (law-free) instance; nonvacuity is clear anyway (e.g. p_b(t,mu) = a
  Lipschitz function of the mean).
Verdict: broader.
Witness: —
Verdict: broader — Broader: any filtered probability space (not only the sec. 2 basis), any square G (full rank not
required), and none of Corollary 3.6's other hypotheses (baseline Assumptions 2.2-2.5 with margin,
origin integrability and diagonal Lipschitz of the perturbations), which the implication does not
use. Instantiation giving the printed clause: the sec. 2 filtration enlJoint of a Levy driver,
m = n, G of full rank, p the perturbations of Corollary 3.6 satisfying its hypotheses; then
(3.5) with L_p and theta-independence give (3.4) with c_pert = ||G|| L_p, ||G|| the operator norm
(||GX G||). Note: the witness is a constant perturbation (dp = 0), a degenerate but valid instance.
Disagreements with the author's review (shown 2026-10-19T03:32:45Z): Verdict agrees (broader), same instantiation. One addition: the witness cor_robust_lip_hypotheses
is a constant perturbation (p_sigma constant, so every difference dp is 0 and (3.5) holds with
L_p = 1 trivially). It establishes that the hypotheses can be met, but only by a degenerate,
law-free instance; an instance with genuinely law-dependent p (e.g. a Lipschitz function of the
mean) would match the corollary's intent better. Not a defect of the proposition, whose hypotheses
are evidently satisfiable.
