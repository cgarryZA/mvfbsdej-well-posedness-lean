### A:ex:expfunc, A:sec5:overview: Dissertation.PaperSpec.A.ex_expfunc
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba1c0ebc41bbfe679cc (pl-fp-v1:3d4ecbb5d8926d5ff6a74a36bf67cd9a917cf8d1926332824b74ea7e267591a6)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:34:12Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:16:12Z):
Reading of spec ex_expfunc: Example 5.3 first paragraph (05-examples.tex:211-221) and the sec. 5
overview "Example 5.3 recovers the expectation-functional subclass".

Paper claim. Let phibar : [0,T] x H x H -> R^k be measurable and Lipschitz in (theta,theta')
uniformly in t (one constant Lip(phibar) for all t). Set
phi(t,theta,mu) := int_H phibar(t,theta,theta') mu(dtheta'), mu in P_2(H). At each fixed t,
theta this is the Bochner mean of theta' |-> phibar(t,theta,theta') (Lipschitz with constant
<= Lip(phibar)), so (2.10) gives the law-dependence component of Assumption 2.3:
|phi(t,theta,mu) - phi(t,theta,mu')| <= Lip(phibar) W_2(mu,mu') for all t, theta, mu, mu' in
P_2(H). The state-variable Lipschitz and integrability requirements are NOT claimed (imposed on
the full coefficient system).

A faithful formal statement must contain:
- H the paper's Hilbert space (R^n x R^m x R^{m x d} x L^2(nu;R^m)); a statement over a general
  separable Hilbert (or normed) space in place of H, or a separable Hilbert K in place of R^k,
  is broader with instantiation H, K = R^k.
- Hypotheses: phibar measurable (needed for the integral), and a single constant L >= 0 with
  |phibar(t,th1,th1') - phibar(t,th2,th2')| <= L (|th1-th2| + |th1'-th2'|) (or any product
  norm whose restriction to the theta' slot gives constant <= L) for all t.
- Conclusion: for every t in [0,T], theta in H, mu, mu' in P_2(H): theta' |-> phibar is
  mu-integrable (well-definedness of the Bochner mean) and
  |phi(t,theta,mu) - phi(t,theta,mu')| <= L * W_2(mu,mu'), W_2 the quadratic Wasserstein
  distance (infimum over couplings of (int |theta-theta'|^2 dpi)^{1/2}).
- Possibly additionally: phi as a coefficient satisfies the law component of the diagonal
  Lipschitz bound along diagonal inputs (weaker, implied).
- The constant must be the Lipschitz constant of phibar, not a larger constant.
- Measures in P_2(H): probability measures with finite second moment; junk values of Bochner
  integrals for non-integrable kernels must not be exploited (integrability holds for P_2 laws).
Comparison (verdict recorded 2026-10-19T03:32:32Z):
Comparison, ex_expfunc (Sec5.lean:349-365) against my locked reading.

- Space: H is TupleH nu n m d (product of R^n, R^m, R^{m x d} Frobenius, L^2(nu;R^m)); the Lipschitz
  hypothesis and W_2 use the Hilbert norm through toL2 (|toL2 theta|^2 = |x|^2+|y|^2+|z|_F^2+||u||^2)
  and w2H (W_2 of the images under toL2) - the paper's norm and the paper's W_2. P2 (TupleH) is the
  set of probability laws with finite second moment (max norm; equivalent finiteness).
- Hypotheses: phibar : R -> H -> H -> R^k, jointly measurable on R x H x H; L >= 0 with
  |phibar(t,th1,th1') - phibar(t,th2,th2')| <= L(|th1-th2|_H + |th1'-th2'|_H) for all t: Lipschitz
  in (theta,theta') uniformly in t, the sum product norm as in my reading. t ranges over R instead
  of [0,T]: a phibar on [0,T] extends (e.g. by 0) without losing measurability or the bound.
- Conclusion, for every t, theta: (a) theta' |-> phibar(t,theta,theta') is L-Lipschitz (the
  "kernel has Lipschitz constant at most Lip(phibar)" sentence) and (b) for all mu, mu' in P_2(H),
  |int phibar(t,theta,.) dmu - int phibar(t,theta,.) dmu'| <= L W_2(mu,mu'): the law-dependence
  component, constant = the Lipschitz constant. Matches.
- Integrability of the kernel under mu is not stated as a conclusion; it is automatic (continuous
  kernel with linear growth, P_2 law), so the Bochner means are genuine and no junk value is used.
- State-variable Lipschitz/integrability not claimed - correctly absent.
- Witness ex_expfunc_hypotheses: phibar(t,theta,theta') = x - x', L = 1, nu = delta_0; a genuine
  nonzero instance of the class.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless: (1) H is realised as the product TupleH with the max norm,
but the Lipschitz hypothesis and W_2 are those of the Hilbert norm (toL2, w2H), so the inequality is
the paper's; P_2(H) as laws of finite second moment is the same set under either norm. (2) Time
ranges over R rather than [0,T]; a kernel on [0,T] extends by 0 measurably and Lipschitz uniformly,
so the printed claim is the restriction to t in [0,T]. (3) Integrability of theta' |-> phibar under
mu in P_2(H) is not stated, but it holds automatically (Lipschitz => linear growth, P_2 => finite
first moment), so the Bochner means are the paper's and no junk value is involved.
Disagreements with the author's review (shown 2026-10-19T03:32:44Z): none
