### A:ex:expfunc, A:intro:limin-comparison: Dissertation.PaperSpec.A.ex_expfunc_limin
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba1dc8d682dbdc81fa7 (pl-fp-v1:1e1ab0c67785fa52b5a1f9bef7131e316e50d1d128573afa2898409a304bec5e)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:34:13Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:16:14Z):
Reading of spec ex_expfunc_limin: Example 5.3, second and third paragraphs (05-examples.tex:223-271),
and the intro's "Example 5.3 details the embedding of their interaction class".

Paper claim. Finite activity nu(E) < infinity. Let psibar : [0,T] x (R^n x R^m x R^{m x d} x R^m)^2
-> R^k be Lipschitz in all arguments except t, constant Lip(psibar) uniform in t, w.r.t. the
Euclidean norm on each argument block a = (x,y,z,u(e)), a' = (x',y',z',u'(e)), i.e.
|psibar(t,a1,a1') - psibar(t,a2,a2')| <= Lip (|a1-a2| + |a1'-a2'|); measurable; with
psibar(.,0,...,0) in L^2(0,T). Then
 phibar(t,theta,theta') := int_E psibar(t,x,y,z,u(e),x',y',z',u'(e)) nu(de)
(1) is finite (integrable in e) at every (theta,theta') in H x H;
(2) is well defined on equivalence classes (changing u, u' on nu-null sets does not change it);
(3) satisfies |phibar(t,th1,th1') - phibar(t,th2,th2')|
      <= Lip(psibar) max{nu(E), nu(E)^{1/2}} (|th1-th2|_H + |th1'-th2'|_H)
  (correct with the block-Euclidean Lipschitz norm via Cauchy-Schwarz in L^2(nu)), so phibar is
  Lipschitz on H x H and the first paragraph (ex_expfunc) applies;
(4) for the jump coefficient: the Nemytskii map [H_t(theta,theta')](e) = hbar(t,x,y,z,u(e),
  x',y',z',u'(e),e) is well defined on classes; ASSUMING it is jointly Borel, Lipschitz into
  L^2(nu;R^n) with constant C and int_0^T ||H_t(0,0)||^2 dt < inf, (2.10) applies with K = L^2(nu;R^n)
  to h(t,theta,mu) = int_H H_t(theta,theta') mu(dtheta'): ||h(t,theta,mu) - h(t,theta,mu')|| <= C W_2.
A faithful formal statement must contain at least (1)-(3) for the drift/diffusion/driver kernels
(the clause is "the kernels of independent-copy interactions"), with nu finite as a hypothesis,
the stated constant (or a statement with the exact constant; a mere "exists a constant" loses the
printed constant and is narrower in conclusion), the H-norm |theta|_H = sqrt(|x|^2+|y|^2+|z|_F^2
+ ||u||^2), and (2) if the formalisation works on representatives. (4) may be in a separate clause.
The "embedding" claim: the resulting phi (Bochner mean of phibar) is of the ex_expfunc class.
Comparison (verdict recorded 2026-10-19T03:32:34Z):
Comparison, ex_expfunc_limin (Sec5.lean:367-399).

- nu finite (IsFiniteMeasure): the finite-activity hypothesis. OK.
- psibar : R -> B -> B -> R^k, B = R^n x R^m x R^{m x d} x R^m; hypothesis: for all t, a, a', b, b',
  |psibar t a a' - psibar t b b'| <= Lip (|a - b|_2 + |a' - b'|_2) with |.|_2 the Euclidean norm of
  each block (sqrt of the sum of the four squared channel norms): "Lipschitz in all arguments except
  t, constant uniform in t, Euclidean norm on each argument block". OK.
- Hypotheses NOT present: measurability of psibar, psibar(.,0,...,0) in L^2(0,T). Neither is used
  by the three conclusions (for fixed t, psibar t is continuous, so the composition with a measurable
  representative is measurable). Dropping them makes the statement broader.
- Conclusions, for every t: (1) e |-> psibar(t,(x,y,z,u(e)),(x',y',z',u'(e))) is nu-integrable for all
  theta, theta' (finite at every pair); (2) the Lipschitz bound with constant
  Lip * max(nu(E), nu(E)^{1/2}) in the Hilbert norm |.|_H (toL2) - the printed constant; (3) changing
  u, u' on nu-null sets does not change phibar (well-defined on classes). These are (1)-(3) of my
  reading, with the exact constant.
- (4) (the Nemytskii jump map) is the separate clause ex_expfunc_jump - not required here.
- "Embedding of their interaction class" (intro clause): phibar Lipschitz on H x H is the input of
  the first paragraph (ex_expfunc); measurability of phibar in t is not shown here (no measurability
  hypothesis), so the full hypothesis set of ex_expfunc is not produced - but the paper's text only
  claims the finiteness, class-independence and the Lipschitz bound, which is what is stated.
- Witness ex_expfunc_limin_hypotheses: nu = delta_0, psibar = x - x', Lip = 1.
Verdict: broader.
Witness: —
Verdict: broader — Broader than the printed claim: it drops the hypotheses that psibar is measurable and that its
origin values are square integrable in time, and lets t range over R; neither is used for the
finiteness, class-independence and Lipschitz statements. Instantiation giving the printed claim:
take a measurable kernel psibar on [0,T] with psibar(.,0,...,0) in L^2(0,T), Lipschitz in the
block-Euclidean norms uniformly in t (extended by 0 outside [0,T]), and nu finite; the conclusions
(1) finiteness at every (theta,theta'), (2) the bound with constant Lip(psibar) max{nu(E),
nu(E)^{1/2}} in |.|_H, (3) independence of the representatives of u, u' are then the printed ones.
Disagreements with the author's review (shown 2026-10-19T03:32:45Z): none
