### A:ex:expfunc, A:intro:limin-comparison: Dissertation.PaperSpec.A.ex_expfunc_limin
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash ed839d34f480cba1dc8d682dbdc81fa7 (pl-fp-v1:1e1ab0c67785fa52b5a1f9bef7131e316e50d1d128573afa2898409a304bec5e)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T16:03:52Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T15:47:46Z):
Reading of spec ex_expfunc_limin (Example 5.3: "This class contains the deterministic-
coefficient, finite-activity independent-copy interactions of [LiMin]... The pointwise-jump form
embeds via phibar(t,theta,theta') = int_E psibar(t,x,y,z,u(e),x',y',z',u'(e)) nu(de). The
integral is finite at every (theta,theta')...; the same bounds give, with a constant finite when
nu(E) < infinity, |phibar(t,th1,th1') - phibar(t,th2,th2')| <= Lip(psibar) max{nu(E),
nu(E)^{1/2}} (|th1-th2|_H + |th1'-th2'|_H), so phibar is Lipschitz on H x H. ... well defined
on equivalence classes"; plus the introduction's "Example 5.3 details the embedding of their
interaction class").

Setting: finite nu (nu(E) < infinity), standing H with dimensions n, m, d; psibar : [0,T] x
R^n x R^m x R^{m x d} x R^m x R^n x R^m x R^{m x d} x R^m -> R^k measurable, Lipschitz in all
arguments except t with constant Lip(psibar) uniform in t, psibar(., 0,...,0) in L^2(0,T).
Conclusions:
 1. for every (t, theta, theta'), e |-> psibar(t,x,y,z,u(e),x',y',z',u'(e)) is nu-integrable,
    so phibar is finite (well defined), and phibar depends only on the L^2(nu) classes of
    u, u';
 2. phibar is Lipschitz on H x H, uniformly in t, with constant Lip(psibar) max{nu(E),
    nu(E)^{1/2}} (in the printed (|.|_H + |.|_H) form); the constant depends only on
    Lip(psibar) and nu(E) (finite);
 3. (embedding) phibar is a kernel of the Example 5.3 class: measurable, Lipschitz in
    (theta, theta') uniformly in t; so phi(t,theta,mu) = int phibar(t,theta,.) dmu is W_2-
    Lipschitz by (2.10); origin: phibar(t,0,0) = nu(E) psibar(t,0,...,0) in L^2(0,T).
The printed constant depends on the convention for "Lipschitz in all arguments" of psibar
(sum of component norms vs Euclidean norm of the concatenation); under the sum convention the
bound has the extra factor from |dx|+|dy|+|dz|_F+|du| <= 2|dtheta|_H, so the printed
constant may be off by a factor up to 2 (or sqrt 2). A faithful statement should state
Lipschitz-ness with a constant depending only on Lip(psibar), nu(E); if it states the printed
constant, the convention must make it true. Hypothesis nu(E) < infinity is essential (infinite
nu breaks finiteness unless psibar(t,0..0)=0 etc.), and must be present.
Comparison (verdict recorded 2026-10-17T16:01:29Z):
Comparison, ex_expfunc_limin (Sec5.lean:368-400).
Setting: nu finite (IsFiniteMeasure) - the printed finite-activity class; n m d k; psibar :
R -> B -> B -> R^k, Lip >= 0, Lipschitz as |psi(t,a,a') - psi(t,b,b')| <= Lip (|a-b|_2 +
|a'-b'|_2) with |.|_2 the Euclidean norm of the block (x,y,z,u(e)) - a precise convention for
"Lipschitz in all arguments except t, uniformly in t". Under this convention the printed constant
is exact: int sqrt(A + |du(e)|^2) dnu <= nu(E)^{1/2} (A nu(E) + |du|^2)^{1/2} <= max(nu(E),
nu(E)^{1/2}) |dtheta|_H.
Conclusions for every t: (1) the integrand e |-> psi(t, x,y,z,u(e), x',y',z',u'(e)) is nu-
integrable for all theta, theta' (finite phibar); (2) |phibar(t,th1,th1') - phibar(t,th2,th2')|
<= Lip max(nu(E), sqrt nu(E)) (|th1-th2|_H + |th1'-th2'|_H) with the Hilbert norm (toL2) - the
printed constant; (3) phibar unchanged when u, u' change on nu-null sets. All three printed
conclusions present.
Differences: the origin-integrability hypothesis psibar(., 0,...,0) in L^2(0,T) and
measurability of psibar are not assumed (unused by the three conclusions; broader); t in R;
the "embedding" consequences not spelled out (phibar measurable in t, phibar(t,0,0) = nu(E)
psibar(t,0) in L^2(0,T)) - the passage does not assert them as separate conclusions.
Instantiation: the paper's psibar (Lipschitz in the block-Euclidean sense, with L^2 origin
values) is an instance; the conclusions are the printed ones.
Representation choice: the Lipschitz convention (sum of the Euclidean norms of the two argument
blocks), the one under which the printed constant is correct.
Witness ex_expfunc_limin_hypotheses: psibar = x - x' at nu = delta_0 - fine.
Verdict: broader (with the representation choice of the Lipschitz convention).
Witness: —
Verdict: broader — Broader than printed, with one representation choice. The Lean drops the printed hypothesis
psibar(., 0, ..., 0) in L^2(0,T) (and any measurability of psibar in t), which none of its three
conclusions (finiteness, the Lipschitz bound with constant Lip max{nu(E), nu(E)^{1/2}}, class
independence) uses, and lets t range over R. Instantiation: the paper's finite-activity Li-Min
kernel psibar, Lipschitz with constant Lip in the block-Euclidean sense and with L^2 origin
values, is an instance and the conclusions are the printed ones. Representation choice: "Lipschitz
in all arguments except t" is fixed as |psi(t,a,a') - psi(t,b,b')| <= Lip(|a-b| + |a'-b'|) with
Euclidean norms of the blocks (x,y,z,u(e)); under it the printed constant is exact (Cauchy-Schwarz
gives int sqrt(A + |du(e)|^2) dnu <= max{nu(E), nu(E)^{1/2}} |dtheta|_H).
Disagreements with the author's review (shown 2026-10-17T16:01:36Z): The author's review recorded for this unit is empty (its text is attached to an adjacent review marker of a unit outside this chunk and was not shown), so there is nothing to compare point by point. My verdict: broader - the proposition drops the printed origin integrability psibar(.,0,...,0) in L^2(0,T) (unused), and fixes the Lipschitz convention as the sum of the Euclidean norms of the two argument blocks, under which the printed constant Lip max{nu(E), nu(E)^{1/2}} is exact.
