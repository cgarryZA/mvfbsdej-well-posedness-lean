### A:ex:expfunc: Dissertation.PaperSpec.A.ex_expfunc
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash ed839d34f480cba1c0ebc41bbfe679cc (pl-fp-v1:3d4ecbb5d8926d5ff6a74a36bf67cd9a917cf8d1926332824b74ea7e267591a6)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T12:20:36Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:19:52Z):
# Reading: ex_expfunc, clause "the expectation-functional class"

Paper (Ex 5.3, first paragraph): phibar : [0,T] x H x H -> R^k measurable and Lipschitz in
(theta, theta') uniformly in t; phi(t, theta, mu) := int_H phibar(t, theta, theta') mu(dtheta').
"At each fixed t and theta this is the Bochner mean of the kernel phibar(t, theta, .), whose
Lipschitz constant is at most Lip(phibar), so (2.10) supplies the law-dependence component of
Assumption 2.3. Its state-variable Lipschitz and integrability requirements are imposed on the
full coefficient system."
Faithful statement:
- Data: T, k, a sigma-finite nu (on countably generated E) defining H with its Hilbert norm;
  phibar measurable with |phibar(t, th1, th1') - phibar(t, th2, th2')| <= L (|th1 - th2|_H +
  |th1' - th2'|_H) for all t, (or any equivalent Lipschitz formulation on H x H with constant
  L = Lip(phibar)).
- Conclusions: (i) phi(t, theta, mu) is well defined (phibar(t, theta, .) is Bochner integrable
  w.r.t. every mu in P_2(H), by linear growth); (ii) the law-dependence bound
  |phi(t, theta, mu) - phi(t, theta, mu')| <= L W_2(mu, mu') for all t, theta, mu, mu' in P_2(H),
  W_2 the Hilbert-norm Wasserstein distance; possibly (iii) the joint bound
  |phi(t, th, mu) - phi(t, th', mu')| <= L (|th - th'|_H + W_2(mu, mu')).
- Not part of the claim: the full Assumption 2.3 / 2.2 (explicitly left to the full coefficient
  system), measurability of phi.
- Hypothesis must be satisfiable (e.g. phibar = 0 or linear) -- trivial.
Comparison (verdict recorded 2026-10-17T12:20:20Z):
# Comparison: ex_expfunc

Lean (Sec5.lean:351): for every sigma-finite nu on a countably generated E, n, m, d, k, every
phibar : R -> H -> H -> R^k jointly measurable with
|phibar(t, th1, th1') - phibar(t, th2, th2')| <= L (|th1 - th2|_H + |th1' - th2'|_H) for all t in R
(|.|_H the Hilbert norm via toL2), L >= 0: for every t, theta, (i) phibar(t, theta, .) is
L-Lipschitz, and (ii) for all mu, mu' in P_2(H): |int phibar(t, theta, .) dmu -
int phibar(t, theta, .) dmu'| <= L w2H(mu, mu').

Against my reading:
- (ii) is the law-dependence component of Assumption 2.3 via (2.10), with W_2 the Hilbert-norm
  W_2: yes. (i) "whose Lipschitz constant is at most Lip(phibar)": yes.
- The integrals are Bochner integrals; integrability is not stated, but phibar(t, theta, .) is
  measurable (sections of a jointly measurable map) and of linear growth (L-Lipschitz), so it is
  integrable for every mu in P_2(H); the inequality is about genuine means, not junk zeros.
- Domain of time: phibar is defined on R x H x H with the Lipschitz bound for every real t,
  whereas the paper has [0,T]. Any paper kernel on [0,T] extends (e.g. by 0 outside [0,T]) to
  one meeting the Lean hypotheses, and the conclusion at t in [0,T] concerns the original kernel;
  so the hypothesis "for all t in R" is not a restriction. Representation choice.
- The joint (theta, mu) bound and Assumption 2.3/2.2 in full are not stated; the paper leaves the
  state-variable and integrability requirements to the full coefficient system.
- Dimensions n, m, d, k arbitrary (paper: general H). Non-vacuity: witness
  ex_expfunc_hypotheses gives phibar(t, th, th') = x - x' with L = 1 on nu = dirac 0.

Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless:
1. The kernel phibar is a function on R x H x H, with the uniform Lipschitz bound required for
   every real t rather than t in [0,T]; a kernel on [0,T] extends (by 0, or by clamping t)
   to one satisfying the hypotheses, and the conclusion at t in [0,T] is about the original
   kernel.
2. "Lipschitz in (theta, theta')" is taken in the sum-of-Hilbert-norms form
   |th1 - th2|_H + |th1' - th2'|_H, the form the example itself uses later; any equivalent
   Lipschitz formulation changes only the constant.
3. The Bochner integrability of phibar(t, theta, .) under mu in P_2(H) is not stated (it holds by
   measurability and linear growth), so the inequality is between genuine means.
Disagreements with the author's review (shown 2026-10-17T12:20:20Z): Agreement on the correspondence for ex_expfunc; verdict class agrees (faithful with
representation choices). Two small points:
1. The author's verdict line calls all three propositions "broader than printed"; for
   ex_expfunc I see no broadening in substance: it assumes the measurability and the uniform
   Lipschitz bound the example assumes, and does not drop any printed hypothesis (the dropped
   origin-integrability / Borel conditions concern ex_expfunc_limin and ex_expfunc_jump).
2. A representation choice the author does not mention: phibar is defined on R x H x H with the
   Lipschitz bound for every real t, not on [0,T]; harmless since a kernel on [0,T] extends
   (e.g. by 0) to one satisfying the hypotheses.
