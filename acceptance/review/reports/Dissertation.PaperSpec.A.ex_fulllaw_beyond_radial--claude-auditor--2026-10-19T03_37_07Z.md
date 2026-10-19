### A:ex:fulllaw, A:rem:regimes, A:sec5:overview: Dissertation.PaperSpec.A.ex_fulllaw_beyond_radial
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba1fc87ff54d30df5ad (pl-fp-v1:bd2ddc0359d2a5b2d4c03423f40aa608755e4946bbbc872ba727421245fc5f80)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:37:07Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:18:00Z):
Reading of spec:Dissertation.PaperSpec.A.ex_fulllaw_beyond_radial (Example 5.4, 05-examples.tex:301-318;
also Rem 5.7 and the Sec. 5 overview "Example 5.4 then carries the law dependence beyond those
subclasses, to genuinely nonlinear functionals of the full tuple").

Printed claim: "For nonconstant q, q~, q^, the radial statistics lie beyond the expectation and
two-point-kernel jump-integrand interactions of the preceding examples, and beyond the linear
jump-integrand expectations of the cited models." This unit: the radial statistic of the FULL tuple
law, mu -> q(W_2(mu, mu_0)), with q : R_+ -> R bounded, Lipschitz (standing in Ex 5.4) and
nonconstant, mu_0 in P_2(H) arbitrary.

"Expectation functional" (Example 5.3): phi(t,theta,mu) = int_H phibar(t,theta,theta') mu(dtheta')
with phibar measurable, Lipschitz in (theta,theta') uniformly in t (two-point kernels, including the
Nemytskii/jump-integrand forms, and linear functionals of E[U], are all of this type).

A faithful formal statement must contain:
- Setting: H = R^n x R^m x R^{m x d} x L^2(nu;R^m) for the standing nu (any nu; H is never {0}
  since n>=1); P_2(H) with W_2.
- Quantifiers: for every mu_0 in P_2(H) and every bounded Lipschitz nonconstant q on [0,oo)
  (nonconstant on R_+, which is the attained range of W_2(.,mu_0) since translates of mu_0 reach
  every distance); the paper does not restrict mu_0.
- Conclusion: there is NO kernel phibar of the Example 5.3 class with
  q(W_2(mu,mu_0)) = int phibar(theta') mu(dtheta') for all mu in P_2(H) (allowing also t- and
  theta-dependence of phibar is a stronger, still true, form). A statement that excludes all
  measurable integrable kernels (no Lipschitz requirement), or that shows the functional is not
  affine under mixtures, is stronger than (implies) the printed claim and is acceptable.
  (True: mixture-affinity plus boundedness forces q constant: mix mu_0 with a far Dirac of
  mass p, p|theta*|^2 = s fixed, p -> 0.)
- The vector form q(W_2(mu,mu_0)) w_0 times eps in f is the claim only for w_0 != 0, eps > 0; the
  scalar statistic is the natural reading.
- Narrowing to watch for: a specific mu_0 (e.g. delta_0), a specific q, a specific nu, or an
  extra hypothesis that is not in the paper.
Comparison (verdict recorded 2026-10-19T03:34:54Z):
Comparison: spec ex_fulllaw_beyond_radial (PaperSpec/A/Sec5.lean:582-595).
Lean: for every sigma-finite nu on a countably generated E, all n >= 1, m, d, every q : R -> R
Lipschitz (constant Lq) and bounded (B), not constant on [0,oo) (exists a, b >= 0, q a != q b),
every mu0 in P_2(H), and every phi : H -> R integrable against every law of P_2(H): there is
mu in P_2(H) with q(W_2(mu,mu0)) != int phi dmu, W_2 = w2H, the distance of the Hilbert norm
|theta|^2 = |x|^2+|y|^2+|z|_F^2+||u||^2 (System/HilbertW2.lean).
Reading: for all mu0, all bounded Lipschitz nonconstant q on R_+, the full-law radial statistic
mu -> q(W_2(mu,mu0)) is not an Example 5.3 expectation functional (no Lipschitz kernel phibar
with q(W_2(mu,mu0)) = int phibar(t,theta,theta') mu(dtheta') for all mu). A stronger form (no
integrable kernel at all) is acceptable.
- Quantifiers: mu0 arbitrary, q arbitrary in the paper's class (bounded, Lipschitz, nonconstant
  on R_+). H for arbitrary nu (no nu != 0 needed for the full-law statistic), n >= 1 standing.
  Matches, with m, d >= 0 allowed (harmless).
- W_2 is the paper's (Hilbert norm on H), not the max-norm one. Matches.
- Conclusion: excludes every phi that is integrable against all P_2 laws, a class containing every
  Example 5.3 kernel frozen at (t, theta) (Lipschitz implies linear growth, hence integrable
  against P_2 laws). Stronger than printed, hence broader.
- Scalar statistic rather than the vector term eps q(W_2(mu,mu0)) w0 of f: with eps > 0 and
  w0 != 0, a coordinate j with w0_j != 0 reduces the vector claim to the scalar one.
- The clause is in the paper at f598204 ("For nonconstant q, q~, q^, the radial statistics lie
  beyond the expectation and two-point-kernel ... interactions"; Rem 5.7 and the Sec. 5 overview
  speak of genuinely nonlinear functionals of the full tuple). The statement is true: an
  expectation functional is mixture-affine, and mixing mu0 with a far Dirac of mass p, with
  p |theta*|^2 = s fixed and p -> 0, forces a bounded q to be constant.
- Non-vacuous: witness ex_fulllaw_beyond_hypotheses (q = min(|r|,1), phi = 0 integrable).
Verdict: broader.
Witness: —
Verdict: broader — Broader than the printed claim in its conclusion (and slightly in its index set, m, d >= 0 and any
nu). It excludes every phi : H -> R integrable against all laws of P_2(H), not only the kernels
of Example 5.3. Instantiation giving the printed claim: suppose mu -> q(W_2(mu,mu0)) were an
Example 5.3 expectation functional, q(W_2(mu,mu0)) = int phibar(t,theta,theta') mu(dtheta') for
all mu, with phibar measurable and Lipschitz in (theta,theta'). Fix any t and theta and take
phi := phibar(t,theta,.). It is continuous with linear growth, so it is integrable against every
mu in P_2(H). The proposition then gives mu with q(W_2(mu,mu0)) != int phi dmu, a contradiction.
For the vector term eps q(W_2(mu,mu0)) w0 in f (eps > 0, w0 != 0), apply this to the coordinate
j with w0_j != 0 and the kernel phibar_j / (eps w0_j). The hypotheses (bounded, Lipschitz,
nonconstant on R_+; mu0 arbitrary; n >= 1) are exactly the paper's.
Disagreements with the author's review (shown 2026-10-19T03:36:54Z): 1. Verdict label. The author records "faithful", but the review's own correspondence says the
   proposition is broader: phi ranges over every function integrable against all laws of P_2(H),
   not only Example 5.3 kernels. Under this review scheme that is the "broader" verdict, with the
   instantiation stated: freeze an Example 5.3 kernel phibar at (t, theta). It is Lipschitz,
   hence of linear growth and integrable against every P_2 law, so the proposition excludes it.
   For the vector term eps q(W_2(mu,mu0)) w0 use a coordinate with w0_j != 0. The proposition
   also allows m, d >= 0 and any nu (no nu != 0 needed for the full-law statistic). I agree with
   the substance.
2. No disagreement on the hypotheses: bounded, Lipschitz, nonconstant on [0,oo), mu0 arbitrary,
   n >= 1, W_2 of the Hilbert norm (w2H).
