### A:ex:fulllaw: Dissertation.PaperSpec.A.ex_fulllaw_beyond_Q
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba12be9f13eb8df21c1 (pl-fp-v1:77391c424ac867b33c84ccb47f92f2979db03059f85ddcadebf00bcf5fe4dbae)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:38:27Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:18:01Z):
Reading of spec:Dissertation.PaperSpec.A.ex_fulllaw_beyond_Q (Example 5.4, 05-examples.tex:314-318).

Printed claim: "The cylindrical term does so [lies beyond the expectation and two-point-kernel
jump-integrand interactions of the preceding examples] when Q is non-affine on the attained range
of the feature vector (int phi_1 dmu^U, ..., int phi_J dmu^U)".

A faithful formal statement must contain:
- Setting: H = R^n x R^m x R^{m x d} x L^2(nu;R^m), P_2(H), mu^U the U-marginal; standing nu
  (Ex 5.4 takes nu != 0; a one-point attained range makes every Q affine there, so for nu = 0
  the hypothesis below is unsatisfiable and no extra nu-hypothesis is needed).
- Data: J, features phi_1..phi_J : L^2(nu;R^m) -> R bounded Lipschitz, Q : R^J -> R bounded
  Lipschitz (standing hypotheses of Ex 5.4; if the Lean drops them, it is broader).
- Hypothesis: Q is NOT affine on the attained range A = {(int phi_j(u) mu(dtheta))_j : mu in P_2(H)},
  i.e. there are no a, c with Q(s) = a + sum c_j s_j for all s in A (the negation of the
  hypothesis of ex_fulllaw_affineQ). Using "Q not affine on R^J" instead would be a weaker
  hypothesis, making a false (too strong) statement; using a stronger non-affinity hypothesis
  (e.g. strict convexity on some segment of A) would narrow it.
- Conclusion: mu -> Q(int phi dmu^U) is not an expectation functional of Example 5.3: no kernel
  phibar (measurable, Lipschitz) with Q(...) = int phibar(theta') mu(dtheta') for all mu in P_2(H)
  (excluding all measurable kernels, or showing failure of mixture-affinity, is stronger and fine).
  (True: the feature map is mixture-affine, A is convex, and mixture-affinity of Q o s would make
  Q affine on A.)
Comparison (verdict recorded 2026-10-19T03:34:55Z):
Comparison: spec ex_fulllaw_beyond_Q (PaperSpec/A/Sec5.lean:610-627).
Lean: for every nu, n m d J, Q : R^J -> R Lipschitz (LQ), phi_j : L^2(nu;R^m) -> R Lipschitz (K_j)
and bounded (B): if NOT (exists a, c, for all mu in P_2(H), Q((int phi_j dmu^U)_j) =
a + sum c_j int phi_j dmu^U), then for every phi' : H -> R integrable against every law of
P_2(H) there is mu with Q((int phi_j dmu^U)_j) != int phi' dmu.
Reading: features bounded Lipschitz, Q bounded Lipschitz. Hypothesis exactly "Q not affine on the
attained range A" (neither the weaker "not affine on R^J" nor anything stronger). Conclusion: no
Example 5.3 kernel represents mu -> Q(s(mu)). Excluding all integrable kernels is acceptable.
- Hypothesis: the negation of affinity on {s(mu) : mu in P_2(H)} = A. Exactly the printed
  condition. Matches.
- Data: features bounded Lipschitz (as printed); Q Lipschitz, with boundedness of Q dropped
  (broader; the claim stays true, since mixture-affinity of Q o s plus convexity of A forces Q to
  be affine on A, with no boundedness needed).
- Conclusion: no integrable phi' (stronger than "no Example 5.3 kernel"), hence broader.
- No nu != 0 hypothesis: for nu = 0 the range A is a single point, so the hypothesis is
  unsatisfiable. Nothing is lost and nothing false is claimed.
- The clause is in the paper at f598204 ("The cylindrical term does so when Q is non-affine on the
  attained range of the feature vector").
- Non-vacuous: witness ex_fulllaw_beyond_Q_hypotheses (J = 1, phi_1 = min(||u||,1),
  Q = min(|s|,1/2), not affine on the range [0,1] reached at three Dirac laws).
Verdict: broader.
Witness: —
Verdict: broader — Broader than the printed claim. (i) Q is only assumed Lipschitz; the paper's standing data also
make it bounded. (ii) The conclusion excludes every phi' : H -> R integrable against all P_2(H)
laws, not just Example 5.3 kernels. Instantiation giving the printed claim: take the paper's
bounded Lipschitz features phi_j and bounded Lipschitz Q. The hypothesis "no a, c with
Q(s) = a + sum c_j s_j at every s = (int phi_j dmu^U)_j, mu in P_2(H)" is the printed "Q non-affine
on the attained range". If the Q-term were an Example 5.3 expectation functional
int phibar(t,theta,theta') mu(dtheta'), the frozen kernel phibar(t,theta,.) is Lipschitz, hence
integrable against every P_2 law, which contradicts the proposition. The vector term
eps Q(...) w1 (eps > 0, w1 != 0) reduces to the scalar one through a coordinate with w1_j != 0.
Disagreements with the author's review (shown 2026-10-19T03:38:14Z): 1. Verdict label. The author's summary says "faithful", with the parenthesis "without the bounds:
   broader". The proposition is broader in two ways. Q is not assumed bounded. And the conclusion
   excludes every phi' integrable against all P_2(H) laws, not only Example 5.3 kernels; the
   author notes this for the radial statistics, and it applies here as well. So the verdict should
   be "broader". The instantiation is the paper's bounded Lipschitz Q and features, with an
   Example 5.3 kernel frozen at (t, theta) being integrable against every P_2 law.
2. Agreement that the hypothesis is exactly "Q not affine on the attained range" (the negation of
   affinity at every s = (int phi_j dmu^U)_j), neither the weaker "not affine on R^J" nor a
   stronger condition. For nu = 0 the range is a single point, so the hypothesis cannot hold and
   nothing false is claimed.
