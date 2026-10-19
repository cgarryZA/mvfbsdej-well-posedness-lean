### A:ex:fulllaw, A:sec5:overview: Dissertation.PaperSpec.A.ex_fulllaw_beyond_U_corr
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba193f328d7c8c243ea (pl-fp-v1:22af2162ff7a9dc3738d459ea4684b8119c137c19dfd0e9d5933ec4b647475a6)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:37:48Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:18:01Z):
Reading of spec:Dissertation.PaperSpec.A.ex_fulllaw_beyond_U_corr (Example 5.4, 05-examples.tex:311-313,
with the standing "In Examples 5.4 and 5.5, we take nu != 0" of 05-examples.tex:22; Sec. 5 overview).

Printed claim: "For nonconstant q, q~, q^, the radial statistics lie beyond the expectation and
two-point-kernel jump-integrand interactions ...". This unit: the U-MARGINAL radial statistics
mu -> q~(W_2(mu^U, Lambda_0)) (entering b with v_0) and mu -> q^(W_2(mu^U, Lambda_0)) (entering h with
h^), q~, q^ : R_+ -> R bounded Lipschitz nonconstant, Lambda_0 in P_2(L^2(nu;R^m)) arbitrary,
under the paper's standing nu != 0 for Ex 5.4 (equivalently, nu sigma-finite, L^2(nu) != {0}, as
in Rem 2.10 "Suppose nu != 0, so that L^2(nu) != {0}"). With nu = 0 the claim would be false
(mu^U = delta_0 always, statistic constant), so the hypothesis L^2(nu) != 0 is the paper's own
standing hypothesis, not an added restriction.

A faithful formal statement must contain:
- Setting: standing nu with L^2(nu;R^m) != {0} (or nu != 0); H, P_2(H), mu^U the U-marginal.
- For every Lambda_0 and every bounded Lipschitz nonconstant q~ (resp. q^): no Example 5.3
  kernel phibar with q~(W_2(mu^U,Lambda_0)) = int phibar dmu for all mu in P_2(H) (stronger forms
  -- no measurable kernel at all / not mixture-affine -- are acceptable). Both q~ and q^ (same
  statement for each; a single statement for an arbitrary nonconstant q covers both).
- Nonconstant on R_+ (= attained range of W_2(mu^U,Lambda_0) when L^2(nu) != 0).
- Narrowing to watch: a particular Lambda_0 (e.g. delta_0), particular nu, extra hypotheses.
Comparison (verdict recorded 2026-10-19T03:34:54Z):
Comparison: spec ex_fulllaw_beyond_U_corr (PaperSpec/A/Sec5.lean:595-608).
Lean: for every sigma-finite nu (countably generated E), n m d, if L^2(nu;R^m) contains u != 0,
then for every q Lipschitz, bounded, not constant on [0,oo), every Lambda0 in
P_2(L^2(nu;R^m)) and every phi : H -> R integrable against every law of P_2(H), there is mu in
P_2(H) with q(W_2(mu^U, Lambda0)) != int phi dmu. W_2 here is w2P on P_2(L^2(nu;R^m)) (the W_2
of the L^2(nu) norm) and mu^U = mu.margU.
Reading: the U-marginal radial statistics q~(W_2(mu^U,Lambda0)) (b) and q^(W_2(mu^U,Lambda0))
(h) are not expectation functionals, under the paper's standing nu != 0 for Ex 5.4 (= L^2(nu) !=
{0} for sigma-finite nu, as in Rem 2.10), for all Lambda0 and all bounded Lipschitz nonconstant
profiles. A stronger conclusion (no integrable kernel) is acceptable.
- Hypothesis L^2(nu;R^m) != 0: the paper's own standing hypothesis "In Examples 5.4 and 5.5, we
  take nu != 0" (05-examples.tex:22), with m >= 1 (sigma-finite nu != 0 has a set of finite
  positive mass, whose indicator times e_1 is a nonzero element). It is not an added restriction.
  Without it the claim is false (mu^U = delta_0 always, so the statistic is constant).
- One statement for an arbitrary profile q covers both q~ (b-term) and q^ (h-term). Matches.
- Lambda0 arbitrary, q bounded Lipschitz nonconstant on R_+ (the attained range of
  W_2(mu^U,Lambda0) when L^2(nu) != 0, via translates of Lambda0). Matches.
- Conclusion stronger than printed (excludes all integrable phi). Broader, same reduction as for
  the radial unit. For the h-term the printed class is the jump expectation functional
  int H_t(theta,theta') mu(dtheta') in L^2(nu;R^n). Pairing with h^ != 0 reduces it to a scalar
  kernel <H_t(theta,.), h^>, which is integrable.
- Is the clause in the paper at f598204? Yes: "For nonconstant q, q~, q^, the radial statistics lie
  beyond ...", under the Ex 5.4 standing nu != 0. The suffix _corr records no refutation in the
  inventory (claims.json lists it as a plain clause).
- Non-vacuous: witness ex_fulllaw_beyond_hypotheses (nu = delta_0, u = e_1).
Verdict: broader.
Witness: —
Verdict: broader — Broader than the printed claim in its conclusion. It excludes every phi : H -> R integrable
against all laws of P_2(H), not only Example 5.3 kernels. It also allows any n, d and any m with
L^2(nu;R^m) != 0. Instantiation giving the printed claim: the hypothesis L^2(nu;R^m) != {0} is the
paper's standing nu != 0 for Ex 5.4 (with m >= 1 and nu sigma-finite, the indicator of a set of
finite positive mass times e_1 is nonzero). Take q := q~ (resp. q^) and Lambda0 the paper's
reference law. If mu -> q~(W_2(mu^U,Lambda0)) were an Example 5.3 functional
int phibar(t,theta,theta') mu(dtheta'), freeze (t, theta): phibar(t,theta,.) is Lipschitz, hence
integrable against every P_2 law, which contradicts the proposition. For the h-term
eps q^(W_2(mu^U,Lambda0)) h^ (h^ != 0) against a jump expectation functional
int H_t(theta,theta') mu(dtheta') in L^2(nu;R^n), take the L^2(nu) inner product with h^. This
gives the scalar kernel <H_t(theta,.), h^>/(eps ||h^||^2), which is Lipschitz and hence
integrable. For the b-term with v0 != 0, use a coordinate.
Disagreements with the author's review (shown 2026-10-19T03:37:37Z): 1. Verdict label. As for the full-law statistic, the proposition excludes every phi integrable
   against all P_2(H) laws, not only Example 5.3 kernels. The author's correspondence says so
   ("broader") but the recorded verdict is "faithful". It should be "broader", with the
   instantiation: freeze an Example 5.3 kernel at (t, theta). For the jump term
   eps q^(W_2(mu^U,Lambda0)) h^, pair the Nemytskii expectation functional with h^ != 0 to get a
   scalar Lipschitz kernel.
2. Agreement on the hypothesis L^2(nu;R^m) != {0}. It is the paper's own standing "we take
   nu != 0" for Ex 5.4 (05-examples.tex:22, the overview, as the author says), with m >= 1 and nu
   sigma-finite. It is not an added restriction and it is necessary. The suffix "_corr" does not
   mark a refuted original in the inventory. No other disagreement.
