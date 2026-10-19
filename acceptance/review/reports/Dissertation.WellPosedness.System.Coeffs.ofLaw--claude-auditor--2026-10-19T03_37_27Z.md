### A:ex:fulllaw, A:rem:regimes: Dissertation.WellPosedness.System.Coeffs.ofLaw
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash 078c486754be7860fbd98d3584940f30 (pl-fp-v1:44f5a645452e175c3590759203a38f24a5591d6f7878275ccf74a9eacefa118f)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:37:27Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:18:01Z):
Reading of def:Dissertation.WellPosedness.System.Coeffs.ofLaw (used by Ex 5.4 and Rem 5.7).

Paper notion: a coefficient system built from law functionals alone, i.e. the theta-independent
perturbation coefficients of Example 5.4 p_psi(t,theta,mu) = P_psi(t,mu) (in Ex 5.4 also
t-independent). Given maps P_b : [0,T] x P_2(H) -> R^n (or P_2(H) -> R^n), P_sigma -> R^{n x d},
P_h -> L^2(nu;R^n), P_f -> R^m, the coefficient system
  b(t,theta,mu) = P_b(t,mu), sigma = P_sigma(t,mu), h(t,theta,.,mu) = P_h(t,mu), f = P_f(t,mu),
and, as a perturbation of the interior coefficients only, the terminal function g = 0 (or absent):
the perturbed system keeps the baseline g.

A faithful Lean definition must: ignore theta in all four interior channels; use the given law
maps unchanged; set the terminal component to zero if the structure has one (so that adding it
leaves g unchanged), and not introduce any t- or theta-dependence. Any junk (e.g. laws outside
P_2) only at arguments that never occur on diagonal inputs.
Comparison (verdict recorded 2026-10-19T03:34:54Z):
Comparison: def Coeffs.ofLaw pb psigma ph pf (Robustness/Perturb.lean:107-117):
b t _ mu = pb t mu, sigma t _ mu = psigma t mu, h t _ mu = ph t mu, f t _ mu = pf t mu,
g _ _ = 0.
Reading: theta-independent coefficients from law maps, terminal component zero (or absent), no
added dependence.
Ignores theta in all four channels, uses the given maps unchanged, terminal function 0 (and in
any case perturb never uses p.g). Matches.
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-19T03:37:19Z): none
