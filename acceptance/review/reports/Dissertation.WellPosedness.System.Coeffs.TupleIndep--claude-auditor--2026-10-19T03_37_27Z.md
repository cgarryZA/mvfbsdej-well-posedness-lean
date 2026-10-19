### A:cor:robust, A:ex:fulllaw, A:rem:regimes: Dissertation.WellPosedness.System.Coeffs.TupleIndep
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash bb2f84e84c27fd8b0000000000000000 (pl-fp-v1:c0f2579dfd96ec2ea3d8308384eaa6db6c267b6690eb583297b00466aee85c01)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:37:27Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:18:01Z):
Reading of def:Dissertation.WellPosedness.System.Coeffs.TupleIndep (Cor 3.6 "the perturbations are
independent of theta"; Ex 5.4 "They are independent of theta").

Paper notion: the interior coefficients b, sigma, h, f of a system do not depend on the point
theta in H: psi(t,theta,mu) = psi(t,theta',mu) for all t, theta, theta', mu (psi in {b,sigma,f}),
and h(t,theta,.,mu) = h(t,theta',.,mu) in L^2(nu;R^n). The terminal function g is not part of the
condition (the perturbation has no terminal component). They may depend on t and mu.

A faithful Lean definition must: quantify over all t, all theta, theta', all mu (pointwise
everywhere is the paper's sense of "independent of theta"); cover all four interior channels;
not constrain g; not require independence of mu or t.
Comparison (verdict recorded 2026-10-19T03:34:54Z):
Comparison: structure Coeffs.TupleIndep p (Robustness/Perturb.lean:94-105): fields b, sigma, h, f,
each: forall t theta theta' mu, p_psi t theta mu = p_psi t theta' mu.
Reading: b, sigma, h, f independent of theta for all t, theta, theta', mu (h as an element of
L^2(nu;R^n)); g not constrained; t- and mu-dependence allowed.
All four interior channels, everywhere in t, with equality in L^2(nu) for h (Coeffs.h is
Lp-valued), g untouched, t and mu free. Matches exactly.
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-19T03:37:19Z): none
