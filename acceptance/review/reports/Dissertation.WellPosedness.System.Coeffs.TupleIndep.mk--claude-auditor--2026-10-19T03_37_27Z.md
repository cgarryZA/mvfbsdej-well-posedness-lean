### A:cor:robust, A:ex:fulllaw, A:rem:regimes: Dissertation.WellPosedness.System.Coeffs.TupleIndep.mk
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash 54322416b320749b0000000000000000 (pl-fp-v1:3d054c77d9dfbb1b54748d12ff036be0390b69ac93f5d949db9891e0b16a2354)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:37:27Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:18:01Z):
Reading of def:Dissertation.WellPosedness.System.Coeffs.TupleIndep.mk (constructor of the structure TupleIndep; its type lists the fields, so the reading is that of the structure: Cor 3.6 "the perturbations are independent of theta"; Ex 5.4).


Paper notion: the interior coefficients b, sigma, h, f of a system do not depend on the point
theta in H: psi(t,theta,mu) = psi(t,theta',mu) for all t, theta, theta', mu (psi in {b,sigma,f}),
and h(t,theta,.,mu) = h(t,theta',.,mu) in L^2(nu;R^n). The terminal function g is not part of the
condition (the perturbation has no terminal component). They may depend on t and mu.

A faithful Lean definition must: quantify over all t, all theta, theta', all mu (pointwise
everywhere is the paper's sense of "independent of theta"); cover all four interior channels;
not constrain g; not require independence of mu or t.
Comparison (verdict recorded 2026-10-19T03:34:54Z):
Comparison: constructor Coeffs.TupleIndep.mk. Its type lists the four fields b, sigma, h, f of
TupleIndep (Robustness/Perturb.lean:94-105), each forall t theta theta' mu,
p_psi t theta mu = p_psi t theta' mu.
Same content as the structure: independence of theta in the four interior channels, everywhere,
with g unconstrained. Matches the paper's "the perturbations are independent of theta"
(Cor 3.6, Ex 5.4).
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-19T03:37:19Z): none
