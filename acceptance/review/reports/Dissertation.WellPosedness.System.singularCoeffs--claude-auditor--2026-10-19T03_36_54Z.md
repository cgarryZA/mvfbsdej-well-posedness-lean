### A:rem:uniq-no-integ: Dissertation.WellPosedness.System.singularCoeffs
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash 9cbaca3d28850a562cb0f143b2b54981 (pl-fp-v1:fcc8ca9df57698ede3bf5d1eb75d560606fe74d5db986d3e3cd83a7dfdda57d2)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:36:54Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:18:00Z):
Reading of def:Dissertation.WellPosedness.System.singularCoeffs (Remark 3.4).

Paper notion: the coefficient system of Remark 3.4's instance: a system satisfying Assumptions
2.2-2.5 with the deterministic drift t^{-1/2} added to b; per the clause of rem_uniq_singular,
the base is a system of Example 5.1(i):
  n=m=d=1, G=1, b(t,theta,mu) = -beta1 y + t^{-1/2}, sigma = sigma_c - beta1 z,
  h(t,theta,e,mu) = h_c(e) - beta1 u(e), f = beta2 x, g(x,rho) = x,
with beta1,beta2>0, sigma_c in R, h_c in L^2(nu).
A faithful Lean definition must be exactly this (or addDrift applied to the Example 5.1(i) system
with singularDrift), all other coefficients unchanged, the drift independent of (theta, mu).
Comparison (verdict recorded 2026-10-19T03:34:54Z):
Comparison: def singularCoeffs (Examples/SingularDrift.lean:86-90) =
(affineCoeffs 1 0 0 0).addDrift singularDrift : Coeffs nu 1 1 d, i.e. (Existence/AffineExample.lean:69-75)
b = t^{-1/2} - y, sigma = 0 - 1*z, h = 0 - 1*u, f = 0*x = 0, g(x,rho) = x.
Reading: Remark 3.4's system: a system satisfying Assumptions 2.2-2.5 with t^{-1/2} added to b; per
the clause label, a base from Example 5.1(i) (b=-beta1 y, sigma=sigma_c-beta1 z, h=h_c-beta1 u,
f=beta2 x, g=x, beta1,beta2>0).
- Structure: exactly addDrift of an affine Example 5.1(i)-type base with singularDrift. Other
  coefficients unchanged; the drift is independent of (theta,mu). Matches.
- Parameters: beta1 = 1, beta2 = 0, sigma_c = 0, h_c = 0. beta2 = 0 is outside Example 5.1(i)'s
  printed range beta1, beta2 > 0. The base nevertheless satisfies Assumptions 2.2-2.5
  (n = m = 1: Lipschitz with L = 1; (2.7) with G = 1, beta1 = 1, beta2 = 0 holds with equality
  -beta1 E[|dY|^2+|dZ|^2+||dU||^2]; terminal alpha = 1; constants admissible at m = n). It is
  therefore a legitimate instance of Remark 3.4's "a system satisfying Assumptions 2.2-2.5". The
  remark does not fix the system, so choosing one is the formalisation's prerogative. Only the
  inventory's wording "one system of Example 5.1(i)" is met loosely.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choice: the formalisation fixes the base system of Remark 3.4's instance. It is
the affine Example 5.1(i) form at beta1 = 1, beta2 = 0, sigma_c = 0, h_c = 0 (n = m = 1, any d),
i.e. b = t^{-1/2} - y, sigma = -z, h = -u, f = 0, g = x. This is harmless: Remark 3.4 asks only
for some system satisfying Assumptions 2.2-2.5, and this base satisfies them (L = 1; G = 1,
alpha = 1, beta1 = 1, beta2 = 0 are admissible at m = n). Caveat for the record: beta2 = 0 is
outside Example 5.1(i)'s printed parameter range (beta1, beta2 > 0), so the system is "of
Example 5.1(i) form" rather than literally one of Example 5.1(i).
Disagreements with the author's review (shown 2026-10-19T03:36:40Z): Agreement on substance (the recorded review is by claude-reviewer, "faithful"). It is a matter of
labelling only: since beta2 = 0 lies outside Example 5.1(i)'s printed range (beta2 > 0), which the
review itself notes, I record the choice of base system as a representation choice ("faithful with
representation choices") rather than plain "faithful". The choice is harmless because Remark 3.4
asks only for some system satisfying Assumptions 2.2-2.5. No other disagreement.
