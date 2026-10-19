### A:ex:brownian: Dissertation.WellPosedness.Spec.BrownianMonoAt
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash e073370a300411e99f39979ae6c8f92b (pl-fp-v1:057471d174fc8814d9b2c898c5ab8ee2d8fb06c861c2a42f0e1850ab8dfe76e3)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:34:13Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:16:13Z):
Reading of def Spec.BrownianMonoAt (interior G-monotonicity of Assumption 2.5 at a fixed time t,
Brownian form).

Paper notion. For fixed t, G in R^{m x n}, beta_1, beta_2: for all Theta, Theta' in
L^2(Omega,F_t;H_B) with mu, mu' their laws,
  E[<delta b, G^T delta Y> + <delta sigma, G^T delta Z>_F + <-delta f, G delta X>]
    <= -beta_1 E[|G^T delta Y|^2 + |G^T delta Z|_F^2] - beta_2 E|G delta X|^2,
where delta psi = psi(t,Theta,mu) - psi(t,Theta',mu'). Expectation outside the pairing (the
"expected" form, not pointwise). G^T delta Y in R^n, G^T delta Z in R^{n x d} (columnwise),
G delta X in R^m. Frobenius inner product for the matrix pairing.
A faithful Lean definition: exactly this (possibly via a pairing function as r_19). Junk value of
Bochner expectation for non-integrable integrand: the condition then reads 0 <= RHS at such
inputs, stronger than the paper (which presupposes integrability); harmless when used together
with Lipschitz (integrability then holds), to be noted.
Comparison (verdict recorded 2026-10-19T03:32:33Z):
Comparison, Spec.BrownianMonoAt (BrownianForms.lean:118-127).

For all diagonal inputs p, p' at t: the brownianPairing is integrable and
E[brownianPairing] <= -beta_1 E[|G^T dY|^2 + |G^T dZ|_F^2] - beta_2 E|G dX|^2.
Expectation outside the pairing (expected, not pointwise, form). brownianPairing as in c_19.
Integrability is required explicitly instead of a junk-0 Bochner value: if the pairing were not
integrable, the condition fails (the paper's expectation would not exist either); under Assumption
2.3 for L^2 inputs it holds. Matches my reading.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices: integrability of the pairing is an explicit conjunct (the paper's
expectation presupposes it; it holds under Assumption 2.3 for square-integrable inputs, and no junk
Bochner value is used); the inputs are tuples of TupleH at nu = 0 with the jump terms deleted; the
filtration is a parameter.
Disagreements with the author's review (shown 2026-10-19T03:32:44Z): none
