### A:ex:brownian: Dissertation.WellPosedness.Spec.brownianPairing
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash de8a42fe1472d600a546e2f6903660ba (pl-fp-v1:d3201121997966bb6efb114dd989b20ebc9b0ba51dc065fb36678d49c60b2d69)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:34:13Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:16:13Z):
Reading of def Spec.brownianPairing (the interior pairing of Assumption 2.5 in Brownian form).

Paper notion. For two input values with differences delta b in R^n, delta sigma in R^{n x d},
delta f in R^m, delta X in R^n, delta Y in R^m, delta Z in R^{m x d} and G in R^{m x n}:
   <delta b, G^T delta Y> + <delta sigma, G^T delta Z>_F + <-delta f, G delta X>
(pointwise in omega; Assumption 2.5 takes its expectation). <.,.>_F is the Frobenius inner product
sum_{ij} a_ij b_ij; G^T delta Z is the matrix product (n x m)(m x d). The deltas are
psi(t,Theta,mu) - psi(t,Theta',mu') for psi in {b,sigma,f} and the tuple differences.
A faithful Lean definition: this expression (or its expectation if the def includes E), with the
right transposes and signs: the f-term is <-delta f, G delta X> = -<delta f, G delta X>, the b-term
pairs with G^T delta Y (not G delta Y), the sigma-term with G^T delta Z. Equivalent rewrites
(e.g. <G delta b, delta Y> = <delta b, G^T delta Y>) are harmless.
Comparison (verdict recorded 2026-10-19T03:32:34Z):
Comparison, Spec.brownianPairing (BrownianForms.lean:107-112).

inner(db, GX G^T dY) + inner(dsigma, GZ G^T dZ) + inner(-df, GX G dX), with db = C.b t theta mu -
C.b t theta' mu' etc. GX G^T : R^m -> R^n (G^T dY), GZ G^T : R^{m x d} -> R^{n x d} via the Kronecker
G^T (x) I_d (the matrix product G^T dZ), inner on EuclideanSpace (Fin n x Fin d) = Frobenius; the f-term
is <-df, G dX>. Signs and transposes as printed; pointwise (the expectation is taken in
BrownianMonoAt).
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-19T03:32:45Z): Label only. I recorded "faithful": the pairing is printed one-for-one (pointwise integrand, G^T on
R^{m x d} as the Kronecker G^T (x) I_d, which is the matrix product G^T dZ with the Frobenius inner
product). The review's listed choices (pointwise integrand, nu = 0 typing, Kronecker realisation)
I agree with; I do not regard them as departures. No disagreement in substance.
