### A:ex:brownian: Dissertation.WellPosedness.Spec.brownianPairing
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash de8a42fe1472d600a546e2f6903660ba (pl-fp-v1:d3201121997966bb6efb114dd989b20ebc9b0ba51dc065fb36678d49c60b2d69)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T16:01:16Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T15:42:32Z):
Reading for def:Dissertation.WellPosedness.Spec.brownianPairing (locked before seeing Lean).

The interior pairing of Assumption 2.5 in the Brownian reduction (no h-term): for coefficients
(b, sigma, f), G in R^{m x n}, time t and two inputs Theta=(X,Y,Z), Theta' with laws mu, mu':
 E[ <db, G^T dY> + <dsigma, G^T dZ>_F + <-df, G dX> ],
db = b(t,Theta,mu) - b(t,Theta',mu'), dsigma likewise (in R^{n x d}), df likewise, dX = X - X',
dY, dZ likewise. <.,.>_F is the Frobenius inner product sum_ij A_ij B_ij. The measure arguments
are the laws of the inputs (diagonal). Faithful: these three terms with correct signs and
transposes, under the expectation. Junk: non-integrable integrand gives 0 in Lean; harmless under
the L^2 + Lipschitz setting where it is used.
Comparison (verdict recorded 2026-10-17T15:54:25Z):
Comparison for def:Dissertation.WellPosedness.Spec.brownianPairing.

Lean: brownianPairing G C t theta theta' mu mu' = <b(t,theta,mu) - b(t,theta',mu'), G^T (y - y')>
 + <sigma(..) - sigma(..), (G^T (x) I_d)(z - z')> + <-(f(..) - f(..)), G (x - x')>, a real number at two
 points and two laws (the integrand; the expectation over diagonal inputs is taken in BrownianMonoAt).

Against my reading: the three terms with the right signs and transposes: yes; Frobenius pairing of
dsigma in R^{n x d} with G^T dZ (GZ G^T is G^T acting column by column, i.e. vec(G^T Z)): yes; no
jump term (nu = 0): yes. My reading put the expectation inside this unit; the Lean def is the
pointwise integrand and the expectation, with the diagonal laws mu = Law Theta, is applied by its
user BrownianMonoAt, which is the same quantity. Taking the laws as free arguments here is harmless
since the user instantiates them with the inputs' own laws.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices: (1) the def is the pointwise integrand at two points and two laws; the
expectation along diagonal inputs (laws = the inputs' own laws) is taken by BrownianMonoAt;
(2) Brownian reduction at nu = 0 (no jump pairing); (3) G^T on R^{m x d} realised as the Kronecker
product G^T (x) I_d on Euclidean vectors indexed by pairs, which is G^T Z column by column with the
Frobenius inner product.
Disagreements with the author's review (shown 2026-10-17T16:01:12Z): none
