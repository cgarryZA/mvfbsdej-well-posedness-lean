### A:ex:brownian: Dissertation.WellPosedness.Spec.BrownianMonoAt
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash e073370a300411e99f39979ae6c8f92b (pl-fp-v1:057471d174fc8814d9b2c898c5ab8ee2d8fb06c861c2a42f0e1850ab8dfe76e3)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T16:00:44Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T15:42:31Z):
Reading for def:Dissertation.WellPosedness.Spec.BrownianMonoAt (locked before seeing Lean).

Brownian Assumption 2.5 interior inequality at a fixed time t (Ex 5.2, no h, no U): given G in
R^{m x n}, beta1, beta2, for all diagonal inputs Theta=(X,Y,Z), Theta' in L^2(Omega,F_t;H_B)
with mu = Law Theta, mu' = Law Theta',
 E[ <db, G^T dY> + <dsigma, G^T dZ>_F + <-df, G dX> ]
   <= -beta1 E[ |G^T dY|^2 + |G^T dZ|_F^2 ] - beta2 E|G dX|^2,
where db = b(t,Theta,mu) - b(t,Theta',mu') etc. Dimensions: G^T dY in R^n paired with db in R^n;
G^T dZ in R^{n x d} paired (Frobenius) with dsigma in R^{n x d}; G dX in R^m with df in R^m.
Faithful: expectation (not pointwise), diagonal inputs only, F_t the Brownian filtration, the
correct transposes and signs. Junk: Lean's integral of a non-integrable function is 0; with
Lipschitz coefficients and L^2 inputs every term is integrable, so the junk does not arise
where the definition is used with the Lipschitz assumption; splitting the expectation into a sum
of expectations is equivalent under integrability.
Comparison (verdict recorded 2026-10-17T15:49:59Z):
Comparison for def:Dissertation.WellPosedness.Spec.BrownianMonoAt.

Lean: for all p, p' in diagonalInputs (0 : Measure E) n m d F P t:
 Integrable (omega |-> brownianPairing G C t (Theta omega) (Theta' omega) mu mu') P  ∧
 E[brownianPairing] <= -beta1 E[|G^T dY|^2 + |G^T dZ|^2] - beta2 E[|G dX|^2],
brownianPairing = <db, G^T dY> + <dsigma, (G^T (x) I_d) dZ> + <-df, G dX> (GX, GZ: G acting on vectors and
column by column on matrices).

Item by item:
- diagonal inputs only, measure argument = own law, Brownian setting via nu = 0: yes.
- expectation form (not pointwise): yes.
- transposes and signs: G^T dY in R^n against db; G^T dZ in R^{n x d} (Frobenius) against dsigma;
  G dX in R^m against -df; right side -beta1 E[|G^T dY|^2 + |G^T dZ|_F^2] - beta2 E|G dX|^2: yes.
- extra conjunct: integrability of the pairing. The paper's inequality presupposes the
  expectation is defined; with it, the Lean integral is the genuine expectation (no junk 0).
  Wherever the condition is assumed together with Assumption 2.3 (as in the paper), the pairing
  is integrable automatically (Lipschitz coefficients, L^2 inputs), so nothing is lost; the right
  side integrands are integrable for L^2 inputs. Harmless.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices: (1) Brownian reduction at nu = 0 (the U channel is the single point of
L^2(0), so the jump pairing and ||G^T dU||^2 are absent); (2) the condition includes
integrability of the pairing, which makes the Lean integral the genuine expectation; under
Assumption 2.3 with L^2 diagonal inputs it holds automatically, so the condition is equivalent to
the paper's wherever the paper uses it; (3) G^T acting on R^{m x d} realised as the Kronecker
product G^T (x) I_d on Euclidean vectors indexed by pairs (column-by-column action, Frobenius
inner product).
Disagreements with the author's review (shown 2026-10-17T16:00:39Z): No disagreement on the meaning. The review should say why the integrability conjunct is harmless
(the paper presupposes the expectation exists, and under Assumption 2.3 with L^2 diagonal inputs it
holds automatically), since as written it is an added requirement relative to the printed
inequality.
