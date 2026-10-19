### A:rem:generalrank: Dissertation.PaperSpec.A.PairingBound34W
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash 2b1db421079e9e76f26e2afdddf6a5b4 (pl-fp-v1:683e0ac0a281424ee4e2bab8a001690f4a140d723462f6fc4a511f402726e476)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:36:24Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:15:38Z):
Reading (locked before any Lean): def PairingBound34W - the weighted perturbation-pairing bound,
i.e. (3.4) "recorded in the weighted quantities of (2.12)" (Remark 3.7).

Paper notion. For perturbations p_b, p_sigma, p_h, p_f (deterministic functions on
[0,T] x H x P_2(H), values R^n, R^{n x d}, L2(nu;R^n), R^m), a coupling matrix G in R^{m x n}
and a constant c_pert (>= 0, possibly carried as a separate hypothesis), the condition: for a.e.
t in [0,T] and all diagonal pairs (Theta, Law Theta), (Theta', Law Theta') with Theta, Theta' in
L2(Omega, F_t; H) on the standing basis,
  E[ <dp_b, G^T dY> + <dp_sigma, G^T dZ>_F + <-dp_f, G dX>
     + int_E <dp_h(e), G^T dU(e)> nu(de) ]
  <= c_pert E[ |G^T dY|^2 + |G^T dZ|_F^2 + ||G^T dU||^2_{L2(nu)} + |G dX|^2 ],
where dp_psi = p_psi(t, Theta, mu) - p_psi(t, Theta', mu'), dX = X - X' etc. (componentwise
differences of the tuples), and the jump term is the L2(nu) inner product <dp_h, G^T dU>_{L2(nu)}.
The weighted quantities are exactly the margin term of (2.12): |G^T dY|^2 + |G^T dZ|_F^2 +
||G^T dU||^2 + |G dX|^2 (G^T acting on Y in R^m, columnwise on Z in R^{m x d}, pointwise on U).

A faithful Lean definition must be:
- a Prop on (basis/setting, T, p's, G, c_pert) quantifying "for a.e. t in [0,T]" (the null set
  of times chosen before the pairs; an "every t" version would be a stronger condition, hence a
  narrower hypothesis where it is assumed) and "for all F_t-measurable square-integrable H-valued
  Theta, Theta'", with the measure arguments the laws of Theta, Theta' (diagonal);
- the inequality with Lean expectations (Bochner integrals) of the stated integrands, signs as
  above (note <-dp_f, G dX>), the G^T / G placements as above;
- edge cases: Bochner expectation of a non-integrable integrand is 0 in Lean; with Lipschitz
  perturbations and L2 inputs the pairing is integrable so this only matters if the definition is
  used without Lipschitz; laws on P_2(H) (Law of an L2 variable is in P_2); measurability w.r.t.
  F_t of the standing filtration (not F or F_T).
Comparison (verdict recorded 2026-10-19T03:28:22Z):
Comparison: def PairingBound34W (Sec3GeneralRank.lean:36-51) against my locked reading.

Arguments: filtration F, P, T, G in R^{m x n}, constant c, perturbation p : Coeffs (its b, sigma,
h, f used; g irrelevant). Quantifiers: for a.e. t in [0,T] (Lebesgue restricted to [0,T]; the
null set chosen before the pairs, as printed "for a.e. t and all pairs"), for all q, q' in
diagonalInputs at t (strongly F_t-measurable square-integrable H-valued Theta with q.2 = lawP2 of
it — Definition 2.1). Matches.

Inequality: pairing27 G p t = <dp_b, G^T dY> + <dp_sigma, G^T dZ>_F + <-dp_f, G dX> +
int_E <dp_h(e), G^T dU(e)> nu(de), with dp_psi = p_psi(t, Theta, mu) - p_psi(t, Theta', mu') and
dX..dU the channels of Theta - Theta' — the left side of (3.4). Right side
c E[|G^T dY|^2 + |G^T dZ|_F^2 + ||G^T dU||^2_{L2(nu)} + |G dX|^2], with GX G^T on R^m, GZ G^T
(G^T acting columnwise, Kronecker with I_d) on R^{m x d}, GU G^T nu acting markwise on L2(nu):
exactly the weighted quantity of (2.12). Signs and placements match.

Edge cases: the definition adds integrability of the pairing as a conjunct. Without it a
non-integrable pairing would have Bochner integral 0 and the bound would hold vacuously; with it,
the definition says what the paper means whenever the paper's expectation is finite. For the
perturbations to which it is applied (diagonal Lipschitz, Remark 3.7/Cor 3.6) the pairing is
integrable on L2 inputs, so nothing is lost; for a non-Lipschitz p whose pairing has expectation
-infinity the Lean definition would be stricter than an extended-real reading, a case the paper
never uses. The right side is integrable for L2 inputs. F_t is the filtration passed in (the
standing enlJoint at every use).

Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless:
1. Integrability of the pairing is a conjunct of the condition. It rules out the Bochner junk
   value 0 for a non-integrable pairing. It is automatic for the diagonally Lipschitz
   perturbations the paper applies it to, and differs from an extended-real reading only for a
   pairing with expectation -infinity, which the paper never considers.
2. Expectations are Bochner integrals; the L2(nu) pairing is int_E of the pointwise inner product
   of representatives (independent of the representative); G acts through the continuous linear
   maps GX, GZ (G tensor I_d), GU (markwise).
3. The diagonal is diagonalInputs (strongly F_t-measurable L2 tuples with their lawP2 laws), and
   "a.e. t" is with respect to Lebesgue measure on [0,T].
Disagreements with the author's review (shown 2026-10-19T03:36:13Z): none
