### A:ex:brownian: Dissertation.WellPosedness.Spec.BrownianAssumption23
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash 9e0655ad2249204f01324c504097ee3a (pl-fp-v1:1d47c84421e5227b21fdd889da29c4e400c5821d41885c29998ef92555454408)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:34:13Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:16:13Z):
Reading of def Spec.BrownianAssumption23 (Assumption 2.3 in the Brownian reduction of Example 5.2;
if the Lean bundles Assumption 2.2 with it, the integrability part too).

Paper notion (Assumption 2.3, Brownian form). There is L >= 0 such that
(a) for a.e. t in [0,T] and all diagonal inputs (Theta,mu), (Theta',mu') in D_t, i.e. Theta,
Theta' in L^2(Omega, F_t; H_B) with mu = Law(Theta), mu' = Law(Theta') (H_B = R^n x R^m x R^{m x d},
F_t of the Brownian filtration), almost surely
 |delta b| + |delta sigma|_F + |delta f| <= L (|delta X| + |delta Y| + |delta Z|_F + W_2(mu,mu'));
(b) for all X_T, X'_T in L^2(Omega, F_T; R^n), almost surely
 |g(X_T,rho) - g(X'_T,rho')| <= L (|X_T - X'_T| + W_2(rho,rho')), rho = Law X_T, rho' = Law X'_T.
Norms: Euclidean on R^n, R^m, Frobenius on matrices; W_2 quadratic Wasserstein on P_2(H_B) with
the product Hilbert norm |x|^2 + |y|^2 + |z|_F^2 and on P_2(R^n).
(If 2.2 is included: xi_0 in L^2(Omega,F_0;R^n) and b(.,0,delta_0), sigma(.,0,delta_0),
f(.,0,delta_0) in L^2(0,T).)
A faithful Lean definition: the same, with L either existentially quantified or a parameter
(both fine if used consistently), the a.e. t quantifier outside the "for all diagonal inputs",
"a.s." inside; diagonal inputs exactly the F_t-measurable square-integrable tuples with their
own laws (not free measures - restricting to diagonal is the paper's; quantifying over free
(theta,mu) would be stronger, a narrower theorem when used as hypothesis). Measurability w.r.t.
F_t: strongly measurable / ae-strongly measurable both acceptable (completed filtration).
Comparison (verdict recorded 2026-10-19T03:32:33Z):
Comparison, Spec.BrownianAssumption23 (BrownianForms.lean:97-99).

BrownianAssumption23 F P T L C := 0 <= L /\ BrownianLipInterior F P T L C /\ LipTerminal F P T L C.g.
- L a parameter with 0 <= L (the paper's "there is L >= 0" is recovered by an outer existential at
  the use site). Assumption 2.2 is not bundled (as Assumption 2.3 alone). OK.
- Interior: for a.e. t in [0,T] (volume restricted to Icc 0 T), for all diagonal inputs at t
  (Theta strongly F_t-measurable, in L^2, mu = lawP2 P Theta), a.s.
  |db| + |dsigma|_F + |df| <= L (|dX| + |dY| + |dZ|_F + W_2(mu^{XYZ}, mu'^{XYZ})), W_2 = w2P on the
  reduced space R^n x R^m x R^{m x d} with its Hilbert norm (projP2). Quantifier order a.e. t, all
  inputs, a.s. - as printed. Frobenius norms on the matrix channels (EuclideanSpace on pairs).
- Terminal (2.6): for X_T, X'_T strongly F_T-measurable in L^2, a.s.
  |g(X_T,rho) - g(X'_T,rho')| <= L(|X_T - X'_T| + W_2(rho,rho')), w2P on P_2(R^n). OK.
- Diagonal inputs are tuples in TupleH(0) (trivial U-channel) - equivalent to tuples in the reduced
  space; the measure argument is the input's own law (diagonal, not free). OK.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices: the Brownian tuple space is TupleH at nu = 0 (U-channel L^2(0) = {0}) rather
than R^n x R^m x R^{m x d}, with W_2 taken on the projected laws (projP2, the reduced Hilbert norm);
the constant L is a parameter with 0 <= L instead of an existential (the existential is placed at
use sites); the filtration is a parameter (instantiated with enlBrownian).
Disagreements with the author's review (shown 2026-10-19T03:32:44Z): none
