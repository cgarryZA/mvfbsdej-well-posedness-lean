### A:ass:mono, A:cor:robust, A:ex:brownian, A:ex:concrete, A:lem:cont, A:lem:pert, A:rem:diag-mono, A:rem:generalrank, A:rem:intrinsic, A:sec4:horizon-not-contractive, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: Dissertation.WellPosedness.Spec.Assumption25
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 2ad64300a1211b960000000000000000 (pl-fp-v1:5131e5ce858f7b44ab6c10cd0a24079131b811301c79042576510828013b6193)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:04:37Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:35:45Z):
Unit: def Spec.Assumption25 (Assumption 2.5, terminal and interior jump-extended
G-monotonicity; 13 more claims).
Paper: with G in R^{m x n} (full rank by Assumption 2.4), constants alpha, beta1, beta2:
 (terminal) for all X_T, X'_T in L^2(Omega, F_T; R^n), with rho, rho' their laws,
   E <g(X_T,rho) - g(X'_T,rho'), G (X_T - X'_T)> >= alpha E |G (X_T - X'_T)|^2;
 (interior) for a.e. t in [0,T] and all diagonal inputs (Theta,mu), (Theta',mu') in D_t,
   E[ <db, G^T dY> + <dsigma, G^T dZ>_F + <-df, G dX> + int_E <dh(e), G^T dU(e)> nu(de) ]
     <= -beta1 E[ |G^T dY|^2 + |G^T dZ|_F^2 + ||G^T dU||^2_{L^2(nu)} ] - beta2 E|G dX|^2,
   (sigma in R^{n x d}, so G^T dZ in R^{n x d} pairs with dsigma; h in L^2(nu;R^n), G^T dU in
   L^2(nu;R^n); <.,.>_F the Frobenius pairing);
 (constants) alpha, beta1, beta2 >= 0, alpha + beta1 > 0, beta1 + beta2 > 0, beta1 > 0 if m < n,
   alpha, beta2 > 0 if m > n.
Faithful Lean: a predicate over (F, P, T, G, alpha, beta1, beta2, C) containing the terminal
inequality in expectation (all square-integrable F_T-measurable pairs), the interior one in
expectation for a.e. t (one null set chosen before the inputs) and all pairs of F_t-measurable
square-integrable inputs with their own laws, and the constant pattern (the Constants
structure). Expectations must be genuine (the integrands are integrable for L^2 inputs if the
coefficients are Lipschitz; but Assumption 2.5 itself does not presuppose 2.3 — if the Lean
uses Bochner integrals, a non-integrable integrand gives junk 0, which would change the meaning
when integrability fails; check how integrability is handled). Full rank of G belongs to
Assumption 2.4, not 2.5.
Comparison (verdict recorded 2026-10-17T15:02:05Z):
Assumption25 F P T G alpha beta1 beta2 C (Spec/Assumptions.lean:187): fields
 terminal: for all strongly F_T-measurable square-integrable X_T, X'_T: the pairing
   omega |-> <g(X_T, lawP2 X_T) - g(X'_T, lawP2 X'_T), G (X_T - X'_T)> is integrable and its integral
   is >= alpha * E ||G (X_T - X'_T)||^2;
 interior: for a.e. t in [0,T], Mono27At F P t G beta1 beta2 C: for all p, p' in the diagonal at t,
   pairing27 integrable and E pairing27 <= -beta1 E(|G^T dY|^2 + |G^T dZ|_F^2 + ||G^T dU||^2)
   - beta2 E |G dX|^2, with pairing27 = <db, G^T dY> + <dsigma, G^T dZ>_F + <-df, G dX>
   + int_E <dh(e), G^T dU(e)> nu(de) (GX G^T : R^m -> R^n, GZ G^T = G^T (x) I_d columnwise,
   GU G^T the markwise action on L^2(nu), the jump pairing a Bochner integral over e of
   representatives, integrable by Cauchy-Schwarz, independent of representatives);
 constants: Constants n m alpha beta1 beta2 (reviewed: exactly the printed side conditions).
Comparison with the reading: terminal and interior inequalities, quantifier order (a.e. t before
the inputs), diagonal inputs with their own laws, G-weights and sign of f, and the constant pattern
all match. Full rank of G is not included (it is Assumption 2.4, separate), as it should be.
Representation choices: (1) the expectations of the two pairings are required to exist
(Integrable); the paper writes E[...] without comment. Under Assumption 2.3 together with the
joint measurability (2.3), which every statement assumes alongside 2.5, the pairings of
square-integrable inputs are integrable (|db| <= L(...) in L^2 and G^T dY in L^2), so the extra
requirement is automatic there; without it an undefined (or -infinity) expectation would make the
printed inequality meaningless or trivial, and asking existence is the natural reading. The
right-hand Bochner integrals are of integrable nonnegative functions for L^2 inputs, so no junk.
(2) inputs strongly F_t-measurable representatives of L^2 classes (harmless, as for 2.3).
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — 1. Each of the two expectations of pairings is required to exist (Integrable) before the
   inequality; automatic under Assumption 2.3 and the joint measurability (2.3), which the
   statements always assume together with 2.5, and the natural reading of the printed E[...].
2. Inputs are strongly F_t- (resp. F_T-) measurable square-integrable representatives with their
   laws lawP2; every L^2 class has such a representative and the conditions are invariant under
   null modifications.
3. Expectations are Bochner integrals; the right-hand ones are of integrable functions for L^2
   inputs, so no junk value enters.
Disagreements with the author's review (shown 2026-10-17T15:04:21Z): No disagreement on substance. The author's review is an empty marker with no recorded
comparison; the representation choices listed in my detail are not recorded there.
