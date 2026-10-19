### A:ex:concrete: Dissertation.PaperSpec.A.ex_concrete_i_pairing
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba1272d037d1e16e040 (pl-fp-v1:6bf70d33977df7022eecd20e2968bdde3b0930239f28c6c0a6699f06ef429f4c)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:38:21Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:16:44Z):
# Reading: spec ex_concrete_i_pairing (Example 5.1(i): the exact pairings, the margin and the jump identity)

Setting of Example 5.1(i) (n=m=d=1, G=1, nu arbitrary sigma-finite, sigma_c, h_c in L^2(nu),
beta1, beta2 > 0; b=-beta1 y, sigma=sigma_c-beta1 z, h=h_c-beta1 u, f=beta2 x, g=x).
Content (conjunction):
(a) interior pairing, exactly: for every t (or a.e. t) and all diagonal pairs at t,
    E[<db,dY> + <dsigma,dZ> + <-df,dX> + int <dh(e),dU(e)> nu(de)]
      = -beta1 E[|dY|^2+|dZ|^2+||dU||^2] - beta2 E|dX|^2;
(b) terminal pairing, exactly: for all X_T, X'_T in L^2(F_T), E<dg_T, dX_T> = E|dX_T|^2;
(c) the margin: for every 0 < c < min{beta1, beta2}, the system carries margin c, unweighted with
    the same constant (G = 1, c_G = 1): by Remark 2.11 the bound is (2.12)/(2.13) with the REDUCED
    constants beta1 - c, beta2 - c and margin c, i.e.
    E[pairing] <= -(beta1-c) E[|dY|^2+|dZ|^2+||dU||^2] - (beta2-c) E|dX|^2
                  - c E[|dY|^2+|dZ|^2+||dU||^2+|dX|^2]   (for a.e. t, all diagonal pairs);
    (with G = 1 the weighted and unweighted forms coincide). A version with constants
    beta1' <= beta1 - c, beta2' <= beta2 - c is also faithful; a version with the original
    constants and margin c would be false; one with zero constants would be weaker than printed
    (and would not give a baseline satisfying Assumption 2.5 with margin).
(d) the jump identity: int_E <dh(e), dU(e)> nu(de) = -beta1 ||dU||^2 (pointwise for
    u, u' in L^2(nu), i.e. without expectation; a.s. for random inputs).
The quantifiers: every basis/T/nu, sigma_c, h_c, beta1, beta2 > 0.
Comparison (verdict recorded 2026-10-19T03:34:41Z):
# Comparison: ex_concrete_i_pairing (Example 5.1(i): exact pairings, margin, jump identity)

Lean (Sec5.lean): for every standing basis (any sigma-finite nu, d = 1, G0 independent), T > 0,
beta1, beta2 > 0, sigma_c, h_c, with the affine coefficients and G = 1, the conjunction of:
 (a) for EVERY t and all pairs of diagonal inputs at t:
     E[pairing27 1 C t Theta Theta' mu mu'] = -beta1 E[|dY|^2 + |dZ|^2 + ||dU||^2] - beta2 E|dX|^2;
 (b) for all F_T-measurable square-integrable X_T, X'_T: E<g(X_T, rho) - g(X'_T, rho'), dX_T> = E|dX_T|^2;
 (c) for every 0 < c < min{beta1, beta2}: Margin213 with constants (beta1 - c, beta2 - c) and margin
     c — (2.13): for a.e. t and all diagonal pairs, the pairing is integrable and its expectation is
     <= -(beta1-c) E[|G^T dY|^2 + |G^T dZ|^2 + ||G^T dU||^2] - (beta2-c) E|G dX|^2
        - c E[|dY|^2 + |dZ|^2 + ||dU||^2 + |dX|^2];
 (d) for all t, theta, theta', mu, mu': int_E <h(theta)(e) - h(theta')(e), du(e)> nu(de) = -beta1 ||du||^2.

Against my reading: (a) exact interior identity (every t, stronger than a.e.), (b) exact terminal
identity, (c) the margin with the REDUCED constants (beta1 - c, beta2 - c) for every c in
(0, min{beta1, beta2}) — the Remark 2.11 reading, not the false one with the original constants
nor the weak one with zero constants; unweighted form, which equals the weighted one at G = 1
(c_G = 1); (d) the jump identity pointwise, without expectation. Setting universally quantified
as printed (any nu, T, sigma_c, h_c, beta's). The Bochner expectations are of integrable functions
(affine coefficients, L^2 inputs), so the equalities are genuine, not junk.
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-19T03:38:15Z): none
