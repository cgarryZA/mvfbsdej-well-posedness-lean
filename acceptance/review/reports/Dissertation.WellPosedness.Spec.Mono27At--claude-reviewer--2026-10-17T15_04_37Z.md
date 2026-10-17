### A:ass:mono, A:cor:robust, A:ex:brownian, A:ex:concrete, A:lem:cont, A:lem:pert, A:rem:diag-mono, A:rem:generalrank, A:rem:intrinsic, A:sec4:horizon-not-contractive, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: Dissertation.WellPosedness.Spec.Mono27At
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash a59346236526d219b3e1099916102f71 (pl-fp-v1:39cd9671497b1f96f995f13a8c7387cca6b9e45fbf15c3e30bb34b3e19bcdf35)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:04:37Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:37:09Z):
Unit: def Spec.Mono27At (the interior monotonicity (2.7) at one time t).
Paper: at time t, for all (Theta,mu), (Theta',mu') in D_t (F_t-measurable square-integrable
H-valued tuples with their laws),
  E[ <db, G^T dY> + <dsigma, G^T dZ>_F + <-df, G dX> + int_E <dh(e), G^T dU(e)> nu(de) ]
    <= -beta1 E[ |G^T dY|^2 + |G^T dZ|_F^2 + ||G^T dU||_{L^2(nu)}^2 ] - beta2 E |G dX|^2,
with db = b(t,Theta,mu) - b(t,Theta',mu') etc., G in R^{m x n}, G^T dY in R^n, G^T dZ in R^{n x d},
G^T dU in L^2(nu;R^n) (pointwise in e), <.,.>_F Frobenius, the jump pairing
int_E <dh(e), G^T dU(e)> nu(de) = the L^2(nu;R^n) inner product <dh, G^T dU>.
Faithful Lean: a predicate over (F, P, t, G, beta1, beta2, C) quantifying over all such pairs,
with genuine expectations. Caveat on integrability: in the paper the expectations are finite
for square-integrable inputs when the coefficients satisfy the growth implied by Assumptions
2.2-2.3; if Lean uses Bochner integrals, a non-integrable left side would be read as 0 (junk);
check whether this can make the condition weaker or stronger than intended. Sign convention:
<-df, G dX> (minus on f).
Comparison (verdict recorded 2026-10-17T15:03:41Z):
Mono27At F P t G beta1 beta2 C (Spec/Assumptions.lean): for all p, p' in diagonalInputs F P t,
Integrable (pairing27 G C t (p.1 .) (p'.1 .) p.2 p'.2) and
 E pairing27 <= -beta1 E(||G^T dY||^2 + ||G^T dZ||^2 + ||G^T dU||^2_{L^2(nu)}) - beta2 E||G dX||^2,
pairing27 = <db, G^T dY> + <dsigma, G^T dZ>_F + <-df, G dX> + int_E <dh(e), G^T dU(e)> nu(de)
(GX G^T : R^m -> R^n; GZ G^T = (G^T (x) I_d) acting on R^{m x d} columnwise, the Frobenius pairing
being the EuclideanSpace (Fin n x Fin d) inner product; the jump pairing a Bochner integral over e
of representatives, integrable by Cauchy-Schwarz and independent of representatives, equal to the
L^2(nu;R^n) inner product <dh, G^T dU>; GU G^T the markwise action).
Matches the reading: diagonal pairs at t with their genuine laws, sign of f, G-weights, beta-blocks.
Representation choice: integrability of the pairing required (the junk-0 concern of my reading is
thereby avoided on the left side; right-hand integrands are integrable for L^2 inputs). Under
Assumption 2.3 at t and (2.3) the integrability is automatic.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — The expectation of the pairing is required to exist (Integrable) before the inequality, the natural
reading of the printed E[...] and automatic under Assumption 2.3 with (2.3); inputs are strongly
F_t-measurable representatives of L^2 classes; the jump pairing is the Bochner integral over the mark
of representatives, equal to the L^2(nu) inner product.
Disagreements with the author's review (shown 2026-10-17T15:04:22Z): No disagreement on substance. The author's review is an empty marker with no recorded
comparison; the representation choices listed in my detail are not recorded there.
