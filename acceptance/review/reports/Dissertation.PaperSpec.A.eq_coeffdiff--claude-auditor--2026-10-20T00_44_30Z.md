### A:eq:coeffdiff: Dissertation.PaperSpec.A.eq_coeffdiff
Pins: manuscript A None; project 6d403c197bfb10fe8808933c6e525ee0ae544fb1; hash ed839d34f480cba1b363f744d12fe99d (pl-fp-v1:c57e5e67224c9c26045dfe642c049155497b53bcb37527a88f97ea0b2013990c)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-20T00:44:30Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-20T00:30:26Z):
Reading of (4.9) (eq:coeffdiff, manuscript/paper/sections/04-proof-wellposedness.tex,
lines 312-348, Step 1 of the contraction in the proof of Lemma 4.2 = lem:small).

Setting: the standing setting of Section 2; coefficients deterministic, jointly Borel. Hypotheses
in force: Assumptions 2.2-2.3 (Lemma 4.2); the inequality itself uses only Assumption 2.3
(diagonal Lipschitz bound for b, sigma, h, f with constant L) and the coupling bound (2.x)
eq:coupling (W_2(mu,mu')^2 <= E|Theta - Theta'|_H^2 for two inputs on the same space), which is a
fact, not a hypothesis. lambda and the forcing q cancel and play no role. Two trial tuples
Theta^1, Theta^2 in S (the solution space \HH), with Borel law flows mu^{Theta^k}_s.

Objects: delta psi_s := psi(s, Theta^1_s, mu^{Theta^1}_s) - psi(s, Theta^2_s, mu^{Theta^2}_s),
psi in {b, sigma, h, f} (for h, either at (Theta_s, mu_s) or at the left-limit tuple and its
law: the text after (4.7) says either form may be used inside dt x dP integrals);
S_s := |delta b_s| + |delta sigma_s|_F + ||delta h_s||_{L^2(nu)} + |delta f_s| (Euclidean,
Frobenius, L^2(nu) norms); delta X = X^1 - X^2 etc.; ||.||_S the solution-space norm
E sup|X|^2 + E sup|Y|^2 + E int (|Z|_F^2 + ||U||^2).

Claim: the chain
  E int_0^T S_s^2 ds
   <= 10 L^2 E int_0^T (|dX_s|^2 + |dY_s|^2 + |dZ_s|_F^2 + ||dU_s||^2) ds
   <= 10 L^2 (T E sup_{t<=T}|dX_t|^2 + T E sup_{t<=T}|dY_t|^2
              + E int_0^T (|dZ_s|_F^2 + ||dU_s||^2) ds)
   <= 10 L^2 max{T,1} ||Theta^1 - Theta^2||_S^2,
(also the pointwise-in-s intermediate E S_s^2 <= 10 L^2 E|delta Theta_s|^2 for a.e. s, displayed
just before, which is a separate step). The constant is explicit: 10 L^2 and L_*^2 = 10 L^2
max{T,1}, with L the Lipschitz constant of Assumption 2.3; nothing to choose before anything
else, but L must be the same L as in the hypothesis.

A faithful formal statement: for every basis, every coefficient system satisfying Assumption 2.3
with constant L (Assumption 2.2 may be present or not: including it matches the point of the
proof; omitting it gives a broader statement that contains the printed one), every lambda and q
(or none, as they are irrelevant), and every Theta^1, Theta^2 in S: the three inequalities, with
all quantities either in [0, infinity] (lintegral) or real with integrability established, so
that no Bochner junk value 0 can make a term vanish. Norms must be the Euclidean, Frobenius and
L^2(nu) norms (with the sup norm on R^n the hypothesis "Lipschitz with constant L" would mean
something else). The law arguments are the laws (Borel flow) of Theta^k_s. Extra hypotheses
(monotonicity, finite nu, continuity of coefficients in t, Theta^k solutions of anything) would
make it narrower.
Comparison (verdict recorded 2026-10-20T00:43:39Z):
Comparison of Dissertation.PaperSpec.A.eq_coeffdiff (Dissertation/PaperSpec/A/Sec4Frozen.lean)
with (4.9) (manuscript/paper/sections/04-proof-wellposedness.tex, lines 325-348, Step 1 of the
contraction in the proof of Lemma 4.2).

Setting and hypotheses: the standing setting (driver, independent G0, augmented filtration,
n, m, d > 0, T > 0); JointBorel, Assumption22 (with some xi0), Assumption23 with constant L; two
trial tuples (X1,Y1,Z1,U1), (X2,Y2,Z2,U2) with HTuple. lambda and the forcing q, fixed in the proof
but cancelling in every difference, are omitted; they do not occur in (4.9). The hypotheses are
those in force (Lemma 4.2: Assumptions 2.2-2.3; the inequality itself uses only 2.3).

Objects. coeffDiffNorm P C Theta1 Theta2 s omega = ||delta b|| + ||delta sigma|| + ||delta h|| +
||delta f|| in [0, infinity], with delta psi = psi(s, Theta1_s(omega), Law Theta1_s) - psi(s,
Theta2_s(omega), Law Theta2_s), norms Euclidean (R^n, R^m), Frobenius (EuclideanSpace on index
pairs), L^2(nu) (Lp norm); Theta^k_s = tupleAt of the coordinate processes. This is S_s, with h at
(Theta_s, mu_s), which the paper allows. The right-hand sides: esq of the X- and Y-differences
(squared Euclidean norms), sum over rows of esq of the Z-difference (squared Frobenius norm), sum
over coordinates of the nu-lintegral of the squared U-difference (squared L^2(nu) norm, infinite
when not square integrable); E sup over [0,T] of the squared X- and Y-differences; energies and
marked energies of the Z- and U-differences (E int_0^T |dZ|_F^2, E int_0^T ||dU||^2); supSize is
||Theta1 - Theta2||_S^2 = E sup|dX|^2 + E sup|dY|^2 + E int (|dZ|_F^2 + ||dU||^2).

Conclusion: the three inequalities, with constants ofReal(10 L^2) and ofReal(10 L^2 max{T,1}),
L the constant of Assumption 2.3 (L >= 0 there). Item by item this is the printed chain:
  E int S^2 <= 10L^2 E int (|dX|^2+|dY|^2+|dZ|_F^2+||dU||^2)
            <= 10L^2 (T E sup|dX|^2 + T E sup|dY|^2 + E int(|dZ|_F^2+||dU||^2))
            <= 10L^2 max{T,1} ||Theta1-Theta2||_S^2.
All quantities are lintegrals in [0, infinity]: no Bochner junk value can make a side vanish.

Representation choices (harmless): [0, infinity]-valued expectations; the law at each time is
lawP2 (the law of Theta^k_s when it is square integrable, which holds for a.e. s for a tuple of S;
the Borel representative of Lemma A.1 agrees with it for a.e. s, so the ds-integral is the same);
h at (Theta_s, mu_s) instead of the left-limit tuple (permitted by the text after (4.7)); the U
channel of the tuple is the L^2(nu) class of the coordinates, 0 off L^2(nu) (a dt x dP-null set for
a tuple of S); iterated integrals in s then omega on one side and omega then s in energy (equal by
Tonelli for the measurable integrands at hand, and in any case the statement is as printed in
content); lambda and q omitted.

Witness: Dissertation.Acceptance.A.frozen_hypotheses exhibits the hypotheses at the affine
instance of Example 5.1(i) (nu a Dirac mass, n = m = d = 1, T = 1, L = 1) with two trial tuples
of S. Non-vacuous. The two trials are both the zero process there (homogeneous system, zero data),
so the witness is degenerate as an instance of the inequality, but the hypotheses on the pair are
separate memberships in S, so satisfiability is all a witness has to show.

Coverage (claim A:eq:coeffdiff in acceptance/claims.json, one clause). The passage is the display
(4.9): the three inequalities and the definition L_*^2 := 10 L^2 max{T,1}. The clause states all
three inequalities, with the constant written out, so it states every assertion of the display.
The pointwise steps just before it (S_s <= L(...) from Assumption 2.3, and E S_s^2 <= 10 L^2
E|delta Theta_s|^2 for a.e. s) lie outside the display and are integrated into its first
inequality; leaving them unstated loses nothing that (4.9) needs. No clause states something the
passage does not claim. The hypotheses are those in force at that point of the printed proof
(standing setting, Assumptions 2.2-2.3, two trials in S). lambda and q are fixed there but do not
enter, so omitting them is immaterial. Nothing beyond these is assumed.
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless:
(1) Every expectation and integral is a lintegral in [0, infinity], so there is no junk value.
(2) The law at each time is lawP2, the actual law of Theta^k_s (Dirac at 0 off L^2). It agrees
with the paper's Borel representative for a.e. s, which leaves the ds-integrals unchanged.
(3) h is evaluated at (Theta_s, mu_s) rather than at the left-limit tuple, which the paper allows
inside dt x dP-integrals.
(4) The U channel enters through its L^2(nu) class, 0 off L^2(nu); that happens only on a
dt x dP-null set for a tuple of S. On the right-hand side ||dU||^2 is computed from coordinates as
sum_k int |dU_k|^2 dnu.
(5) ||Theta1 - Theta2||_S^2 is supSize, and E int |dZ|_F^2 and E int ||dU||^2 are the energies of
the coordinate differences.
(6) lambda and the forcing are omitted, since they cancel and do not occur in (4.9).
(7) The constants are ofReal(10 L^2) and ofReal(10 L^2 max{T,1}), with the same L as in
Assumption 2.3.
Disagreements with the author's review (shown 2026-10-20T00:43:45Z): No disagreement on the reading or on the faithfulness of eq_coeffdiff. My verdict, "faithful with
representation choices", only lists explicitly the conventions the review also describes: the
[0, infinity] reading, the pointwise law flow lawP2 in place of the Borel representative, h at
(Theta_s, mu_s), and the time-outer versus sample-outer integrals.

One remark on the witness. In frozen_hypotheses "the zero tuple and the solution of Theorem 3.5"
are presented as two trials, but at that instance (the homogeneous affine system with xi0 = 0) the
solution is the zero tuple up to indistinguishability. Every quantity in (4.9) is then 0. This is
enough for satisfiability, since the hypotheses on the pair are two separate memberships in S, but
the witness does not exhibit a nondegenerate instance of the inequality.
