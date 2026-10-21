### A:eq:coeffdiff: Dissertation.PaperSpec.A.eq_coeffdiff_ae
Pins: manuscript A None; project 53a4ee4fc8767ba8884b5732431dded9772b47df; hash ed839d34f480cba122e3ae64778e3109 (pl-fp-v1:6bdc1c3650498f685dc2a56ca7709e1d5758e26e1885fffd844b9de4b9317250)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-20T15:31:29Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-20T15:21:23Z):
Reading of the clause "the bound before (4.9), at almost every s in [0,T]" of claim
A:eq:coeffdiff (manuscript/paper/sections/04-proof-wellposedness.tex, proof of Lemma lem:small,
Step 1, lines 325-337, the display just before (4.9)).

Setting: the standing basis of Section 2 (W d-dimensional Brownian motion, independent Poisson
random measure N with intensity dt nu(de), nu sigma-finite, filtration the usual augmentation of
W, N, F_0); dimensions n, m, d >= 1; the Hilbert space H = R^n x R^m x R^{m x d} x L^2(nu;R^m)
with the sum-of-squares norm; P_2(H) with W_2.

Hypotheses in force (Lemma lem:small: Assumptions ass:integ and ass:lip; only ass:lip is used
by this step):
- deterministic, jointly Borel coefficients b, sigma, h, f on [0,T] x H x P_2(H) with values
  in R^n, R^{n x d}, L^2(nu;R^n), R^m;
- Assumption ass:lip with constant L >= 0: for a.e. t and all diagonal inputs
  (Theta, Law Theta), (Theta', Law Theta') at t (Theta, Theta' in L^2(Omega, F_t; H)),
  |db| + |dsigma|_F + ||dh|| + |df| <= L(|dX| + |dY| + |dZ|_F + ||dU|| + W_2(mu, mu')) a.s.;
- two trial tuples Theta^1, Theta^2 in the solution space S (X, Y cadlag adapted with
  E sup|.|^2 < infinity; Z, U predictable square-integrable), not solutions of anything;
- mu^{Theta^k}_s = Law(Theta^k_s) (the Borel law flow, equal to the law for a.e. s);
- delta psi_s = psi(s, Theta^1_s, mu^{Theta^1}_s) - psi(s, Theta^2_s, mu^{Theta^2}_s) for psi in
  {b, sigma, h, f} (here h is evaluated at Theta_s, mu_s; the left-limit form agrees a.e.);
- S_s := |delta b_s| + |delta sigma_s|_F + ||delta h_s||_{L^2(nu)} + |delta f_s|.

Conclusion: for almost every s in [0,T] (Lebesgue),
  E[S_s^2] <= 10 L^2 E[|dX_s|^2 + |dY_s|^2 + |dZ_s|_F^2 + ||dU_s||^2],
with the explicit constant 10 L^2 (Cauchy-Schwarz in R^5 gives 5L^2 times the five squares,
and W_2^2 <= E[...] by the synchronous coupling doubles it). "a.e. s" is as printed (the
Lipschitz assumption is a.e. in t and the diagonal property holds for a.e. s).

Faithful formal statement: for all such coefficients satisfying ass:lip with L, all Theta^1,
Theta^2 in S (or a broader class: tuples whose time-s values are square-integrable and
F_s-measurable for a.e. s), for a.e. s in [0,T], the displayed bound. L is the constant of the
assumption, not existentially chosen afterwards. Junk values: if E is a Bochner integral, S_s^2
must be integrable at the relevant s (it is, under ass:lip with square-integrable inputs), or
the statement must not be vacuously satisfied by a junk 0 on the left. Broader acceptable
(drop ass:integ, weaker class of tuples); the printed step is the instance Theta^k in S. A
witness should show coefficients satisfying ass:lip with L > 0 and trial tuples with nonzero
differences.
Comparison (verdict recorded 2026-10-20T15:24:27Z):
Comparison of Dissertation.PaperSpec.A.eq_coeffdiff_ae (Dissertation/PaperSpec/A/Sec4ProofSteps.lean)
with the locked reading (Step 1 of the proof of Lemma lem:small, lines 325-337).

Setting. Standing basis as in the other units of this file: Levy driver D (d-dimensional W,
Poisson random measure N with sigma-finite nu on a countably generated E), G0 independent of the
driver's whole filtration, filtration enlJoint = usual augmentation of F^{W,N}_t v G0;
n, m, d > 0, T > 0. Match.

Hypotheses in force at that point of the proof.
- Coefficients C : Coeffs nu n m d (b, sigma with values in R^{n x d} as EuclideanSpace over
  Fin n x Fin d, h with values in L^2(nu; R^n), f, g; arguments t, a point of
  H = TupleH and a law in P_2(H)); deterministic. Match.
- JointBorel T C ((2.3), standing), Assumption22 (xi_0 in L^2(F_0), origin values in
  L^2(0,T)) and Assumption23 with the constant L (L >= 0, the diagonal interior bound for a.e.
  t over all pairs of diagonal inputs, and the terminal bound). These are exactly Assumptions
  ass:integ and ass:lip of Lemma lem:small; L is the given constant of the assumption, not
  chosen afterwards. Match. (Only the interior Lipschitz bound is used by the step; the extra
  assumptions are those in force, so the statement is not narrower than the step as printed.)
- Two trial tuples (X_k, Y_k, Z_k, U_k) with HTuple: PaperWeakTuple (X, Y adapted on [0,T],
  right-continuous paths on [0,T), finite energy; Z coordinates predictable, zero off [0,T],
  finite energy; U coordinates marked predictable, zero off [0,T], finite marked energy) plus
  left limits of every path on (0,T] and E sup_{[0,T]} |X|^2 < infinity, E sup |Y|^2 < infinity:
  membership of the solution space S. No equation is imposed on the trials. Match.

Object S_s. coeffDiffNorm P C Theta_1 Theta_2 s omega = |b(s, Theta_1(s,omega), Law Theta_1(s))
- b(s, Theta_2(s,omega), Law Theta_2(s))| + the same for sigma (Frobenius norm), h (L^2(nu) norm)
and f, in [0, infinity], with Theta_k(s) = tupleAt nu X_k Y_k Z_k U_k s (the point of H made of the
coordinates, the jump channel being the L^2(nu) class of e -> U_k(s, omega, e)). As in the paper's
definition at line 316, h is evaluated at Theta_s, mu_s (not at the left-limit tuple). The law
is lawP2 P (Theta_k s), the image measure when Theta_k(s) is square integrable and a junk Dirac
mass otherwise; since Theta_k(s) is square integrable for a.e. s, this agrees with the paper's
Borel representative mu^{Theta_k}_s for a.e. s, which is all an a.e.-s statement sees.

Conclusion. For volume-a.e. s in [0,T]:
  int^- (S_s)^2 dP <= ofReal(10 L^2) * int^- (|dX_s|^2 + |dY_s|^2 + sum_k |dZ_{k,s}|^2
                                             + sum_k int |dU_{k,s}(e)|^2 nu(de)) dP,
expectations in [0, infinity]. The bracket is |dX_s|^2 + |dY_s|^2 + |dZ_s|_F^2 + ||dU_s||^2
written in coordinates (equal to the H-norm of the difference whenever both jump channels are
in L^2(nu), which holds for a.e. (s, omega)). Constant 10 L^2 exactly; "almost every s" as
printed. Match.

Representation choices (harmless): coordinate processes; Z, U extended by zero off [0,T];
expectations in [0, infinity]; the jump channel as the L^2(nu) class of the coordinate
function (junk 0 if not square integrable, which happens only on a dt x dP-null set); the law by
lawP2 with a junk value off L^2 (only on a Lebesgue-null set of times); the norm of dU on the
right in coordinates rather than as the norm of a difference of classes (equal a.e.).

Witness. Dissertation.Acceptance.A.frozen_pair_window_hypotheses: nu = Dirac mass at 0, d = n =
m = 1, T = 1, G0 trivial, the affine system of Example 5.1(i) with b = -y, sigma = -z, h = -u
(L = 1, JointBorel, Assumption22 with xi_0 = 0, Assumption23 all proved), and the two trials of S
the zero tuple and (1, 1, 1_{(0,1]}, 1_{(0,1]}) (HTuple for both proved). It provides every
hypothesis of the proposition, and the instance is not degenerate: db = 1, dsigma = dh = 1 on
(0,1], so E S_s^2 > 0 and the right side is 10 * 4 at a.e. s. It is an instance the paper
intends (Example 5.1(i) satisfies Assumptions ass:integ-ass:lip).

Coverage. Claim A:eq:coeffdiff has two clauses: eq_coeffdiff ((4.9): the three-link chain
from E int S^2 to L_*^2 ||Theta^1 - Theta^2||^2 with L_*^2 = 10 L^2 max{T,1}) and this one (the
bound at a.e. s before (4.9), lines 333-337). Together they state every mathematical assertion of
the passage from the definition of S_s through (4.9); the pointwise bound S_s <= L(...) (line
330) is the instance of Assumption ass:lip that this clause integrates and needs no separate
clause. Neither clause states something not claimed, and the hypotheses (Assumptions
ass:integ-ass:lip, trials in S) are those in force. As for the other units, the clause reads a
passage outside the pinned source region (lines 339-348), so a change to lines 333-337 would
not by itself reopen the review.
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless: (1) the trial tuples are coordinate processes, with Z, U
extended by zero off [0,T]; (2) expectations are lower Lebesgue integrals in [0, infinity];
(3) the jump channel of the tuple is the L^2(nu) class of the coordinate function, with a junk 0
when it is not square integrable, which happens only on a dt x dP-null set; (4) the law is
lawP2, the image measure for a square-integrable time-s tuple and a junk Dirac mass otherwise,
so it agrees with the paper's Borel law flow for a.e. s, all that an a.e.-s statement sees;
(5) ||dU_s||^2 on the right is written in coordinates, equal to the norm of the difference of
classes for a.e. (s, omega). Hypotheses (Assumptions ass:integ-ass:lip with the given L, (2.3),
two trials of S), the a.e.-s quantifier, the evaluation of h at Theta_s and the constant 10 L^2
match the printed step.
Disagreements with the author's review (shown 2026-10-20T15:30:33Z): No disagreement on substance: same hypotheses (Assumptions ass:integ-ass:lip with the given L, two
trials of S), same a.e.-s reading, same constant 10 L^2, same evaluation of h at Theta_s, and the
witness computation (S_s = 4 on (0,1], 16 <= 40) agrees with mine. Verdict label: I record
"faithful with representation choices" because of choices the review leaves implicit (coordinates;
Z, U extended by zero off [0,T]; expectations in [0, infinity]; junk values of uLift and lawP2,
which occur only on null sets of times or of (s, omega); ||dU_s||^2 written in coordinates rather
than as the norm of a difference of L^2(nu) classes, equal a.e.). Procedural remark: the clause
reads lines 333-337, outside the pinned region of A:eq:coeffdiff (lines 339-348).
