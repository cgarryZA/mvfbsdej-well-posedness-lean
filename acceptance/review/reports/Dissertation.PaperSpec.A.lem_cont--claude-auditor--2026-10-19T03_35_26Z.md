### A:lem:cont: Dissertation.PaperSpec.A.lem_cont
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba15f6eb38f12c8d372 (pl-fp-v1:d11b2d38f5f18a28c2f9963e544bf04c0892ed192488ded686e8fe3f4b22060b)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:35:26Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:15:37Z):
Reading (locked before any Lean): spec lem_cont, Lemma 4.4 (Continuation), clause "main".

Paper content. Let Assumptions 2.2-2.5 hold and lambda_* be the small-coupling threshold of Lemma
4.2 (lambda_* = (2 sqrt C_Phi)^{-1} in (0,1/2], depending only on T, L, c_BDG). There is
zeta_0 > 0 depending only on T, L, ||G||, c_G, alpha, beta1, beta2, lambda_*, c_BDG, such that:
if lambda_0 in [lambda_*, 1] and WP(lambda_0) holds, then WP(lambda_0 + zeta) holds for every
zeta in [0, zeta_0] with lambda_0 + zeta <= 1.
WP(lambda): the lambda-scaled forced system (4.1) (with the system's fixed xi_0) has a unique
solution in HH for EVERY square-integrable forcing q = (q^b, q^sigma, q^h, q^f, q^g_T)
(q^b, q^sigma, q^f progressively measurable and in L2(Omega x [0,T]); q^h predictable
P x calE-measurable in L2(dP dt nu); q^g_T in L2(Omega, F_T; R^m)).

A faithful formal statement must contain:
- Quantifier order: for all parameter values (T, L, ||G||, c_G, alpha, beta1, beta2, lambda_*)
  there exists zeta_0 > 0 (a function of these only; c_BDG universal so may be absorbed), and
  THEN for all dims n,m,d, nu, bases, coefficient systems and xi_0 satisfying Assumptions 2.2-2.5
  with those constants (||G|| and c_G the norm and s_min^{-2} of the system's G), for all
  lambda_0 in [lambda_*,1], WP(lambda_0) implies WP(lambda_0+zeta) for all zeta in [0,zeta_0]
  with lambda_0+zeta <= 1. zeta_0 must not depend on n, m, d, nu, the basis, the coefficients,
  lambda_0, or q.
- lambda_*: either the specific threshold of Lemma 4.2 (then its definition must be that of the
  paper, depending on T, L, c_BDG) or an arbitrary lambda_* in (0,1] (broader: the lemma's proof
  only uses lambda_0 >= lambda_* > 0 via Lemma 4.3 with underline-lambda = lambda_*; the printed
  claim is the instance at the threshold). Both acceptable; a fixed lambda_* not equal to the
  paper's threshold and not quantified would be mismatched.
- WP must be defined as in the paper: unique HH-solution for every square-integrable forcing with
  the stated measurability; solutions of (4.1) with genuine integrals and law flows.
- Watch for vacuity: WP(lambda_0) must be satisfiable (e.g. WP(lambda) for lambda <= lambda_* by
  Lemma 4.2), so the implication is not vacuous; the forcing class must not be empty or trivial.
Comparison (verdict recorded 2026-10-19T03:24:45Z):
Comparison: spec lem_cont (Sec4.lean:154-177) against my locked reading.

Quantifier order. "exists zeta0 : R^8 -> R" first, then all bases, dims, coefficients, data: zeta0
is a function of (T, L, ||G||, c_G, alpha, beta1, beta2, lambda_*) only, evaluated at
(T, L, ||GX G|| (operator norm of G), (sMin G ^ 2)^{-1} = c_G, alpha, beta1, beta2, lamStar). It
cannot depend on n, m, d, nu, the basis, the coefficients, lambda_0 or q. c_BDG is universal and
absorbed. Matches.

Hypotheses. Standing setting (G0 independent, enlJoint, nu sigma-finite, n, m, d > 0, T > 0),
JointBorel, Assumptions 2.2, 2.3 (L), 2.4 (G.rank = min m n), 2.5 (G, alpha, beta1, beta2): the
paper's Assumptions 2.2-2.5. lamStar: any real in (0, 1], not specifically the threshold of Lemma
4.2. This is broader: the paper's lambda_* is one such value (lambda_* in (0, 1/2]), and the proof
only uses lambda_0 >= lambda_* > 0 through Lemma 4.3 with lower bound lambda_*.

Conclusion. zeta0(...) > 0 (at the parameters of every system satisfying the hypotheses, which is
what "there is zeta_0 > 0" means), and for all lambda_0 in [lamStar, 1], WP(lambda_0) implies
WP(lambda_0 + zeta) for all zeta in [0, zeta0] with lambda_0 + zeta <= 1. Matches.

WP (Setting.lean): for every forcing q in PredForcing (q^b, q^sigma, q^f jointly and progressively
measurable, square integrable on [0,T], normalised to vanish off [0,T]; q^h marked predictable,
the paper's P x calE, square integrable; q^g_T F_T-measurable in L2), there is a ForcedSolution of
(4.1) in HH (PaperSolutionForced: S^2 X, Y, H^2 Z, U, the forced identities with lambda on b,
sigma, h, f, g and the forcing unscaled, initial datum xi0), and any two ForcedSolutions agree
(X, Y indistinguishable on [0,T], zero energy of the Z-, U-differences). This is the paper's
WP(lambda). The forced integrands lambda psi + q^psi are required square integrable as a whole;
with q square integrable this is equivalent to the paper's separate integrals for lambda != 0 and
is the paper's notion at lambda = 0.

Witness lem_cont_hypotheses: Example 5.1(i) with lamStar = lambda_0 = the Lemma 4.2 constant and
WP(lambda_0) holding (from lem_small), so the hypotheses, including WP(lambda_0), are met.

Verdict: broader.
Witness: —
Verdict: broader — Broader in lambda_*: the proposition holds for every lamStar in (0, 1], with zeta0 a function of
(T, L, ||G||, c_G, alpha, beta1, beta2, lamStar). The printed claim is the instance
lamStar := lambda_*(T, L) = (2 sqrt(C_Phi))^{-1} in (0, 1/2], the small-coupling threshold of
Lemma 4.2 (lem_small supplies it as a function of T and L): then zeta0 depends only on
T, L, ||G||, c_G, alpha, beta1, beta2, lambda_* (and the universal c_BDG), and for lambda_0 in
[lambda_*, 1], WP(lambda_0) gives WP(lambda_0 + zeta) for zeta in [0, zeta0] with
lambda_0 + zeta <= 1. Everything else (quantifier order, hypotheses, WP) matches the paper.
Disagreements with the author's review (shown 2026-10-19T03:35:07Z): Labelling and witness, no disagreement of substance.
(1) The review records "faithful with representation choices" with lambda_* over (0, 1] listed as
a broadening; I record "broader" for that same reason, with the instantiation lambda_* := the
Lemma 4.2 threshold.
(2) The review's caveat that the linked witness exhibits only the coefficient hypotheses no
longer applies at the current state. The linked witness lem_cont_hypotheses
(Acceptance/A/WitnessSec4.lean:121) also exhibits WP(lambda_0) at lambda_0 = lamStar = the
Lemma 4.2 constant, obtained from lem_small. So the inductive premise is shown satisfiable in
Lean.
