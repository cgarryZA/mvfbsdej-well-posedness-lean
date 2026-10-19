### A:lem:small: Dissertation.PaperSpec.A.lem_small
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba12f6a12214671fd14 (pl-fp-v1:1bfa7ca8c569a48a41882963525fb17c2548c974895451fd53b2baebd0cdf559)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:37:18Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:16:44Z):
# Reading: spec lem_small (Lemma 4.2, main)

Lemma 4.2: Under Assumptions 2.2-2.3, there is lambda* in (0,1], depending only on T, L and c_BDG,
such that WP(lambda) holds for every lambda in [0, lambda*].
A faithful formal statement must contain:
* Constant: lambda* chosen BEFORE the basis, dimensions n,m,d, nu, the coefficients and xi0: as a
  function of (T, L) (c_BDG is universal), with 0 < lambda* <= 1. A lambda* chosen after nu, the
  dimensions or the coefficients would be weaker than printed.
* Hypotheses: standing basis, T > 0; coefficients b, sigma, h, f, g (deterministic, jointly Borel,
  incl. (2.3)) satisfying Assumption 2.2 (with xi0 in L^2(F_0)) and Assumption 2.3 with constant
  L >= 0. NO monotonicity, no G.
* Conclusion: for every lambda in [0, lambda*], WP(lambda): for EVERY square-integrable forcing q
  (q^b, q^sigma, q^f progressive and in L^2(Omega x [0,T]), q^h predictable P (x) E-measurable and
  in L^2(dP x dt x nu), q^g_T in L^2(Omega,F_T)), the forced system (4.1) at lambda with initial
  datum xi0 has a solution in HH and it is unique (modulo the HH identification).
* The solution notion of (4.1): Theta in HH, both identities a.s. for every t in [0,T], h at the
  predictable tuple, law arguments Law(Theta_s), Law(Theta^-_s), Law(X_T).
Comparison (verdict recorded 2026-10-19T03:30:42Z):
# Comparison: lem_small (Lemma 4.2)

Lean (Sec4.lean): EXISTS lamStar : R -> R -> R such that for every standing basis (any
sigma-finite nu on countably generated E, n, m, d >= 1, G0 independent, filtration enlJoint),
every T > 0, L, coefficients C and xi0: JointBorel T C (the standing (2.3)), Assumption22 (with
xi0) and Assumption23 (constant L) imply 0 < lamStar T L <= 1 and WP(lam) for every
lam in [0, lamStar T L].

Against my reading:
* Constant: lambda* = lamStar(T, L) chosen FIRST, as a function of (T, L) only (c_BDG universal),
  before the basis, the dimensions, nu, the coefficients and xi0: yes.
* lambda* in (0, 1]: yes (asserted under the hypotheses, which is where the paper asserts it).
* Hypotheses: Assumptions 2.2-2.3 and the standing joint Borel measurability; no G, no
  monotonicity: yes.
* Conclusion: WP(lambda) for all lambda in [0, lambda*], with WP = PaperSpec.A.WP (for every
  forcing in the paper's class PredForcing: existence of a solution of (4.1) in HH
  (ForcedSolution) and uniqueness modulo the HH identification): yes. See the reviews of WP,
  ForcedSolution, PaperSolutionForced, Forcing, PredForcing for their representation choices.
* Setting: arbitrary nu (finite or infinite activity), n, m, d >= 1, any T > 0: yes.
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-19T03:37:10Z): Classification only. The reviewer records "faithful with representation choices"; I record
"faithful" for the proposition itself: lambda* = lamStar(T, L) is chosen first, depends only on
(T, L), and the hypotheses (Assumptions 2.2-2.3 with the standing Borel measurability) and the
conclusion (lambda* in (0,1], WP(lambda) on [0, lambda*]) are the printed ones. The representation
choices live in the definitions WP, ForcedSolution, PaperSolutionForced, Forcing and PredForcing,
which I reviewed separately as "faithful with representation choices". No disagreement about the
mathematics.
