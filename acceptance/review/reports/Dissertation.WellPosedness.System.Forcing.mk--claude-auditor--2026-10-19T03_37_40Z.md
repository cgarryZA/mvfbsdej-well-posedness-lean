### A:eq:forced, A:lem:cont, A:lem:pert, A:lem:small, A:sec4:WP-def: Dissertation.WellPosedness.System.Forcing.mk
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash de3e0249fbf732c50000000000000000 (pl-fp-v1:2c845628ef564e2ab7a5398fa29edf4ae270d66944ca1f9eeb36f59caba60a1f)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:37:40Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:16:44Z):
# Reading: def WellPosedness.System.Forcing.mk (constructor)

The constructor of Forcing. Its arguments must be the five forcing components
(q^b : R^n-valued, q^sigma : R^{n x d}-valued, q^h : R^n-valued in (omega,t,e) or L^2(nu;R^n)-valued,
q^f : R^m-valued, q^g_T : R^m-valued F_T-measurable random variable) together with whatever
measurability / square-integrability fields the structure bundles (progressive for b, sigma, f;
F_T-measurability and L^2 for g_T; L^2 for all). Faithful iff these match the paper's forcing class
(with predictability of q^h supplied here or by the companion predicate).
Comparison (verdict recorded 2026-10-19T03:32:15Z):
# Comparison: def System.Forcing.mk (constructor; the arguments are exactly the fields of Forcing listed below)

Lean (System/Coefficients.lean): structure Forcing F P nu T qb qsigma qh qf qg with fields
qb_meas, qb_prog (progressive), qb_vanish (0 off [0,T]), qb_sq (finite energy on [0,T]); the same
for qsigma (coordinates of R^{n x d}) and qf; qh_meas (jointly measurable in (omega, s, e)), qh_prog
(marked progressively measurable), qh_vanish, qh_sq (finite marked energy dP x dt x nu);
qg_meas (strongly F_T-measurable), qg_sq (L^2). Components: qb : Fin n -> Omega -> R -> R,
qsigma : Fin n -> R -> Omega -> Fin d -> R, qh : Fin n -> R -> Omega -> E -> R (pointwise in the
mark), qf : Fin m -> Omega -> R -> R, qg : Fin m -> Omega -> R.

Against my reading: the five components with the paper's value spaces (coordinatewise; q^h as a
function of (omega, t, e), the paper's L^2(Omega x [0,T] x E; R^n) element): yes. Square
integrability of all, progressive measurability of q^b, q^sigma, q^f, F_T-measurability of q^g_T:
yes. q^h is only marked PROGRESSIVE, not predictable; as my reading anticipated, the companion
PredForcing adds marked predictability, and WP quantifies over PredForcing. On its own Forcing is
the paper's class up to dP x dt x nu-null changes of q^h: every marked progressive q^h of finite
energy agrees a.e. with a marked predictable one (Forcing.exists_predForcing), and q^h enters
(4.1) only through its L^2 Poisson integral, which sees only that class
(PaperSolutionForced.congr_qh).
Representation choices: coordinates; extension by 0 off [0,T]; q^h marked progressive (paired
with PredForcing where the paper's predictable class is needed).
Verdict: faithful with representation choices.

Constructor check: Forcing.mk takes exactly the 18 fields of Forcing in order (qb_meas, qb_prog,
qb_vanish, qb_sq, the four for qsigma, the four for qh, the four for qf, qg_meas, qg_sq). The
printed signature shows `StronglyMeasurable (qg k)` without the sigma-algebra; the source field is
`StronglyMeasurable[ℱ T] (qg k)` (the explicit-measurable-space notation is not displayed by the
pretty-printer), i.e. F_T-measurability as required.
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless:
1. Coordinate encoding of the five components, q^h as a real function of (omega, t, e) per
   coordinate (the paper's L^2(Omega x [0,T] x E; R^n) representative).
2. Each process is extended by 0 off [0,T] (field *_vanish), as the integrands of the linear
   equations are.
3. q^h is required marked progressively measurable rather than predictable; every such q^h of
   finite energy agrees dP x dt x nu-a.e. with a predictable one, and q^h enters (4.1) only
   through its L^2 compensated integral, so the class is the paper's up to null changes; where the
   predictable class itself is quantified (WP), the companion PredForcing adds predictability.
4. Joint measurability fields are redundant with progressive measurability.
Disagreements with the author's review (shown 2026-10-19T03:37:36Z): none
