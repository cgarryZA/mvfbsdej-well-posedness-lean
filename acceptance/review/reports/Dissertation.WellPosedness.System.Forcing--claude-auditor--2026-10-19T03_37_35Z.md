### A:eq:forced, A:lem:cont, A:lem:pert, A:lem:small, A:sec4:WP-def: Dissertation.WellPosedness.System.Forcing
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash a3ba59f5823fbe6a0000000000000000 (pl-fp-v1:a0b53f2bd3cc2761240a40da2e50fb1607c62933350668a2055e73a26be013ca)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:37:35Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:16:44Z):
# Reading: def WellPosedness.System.Forcing

Paper notion: a square-integrable forcing q = (q^b, q^sigma, q^h, q^f, q^g_T) of (4.1):
  q^b in L^2(Omega x [0,T]; R^n), q^sigma in L^2(Omega x [0,T]; R^{n x d}),
  q^h in L^2(Omega x [0,T] x E; R^n), q^f in L^2(Omega x [0,T]; R^m), q^g_T in L^2(Omega,F_T;R^m),
with q^b, q^sigma, q^f progressively measurable and q^h predictable (P (x) E-measurable as in (2.4),
square-integrable for dP x dt x nu).
A faithful Lean structure "Forcing" must carry the five components with these value spaces (q^h
either as a function of (omega,t,e) or as an L^2(nu;R^n)-valued process, identified by (2.4)), and,
either in this structure or in a companion predicate (e.g. "PredForcing"), the measurability
(progressive for b, sigma, f; predictable for h; F_T-measurable for g_T) and square-integrability
conditions. If Forcing itself requires only progressive measurability of q^h, the companion must
add predictability so that the class used in WP is exactly the paper's. A field set that is too
strong (excluding paper forcings) or too weak (when used alone as the forcing class) changes WP.
Comparison (verdict recorded 2026-10-19T03:31:52Z):
# Comparison: def System.Forcing

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
Disagreements with the author's review (shown 2026-10-19T03:37:30Z): none
