### A:eq:forced, A:lem:cont, A:lem:pert, A:lem:small, A:sec4:WP-def: Dissertation.WellPosedness.System.Forcing.mk
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash de3e0249fbf732c50000000000000000 (pl-fp-v1:2c845628ef564e2ab7a5398fa29edf4ae270d66944ca1f9eeb36f59caba60a1f)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T16:02:38Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T15:42:32Z):
Reading for def:Dissertation.WellPosedness.System.Forcing.mk (locked before seeing Lean).

Constructor of the forcing structure of (4.1): q = (q^b, q^sigma, q^h, q^f, q^g_T) with
 q^b : [0,T] x Omega -> R^n, q^sigma : -> R^{n x d}, q^f : -> R^m progressively measurable and
 square-integrable for dt(x)dP;
 q^h : [0,T] x Omega x E -> R^n (or L^2(nu;R^n)-valued) predictable (P(x)E-measurable),
 square-integrable for dP dt nu;
 q^g_T : Omega -> R^m, F_T-measurable, square-integrable.
Faithful constructor: these five fields with these types. Measurability/integrability may be
fields or imposed by a separate predicate where WP quantifies over forcings; if the structure has
no conditions and WP quantifies over all such structures, WP would range over non-admissible
forcings (then WP would be a stronger notion). q^h must be a genuine Poisson-integrand
(predictable) so that int int q^h dNtilde is defined.
Comparison (verdict recorded 2026-10-17T15:58:30Z):
Comparison for def:Dissertation.WellPosedness.System.Forcing.mk (constructor of the Prop structure Forcing).

Lean fields (System/Coefficients.lean): q^b, q^sigma, q^f (coordinates): jointly measurable, progressively
measurable, 0 off [0,T], finite energy on [0,T]; q^h: jointly measurable in (omega, s, e), marked
progressively measurable, 0 off [0,T], finite marked energy E int_0^T int_E |q^h|^2 dnu ds; q^g_T: strongly
F_T-measurable (source: StronglyMeasurable[F T]) and in L^2(P).

Against my reading:
- the five components with the paper's types (coordinates of R^n, R^{n x d}, R^n-valued mark
  function, R^m, R^m): yes.
- q^b, q^sigma, q^f progressive and square integrable on Omega x [0,T]: yes.
- q^g_T in L^2(Omega, F_T; R^m): yes.
- q^h: square integrable for dP dt nu: yes; but marked progressive rather than predictable
  (P(x)E-measurable). Broader than the paper's class. Where the paper's exact class matters (WP
  quantifies over all forcings) the Lean uses PredForcing = Forcing + q^h marked predictable, which is
  the paper's class; elsewhere (forcing hypotheses of Lemma 4.3, forcings built in proofs) the
  broader class only strengthens statements, and Forcing.exists_predForcing gives a predictable
  version a.e. equal, with the same library integral.
- extension by 0 off [0,T]: convention (bijective with forcings on [0,T]).
My reading's concern (WP must not range over non-admissible forcings) is met by PredForcing.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices: (1) forcings in coordinates and extended by 0 off [0,T]; (2) q^h is
required jointly measurable and marked progressively measurable instead of predictable; the
paper's predictable class is PredForcing (Forcing plus marked predictability of q^h), which is what
WP quantifies over, and every Forcing has an a.e.-equal predictable version
(Forcing.exists_predForcing) with the same L^2 integral; (3) the progressive components are also
required jointly measurable (implied by progressive measurability in the paper's sense).
Disagreements with the author's review (shown 2026-10-17T16:02:32Z): The author's review entry is empty (no recorded reading). It should record that q^h is only marked
progressive here (broader than the paper's predictable class), that the paper's class is
PredForcing (used by WP), and the extension-by-0 convention.
