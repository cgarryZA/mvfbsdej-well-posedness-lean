### A:eq:forced, A:lem:cont, A:lem:pert, A:lem:small, A:sec4:WP-def: Dissertation.WellPosedness.System.Forcing
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash a3ba59f5823fbe6a0000000000000000 (pl-fp-v1:a0b53f2bd3cc2761240a40da2e50fb1607c62933350668a2055e73a26be013ca)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:50:57Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T15:41:48Z):
Reading for def:Dissertation.WellPosedness.System.Forcing (paper §4, before (4.1)).

Paper notion: a square-integrable forcing q = (q^b, q^sigma, q^h, q^f, q^g_T) with
  q^b in L^2(Omega x [0,T]; R^n), progressively measurable
  q^sigma in L^2(Omega x [0,T]; R^{n x d}), progressively measurable
  q^h in L^2(Omega x [0,T] x E; R^n), predictable (P (x) E-measurable), square integrable for
      dP x dt x nu (equivalently, via (2.4), an L^2(nu;R^n)-valued predictable square-integrable process)
  q^f in L^2(Omega x [0,T]; R^m), progressively measurable
  q^g_T in L^2(Omega, F_T; R^m).
WP(lambda) quantifies over EVERY such forcing.

Faithful Lean: a structure with these five components with exactly these codomains (dimensions
n, n x d, n (jump, forward), m, m), with the measurability (progressive w.r.t. the paper's
filtration for q^b, q^sigma, q^f; predictable for q^h; F_T-measurable for q^g_T) and square
integrability either as fields of the structure or as a predicate imposed in WP(lambda). Edge
cases: if the Lean Forcing imposes stronger conditions (e.g. continuity, boundedness, or
deterministic forcings), WP(lambda) quantifies over fewer forcings and becomes weaker than the
paper's (narrower); if it imposes weaker ones (no measurability), WP(lambda) becomes stronger
(possibly ill-posed: stochastic integrals of non-predictable integrands are junk).
Comparison (verdict recorded 2026-10-17T15:50:04Z):
Comparison for def:Dissertation.WellPosedness.System.Forcing (System/Coefficients.lean:191-236), a
Prop-valued structure on coordinate families qb : Fin n -> Omega -> R -> R, qsigma : Fin n -> R ->
Omega -> Fin d -> R, qh : Fin n -> R -> Omega -> E -> R, qf : Fin m -> Omega -> R -> R, qg : Fin m ->
Omega -> R, over a filtration F and P, nu, T.

Item by item:
- q^b: jointly measurable, ProgressivelyMeasurable F (LevyStochCalc: for every t the process cut
  at Iic t is F_t (x) Borel strongly measurable -- the standard notion), vanishes off [0,T], finite
  energy int^- omega int^-_{[0,T]} |q|^2 (= L^2(Omega x [0,T]) per coordinate, equivalent to the
  vector norm). Matches.
- q^sigma: same, entrywise for the n x d entries (Frobenius-square-integrable iff each entry is).
  Matches.
- q^f: same, m coordinates. Matches.
- q^h: jointly measurable in (omega, s, e), MarkedProgressivelyMeasurable (F_t (x) Borel (x) E cut at t),
  vanishes off [0,T], finite marked energy int int int |q|^2 dnu ds dP. Paper: predictable
  (P (x) E-measurable). Lean asks only marked progressive measurability, which is weaker; the class of
  forcings is therefore (as functions) larger. Harmless: a progressively measurable (marked)
  square-integrable integrand coincides dt x dP x nu-a.e. with a predictable one (time is integrated
  against Lebesgue measure), and the L^2 compensated-Poisson integral only depends on the
  dt x dP x nu class; so the L^2 classes of admissible q^h are the paper's. Documented in the
  module docstring.
- q^g_T: strongly F_T-measurable and MemLp 2 P. Matches L^2(Omega, F_T; R^m).
- Extension by 0 off [0,T]: the paper's forcings live on [0,T]; extension by 0 is a bijective
  convention (and preserves progressive measurability).
- Codomains/dimensions: n, n x d, n (jump, forward), m, m. Match.
- Filtration: generic F; which filtration is used (the paper's augmented one) is decided by the
  propositions.
Neither stronger restrictions (boundedness, continuity) nor missing measurability. Verdict: faithful
with representation choices.
Witness: —
Verdict: faithful with representation choices — Choices: (1) coordinates (each R^j- or R^{n x d}-valued process as a family of scalar processes; vector
square integrability iff each coordinate is); (2) every component extended by 0 off [0,T] (bijective
with the paper's forcings on [0,T], keeps progressive measurability); (3) q^h is required to be
marked progressively measurable rather than predictable -- the class is larger as a set of
functions, but every square-integrable progressive marked integrand agrees dt x dP x nu-a.e. with a
predictable one, and the L^2 compensated Poisson integral depends only on that class, so the
admissible forcings are the paper's up to the identification it makes itself; (4) joint
measurability on Omega x R (x E) stated explicitly (implied by the paper's progressive/predictable
measurability).
Disagreements with the author's review (shown 2026-10-17T15:50:12Z): No disagreement with a stated position (the author's entry shown is only the section heading). For
the record: faithful with representation choices; the one substantive choice is that q^h is required
to be marked progressively measurable instead of predictable, harmless because square-integrable
progressive marked integrands agree dt x dP x nu-a.e. with predictable ones and the L^2 compensated
Poisson integral sees only that class.
