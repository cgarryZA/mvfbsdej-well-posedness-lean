### A:eq:coefmeas: Dissertation.WellPosedness.Existence.ProgTuple.mk
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash e1108dc351d6859c0000000000000000 (pl-fp-v1:cf0954a1720e0ae7553e33bb8b0010fcfc7d6bcca8dffccf5132b2be724a0528)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T16:02:09Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T15:42:32Z):
Reading for def:Dissertation.WellPosedness.Existence.ProgTuple.mk (locked before seeing Lean).

Constructor of a "progressively measurable tuple" structure, used for (2.5) eq:coefmeas (the
coefficient processes along a tuple are progressively measurable / predictable). Paper notion:
Theta = (X,Y,Z,U) with X (R^n), Y (R^m) cadlag adapted (hence progressive), Z (R^{m x d}) and
U (L^2(nu;R^m)) predictable (hence progressive); the claim (2.5) needs psi(s,Theta_s,mu_s)
progressive, which follows from Theta progressive and psi jointly Borel.
Faithful constructor: four component processes on [0,T] x Omega (or R>=0 x Omega) of the right
types with progressive measurability w.r.t. the standing filtration (each component or the
H-valued tuple; equivalent as H is a product of separable metrizable spaces). A weaker
requirement than cadlag adapted/predictable is broader (fine for (2.5) since the paper's tuples
are instances). Any integrability fields must not be stronger than the paper's tuples satisfy.
Comparison (verdict recorded 2026-10-17T15:57:01Z):
Comparison for def:Dissertation.WellPosedness.Existence.ProgTuple.mk (constructor of ProgTuple).

Lean fields (Existence/WPZero.lean): each coordinate of X and Y adapted (on all of R) with every path
right-continuous at every t in R; each coordinate of Z jointly measurable, progressively measurable,
finite energy on [0,T]; each coordinate of U jointly measurable, marked progressively measurable,
finite marked energy on [0,T]. Used in CoeffRegular (for every ProgTuple there is gamma with
CrossEval), the first line of (2.5).

Against my reading:
- four component processes of the right types (R^n, R^m, R^{m x d} coordinates; U as a mark
  function, its L^2(nu) class taken by tupleAt): yes.
- progressive measurability: X, Y adapted and right-continuous, hence progressive; Z, U progressive
  (marked progressive). Weaker than the paper's cadlag adapted / predictable, i.e. a broader class,
  which strengthens a statement quantifying over all such tuples: fine.
- integrability: Z, U of finite energy, which the paper's tuples (H^2_W, H^2_N) have; X, Y carry no
  integrability requirement (broader). Fine.
- every path right-continuous on all of R (not a.s., and also off [0,T]): a version/extension
  convention; the paper's cadlag tuples on [0,T] extended constantly outside [0,T] satisfy it over
  the standing filtrations (frozen before 0), and a.s.-cadlag adapted processes on an augmented
  filtration have everywhere-cadlag versions.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices: (1) X, Y adapted with every path right-continuous at every real time (a
version and an extension off [0,T]; cadlag tuples on [0,T] extended constantly satisfy it on the
standing filtrations), left limits not required (broader); (2) Z, U progressively (marked
progressively) measurable instead of predictable (broader class, enough for (2.5)'s
progressive-measurability line); (3) Z, U of finite energy on [0,T], as every tuple of HH/Hweak is;
(4) coordinatewise components, U as a jointly measurable mark function.
Disagreements with the author's review (shown 2026-10-17T16:02:02Z): The author's review entry is empty (no recorded reading). It should record that the class is
X, Y adapted with every path right-continuous on all of R (no left limits, no integrability) and
Z, U progressive (not predictable) with finite energy: broader than the paper's cadlag/predictable
tuples in measurability, with the every-path, all-of-R right-continuity a version/extension
convention.
