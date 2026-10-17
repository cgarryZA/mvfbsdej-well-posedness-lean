### A:ass:lip, A:ass:mono, A:cor:robust, A:def:diag, A:eq:coeffint, A:eq:coefmeas, A:eq:forced, A:eq:mvfbsdej, A:eq:termg, A:ex:brownian, A:ex:concrete, A:intro:mvfbsdej, A:lem:cont, A:lem:lawflow, A:lem:pert, A:lem:small, A:prop:strict, A:rem:cwp-class, A:rem:diag-mono, A:rem:generalrank, A:rem:intrinsic, A:remark-2.6, A:sec2:coefmeas, A:sec3:one-null-set, A:sec4:WP-def, A:sec4:horizon-not-contractive, A:sec:examples, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: Dissertation.Law.lawP2
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 8e02ec4a91100180227c044dc87cf8fe (pl-fp-v1:f1b949e124e025a0e3187c223f672d5abc484a3e23c69270b1d0ca566cb245a9)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T12:12:13Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:11:41Z):
# Reading: the law of a square-integrable random tuple (def:Dissertation.Law.lawP2)

Paper's notion. For Theta in L^2(Omega, F_t; E) (E = H or R^n), Law(Theta) = P ∘ Theta^{-1}, the
image of P under Theta, an element of P_2(E) since E|Theta|^2 < ∞ (Def. 2.1: diagonal input
(Theta, Law(Theta)); mu_t = Law(Theta_t); rho = Law(X_T); g(X_T, Law(X_T))). It depends only on
the a.s.-class of Theta. Law is defined on the probability space of the standing basis (P).

A faithful Lean definition: a function of (P, Theta) returning an element of `P2 E` whose law is
`P.map Theta` whenever Theta is (a.e.-strongly) measurable with finite second moment
(`MemLp Θ 2 P`); P a probability measure. Since Lean functions are total, a junk value for
Theta not in L^2 is acceptable provided every proposition only evaluates it on square-integrable
Theta (diagonal inputs) or quantifies with that hypothesis; the junk value must not leak into
a claim (e.g. Ass. 2.3 for g "for all X_T in L^2(Omega,F_T;R^n)" is fine if the hypothesis is
present). Edge cases: Mathlib's `Measure.map` of a non-AEMeasurable function is 0 (not a
probability measure), so a definition of the form `P.map Θ` with no membership must not be
claimed as an element of P_2 without proof; with AEMeasurable Theta, `P.map Θ` agrees with the
pushforward of any measurable modification.
Comparison (verdict recorded 2026-10-17T12:12:05Z):
# Comparison: lawP2

Lean: `lawP2 P Θ : P2 F` := if `MemLp Θ 2 P` then the element with law `P.map Θ` else
`P2.dirac 0` (LawP2.lean:66-76); P a probability measure, F Borel.

- On square-integrable Theta (MemLp = a.e.-strongly measurable and E‖Θ‖^2 < ∞): law =
  `P.map Θ`, the image measure, a probability measure of finite second moment. Matches
  Law(Theta) exactly. For the paper's separable F, a.e.-strong measurability = a.e.
  measurability, so `MemLp Θ 2 P` is exactly Theta ∈ L^2(Omega; F). `Measure.map` of an
  AEMeasurable map is the pushforward of a measurable modification, so it depends only on the
  a.s. class (lemma `lawP2_congr`), as the paper's law.
- Off L^2: junk value δ_0. The paper's Law(Theta) in P_2 is only defined for Theta in L^2, so
  this is a totalisation; it is harmless where the propositions evaluate it only on
  square-integrable tuples (diagonal inputs Θ ∈ L^2(Ω, F_t; H), X_T ∈ L^2). Where a statement
  evaluates `lawP2` on a random variable not assumed square-integrable (e.g. g(X_T, Law X_T)
  for a solution class that does not force X_T ∈ L^2), the junk value could matter: that is to
  be checked at the use site (notably the weak-solution notion, a later unit).
- The σ-algebra of Omega used is the ambient `m` (implicit); F_t-measurability is a separate
  hypothesis at the use sites. Fine.

Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choice: Lean's total `lawP2 P Θ` returns the Dirac mass at the origin when Θ is
not square integrable (not `MemLp Θ 2 P`); on square-integrable Θ it is exactly the image law
P ∘ Θ^{-1} as an element of P_2. Harmless because the paper's Law(Θ) ∈ P_2 is only defined for
Θ ∈ L^2, and the diagonal inputs, the terminal laws Law(X_T) of S^2 solutions and the coupling
bounds are all taken on square-integrable variables. Each proposition that applies `lawP2` to
a variable not assumed square integrable must be checked at the use site (the junk δ_0 then
enters a coefficient evaluation such as g(X_T, Law X_T)).
Disagreements with the author's review (shown 2026-10-17T12:12:05Z): Agree with the reading of the definition. Caveat: the author's justification ('a statement quantifying over L^2 variables never reaches it') covers only uses that carry an L^2 hypothesis; whether every proposition does (e.g. a solution class in which X_T is not forced to be square integrable, so that g(X_T, lawP2 P X_T) could see the junk delta_0) must be checked at each use site, not settled by this definition review.
