### A:abstract, A:ass:integ, A:ass:lip, A:ass:mono, A:conclusion, A:cor:robust, A:eq:coeffint, A:eq:coefmeas, A:eq:forced, A:eq:hborel, A:eq:monomargin, A:eq:monomarginu, A:eq:mvfbsdej, A:ex:brownian, A:ex:concrete, A:ex:dealer, A:ex:fulllaw, A:intro:limin-comparison, A:intro:mvfbsdej, A:lem:cont, A:lem:pert, A:lem:small, A:rem:beta1-dich, A:rem:cwp-class, A:rem:diag-mono, A:rem:freelaw, A:rem:generalrank, A:rem:intrinsic, A:rem:margin, A:rem:regimes, A:rem:uniq-no-integ, A:sec2:hborel-derivation, A:sec3:margin-paragraph, A:sec3:one-null-set, A:sec4:WP-def, A:sec4:horizon-not-contractive, A:sec5:overview, A:sec:examples, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: Dissertation.WellPosedness.System.Coeffs
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash fd49e3c7112f41550000000000000000 (pl-fp-v1:f3fdc81bc5c1853ac71563aa1d0b8a132fa576dd15014de49d59d610935378cd)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:50:55Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T15:41:47Z):
Reading for def:Dissertation.WellPosedness.System.Coeffs (paper §2, "Their signatures are ...", lines ~299-331).

Paper notion: the coefficient system (b, sigma, h, f, g) of the MV-FBSDEJ (1.1), deterministic
functions with signatures
  b     : [0,T] x H x P2(H) -> R^n
  sigma : [0,T] x H x P2(H) -> R^{n x d}       (Frobenius norm)
  h     : [0,T] x H x P2(H) -> L^2(nu; R^n)    (h(t,theta,.,mu), the jump coefficient as an L^2(nu)-valued map)
  f     : [0,T] x H x P2(H) -> R^m
  g     : R^n x P2(R^n) -> R^m                  (no time argument; depends on x and its law)
where H = R^n x R^m x R^{m x d} x L^2(nu;R^m) with the Hilbert norm
|theta|^2 = |x|^2+|y|^2+|z|_F^2+||u||^2_{L^2(nu)}, and P2(.) carries the W2 distance.
Standing: all coefficients jointly Borel measurable (for h: Borel as a map into L^2(nu;R^n), (2.3)).
Randomness enters only through the inputs: no omega argument.

What a faithful Lean definition must be: a structure (indexed by n,m,d, nu) with exactly these five
fields of these types. Acceptable representation choices: time domain R instead of [0,T] (values off
[0,T] are never used); the measure argument typed as a P2/P2W wrapper of the paper's P2(H) with the
W2 metric; h valued in Lp R^n 2 nu (i.e. classes, fibre L^2(nu;R^n)). Measurability may be a field
of the structure or imposed separately by each proposition (then check that the propositions impose
it where the paper's standing assumption is needed). To check: no omega-dependence; the codomain
of h is L^2(nu;R^n) (forward dimension n, not m); g takes a law on R^n (not on H); the norms of
R^n, R^m (Euclidean) and R^{m x d}, R^{n x d} (Frobenius) are the paper's; H carries the l^2-type
product norm, not Lean's default sup norm on products.
Comparison (verdict recorded 2026-10-17T15:50:03Z):
Comparison for def:Dissertation.WellPosedness.System.Coeffs (System/Coefficients.lean:73-87).

Lean: structure with fields
  b : R -> TupleH nu n m d -> P2 (TupleH nu n m d) -> EuclideanSpace R (Fin n)
  sigma : ... -> EuclideanSpace R (Fin n x Fin d)
  h : ... -> Lp (EuclideanSpace R (Fin n)) 2 nu
  f : ... -> EuclideanSpace R (Fin m)
  g : EuclideanSpace R (Fin n) -> P2 (EuclideanSpace R (Fin n)) -> EuclideanSpace R (Fin m)
with TupleH = R^n x R^m x EuclideanSpace R (Fin m x Fin d) x Lp (R^m) 2 nu.

Item by item against my reading:
- five fields, deterministic (no omega): yes.
- b codomain R^n Euclidean, f codomain R^m: yes.
- sigma codomain R^{n x d} with Frobenius norm: EuclideanSpace on index pairs (i,j), whose norm is
  exactly the Frobenius norm: yes.
- h codomain L^2(nu; R^n) (forward dimension n): yes (classes).
- g : R^n x P2(R^n) -> R^m, no time argument, law on R^n: yes.
- time domain R instead of [0,T]: representation choice; only [0,T] is used (coefficient processes
  are cut off by indicators of [0,T], Solves.lean).
- measure argument: P2 (TupleH ...), the probability measures of finite second moment on the
  product (sigma-algebra: product of Borel algebras, the L^2(nu) factor with the scoped Borel
  instance lpMeasurableSpace). TupleH carries the MAX of the channel norms, not the paper's Hilbert
  norm; but Coeffs uses only the carrier set, which is the same as P2(H): finiteness of the second
  moment is invariant under the equivalent norm (max <= Hilbert <= 2 max), and the Borel sets agree
  (equivalent norms; product sigma-algebra = Borel for the second-countable components under the
  standing sigma-finite nu / countably generated E). The W2 metric is not part of Coeffs (it enters
  through the assumption predicates, which are separate units).
- joint Borel measurability: NOT part of the structure (docstring of Coefficients.lean says so; it
  is imposed through JointBorel / the solution predicate's measurability fields). This is a
  representation choice for the definition; whether each proposition imposes it where the paper's
  standing assumption is needed is a matter for the proposition reviews.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices: (1) time ranges over R, only [0,T] is used (coefficient processes are cut off
to [0,T]); (2) R^{n x d} is EuclideanSpace R (Fin n x Fin d), whose norm is the Frobenius norm;
(3) the measure argument is P2 of TupleH, which carries the max of the channel norms rather than
the Hilbert norm -- the carrier set (Borel probability measures with finite second moment) is the
same as the paper's P2(H), and no metric is part of Coeffs; (4) the standing joint Borel
measurability is not a field of the structure but a separate hypothesis (JointBorel) / a condition
of the solution predicate, so it must be checked at the propositions, not here.
Disagreements with the author's review (shown 2026-10-17T15:50:11Z): No disagreement with a stated position: the author's entry shown for this unit is only the section
heading. For the record, my verdict is "faithful with representation choices": time over R, matrices
as EuclideanSpace on index pairs (Frobenius), the measure argument P2 of the max-norm product TupleH
(same carrier as the paper's P2(H); no metric in the structure), and joint Borel measurability not
part of the structure (imposed separately), which the proposition reviews must check.
