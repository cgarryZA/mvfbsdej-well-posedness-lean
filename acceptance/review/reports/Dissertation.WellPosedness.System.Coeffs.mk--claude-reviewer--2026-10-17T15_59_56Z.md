### A:abstract, A:ass:integ, A:ass:lip, A:ass:mono, A:conclusion, A:cor:robust, A:eq:coeffint, A:eq:coefmeas, A:eq:forced, A:eq:hborel, A:eq:monomargin, A:eq:monomarginu, A:eq:mvfbsdej, A:ex:brownian, A:ex:concrete, A:ex:dealer, A:ex:fulllaw, A:intro:limin-comparison, A:intro:mvfbsdej, A:lem:cont, A:lem:pert, A:lem:small, A:rem:beta1-dich, A:rem:cwp-class, A:rem:diag-mono, A:rem:freelaw, A:rem:generalrank, A:rem:intrinsic, A:rem:margin, A:rem:regimes, A:rem:uniq-no-integ, A:sec2:hborel-derivation, A:sec3:margin-paragraph, A:sec3:one-null-set, A:sec4:WP-def, A:sec4:horizon-not-contractive, A:sec5:overview, A:sec:examples, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: Dissertation.WellPosedness.System.Coeffs.mk
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 53675b51c8cc7afa0000000000000000 (pl-fp-v1:17fa085a6e9caace7efed59f5f69eb8c6bdb824560418a5d2c3e283fef81bfa4)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:59:56Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T15:42:31Z):
Reading for def:Dissertation.WellPosedness.System.Coeffs.mk (locked before seeing Lean).

This is the constructor of the coefficient-system structure; its meaning is the list of fields.
Paper notion (Sec. 2): a coefficient system is five deterministic functions
  b     : [0,T] x H x P2(H) -> R^n
  sigma : [0,T] x H x P2(H) -> R^{n x d}
  h     : [0,T] x H x P2(H) -> L^2(nu; R^n)   (Borel as a map into L^2(nu;R^n), (2.2))
  f     : [0,T] x H x P2(H) -> R^m
  g     : R^n x P2(R^n) -> R^m
with H = R^n x R^m x R^{m x d} x L^2(nu;R^m) carrying the Hilbert norm
|x|^2 + |y|^2 + |z|_F^2 + ||u||^2, P2 the square-integrable Borel probability measures with W2,
all jointly Borel measurable. (The jump coefficient is evaluated at (Theta^-, mu^-) but has the
same signature.)

Faithful constructor: fields b, sigma, h, f, g with these types (time may be R or R>=0 with only
[0,T] used; matrices as Matrix (Fin m)(Fin d) R with Frobenius norm used where the paper does;
h valued in an L^2(nu;R^n) Lp type). The joint Borel measurability may be a field or imposed
elsewhere (then the structure is broader, which is harmless only if the propositions impose
measurability where needed). No extra fields that restrict (e.g. Lipschitz) unless the
propositions intend them; no missing coefficient.
Comparison (verdict recorded 2026-10-17T15:44:55Z):
Comparison for def:Dissertation.WellPosedness.System.Coeffs.mk (constructor of Coeffs).

Lean fields (System/Coefficients.lean):
 b : R -> TupleH nu n m d -> P2 (TupleH nu n m d) -> R^n (EuclideanSpace)
 sigma : R -> TupleH -> P2 TupleH -> EuclideanSpace R (Fin n x Fin d)
 h : R -> TupleH -> P2 TupleH -> Lp (EuclideanSpace R (Fin n)) 2 nu
 f : R -> TupleH -> P2 TupleH -> R^m
 g : R^n -> P2 (R^n) -> R^m
TupleH = R^n x R^m x EuclideanSpace(Fin m x Fin d) x Lp(R^m) 2 nu (product, max norm);
P2 E = probability measures with finite second moment int ||x||^2 (norm of E).

Against my reading:
- Exactly the five coefficients, with the paper's codomains: yes. n x d matrices as Euclidean
  vectors on index pairs: the norm is the Frobenius norm, inner product the Frobenius product.
- Domain [0,T] x H x P2(H): time ranges over R (only [0,T] is used by the predicates, e.g.
  JointBorel T restricts to Icc 0 T, DiagonalLipschitz is a.e. on Icc 0 T). Harmless.
- H is the product type with the max of the channel norms, not the Hilbert norm. As a set and
  as a measurable space (product Borel) it is the paper's H; the set P2(H) of laws with finite
  second moment is the same for the two equivalent norms. Which norm W2 is computed with is a
  matter of the predicates (P2WH/w2H for the Hilbert one), not of this constructor.
- Joint Borel measurability is not a field; it is imposed by the separate predicate
  Spec.JointBorel (with the Hilbert-norm W2 Borel structure on P2(H) via TupleP2WH), so the
  structure is broader, harmless as the propositions carry JointBorel where the paper assumes it.
- No extra restrictive fields; nothing missing.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices: (1) time domain R instead of [0,T] (only [0,T] is read by the
predicates); (2) R^{n x d} realised as EuclideanSpace R (Fin n x Fin d), whose norm and inner
product are the Frobenius ones; (3) the tuple space carries the max of the channel norms; the
underlying set, the product Borel sigma-algebra and the set P2(H) of finite-second-moment laws are
the same as for the paper's Hilbert norm (W2 with the Hilbert norm is available via P2WH);
(4) joint Borel measurability (2.2)/(2.3) is a separate predicate (Spec.JointBorel) rather than a
field, so the structure is broader; harmless because measurability is imposed where the paper
assumes it.
Disagreements with the author's review (shown 2026-10-17T15:59:48Z): The author's review entry for this constructor is empty (a marker with no recorded reading), so
there is nothing to agree or disagree with on substance. It should at least record what my
comparison records: the fields are the five coefficients with the paper's codomains; time ranges
over R; the tuple space carries the max of the channel norms (same set, Borel structure and P2(H)
as the Hilbert norm); and joint Borel measurability is not a field but the separate predicate
JointBorel.
