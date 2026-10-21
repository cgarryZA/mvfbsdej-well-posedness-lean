### A:lemA1:pettis: Dissertation.PaperSpec.A.lemA1_separable
Pins: manuscript A None; project 6d403c197bfb10fe8808933c6e525ee0ae544fb1; hash ed839d34f480cba1e132af851a6dd7cf (pl-fp-v1:a8c22137a3ba327069a0c54958da10ca87ad8a11f136b59616a8e23c38afdd98)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-20T10:33:33Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-20T10:21:55Z):
Reading of the clause (Lemma A.1, Step 1: "H is separable because L^2(nu) is"; manuscript/paper/sections/09-appendix.tex
line 28; standing section 2, lines 5-7: "nu is a sigma-finite measure on a countably generated (E, E) (so that
L^2(nu; R^j) is separable for every j >= 1)").

Setting: a measurable space (E, E) that is countably generated, a sigma-finite measure nu on it (nu(E) = infinity
admitted; nu = 0 admitted, then L^2 is trivial), dimensions n, m, d >= 1.
Conclusion: (i) L^2(nu; R^m) (the Lebesgue space of nu-a.e. classes of square integrable R^m-valued functions, with its
norm) is a separable space; (ii) the state space H = R^n x R^m x R^{m x d} x L^2(nu; R^m), with the Hilbert norm
|theta|^2 = |x|^2 + |y|^2 + |z|_F^2 + ||u||^2 (Euclidean, Frobenius, L^2(nu) norms), is separable.
A faithful statement quantifies over every countably generated (E, E) and every sigma-finite nu (not a particular E such
as R^k \ {0} or a finite nu, which would be narrower), and over all dimensions. Separability is a topological property,
so the particular equivalent product norm does not matter, but H should be the type the other statements use for the
paper's H (L^2(nu; R^m) as Lp with p = 2, not some other space). Dropping sigma-finiteness or countable generation would
make the statement false in general (counting measure on [0,1]), so the hypotheses are needed. The paper asserts it for
every j; the clause takes j = m (the U fibre) - fine, that is the instance Step 1 uses. Also the h-codomain L^2(nu; R^n)
is separable by the same fact (not needed in this clause).
Comparison (verdict recorded 2026-10-20T10:25:08Z):
Comparison of Dissertation.PaperSpec.A.lemA1_separable (Dissertation/PaperSpec/A/AppASteps.lean) with my locked reading.

Setting and hypotheses. For every measurable space E that is `MeasurableSpace.CountablyGenerated`, every `SigmaFinite`
measure nu on it (finite, infinite, or zero), and all n, m, d : ℕ. These are exactly the standing hypotheses of section 2
(nu sigma-finite on a countably generated (E, E)), under which the paper asserts the separability; no particular E or
finite nu is imposed. Both hypotheses are needed for the conclusion (counting measure on [0,1] is a counterexample
without sigma-finiteness), so none is superfluous.

Conclusion. (i) `SeparableSpace (Lp (EuclideanSpace ℝ (Fin m)) 2 ν)`: the Lebesgue space L^2(nu; R^m) of a.e.-classes
with its norm (Euclidean norm on R^m) is separable. [match] (ii) `SeparableSpace (TupleL2 (EuclideanSpace ℝ (Fin n))
(EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m × Fin d)) (Lp (EuclideanSpace ℝ (Fin m)) 2 ν))`; `TupleL2` is the
iterated `WithLp 2` product, whose norm is (|x|^2 + |y|^2 + |z|^2 + ||u||^2)^{1/2}; the m x d channel is
EuclideanSpace over Fin m x Fin d, whose norm is the Frobenius norm. This is the paper's H with its Hilbert norm. [match]
The paper's "for every j >= 1" is used at j = m (the U fibre), which is what the statement records; the claim of the
passage is only "H is separable because L^2(nu) is".

Representation choices: matrices R^{m x d} as `EuclideanSpace ℝ (Fin m × Fin d)` (Frobenius norm, same topology and
norm); H as the type `TupleL2 …` (iterated L^2 product), the same type the other statements of this claim use (lemA1_L2,
_fubini, _pettis); dimensions in ℕ including 0 (a trivial extension). Separability is topological, so even the choice
among equivalent product norms would not matter.

Witness. Dissertation.Acceptance.A.lemA1_polish_hypotheses: Lebesgue measure on ℝ is sigma-finite with infinite mass on a
countably generated space, so L^2(nu; R^m) is infinite-dimensional: the hypotheses are met at an instance with
nu(E) = inf, the regime the paper emphasises. The statement has no hypotheses that could be vacuous beyond the type
classes, which every countably generated sigma-finite space meets.

Coverage of the claim A:lemA1:pettis: as recorded in my decision on lemA1_leftlim. The seven clauses state every
assertion of Step 1 (lines 25-51 of manuscript/paper/sections/09-appendix.tex): left limits predictable, equal to X, Y
dt (x) dP-a.e., countable jumps, energy passes; H separable because L^2(nu) is (this clause); U's predictable L^2(nu)
representative; Theta^- predictable, jointly measurable, in L^2; the Fubini isometry; the Pettis/Borel version. No clause
states something the passage does not claim; the hypotheses are those of Lemma A.1 plus the standing sigma-finiteness and
countable generation (this clause uses exactly the latter two); the scope_note is accurate. Witnesses exhibit nonzero
objects (X, Y jumping, Z, U nonzero; Lebesgue nu of infinite mass here).
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless: (1) the m x d matrix channel is `EuclideanSpace ℝ (Fin m × Fin d)`, whose norm is
the Frobenius norm of the paper; (2) H with its Hilbert norm is the iterated `WithLp 2` product `TupleL2`, whose norm
is (|x|^2+|y|^2+|z|_F^2+||u||^2)^{1/2}, the type used by the other clauses of the claim; (3) dimensions range over ℕ
(0 included), a trivial extension of n, m, d >= 1; (4) the paper's "for every j" is taken at j = m, the instance the
passage uses for H.
Disagreements with the author's review (shown 2026-10-20T10:33:10Z): None on substance. Label: the author records `faithful`; I record `faithful with representation choices` (matrices as
EuclideanSpace over Fin m x Fin d for the Frobenius norm, H as the iterated WithLp 2 product `TupleL2`, dimensions in ℕ
including 0, the paper's "every j" taken at j = m). The author notes the last two points in the verdict line; the
difference is only in how the choices are recorded.
