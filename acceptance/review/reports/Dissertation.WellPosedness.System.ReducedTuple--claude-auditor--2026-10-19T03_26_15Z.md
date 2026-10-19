### A:ex:brownian, A:rem:beta1-dich, A:sec5:overview: Dissertation.WellPosedness.System.ReducedTuple
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash d68fe71f65d1320f648e397a6f92aa48 (pl-fp-v1:1ae70923ace02c605de3bad8556855740b42e3f0b4dd26c8883de05479913f07)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:26:15Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:15:06Z):
Reading of def:Dissertation.WellPosedness.System.ReducedTuple.

Paper notion. Example 5.2 (Brownian reduction, 05-examples.tex:197-208): "Delete the
U-coordinate from the tuple, reducing H to R^n x R^m x R^{m x d}."  Remark 2.10 refers to this
case ("When nu = 0 the fibre L2(nu) is trivial ... this is the Brownian case of Example 5.2").
The full space H = R^n x R^m x R^{m x d} x L^2(nu;R^m) carries the Hilbert norm
|theta|^2 = |x|^2 + |y|^2 + |z|_F^2 + ||u||^2 (01-introduction.tex:19-31), with Euclidean norms on
R^j and the Frobenius norm on matrices; the reduced space inherits the same norm with the u-term
removed: |(x,y,z)|^2 = |x|^2 + |y|^2 + |z|_F^2.  The reduced assumptions are "W2-Lipschitz
joint-law dependence of (X,Y,Z)", so W2 on P2(reduced space) is computed in that norm.

What a faithful Lean definition must be. The type of triples (x, y, z) with x in R^n, y in R^m,
z in R^{m x d} (n, m, d the dimensions of the setting), equipped with the l2 (Hilbert-sum)
norm sqrt(|x|^2 + |y|^2 + |z|_F^2): e.g. WithLp 2 of a product of EuclideanSpace ℝ (Fin n),
EuclideanSpace ℝ (Fin m) and the Frobenius-normed matrix space (or a matrix space identified
with EuclideanSpace on Fin m x Fin d), or a structure with an explicitly defined matching inner
product.  The components should be the same types as the first three components of the Lean full
tuple space, so that the projection forgetting u is the coordinate map.
Representation issues to check: Lean's default product norm is the sup norm, and the default
Matrix norm is not Frobenius (no global instance, or an operator/sup norm by local instance);
with a sup-type norm the W2 distance and all Lipschitz/moment constants of the reduced setting
would differ from the paper's (equivalent but not equal), which matters for the W2-Lipschitz
reading of Example 5.2; that would be a non-harmless choice unless the uses only need the
topology/measurable structure.  The Borel sigma-algebra must be the one of this norm (it is the
product Borel structure for second-countable factors).
Comparison (verdict recorded 2026-10-19T03:17:28Z):
Comparison for def:Dissertation.WellPosedness.System.ReducedTuple (Examples/Brownian.lean:59-65).

Lean: ReducedTuple n m d := WithLp 2 (EuclideanSpace R (Fin n) x
  WithLp 2 (EuclideanSpace R (Fin m) x EuclideanSpace R (Fin m x Fin d))).

Against my reading:
- Components: x in R^n (EuclideanSpace, Euclidean norm), y in R^m (Euclidean), z in R^{m x d}
  represented as EuclideanSpace R (Fin m x Fin d), whose norm is sqrt(sum_{ij} z_ij^2), the
  Frobenius norm. These are the same channel types as the first three channels of TupleH
  (System/Tuple.lean:134-136), so dropping u is a coordinate map.
- Norm: nested l2 products (WithLp 2), so ||w||^2 = |x|^2 + |y|^2 + |z|_F^2 - proved in the file
  as norm_reducedTuple_sq. This is the paper's Hilbert norm of the reduced space, NOT the sup norm
  (unlike TupleH, which carries the max of channel norms). Hence W2 on P2(ReducedTuple) (w2P) is the
  paper's W2 for the reduced space.
- Measurable structure: Mathlib's WithLp.measurableSpace (comap of ofLp) with WithLp.borelSpace for
  binary products of second-countable Borel spaces: the Borel sigma-algebra of the norm topology.
  Matches.
- No junk values involved (a type).
Representation choices: (1) matrices as Euclidean vectors on Fin m x Fin d (Frobenius norm exactly;
harmless, matrix actions are implemented separately); (2) the triple as a nested l2 product
(x, (y, z)) instead of a flat triple (norm identical, ordering of components as in the paper).
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — (1) The m x d matrix channel is EuclideanSpace R (Fin m x Fin d): its norm is exactly the Frobenius
norm and it is the same channel type as in TupleH, so nothing changes. (2) The triple is the nested
l2 product WithLp 2 (R^n x WithLp 2 (R^m x R^{m x d})), whose norm squared is
|x|^2 + |y|^2 + |z|_F^2 (lemma norm_reducedTuple_sq), the paper's Hilbert norm, with the Borel
sigma-algebra; the nesting only regroups the coordinates.
Disagreements with the author's review (shown 2026-10-19T03:26:06Z): none
