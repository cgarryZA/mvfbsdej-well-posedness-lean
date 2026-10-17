### A:abstract, A:ass:G, A:ass:mono, A:conclusion, A:cor:robust, A:eq:monomargin, A:eq:monomarginu, A:ex:brownian, A:ex:concrete, A:ex:dealer, A:ex:fulllaw, A:intro:limin-comparison, A:lem:cont, A:lem:pert, A:rem:beta1-dich, A:rem:diag-mono, A:rem:freelaw, A:rem:generalrank, A:rem:intrinsic, A:rem:margin, A:rem:regimes, A:rem:uniq-no-integ, A:sec3:margin-paragraph, A:sec4:horizon-not-contractive, A:sec5:overview, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: Dissertation.WellPosedness.System.GZ
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash c2eb31a2cb944229321c531fa6d8a32a (pl-fp-v1:34e49ac326737a1b507b676e5969437a873dc7cdd96ff8ae9e20d89291445eb6)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:50:56Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T15:41:48Z):
Reading for def:Dissertation.WellPosedness.System.GZ.

Paper notion: the transpose G^T applied to the Brownian integrand: G^T delta Z in R^{n x d}
(paired with delta sigma in R^{n x d} by the Frobenius inner product, and |G^T delta Z|_F^2 in
(2.6)); G in R^{m x n}, z in R^{m x d}.

Faithful Lean: GZ G z = G^T * z (matrix product, (n x m)(m x d) = n x d), with the Frobenius norm
on the result. To check: transpose (not G itself), dimension n x d, Frobenius norm/inner product.
Comparison (verdict recorded 2026-10-17T15:50:04Z):
Comparison for def:Dissertation.WellPosedness.System.GZ: GZ G = toContinuousLinearMap
(toEuclideanLin (G kronecker I_d)) : EuclideanSpace R (Fin n x Fin d) ->L EuclideanSpace R (Fin m x
Fin d). GZ_toLp_apply: (GZ G z)(k, j) = (G *v (i |-> z(i, j)))_k, i.e. sigma |-> G sigma column by
column (Kronecker convention (G kron I)_{(k,j),(i,l)} = G_{k i} delta_{j l}, verified by the proof).

My reading expected GZ to be z |-> G^T z on R^{m x d}. The Lean defines the G-action on the
diffusion side, sigma |-> G sigma (R^{n x d} -> R^{m x d}), and the paper's G^T delta Z is its adjoint:
adjoint_GZ proves adjoint (GZ G) = GZ G^T, and the pairing/dissipation predicates
(Assumptions.lean: interiorPairing uses inner(delta sigma, adjoint GZ delta Z); dissipation uses
||adjoint GZ delta Z||^2) use exactly that adjoint. Since <delta sigma, G^T delta Z>_F =
<G delta sigma, delta Z>_F, this is a representation of the same operator pair. Norms are Frobenius
(Euclidean on index pairs). Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Choice: the paper writes G^T delta Z (R^{m x d} -> R^{n x d}); the Lean defines the forward operator
GZ G : sigma |-> G sigma (R^{n x d} -> R^{m x d}, Kronecker G kron I_d in row-major (i,j) coordinates)
and recovers G^T Z as its Hilbert adjoint (adjoint_GZ : adjoint (GZ G) = GZ G^T), which is how
interiorPairing and dissipation use it. Harmless: same operator, adjoint identity proved; matrices
as EuclideanSpace on index pairs carry the Frobenius norm and inner product.
Disagreements with the author's review (shown 2026-10-17T15:50:11Z): No disagreement with a stated position (the author's entry shown is empty). For the record: GZ is the
G-action sigma |-> G sigma, not the paper's G^T Z; the paper's G^T delta Z is its adjoint (adjoint_GZ),
which is what interiorPairing and dissipation use -- faithful with that representation choice.
