### A:abstract, A:ass:G, A:ass:mono, A:conclusion, A:cor:robust, A:eq:monomargin, A:eq:monomarginu, A:ex:brownian, A:ex:concrete, A:ex:dealer, A:ex:fulllaw, A:intro:limin-comparison, A:lem:cont, A:lem:pert, A:rem:beta1-dich, A:rem:diag-mono, A:rem:freelaw, A:rem:generalrank, A:rem:intrinsic, A:rem:margin, A:rem:regimes, A:rem:uniq-no-integ, A:sec3:margin-paragraph, A:sec4:horizon-not-contractive, A:sec5:overview, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: Dissertation.WellPosedness.System.GZ
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash c2eb31a2cb944229321c531fa6d8a32a (pl-fp-v1:34e49ac326737a1b507b676e5969437a873dc7cdd96ff8ae9e20d89291445eb6)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:27:23Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:13:11Z):
Reading for def:Dissertation.WellPosedness.System.GZ (locked before any Lean is shown).

Paper notion. The paper has no symbol "GZ"; the name points at the G-weighted Z-channel of
Assumption 2.4/2.5 (ass:G, ass:mono): for z in R^{m x d} the quantity G^T z in R^{n x d}
(matrix product of the transpose of the coupling matrix G in R^{m x n} with z), which enters
  <delta sigma, G^T delta Z>_F   (Frobenius pairing in R^{n x d}),
  |G^T delta Z|_F^2              (in the beta_1 coercive term),
  |Z|_F^2 <= c_G |G^T Z|_F^2     (ass:G, when G^T is injective).
(Less likely: "GZ" = the product with G itself, but G z is not defined for z in R^{m x d}
unless n=m; only G^T z makes dimensional sense for the Z-channel pairing with sigma in R^{n x d}.)

A faithful Lean definition must therefore be:
- the linear map z |-> G^T z, R^{m x d} -> R^{n x d}, (G^T z)_{ij} = sum_k G_{ki} z_{kj}, applied
  columnwise (equivalently to each of the d columns of z);
- in whatever encoding of R^{m x d} the development uses (Matrix, EuclideanSpace on Fin m x Fin d,
  Fin d -> EuclideanSpace (Fin m), ...), the encoding of the target must carry the Frobenius
  (Euclidean on all entries) norm/inner product, so that |.|_F and <.,.>_F are the paper's;
- no hidden scaling, no use of G instead of G^T, no restriction to injective G (the map is
  defined for every G; injectivity is a hypothesis elsewhere).
If instead the Lean "GZ" is G applied in a different channel (e.g. to U pointwise), it must be the
pointwise G^T u(e), descending to L^2(nu) classes.
Comparison (verdict recorded 2026-10-19T03:25:27Z):
Comparison for def:Dissertation.WellPosedness.System.GZ.

Lean: GZ G : EuclideanSpace R (Fin n x Fin d) ->L[R] EuclideanSpace R (Fin m x Fin d),
the Euclidean linear map of the Kronecker matrix G (x) I_d. Entry check: ((G (x) I_d) z)(k,j) =
sum_{i,j'} G_{ki} delta_{jj'} z(i,j') = (G z_{.j})_k (GZ_toLp_apply), i.e. sigma |-> G sigma acting
column by column, R^{n x d} -> R^{m x d}.

Against my reading: I expected the Z-channel operator z |-> G^T z. The Lean defines the operator
on the sigma-channel, sigma |-> G sigma, and obtains G^T z in two equivalent ways:
GZ (G^T) (the same construction at the transposed matrix, R^{m x d} -> R^{n x d}), and
adjoint (GZ G) = GZ G^T (adjoint_GZ, proved). Consumers use exactly these: Assumption 2.5
(pairing27, Mono27At) uses inner (delta sigma) (GZ G^T delta Z) and |GZ G^T delta Z|^2, i.e. the
paper's <delta sigma, G^T delta Z>_F and |G^T delta Z|_F^2; ass_G uses
|adjoint (GZ G) Z|^2 = |G^T Z|_F^2. So the paper's G^T Z is recovered exactly.
Encoding: R^{n x d} as EuclideanSpace on Fin n x Fin d: the l2 norm over all entries is the
Frobenius norm, the inner product the Frobenius pairing - the paper's |.|_F, <.,.>_F.
No scaling, defined for every G (no rank assumption inside). No junk values.

Verdict: faithful with representation choices (matrix encoding; operator defined on the sigma
channel with G^T z obtained as GZ G^T or the adjoint).
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless:
1. R^{n x d} and R^{m x d} are encoded as EuclideanSpace R (Fin n x Fin d) (resp. Fin m x Fin d):
   the Euclidean norm on all entries is exactly the Frobenius norm and its inner product the
   Frobenius pairing.
2. The paper writes the Z-channel operator as z |-> G^T z; Lean defines sigma |-> G sigma (the
   Kronecker matrix G (x) I_d, checked entrywise in GZ_toLp_apply to act column by column) and gets
   G^T z as GZ G^T, which is also the adjoint of GZ G (adjoint_GZ). The consumers (pairing27,
   Mono27At, ass_G) use GZ G^T or the adjoint, so they read the paper's <delta sigma, G^T delta Z>_F
   and |G^T delta Z|_F.
Disagreements with the author's review (shown 2026-10-19T03:25:39Z): none
