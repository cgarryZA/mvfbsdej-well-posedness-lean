### A:ass:integ, A:ass:lip, A:ass:mono, A:cor:robust, A:def:diag, A:eq:coeffint, A:eq:coefmeas, A:eq:forced, A:eq:hborel, A:eq:mvfbsdej, A:ex:brownian, A:ex:concrete, A:ex:expfunc, A:intro:mvfbsdej, A:lem:cont, A:lem:lawflow, A:lem:pert, A:lem:small, A:prop:strict, A:rem:cwp-class, A:rem:diag-mono, A:rem:generalrank, A:rem:intrinsic, A:remark-2.6, A:sec2:coefmeas, A:sec2:hborel-derivation, A:sec3:one-null-set, A:sec4:WP-def, A:sec4:horizon-not-contractive, A:sec:examples, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: Dissertation.WellPosedness.Tuple
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash efc2de5eec83280ededc740a2b5da27e (pl-fp-v1:96ed39ead4c0943ad03046030086acabf030465cf0161e81ac094da91e416418)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:01:51Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:34:24Z):
Reading for def:Dissertation.WellPosedness.Tuple (written before seeing any Lean).

Paper notion. The state space H := R^n x R^m x R^{m x d} x L^2(nu;R^m), "the Hilbert space"
carrying |theta|_H^2 := |x|^2 + |y|^2 + |z|_F^2 + ||u||_{L^2(nu)}^2, theta = (x,y,z,u), with
Euclidean norms on R^n, R^m, Frobenius on R^{m x d}, and the L^2(nu;R^m) norm
\int_E |u(e)|^2 nu(de) (Euclidean on R^m inside). nu is a sigma-finite measure on a countably
generated (E, \mathcal E), so L^2(nu) and H are separable. Points of H are lower-case theta;
laws mu in P_2(H) are Borel probability measures on H. The dimensions are n (forward), m
(backward, also the U fibre), d (Brownian).

A faithful Lean definition must:
- have exactly the four components with the right types/dimensions: x in R^n, y in R^m,
  z in R^{m x d}, u in L^2(nu;R^m) (an Lp element for nu, fibre R^m — not R^n, not R^d);
- carry (or be used with) the Hilbert norm above — sum of squares of the component norms, with
  Euclidean (not sup) norms on R^n, R^m, and Frobenius on matrices; Lean's default Prod norm is
  the max norm and Fin n -> R / Matrix carry sup norms, which would NOT be faithful unless the
  type is WithLp 2 / EuclideanSpace / a structure with an explicit norm or inner product;
- its measurable structure should be the Borel sigma-algebra of that norm topology (laws in
  P_2(H) are Borel), separable;
- the origin 0 = (0,0,0,0) used in Ass 2.2 (b(.,0,delta_0)).
If "Tuple" is instead the tuple of processes Theta = (X,Y,Z,U), it must hold X, Y in R^n, R^m
(cadlag adapted), Z in R^{m x d} and U valued in R^m on [0,T] x Omega x E (predictable, P x E
measurable), with the same dimensions.
Comparison (verdict recorded 2026-10-17T12:39:11Z):
Comparison for Tuple.
Lean: abbrev Tuple (HX HY HZY HUY) [NormedAddCommGroup, InnerProductSpace ℝ on each] :=
HX × HY × HZY × HUY. The paper's space is TupleH ν n m d = Tuple (EuclideanSpace ℝ (Fin n))
(EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m × Fin d)) (Lp (EuclideanSpace ℝ (Fin m)) 2 ν).
- Components and dimensions: x ∈ ℝ^n, y ∈ ℝ^m, z ∈ ℝ^{m×d} with the Euclidean norm on
  Fin m × Fin d entries (= Frobenius), u ∈ L²(ν;ℝ^m) with the Euclidean fibre. Matches my reading
  (U fibre ℝ^m, Euclidean, not sup norms).
- Norm: the instance norm on a Lean product is the MAX of the channel norms, not the paper's
  Hilbert norm (|x|²+|y|²+|z|²_F+‖u‖²)^{1/2}; Tuple has no inner-product structure. This is a
  deviation from the paper's "Hilbert space H carrying the norm |θ|_H", flagged in my reading.
  The repository states it openly (Tuple.lean module doc) and supplies the paper's norm separately:
  channelSq θ = sum of squared channel norms, toL2 : Tuple → TupleL2 (nested WithLp 2) with
  ‖toL2 θ‖² = channelSq θ, and w2H for W₂ in the Hilbert norm. The two norms are equivalent
  (‖θ‖ ≤ ‖toL2 θ‖ ≤ 2‖θ‖), so the topology, the Borel σ-algebra, L²(Ω;H) membership, P₂(H) and
  Bochner means are the same as the paper's. Only quantitative uses of ‖θ‖ would differ. I
  checked the PaperSpec files: the Lipschitz/coupling statements on TupleH go through
  ‖toL2 θ - toL2 θ'‖ and w2H, not through ‖θ‖ or w2P on TupleH.
- Measurable structure: the product σ-algebra of Borel σ-algebras (Lp Borel via a scoped
  instance); it equals the Borel σ-algebra of H when L²(ν) is second countable (the paper's
  setting).
- Origin 0 = (0,0,0,0). Matches.
- Generality: Tuple is generic in four inner-product channels; the paper's H is the instance
  TupleH. That is a generalisation of the carrier, not of a claim.
Verdict: faithful with representation choices (the max-norm instance is the choice; harmless only
because quantitative uses go through toL2/channelSq/w2H).
Witness: —
Verdict: faithful with representation choices — Representation choices. (1) H is the Lean product HX × HY × HZY × HUY, instantiated as TupleH
with the paper's four channels (EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin m),
EuclideanSpace ℝ (Fin m × Fin d) for Frobenius, Lp (EuclideanSpace ℝ (Fin m)) 2 ν). (2) The
product's instance norm is the max of the channel norms, not the paper's Hilbert norm, and the
product has no inner product. The paper's norm is supplied separately by channelSq, by toL2 into
the nested WithLp 2 product TupleL2 (where ‖toL2 θ‖² = channelSq θ), and by w2H. The two norms
are equivalent within a factor 2. So the topology, the Borel sets, L² membership, P₂ and Bochner
means are the paper's. This is harmless only if every quantitative use of |θ|_H in a statement
goes through toL2/channelSq/w2H, not through ‖θ‖, w2P or LipschitzWith on Tuple. The current
PaperSpec statements do this. Any spec that uses the instance norm of Tuple for a paper quantity
should be checked at its own review.
Disagreements with the author's review (shown 2026-10-17T15:01:23Z): None. The author's entry says, as I found, that Tuple carries the max of the channel norms, not
the paper's Hilbert norm. I would add that this is harmless only because the paper's |θ|_H enters
the statements through toL2/channelSq/w2H. I checked that the current PaperSpec files do this.
A spec that uses ‖θ‖, w2P or LipschitzWith on Tuple for a paper quantity would not be faithful.
