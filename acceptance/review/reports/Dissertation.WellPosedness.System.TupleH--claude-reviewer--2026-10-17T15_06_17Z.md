### A:ass:integ, A:ass:lip, A:ass:mono, A:cor:robust, A:def:diag, A:eq:coeffint, A:eq:coefmeas, A:eq:forced, A:eq:hborel, A:eq:mvfbsdej, A:ex:brownian, A:ex:concrete, A:ex:expfunc, A:intro:mvfbsdej, A:lem:cont, A:lem:lawflow, A:lem:pert, A:lem:small, A:prop:strict, A:rem:cwp-class, A:rem:diag-mono, A:rem:generalrank, A:rem:intrinsic, A:remark-2.6, A:sec2:coefmeas, A:sec2:hborel-derivation, A:sec3:one-null-set, A:sec4:WP-def, A:sec4:horizon-not-contractive, A:sec:examples, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: Dissertation.WellPosedness.System.TupleH
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash fd49e3c7112f4155a292d8ceeae04f54 (pl-fp-v1:8298b17d4c5d53a77d5b607075522d337e9ca09119fb25c45e988d9b2c376b51)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:06:17Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:33:34Z):
Reading for TupleH (paper: the state space H, §1/§2).
H := R^n x R^m x R^{m x d} x L^2(nu; R^m), with |theta|_H^2 = |x|^2 + |y|^2 + |z|_F^2 + ||u||^2_{L^2(nu)},
|.| Euclidean, |z|_F Frobenius, ||u||^2 = int_E |u(e)|^2 nu(de) with |.| Euclidean on R^m. It is a
(separable) Hilbert space; its Borel sigma-field is used for laws (P_2(H), W_2). Points theta = (x,y,z,u);
u is an a.e.-class. A faithful Lean type must carry exactly this norm (the l^2-sum of the four
component norms, with Euclidean norms on R^n, R^m, the Frobenius norm on R^{m x d}, and the L^2(nu)
norm built from the Euclidean norm on R^m), not the sup-norm of a Prod (which changes W_2 and every
Lipschitz constant by up to factor 2) nor a sup/l^1 norm on vectors; the measurable structure must
be the Borel sigma-field of that norm topology (= product of Borel sigma-fields, H separable).
Dimensions n, m, d and nu as parameters.
Comparison (verdict recorded 2026-10-17T15:02:24Z):
Comparison for TupleH (System/Tuple.lean:134): Tuple (EuclideanSpace R (Fin n)) (EuclideanSpace R (Fin m))
(EuclideanSpace R (Fin m x Fin d)) (Lp (EuclideanSpace R (Fin m)) 2 nu), where Tuple HX HY HZY HUY is the
plain product HX x HY x HZY x HUY (Assumptions.lean:197).
Against my reading:
- Points: (x, y, z, u) with x in R^n, y in R^m, z in R^{m x d} (Euclidean on pairs = Frobenius norm),
  u in L^2(nu; R^m) built from the Euclidean norm on R^m -- matches; dimensions and nu are parameters.
- Measurable structure: product of the Borel sigma-algebras (EuclideanSpace Borel; L^2(nu) gets the
  scoped Borel instance lpMeasurableSpace), which is the Borel sigma-field of H since all four
  factors are second countable (for countably generated E and sigma-finite nu) -- matches.
- Topology/vector structure: the product's, the same as H's -- matches.
- Norm: the Prod norm, i.e. the MAXIMUM of the four channel norms, not the paper's Hilbert norm
  (|x|^2+|y|^2+|z|_F^2+||u||^2)^{1/2}. The docstring says so. The two are equivalent
  (||theta||_max <= |theta|_H <= 2 ||theta||_max), so L^2 membership, P_2 membership and the topology agree,
  but the W_2 distance of the type's norm (w2P) and any Lipschitz constant measured with the type's
  norm differ from the paper's by up to a factor 2. The development supplies the paper's norm
  separately: TupleL2 / toL2 (|toL2 theta|^2 = channelSq theta), w2H (W_2 of the Hilbert norm) and
  tupleNorm (sum of channel norms). I checked the PaperSpec propositions: the laws on H are compared
  with w2H (e.g. LipInteriorAt in Spec/Assumptions.lean, Sec3 prop_strict, Sec5), and squared tuple
  norms appear through channels; w2P appears only on single channels (U-marginal on L^2(nu), laws on
  R^n), where the type's norm is the paper's.
So TupleH is the paper's H as a measurable topological vector space, with a non-paper (equivalent)
norm that the propositions route around. Harmless as a carrier provided every claim measures H-norm
quantities with w2H / channelSq / tupleNorm rather than ||.|| on TupleH; that is a check for each
proposition's review, not something this definition guarantees.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choice: TupleH carries the product (max-of-channels) norm instead of the paper's
Hilbert norm |theta|_H^2 = |x|^2 + |y|^2 + |z|_F^2 + ||u||^2_{L^2(nu)}. Harmless because (i) the two norms are
equivalent within a factor 2, so the topology, the Borel sigma-field, L^2 and P_2 membership coincide;
(ii) the paper's norm is supplied separately (toL2/TupleL2 with |toL2 theta|^2 = channelSq theta; w2H, the
W_2 of the Hilbert norm; tupleNorm, the sum of channel norms of Ass 2.3), and the PaperSpec
propositions I checked use w2H for laws on H and channel norms for points. Caveat for proposition
reviewers: any statement that measures distances on H with the type's own norm (w2P on P2 (TupleH ..),
dist, ||theta - theta'||) is NOT the paper's quantity (off by up to 2), and is faithful only if the
constant is immaterial. Other components (R^n, R^m Euclidean; R^{m x d} Euclidean on pairs = Frobenius;
L^2(nu;R^m) with the Euclidean fibre norm and the Borel sigma-algebra) are exactly the paper's.
Disagreements with the author's review (shown 2026-10-17T15:05:46Z): Disagreement: the author's entry calls TupleH "the space H of the well-posedness paper, §2" and lists
the channel norms, but does not record that the product carries the MAXIMUM of the channel norms,
not the paper's Hilbert norm (|x|^2 + |y|^2 + |z|_F^2 + ||u||^2)^{1/2} (the Lean docstring says so). As a
measurable topological vector space TupleH is H; as a normed space it is not. Consequences the review
should state: W_2 for the type's norm (w2P on P2 (TupleH ..)) and Lipschitz constants measured with
||.|| on TupleH are within a factor 2 of, but not equal to, the paper's; the paper's norm is TupleL2 /
toL2 / channelSq and its W_2 is w2H. My verdict (faithful with representation choices) relies on the
propositions using w2H and channel norms; that should be checked per proposition.
