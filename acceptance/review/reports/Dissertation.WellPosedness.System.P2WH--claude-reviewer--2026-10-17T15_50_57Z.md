### A:abstract, A:conclusion, A:cor:robust, A:eq:coefmeas, A:eq:hborel, A:ex:brownian, A:ex:concrete, A:ex:dealer, A:ex:fulllaw, A:intro:limin-comparison, A:lem:cont, A:lem:lawflow, A:lem:pert, A:lem:small, A:rem:cwp-class, A:rem:diag-mono, A:rem:generalrank, A:rem:intrinsic, A:rem:regimes, A:rem:uniq-no-integ, A:sec2:hborel-derivation, A:sec4:horizon-not-contractive, A:sec5:overview, A:sec:examples, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: Dissertation.WellPosedness.System.P2WH
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 8b570604f2bfe77f0b8346109edf1c66 (pl-fp-v1:d727776f413b6c277cd41f6054252ca4f08714749a04cfa45e42d8e70a9f8f8e)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:50:57Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T15:41:49Z):
Reading for def:Dissertation.WellPosedness.System.P2WH.

Paper notion: (P2(H), W2), the space of measure arguments of b, sigma, h, f, where
H = R^n x R^m x R^{m x d} x L^2(nu;R^m) is the HILBERT space with norm
|theta|_H^2 = |x|^2 + |y|^2 + |z|_F^2 + ||u||^2_{L^2(nu)} (Euclidean, Frobenius, L^2(nu)).

Faithful Lean: P2W applied to a Lean model of H whose norm is exactly this l^2-type norm (e.g.
WithLp 2 of the product, or a structure with that norm), with Euclidean norms on R^n, R^m
(EuclideanSpace, not Fin n -> R with the sup norm), the Frobenius norm on m x d matrices and the
L^2(nu;R^m) norm. Crucial edge case: Mathlib's default product norm is the SUP norm; if H is a plain
product the W2 distance on P2(H) differs from the paper's (equivalent up to a factor, but a
different function), which changes e.g. the radial statistic W2(mu, mu_0) of Ex 5.4, the exact
Lipschitz constants (Prop 3.8: beta_1 + eps), and (2.8). The Borel sigma-algebra on H must be the
Borel algebra of this norm topology (equal for equivalent norms).
Comparison (verdict recorded 2026-10-17T15:50:05Z):
Comparison for def:Dissertation.WellPosedness.System.P2WH (System/HilbertW2Space.lean:50-52):
def P2WH HX HY HZY HUY := P2 (Tuple HX HY HZY HUY), a type synonym; Tuple = HX x HY x HZY x HUY (the
plain product, max norm). The Hilbert-norm W2 is attached by the separate instance
P2WH.instPseudoMetricSpace := PseudoMetricSpace.induced (mu |-> (lawToL2 mu).toP2W), where
lawToL2 mu = pushforward of mu by toL2 : Tuple -> TupleL2 = WithLp 2 (HX x WithLp 2 (HY x WithLp 2 (HZY x
HUY))), whose norm is (|x|^2+|y|^2+|z|^2+||u||^2)^{1/2} (norm_toL2_sq); so dist = w2H = W2 of the
Hilbert norm (P2WH.dist_toP2WH), and the sigma-algebra is the Borel one of that topology.
TupleP2WH nu n m d instantiates HX = R^n, HY = R^m, HZY = EuclideanSpace R (Fin m x Fin d) (Frobenius),
HUY = L^2(nu;R^m).

Against my reading: the key concern (Mathlib's sup norm on products) is addressed: the carrier is the
set of laws of finite second moment on the max-norm product (the same set as for the Hilbert norm,
max <= Hilbert <= 2 max, same Borel sets), and the distance used on P2WH is the Hilbert-norm W2 via
the isometric re-norming toL2, i.e. the paper's W2 on P2(H). The definition is generic in the four
channel spaces (inner product spaces), instantiated to the paper's H by TupleP2WH. Verdict: faithful
with representation choices.
Witness: —
Verdict: faithful with representation choices — Choices: (1) the carrier is P2 of the plain product Tuple (max of the channel norms); it is the same
set of laws as P2(H) for the paper's Hilbert norm (the norms are equivalent, max <= Hilbert <= 2 max:
same finite-second-moment laws, same Borel sets); (2) the paper's W2 is supplied by the separate
instance P2WH.instPseudoMetricSpace, induced by pushing laws forward along the isometric re-norming
toL2 into the l^2-type product TupleL2 = WithLp 2 (...), so dist = W2 for the Hilbert norm, with the
Borel sigma-algebra of that topology; (3) generic in the channel spaces, instantiated to
H = R^n x R^m x R^{m x d} x L^2(nu;R^m) by TupleP2WH.
Disagreements with the author's review (shown 2026-10-17T15:50:12Z): No disagreement with a stated position (the author's entry shown is empty). For the record: the type
synonym's carrier is P2 of the max-norm product; the paper's Hilbert-norm W2 comes from the separate
instance P2WH.instPseudoMetricSpace (induced through the re-norming toL2 into WithLp 2 products),
which I checked; so faithful with representation choices.
