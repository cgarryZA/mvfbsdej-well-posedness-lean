### A:cor:robust, A:eq:coefmeas, A:eq:hborel, A:ex:brownian, A:ex:concrete, A:lem:cont, A:lem:lawflow, A:lem:pert, A:lem:small, A:rem:cwp-class, A:rem:diag-mono, A:rem:generalrank, A:rem:intrinsic, A:sec2:coefmeas, A:sec2:hborel-derivation, A:sec4:horizon-not-contractive, A:sec:examples, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: Dissertation.WellPosedness.System.P2WH.instPseudoMetricSpace
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 82d8357fc285df8b92c2893645916ccb (pl-fp-v1:8fa5db78cc4f52b1cee42483dd55176151b28bae0d090c080d794d9e73af0062)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T12:39:50Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:35:39Z):
Reading: P2WH.instPseudoMetricSpace = the quadratic Wasserstein distance on P_2(H):
  W_2(mu, mu')^2 = inf over couplings pi of (mu, mu') of int |theta - theta'|_H^2 dpi,
with the paper's Hilbert norm |theta|_H^2 = |x|^2 + |y|^2 + |z|_F^2 + ||u||^2_{L^2(nu)}
(Villani Def. 6.1). Used in Assumption 2.3 (|delta psi| <= L(... + W_2(mu,mu'))), (2.8)-(2.9),
(2.10)-(2.11), Corollary 3.6 ((3.6) with c_pert = ||G|| L_p), Example 5.4 etc., where its exact
normalisation matters for constants. A faithful Lean instance has dist = this W_2 (a genuine
metric on P_2(H); a pseudometric structure carrying it is fine). A Wasserstein distance computed
with another norm on H (e.g. the max of the channel norms, giving a distance between 1/2 W_2 and
W_2) would not be the paper's W_2: harmless for topology/measurability, but not for statements
whose constants are quantitative (L, L_p, c_pert = ||G|| L_p).
(Disclosure: earlier, in files opened for other units, I saw that P2WH is defined as P2 over a
tuple type `Tuple HX HY HZY HUY` and that the record TupleH carries a max-of-channels norm with an
associated w2P; I have not seen the P2WH instances themselves.)
Comparison (verdict recorded 2026-10-17T12:39:28Z):
P2WH.instPseudoMetricSpace := PseudoMetricSpace.induced (mu |-> (lawToL2 mu).toP2W) on P2W
(TupleL2), where TupleL2 = WithLp 2 (HX × WithLp 2 (HY × WithLp 2 (HZY × HUY))) has norm^2 =
||x||^2 + ||y||^2 + ||z||^2 + ||u||^2 (norm_toL2_sq = channelSq), lawToL2 mu = toL2 # mu, and the
P2W distance is w2P = w2 = sqrt(toReal(inf over couplings gamma of int ||p1 - p2||^2 dgamma))
(Wasserstein.lean: IsCoupling = marginals equal; transportCostSq = lintegral of the squared norm).
So dist(mu, mu') = W_2 of the pushforwards for the Hilbert norm; since toL2 is a bijective linear
measurable map with measurable inverse, couplings correspond and this is the paper's W_2 on P_2(H)
with |theta|_H^2 = |x|^2+|y|^2+|z|_F^2+||u||^2 (P2WH.dist_toP2WH : dist = w2H). The toReal is not
junk: laws in P2 have finite second moments, so w2sq < inf. With HX = R^n, HY = R^m,
HZY = EuclideanSpace (Fin m x Fin d) (Frobenius), HUY = L^2(nu;R^m) (TupleP2WH) it is the
paper's W_2 with its exact normalisation (not the max-norm w2P on TupleH). It is a genuine metric
(the induced map is injective); recording it as a pseudometric is harmless. Faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-17T12:39:35Z): none (the author review shows only a marker, definitions.md:163; it should say that the distance is W_2 for the Hilbert norm, via toL2, not the max-norm w2P of TupleH).
