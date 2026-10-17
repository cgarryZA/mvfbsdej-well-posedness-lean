### A:cor:robust, A:eq:coefmeas, A:eq:hborel, A:ex:brownian, A:ex:concrete, A:lem:cont, A:lem:pert, A:lem:small, A:rem:cwp-class, A:rem:diag-mono, A:rem:generalrank, A:rem:intrinsic, A:sec2:coefmeas, A:sec4:horizon-not-contractive, A:sec:examples, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: Dissertation.WellPosedness.Spec.JointBorel
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 4b26c5076ea2f4260000000000000000 (pl-fp-v1:10b195ad9f8f537086c161243e7f185b831136d6309edb44549c7d6746cc3fc3)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:04:38Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:36:07Z):
Unit: def Spec.JointBorel (19 claims). Paper (§2): "All coefficients are jointly Borel
measurable in their arguments; for the jump coefficient ... Borel measurability of the map
(t,theta,mu) |-> h(t,theta,.,mu), [0,T] x H x P_2(H) -> L^2(nu;R^n)" (2.3), which follows from joint
pointwise measurability of (t,theta,e,mu) |-> h(t,theta,e,mu) (Pettis).
So: b : [0,T] x H x P_2(H) -> R^n, sigma -> R^{n x d}, f -> R^m Borel; h Borel into L^2(nu;R^n);
g : R^n x P_2(R^n) -> R^m Borel. Borel sigma-algebras: on [0,T] the usual; on H the Borel
sigma-algebra of the Hilbert norm (H separable since nu is on a countably generated space); on
P_2(H) the Borel sigma-algebra of the W_2 topology (equivalently, as P_2(H) is Polish under W_2
and its identity map into P(H) with the weak topology is a continuous injection, the trace of
the evaluation/weak Borel sigma-algebra; so an evaluation sigma-algebra mu |-> mu(A) is an
equivalent choice); joint = product sigma-algebra (equal to Borel of the product for these
second-countable spaces).
Faithful Lean: measurability of the uncurried maps on the product (with t restricted to [0,T] or
on all of R, the latter a harmless strengthening only if the coefficients off [0,T] are
irrelevant), including g in (x, rho) jointly (the paper says "all coefficients ... jointly Borel"),
h as an Lp-valued map (strong/Borel measurability). It must not demand continuity or more.
Comparison (verdict recorded 2026-10-17T15:02:41Z):
JointBorel T C (Spec/Assumptions.lean): b, sigma, h, f measurable from
borel(Icc 0 T x TupleH x TupleP2WH) into borel of R^n, R^{n x d} (EuclideanSpace (Fin n x Fin d)),
Lp(R^n) 2 nu, R^m respectively, as p |-> C.psi p.1 p.2.1 p.2.2.toP2; g measurable from
borel(R^n x P2W R^n) into borel R^m. TupleP2WH is P_2(H) with the W_2 distance of the Hilbert norm
of H and its Borel sigma-algebra (HilbertW2Space.lean:129, P2Metric.lean); P2W R^n likewise.
Comparison with the reading: joint Borel measurability on [0,T] x H x P_2(H) with the W_2-Borel
structure, h as an L^2(nu;R^n)-valued map, g jointly on R^n x P_2(R^n): all present; no continuity
or other extra condition. The domain sigma-algebra is the Borel sigma-algebra of the product
topology; as Icc 0 T, H (separable: nu sigma-finite on countably generated E) and P_2 with W_2 over a
separable space are second countable, this equals the product of the Borel sigma-algebras, so both
readings of "jointly Borel" agree. Time restricted to [0,T] as printed.
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-17T15:04:21Z): none
