### A:ass:integ, A:cor:robust, A:ex:brownian, A:ex:concrete, A:lem:cont, A:lem:small, A:rem:cwp-class, A:rem:generalrank, A:sec4:horizon-not-contractive, A:sec:examples, A:thm3.1:companion, A:thm:cwp, A:thm:stab: Dissertation.WellPosedness.Spec.OriginValues
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 4b26c5076ea2f4260000000000000000 (pl-fp-v1:10b195ad9f8f537086c161243e7f185b831136d6309edb44549c7d6746cc3fc3)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:04:37Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:37:23Z):
Unit: def Spec.OriginValues (the coefficient half of Assumption 2.2).
Paper: with 0 the origin of H and delta_0 the Dirac mass at it:
  t |-> b(t,0,delta_0) in L^2(0,T;R^n), t |-> sigma(t,0,delta_0) in L^2(0,T;R^{n x d}),
  t |-> h(t,0,.,delta_0) in L^2(0,T; L^2(nu;R^n)), t |-> f(t,0,delta_0) in L^2(0,T;R^m).
Faithful Lean: a predicate over (T, C) (no filtration, no P needed) with the four memberships,
each as MemLp 2 on [0,T] with Lebesgue measure (including (a.e.-strong) measurability), the h one
in the Bochner space of L^2(nu)-valued maps (or equivalently the joint L^2(dt x nu) function),
evaluated exactly at theta = 0 and mu = Dirac(0) in P_2(H). Nothing about g or xi_0.
Comparison (verdict recorded 2026-10-17T15:03:56Z):
OriginValues T C (Spec/Assumptions.lean): MemLp (t |-> C.b t 0 (P2.dirac 0)) 2 (volume.restrict
(Ioo 0 T)), and likewise for sigma (R^{n x d}, Frobenius), h (values in Lp R^n 2 nu: membership in the
Bochner space L^2(0,T; L^2(nu;R^n)), with a.e.-strong measurability of the Lp-valued map) and f (R^m).
0 is the origin of H (zero of the product), P2.dirac 0 the Dirac mass there.
Matches the reading: the four memberships, nothing about g or xi0; L^2 includes measurability.
Representation choice: the open interval (0,T) instead of [0,T] (Lebesgue-null difference).
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — L^2(0,T) is taken over Ioo 0 T rather than [0,T]: the two differ by a Lebesgue-null set, so the
memberships are the same. h's origin value is in the Bochner space of L^2(nu;R^n)-valued maps, the
paper's L^2(0,T; L^2(nu;R^n)).
Disagreements with the author's review (shown 2026-10-17T15:04:22Z): No disagreement on substance. The author's review is an empty marker with no recorded
comparison; the representation choices listed in my detail are not recorded there.
