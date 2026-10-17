### A:ass:integ, A:cor:robust, A:ex:brownian, A:ex:concrete, A:lem:cont, A:lem:small, A:rem:cwp-class, A:rem:generalrank, A:sec4:horizon-not-contractive, A:sec:examples, A:thm3.1:companion, A:thm:cwp, A:thm:stab: Dissertation.WellPosedness.Spec.Assumption22.mk
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash f08ed69f41bd56a20000000000000000 (pl-fp-v1:8b66c86d7f0f8d73bdd1908e671f7e176710e55e12400d02a04a5652dd2bcab0)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:04:37Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:35:27Z):
Unit: Assumption22.mk, the constructor of Assumption22 (Assumption 2.2). Its type must take
exactly the clauses of Assumption 2.2 as arguments and return Assumption22 F P T C xi_0:
  * xi_0 in L^2(Omega, F_0; R^n): F_0-measurability (F_0 the time-0 field of the filtration)
    and square integrability;
  * b(., 0, delta_0) in L^2(0,T;R^n); sigma(., 0, delta_0) in L^2(0,T;R^{n x d});
    h(., 0, ., delta_0) in L^2(0,T;L^2(nu;R^n)); f(., 0, delta_0) in L^2(0,T;R^m),
with 0 the origin of H and delta_0 the Dirac mass there; L^2(0,T;.) on [0,T] with Lebesgue
measure, including measurability. Nothing else (no condition on g, no Lipschitz condition).
Comparison (verdict recorded 2026-10-17T12:42:37Z):
Assumption22.mk : StronglyMeasurable[F 0] xi0 -> MemLp xi0 2 P -> OriginValues T C ->
Assumption22 F P T C xi0. (The rv.py signature prints `StronglyMeasurable xi0` without the
sigma-algebra; `#check` with pp.explicit in a scratch file confirms the argument is
@StronglyMeasurable Omega _ _ (F.seq 0) xi0, i.e. F_0-measurability.)
Exactly the clauses of Assumption 2.2 (xi0 in L^2(F_0), the four origin values in L^2(0,T) via
OriginValues), nothing added. Representation choices as for Assumption22: strong
F_0-measurability (equivalent when F_0 contains the null sets, as enlJoint does), Ioo 0 T.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Same as Assumption22: xi0 strongly F_0-measurable (equivalent to a.e. when F_0 holds the null sets,
as the standing filtration does); L^2 on Ioo 0 T rather than [0,T] (null difference); h's origin
value in the Bochner space L^2(0,T; L^2(nu;R^n)).
Disagreements with the author's review (shown 2026-10-17T15:04:21Z): No disagreement on substance. The author's review is an empty marker with no recorded
comparison; the representation choices listed in my detail are not recorded there.
