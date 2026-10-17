### A:ass:integ, A:cor:robust, A:ex:brownian, A:ex:concrete, A:lem:cont, A:lem:small, A:rem:cwp-class, A:rem:generalrank, A:sec4:horizon-not-contractive, A:sec:examples, A:thm3.1:companion, A:thm:cwp, A:thm:stab: Dissertation.WellPosedness.Spec.Assumption22
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 5efdb45a84324ede0000000000000000 (pl-fp-v1:738fc3cb6b77eab5dfe70c0ecdcc8589927bb054c03eb717c2f89ed1541ee699)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:04:37Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:35:10Z):
Unit: def Spec.Assumption22 (Assumption 2.2, Integrability at the origin; 12 more claims).
Paper: xi_0 in L^2(Omega, F_0; R^n) and, with delta_0 the Dirac mass at the origin of H,
   b(., 0, delta_0) in L^2(0,T; R^n),        sigma(., 0, delta_0) in L^2(0,T; R^{n x d}),
   h(., 0, ., delta_0) in L^2(0,T; L^2(nu;R^n)),  f(., 0, delta_0) in L^2(0,T; R^m).
Faithful Lean: a predicate on (filtration F, P, T, coefficients C, xi_0) with
 * xi_0 measurable for the time-0 sigma-algebra F_0 of the standing filtration (a.e.-strong
   measurability w.r.t. F_0 is acceptable up to null sets if F_0 contains the null sets), and
   E|xi_0|^2 < inf (MemLp 2 P);
 * t |-> b(t, 0, delta_0) in L^2([0,T], Lebesgue) (measurable and square integrable), same for
   sigma (Frobenius norm, R^{n x d}), f (R^m), and t |-> h(t, 0, delta_0) in L^2(0,T; L^2(nu)) as a
   Bochner space (strong measurability of the L^2(nu)-valued map and int_0^T ||h||^2 dt < inf),
   or equivalently the joint function in L^2(dt x nu);
 * 0 = the origin of H = (0,0,0,0) and delta_0 = Dirac at it in P_2(H).
No condition on g (g's origin value is not part of 2.2; the paper uses |g(0,delta_0)| finite,
which is automatic). Measurability of t |-> values follows from joint Borel measurability in the
paper; in Lean it may be part of L^2 membership.
Comparison (verdict recorded 2026-10-17T12:41:35Z):
Assumption22 F P T C xi0 (Spec/Assumptions.lean:102): fields
  initial_meas : StronglyMeasurable[F 0] xi0;  initial_memLp : MemLp xi0 2 P;
  origin : OriginValues T C,
OriginValues T C: MemLp (t |-> C.b t 0 (P2.dirac 0)) 2 (volume.restrict (Ioo 0 T)), and the same for
sigma (values in EuclideanSpace R (Fin n x Fin d), Frobenius norm), h (values in Lp R^n 2 nu: the
Bochner space L^2(0,T; L^2(nu;R^n)), with a.e.-strong measurability of the Lp-valued map) and f.
Comparison: xi0 in L^2(Omega, F_0; R^n) = F_0-strongly measurable and square integrable (F 0 is the
time-0 field of the filtration the statements instantiate with enlJoint, which contains the null
sets, so measurability versus a.e.-measurability is immaterial); origin values at theta = 0 (the
origin of H) and mu = Dirac at 0 in P_2(H); L^2 over (0,T) instead of [0,T] (Lebesgue-null
difference). No extra condition, none missing.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — 1. xi0 is asked strongly F_0-measurable (not merely a.e. equal to such): equivalent when F_0
   contains the null sets of the ambient sigma-algebra, as the standing filtration enlJoint does.
2. L^2(0,T) taken on the open interval Ioo 0 T: differs from [0,T] by a Lebesgue-null set.
3. h's origin value in L^2(0,T; L^2(nu;R^n)) as MemLp of the Lp-valued map (Bochner), the paper's space.
Disagreements with the author's review (shown 2026-10-17T15:04:21Z): No disagreement on substance. The author's review is an empty marker with no recorded
comparison; the representation choices listed in my detail are not recorded there.
