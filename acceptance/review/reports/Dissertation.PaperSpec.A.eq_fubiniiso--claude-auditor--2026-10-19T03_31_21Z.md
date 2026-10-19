### A:eq:fubiniiso: Dissertation.PaperSpec.A.eq_fubiniiso
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba1f8905adfcaf41890 (pl-fp-v1:d992d86a1162afdeb7559169e80b9b96dea4f571dcf1f3756f465e6546c7fda1)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:31:21Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:16:07Z):
Reading of spec eq_fubiniiso, clause "the Fubini isometry, the jointly measurable representative and its
uniqueness" ((2.4), 02-model-assumptions.tex:112-123).
Setting: standing basis; calP the predictable sigma-field on Omega x [0,T] (wrt (F_t)), measure dt x dP;
nu sigma-finite on countably generated (E,calE); L2(nu)=L2(nu;R^j) separable.
Claims:
 (a) Fubini isometry: L^2(calP; L2(nu)) ≅ L^2(calP ⊗ calE) isometrically (the map sends a P x E-measurable
     square-integrable u to (s,omega) |-> [u(s,omega,.)] in L2(nu); it is a linear isometric bijection);
 (b) every element U of L^2(calP;L2(nu)) (a strongly calP-measurable, square-integrable L2(nu)-valued
     process) has a calP⊗calE-measurable representative u: Omega x [0,T] x E -> R^j, i.e. u(s,omega,.) is a
     representative of U(s,omega) for dt x dP-a.e. (s,omega), with E int int |u|^2 dnu ds = E int ||U||^2 ds;
 (c) uniqueness: any two such representatives agree dt x dP x nu-a.e.
A faithful formal statement must quantify over all such U (all j or the relevant j), use the predictable
sigma-field of the standing filtration (not merely progressive/product), the product measure
(dt x dP) x nu, and include existence + a.e.-uniqueness of the representative (and the isometry, e.g. as norm
equality or as a LinearIsometryEquiv). Weaker variants (only existence; measurable instead of predictable;
only for a fixed U) are narrower.
Comparison (verdict recorded 2026-10-19T03:29:17Z):
Comparison, eq_fubiniiso (Sec2Basics.lean:147-167) vs reading.
- Setting: an arbitrary σ-finite measure space (X, μ) in place of (Ω×[0,T], P, dt⊗dP); ν σ-finite on a
  countably generated E; every j. The paper's instance: X := Ω × [0,T] with the predictable σ-field P
  of (F_t) as its measurable space, μ := (dt ⊗ dP)|_P (finite). Then "Measurable g" on X × E is
  P⊗E-measurability and μ.prod ν is dt⊗dP⊗ν, exactly (2.4).
- (a) ∃ linear isometric equivalence Φ : L²(μ⊗ν; R^j) ≃ L²(μ; L²(ν; R^j)) with Φ g (x) = [g(x,·)] for
  μ-a.e. x: the Fubini isometry with the section map. Matches.
- (b) every u ∈ L²(μ; L²(ν)) has a jointly measurable representative g (sections represent u(x) for
  μ-a.e. x). Matches the existence of the P⊗E-measurable representative.
- (c) two jointly measurable representatives agree μ⊗ν-a.e. Matches uniqueness.
Verdict: broader (generic σ-finite base).
Witness: —
Verdict: broader — Broader: stated for every σ-finite measure space (X, μ) instead of the predictable σ-field. The printed
(2.4) is the instance X := Ω × [0,T] equipped with the predictable σ-field P of the standing filtration
as its MeasurableSpace, μ := (Lebesgue ⊗ P) restricted to P (a finite measure), ν the standing intensity
(σ-finite, E countably generated), j the relevant dimension: then L²(μ⊗ν; R^j) = L²(P⊗E), L²(μ; L²(ν))
= L²(P; L²(ν)), "Measurable g" = P⊗E-measurable, and the three conjuncts are the isometry, the
representative and its a.e. uniqueness.
Disagreements with the author's review (shown 2026-10-19T03:29:28Z): none
