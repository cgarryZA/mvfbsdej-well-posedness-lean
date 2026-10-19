### A:abstract, A:ex:dealer, A:rem:regimes, A:sec5:overview: Dissertation.PaperSpec.A.ex55Crowd
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash 8d3f49063f9d40bd91804eeb64810052 (pl-fp-v1:467e7411bbbd23eb5cf3ede2855146da942b82a9800e454e22284496fcd71d33)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:28:16Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:15:19Z):
Reading of def:Dissertation.PaperSpec.A.ex55Crowd.

Paper notion (Example 5.5): the crowding correction
  A_lambda(u) := int_{L2(nu)} grad V(u - v) lambda(dv),   lambda in P_2(L2(nu)), u in L2(nu),
  V(w) = sqrt(1+||w||^2) - 1,  grad V(w) = w / sqrt(1+||w||^2),
a Bochner integral with values in L2(nu) (here L2(nu;R), n=m=1). In h it is evaluated at
lambda = mu^U, the U-marginal of the measure argument. Properties claimed (not part of the
definition): 1-Lipschitz in u plus W_2 in lambda; affine in lambda; not a function of the mean.

Faithful Lean definition: ex55Crowd lambda u := Bochner integral over lambda (as a measure on
L2(nu)) of v |-> (1/sqrt(1+||u - v||^2)) . (u - v) (or the same with lambda replaced by mu on H
and v by the U-component). The gradient formula must be exactly w/sqrt(1+||w||^2). If the measure
argument is a measure on H, it must integrate the U-coordinate (i.e. use mu^U). Junk: Bochner
integral = 0 for non-integrable integrands; with a bounded continuous integrand and separable
L2(nu) (E countably generated, nu sigma-finite) no junk occurs; on a non-separable L2(nu) the
integrand might fail to be strongly measurable, a corner the paper excludes by its standing
assumption.
Comparison (verdict recorded 2026-10-19T03:26:34Z):
def:Dissertation.PaperSpec.A.ex55Crowd (Dissertation/PaperSpec/A/Sec5.lean:629-633):
  ex55Crowd Λ u := ∫ v, (Real.sqrt (1 + ‖u - v‖ ^ 2))⁻¹ • (u - v) ∂Λ
for a measure Λ on a real Hilbert space F (InnerProductSpace, CompleteSpace, any MeasurableSpace).
Against the reading: A_λ(u) = ∫ ∇V(u−v) λ(dv) with ∇V(w) = w/√(1+‖w‖²): exact formula (the
inverse is of √(1+…) ≥ 1, never 0). Bochner integral in F; with F = L²(ν) and Λ = μ^U (as used in
ex55Coeffs: μ.margU.law), F carries the Borel σ-algebra and is separable under the standing
assumptions, so the bounded continuous integrand is integrable and no junk arises.
Representation choices: (1) the measure argument is any measure on F (not only P_2(L²(ν))); for
non-finite Λ or a non-Borel σ-algebra / non-separable F the Bochner junk 0 could occur, cases the
paper never forms; (2) the measure is passed directly as a measure on F (the U-marginal is taken
by the caller), equivalent to the paper's A_{μ^U}.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — The formula is exactly A_Λ(u) = ∫ (u−v)/√(1+‖u−v‖²) Λ(dv). Choices: the argument Λ is an arbitrary
measure on an arbitrary real Hilbert space F with an arbitrary measurable structure, so for
non-finite Λ, a non-Borel σ-algebra or a non-separable F the Bochner integral could return its
junk value 0. The paper only forms A at λ = μ^U ∈ P₂(L²(ν)) on the separable L²(ν) with its Borel
σ-algebra (as ex55Coeffs does), where the bounded continuous integrand is integrable.
Disagreements with the author's review (shown 2026-10-19T03:27:50Z): none
