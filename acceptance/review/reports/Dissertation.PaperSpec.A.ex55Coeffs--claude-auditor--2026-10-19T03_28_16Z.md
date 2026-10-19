### A:abstract, A:ex:dealer, A:rem:regimes, A:sec5:overview: Dissertation.PaperSpec.A.ex55Coeffs
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash 7d5b37041cd45e9e4ecfce744149d3e2 (pl-fp-v1:25f386981ef1f7cb663b73c12cf6980b081409a8c456cc71721e73c625beb154)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:28:16Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:15:19Z):
Reading of def:Dissertation.PaperSpec.A.ex55Coeffs.

Paper notion (Example 5.5, built on Ex. 5.1(i)): dimensions n = m = d = 1, G = 1, nu sigma-finite;
parameters beta_1, beta_2 > 0 (Ex. 5.1(i)), sigma_c in R, h_c in L2(nu), and (Ex. 5.5) epsilon >= 0
and h_x in L2(nu). The coefficient system, for theta = (x,y,z,u) in H = R x R x R x L2(nu) and
measure argument mu in P_2(H), time-independent:
  b(t,theta,mu) = -beta_1 y,
  sigma(t,theta,mu) = sigma_c - beta_1 z,
  h(t,theta,mu) = h_c + h_x x - beta_1 u - epsilon A_{mu^U}(u)   (an element of L2(nu);
                  h_x x is the scalar multiple x . h_x),
  f(t,theta,mu) = beta_2 x + <h_x, u>_{L2(nu)},
  g(x,rho) = x,
with mu^U the U-marginal of mu and A the crowding correction A_lambda(u) = int_{L2(nu)}
grad V(u - v) lambda(dv), grad V(w) = w / sqrt(1+||w||^2).

Faithful Lean definition: a coefficient record whose five fields are exactly these maps (with the
types of the paper's general coefficient record specialised to n=m=d=1), the sign conventions as
printed (minus beta_1 y, minus beta_1 z, minus beta_1 u, minus epsilon A, plus <h_x,u>), the
crowding term evaluated at the U-marginal of the measure argument (equivalently
int grad V(u - pi_U theta') mu(dtheta')), and the terminal map independent of rho. Parameters may be
arbitrary reals in the definition (constraints beta_i > 0, epsilon >= 0 belong to the claims) as
long as they are imposed where the paper imposes them. Time domain: defining for all real t
instead of [0,T] is harmless. Z-slot: R^{1x1} may be represented by R. Junk to watch: the
Bochner integral defining A is 0 if the integrand is not integrable; here grad V is bounded and
continuous, so integrable whenever u |-> u is strongly measurable for lambda (true on separable
L2(nu)); inner product must be the L2(nu) inner product.
Comparison (verdict recorded 2026-10-19T03:26:34Z):
def:Dissertation.PaperSpec.A.ex55Coeffs (Dissertation/PaperSpec/A/Sec5Dealer.lean:40-51), a
Coeffs ν 1 1 1 (System/Coefficients.lean:77: b, σ, h, f : ℝ → TupleH → P2 TupleH → …,
g : ℝⁿ → P2 ℝⁿ → ℝᵐ):
  b _ θ _ := -(β₁ • θ.2.1)                      — b = −β₁ y. ✓
  σ _ θ _ := σc - β₁ • θ.2.2.1                   — σ = σ_c − β₁ z (σc, z ∈ ℝ^{1×1}). ✓
  h _ θ μ := hc + θ.1 0 • hx - β₁ • θ.2.2.2 - ε • ex55Crowd μ.margU.law θ.2.2.2
                                                 — h = h_c + x h_x − β₁ u − ε A_{μ^U}(u),
                                                   x = θ.1 0 the scalar state, μ^U = margU. ✓
  f _ θ _ := β₂ • θ.1 + EuclideanSpace.single 0 (inner ℝ hx θ.2.2.2)
                                                 — f = β₂ x + ⟨h_x, u⟩_{L²(ν)} as a vector of ℝ¹. ✓
  g x _ := x                                     — g(x, ρ) = x. ✓
- n = m = d = 1 as in Ex. 5.1(i)/5.5; L²(ν) = Lp (EuclideanSpace ℝ (Fin 1)) 2 ν; inner is the
  L²(ν) inner product; signs as printed; crowding term evaluated at the U-marginal of the measure
  argument (P2.margU, then its underlying measure on L²(ν) with the Borel σ-algebra); the
  crowding correction is the paper's A (see ex55Crowd).
- Representation choices: σ_c is an element of EuclideanSpace ℝ (Fin 1 × Fin 1) (= ℝ^{1×1}, the
  type of the σ-channel) rather than a real; the parameters β₁, β₂, ε are arbitrary reals and
  h_c, h_x arbitrary in L²(ν) (the paper's β_i > 0, ε ≥ 0 must be imposed by the claims); the maps
  are time-independent and defined for all real t; the measure argument is an element of
  P2(TupleH) (the project's coefficient record). SigmaFinite ν and CountablyGenerated E are
  instance arguments (paper's standing setting), making L²(ν) separable so that the Bochner
  integral in A has no junk for the probability measure μ^U (integrand bounded and continuous).
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — (1) σ_c is taken in EuclideanSpace ℝ (Fin 1 × Fin 1) = ℝ^{1×1}, the codomain of σ, instead of ℝ:
the same object for n = d = 1. (2) β₁, β₂, ε range over all reals and h_c, h_x over L²(ν): the
paper's constraints (β_i > 0, ε ≥ 0) are hypotheses of the claims, not of the coefficients.
(3) Time-independent maps defined for every real t; only [0,T] enters. (4) The crowding term is
ex55Crowd evaluated at μ.margU.law, the U-marginal of the measure argument as a Borel probability
on L²(ν), which is the paper's A_{μ^U}(u); with ν σ-finite and E countably generated, L²(ν) is
separable, so the Bochner integral has no junk.
Disagreements with the author's review (shown 2026-10-19T03:27:50Z): none
