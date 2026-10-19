### A:ex:concrete: Dissertation.PaperSpec.A.ex_concrete_ii_pairing
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba16aa5f84a4f3328b5 (pl-fp-v1:24b0e4eed87fe4e05b10f7fe893d24b079c425d5b243a1cbf798ed42fb825cea)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:33:35Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:15:37Z):
Reading (locked before any Lean): spec ex_concrete_ii_pairing, clause "(ii) the pairings along the diagonal"
of Example 5.1(ii).

Paper content. Standing setting of §2 (filtered space with usual conditions, horizon T>0, d-dim
Brownian motion W, independent Poisson random measure N on R_+ x E, intensity dt nu(de), nu
sigma-finite on a countably generated (E, calE), arbitrary activity, nu(E)=infinity allowed).
Example (ii) keeps n=m=d=1 and G=1. Coefficients (deterministic, time-independent):
  b(t,theta,mu) = -2y - m_Y(mu), sigma = -2z - m_Z(mu), h(e) = -2u(e) - m_U(mu)(e),
  f = 2x + m_X(mu), g(x,rho) = 2x + bary(rho),
with m_Psi(mu) = int pi_Psi(theta) mu(dtheta) (Bochner mean of the Psi-marginal; m_U(mu) is an
element of L2(nu)) and bary(rho) = int x rho(dx).
Claim of the clause: along diagonal pairs (Theta, Law Theta), (Theta', Law Theta') in D_t
(Theta, Theta' in L2(Omega, F_t; H)), the interior pairing of (2.7)
  E[<db,dY> + <dsigma,dZ> + <-df,dX> + int_E <dh(e),dU(e)> nu(de)]
  = -2 E[|dX|^2+|dY|^2+|dZ|_F^2+||dU||^2] - (|E dX|^2+|E dY|^2+|E dZ|^2+||E dU||^2)
  <= -2 E[|dX|^2+|dY|^2+|dZ|^2+||dU||^2],
and the terminal pairing, for X_T, X'_T in L2(Omega,F_T;R) with rho = Law X_T, rho' = Law X'_T,
  E<dg_T, dX_T> = 2E|dX_T|^2 + |E dX_T|^2 >= 2 E|dX_T|^2,
hence Assumption 2.5 with alpha = beta1 = beta2 = 2 (G=1, so G^T dY = dY etc.).

A faithful formal statement must contain:
- the setting at arbitrary sigma-finite nu (not only finite nu); n=m=d=1, G=1 (or a broader form
  that specialises to these);
- the exact coefficients above, with the means as integrals against the measure argument
  (on the diagonal they become E Psi); h valued in L2(nu), its mean m_U a Bochner mean in L2(nu);
- quantification: for every (or a.e.) t, for all F_t-measurable square-integrable H-valued Theta,
  Theta' with the measure arguments equal to their own laws (diagonal, not free measures);
  terminal: all F_T-measurable square-integrable X_T, X'_T with their own laws;
- conclusion: the interior inequality with beta1 = beta2 = 2 and the terminal inequality with
  alpha = 2 (either as the two exact identities with the mean-square terms or as the resulting
  inequalities); the interior pairing with the L2(nu) inner product for the jump channel.
- Acceptable: stating the conclusion as "Assumption 2.5's two inequalities hold with
  alpha=beta1=beta2=2". The clause name says "the pairings", so the identities are the most literal
  form; the inequalities are what the example uses.
- Lean junk-value watch: expectations of non-integrable functions (Bochner = 0) - on L2 inputs all
  pairings here are integrable, so no issue if the inputs are genuinely L2; means of measures in
  P_2 are well defined. Witness: none needed beyond existence of L2 inputs (hypotheses are only
  membership of inputs), but a vacuity check: the quantified class must be nonempty/meaningful.
Comparison (verdict recorded 2026-10-19T03:18:02Z):
Comparison: spec ex_concrete_ii_pairing (Sec5.lean:269-318) against my locked reading.

Setting. Arbitrary Ω, initial σ-field 𝒢₀ ≤ mΩ independent of the driver σ-fields, arbitrary
measurable E with CountablyGenerated, arbitrary SigmaFinite ν (infinite activity allowed),
probability P, a LevyDriver with d = 1 (1-dim Brownian motion W and Poisson random measure N,
σ(W) ⊥ σ(N)), filtration enlJoint 𝒢₀ D h𝒢₀ = usual augmentation (right-continuous version,
augmented by null sets) of t ↦ ℱ^{W,N}_t ⊔ 𝒢₀ — the paper's standing filtration. T > 0 arbitrary.
n = m = d = 1 (Coeffs ν 1 1 1 via meanFieldCoeffs ν 1 1), G = 1 (pairing27 with the identity
matrix; GX 1 = toEuclideanLin 1 = id, GZ 1 = 1 ⊗ I = id). Matches.

Coefficients. meanFieldCoeffs: b = −2y − (tupleMean μ).Y, σ = −2z − (tupleMean μ).Z,
h = −2u − (tupleMean μ).U (an element of L²(ν)), f = 2x + (tupleMean μ).X, g(x, ρ) = 2x +
barycentre ρ, with tupleMean μ = Bochner ∫ θ dμ (channels = marginal means, tupleMean_eq) and
barycentre ρ = ∫ x dρ. Exactly the paper's coefficients of (ii).

Quantifiers. ∀ t (every real t, broader than any a.e.-t reading and harmless: the identities are
algebraic and hold at every t, coefficients being time independent), ∀ p, p' ∈ diagonalInputs at
t for the standing filtration: Θ strongly ℱ_t-measurable, MemLp 2, μ = lawP2 P Θ — the diagonal
𝒟_t of Definition 2.1. Terminal: ∀ X_T, X'_T strongly ℱ_T-measurable and square integrable, with
their own laws. Matches.

Conclusion. (0) tupleMean p.2 = E Θ (the paper's m_Ψ(Law Θ) = E Ψ); (1)-(4) the four channel
identities E⟨−δf, δX⟩ = −2E|δX|² − |EδX|², E⟨δb, δY⟩ = ..., E⟨δσ, δZ⟩ = ..., and
E ∫_E ⟨δh(e), δU(e)⟩ ν(de) = −2E‖δU‖²_{L²} − ‖EδU‖²_{L²} (pointwise evaluation of L² classes
under ∫ dν, independent of representatives); (5) the full interior pairing (pairing27 with G = 1,
which is ⟨δb, δY⟩ + ⟨δσ, δZ⟩_F + ⟨−δf, δX⟩ + ∫⟨δh(e), δU(e)⟩ν(de)) equals −2E[sum of squares] −
(sum of squared means); (6) terminal E⟨δg_T, δX_T⟩ = 2E|δX_T|² + |EδX_T|². These are exactly the
paper's displayed identities; the inequalities and "Assumption 2.5 with α = β₁ = β₂ = 2" follow
immediately (the mean squares being nonnegative). The clause is "the pairings along the
diagonal", which the identities state literally.

Junk values: all integrands are integrable for L² inputs (products of L² functions, Bochner means
of P₂ laws), so the Bochner integrals are genuine; lawP2 of a MemLp map is its law in P₂. No
hypotheses beyond the setting, which is inhabited (LevyDriver.exists; witness
ex_concrete_hypotheses exists in Acceptance/A/Witness.lean), and diagonal inputs exist (e.g.
constants), so no vacuity.

Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-19T03:33:25Z): none
