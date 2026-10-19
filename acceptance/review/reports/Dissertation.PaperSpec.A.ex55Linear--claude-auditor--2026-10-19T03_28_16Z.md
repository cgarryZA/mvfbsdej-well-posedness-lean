### A:abstract, A:ex:dealer, A:rem:regimes, A:sec5:overview: Dissertation.PaperSpec.A.ex55Linear
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash 3561bf3607d9b592dcbcbbff1b4dd84b (pl-fp-v1:1713a3d44ede974e7868983a13f6b8827c151dc3aad2e059683f49be85f5b93f)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:28:16Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:15:19Z):
Reading of def:Dissertation.PaperSpec.A.ex55Linear.

Paper notion. In Example 5.5 the word "linear" occurs in "The linear equation
  X^0_t = int_0^t ( -X^0_s ds + (1/2) dW_s ) + (1/2) int_0^t int_E (h_c(e) + h_x(e) X^0_{s-})
          N~(ds,de)
has Lipschitz coefficients, hence a unique solution X^0 in S^2(0,T;R)", in the specialisation
beta_1 = 1, beta_2 = 1/2, sigma_c = 1, xi_0 = 0, c_{+-1} = (2-rho)/2, h_c(s,q) = s q,
h_x(s,q) = q; from it Theta^0 = (X^0, Y^0 = X^0, Z^0 = 1/2, U^0_t = (1/2)(h_c + h_x X^0_{t-})),
which solves the system at epsilon = 0. Another possible reading of the name is the epsilon = 0
("linear", affine) part of the coefficient system of Ex. 5.5 (b = -beta_1 y, sigma = sigma_c -
beta_1 z, h = h_c + h_x x - beta_1 u, f = beta_2 x + <h_x,u>, g = x), i.e. ex55Coeffs at
epsilon = 0, which at h_x = 0 is Ex. 5.1(i).

What a faithful Lean definition must be:
 (a) if it encodes the linear SDE for X^0 (as a predicate on a process, or as the coefficient data
     of that SDE): drift -x (i.e. -beta_1 * y with y = x), Brownian coefficient 1/2 (=
     sigma_c - beta_1 z with z = 1/2), jump coefficient (1/2)(h_c + h_x x_-) evaluated at the left
     limit, initial value 0, with the specialised h_c, h_x on the dealer marks; the identity a.s.
     for every t (or the cadlag solution notion).
 (b) if it encodes the epsilon = 0 coefficient system: exactly the five maps above with general
     parameters (or the specialised ones), identical to ex55Coeffs with epsilon = 0.
Either way the coefficients must be the printed ones with the printed signs; the jump term must
use X_{s-}; h_c, h_x elements of L2(nu) with h_x x the scalar multiple.
Comparison (verdict recorded 2026-10-19T03:26:34Z):
def:Dissertation.PaperSpec.A.ex55Linear (Dissertation/PaperSpec/A/Sec5DealerActive.lean:48-65):
LinearFSDEJ D (enlJoint 𝒢₀ D h𝒢₀) … T (ξ₀ = 0) (b = 1_{[0,T]}(s)·(−X_s)) X (σ = 1_{[0,T]}(s)·½)
(γ = 1_{(0,T]}(s)·½(ς q + q X_{s−})), ς = (if e.1 then 1 else −1), q = e.2, over the driver
D : LevyDriver P 1 (ex55Marks ϱ); LinearFSDEJ from Stability/ForwardEq.lean:64-104.
Against my reading, case (a) (the linear SDE for X⁰):
- Equation: X_t = 0 + ∫_{[0,t]} (−X_s) ds + ∫_0^t ½ dW_s + ∫_0^t∫_E ½(h_c(e) + h_x(e)X_{s−}) Ñ(ds,de)
  with h_c(ς,q) = ς q, h_x(ς,q) = q, the left limit leftLimProc X (Function.leftLim) in the jump
  integrand; d = 1; marks ex55Marks ϱ (c_{±1} = (2−ϱ)/2). Exactly the paper's
  X⁰_t = ∫_0^t(−X⁰_s ds + ½ dW_s) + ½∫_0^t∫_E (h_c + h_x X⁰_{s−}) Ñ(ds,de), ξ₀ = 0, β₁ = 1,
  σ_c = 1 (σ = σ_c − β₁ Z⁰ = ½). ✓
- Filtration: enlJoint (paper's (F_t)); integrals: L² Itô and compensated Poisson integrals. ✓
- Solution notion: X adapted (at every real t), every path right-continuous (at every real t),
  equation a.s. at each t ∈ [0,T]; integrands progressive/marked progressive, finite energy
  (E∫_0^T X² < ∞ via b_sq; marked energy of γ, finite iff E∫(1+X²) < ∞ since ‖h_c‖ = ‖h_x‖ = 1 and
  ⟨h_c,h_x⟩ = 0), vanishing off [0,T]; ξ₀ = 0 ∈ L².
- Representation choices: processes indexed by ℝ with adaptedness and right-continuity asked at
  all real times (a paper solution on [0,T] extends, e.g. frozen after T and 0 before 0; a.s.
  regularity is upgraded to every path by modification on a null set, which is in enlJoint 0);
  "a.s. at each t" instead of "a.s. for all t" (equivalent: both sides right-continuous, the
  integrals being càdlàg versions); the jump integrand cut to (0,T] instead of [0,T] (s = 0 is a
  null time); S²-membership and left limits not asked explicitly but implied by the equation with
  L² integrands (E sup|X|² < ∞ from b_sq, σ, γ energies and BDG/Doob). The parameter ϱ is not
  constrained in the definition (the claims must impose 0 < ϱ < 2).
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — The predicate is the paper's linear equation X⁰_t = ∫_0^t(−X⁰_s ds + ½ dW_s) +
½∫_0^t∫_E(h_c + h_x X⁰_{s−}) dÑ with h_c = ςq, h_x = q, ξ₀ = 0, on the paper's filtration, read as
LinearFSDEJ. Choices: (1) time is ℝ, with adaptedness and every-path right-continuity at all real
times (a paper solution on [0,T] extends constantly and, after modification on a null set, which
the augmented filtration contains, meets them); (2) the equation a.s. at each t ∈ [0,T]
(equivalent to a.s. for all t by right-continuity of both sides); (3) the jump integrand cut to
(0,T] (s = 0 is Lebesgue-null); (4) membership in S² is implied by the equation with its L²
integrands rather than stated; (5) ϱ is a free real, its range 0 < ϱ < 2 left to the claims.
Disagreements with the author's review (shown 2026-10-19T03:27:50Z): No disagreement on the reading. Additions to the author's description, all harmless: LinearFSDEJ
asks adaptedness and every-path right-continuity at all real times, not only on [0,T]. The equation
is required a.s. at each t, which is equivalent to a.s. for all t because both sides are right-
continuous. Membership in S² and the left limits are not stated but follow from the equation with
its L² integrands (the author's review covers them in ex_dealer_zero). The definition leaves ϱ
free, so 0 < ϱ < 2 must come from the propositions.
