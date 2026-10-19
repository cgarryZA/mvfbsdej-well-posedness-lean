### A:rem:uniq-no-integ: Dissertation.PaperSpec.A.rem_uniq_translation
Pins: manuscript A None; project 90f9502669c17b205fb9360fcfbae619d4e499e8; hash ed839d34f480cba13b68ad605862c311 (pl-fp-v1:7fde48591cd1d927a614ab373f162669cba0b97b6e131cde7e1e974ee631cd57)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T05:49:14Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T05:36:17Z):
Reading of the clause "the drift t^{-1/2} e added to a system satisfying (2.3) and Assumptions
2.2-2.5 violates Assumption 2.2 and keeps Assumptions 2.3-2.5; the shift X -> X - 2 sqrt t e
returns a system satisfying Assumptions 2.2-2.5, so a solution exists" (Remark 3.4,
03-main-results.tex:180-194; (2.3) = eq:hborel, Borel measurability of h into L2(nu);
Assumptions 2.2 integ, 2.3 lip, 2.4 G, 2.5 mono).

Faithful formal statement. For every T > 0, n, m, d >= 1, standing basis, coefficient system
(b, sigma, h, f, g) (deterministic, jointly Borel, h Borel into L2(nu) as (2.3)), initial
datum xi_0, coupling matrix G and constants L, alpha, beta_1, beta_2 such that Assumptions
2.2-2.5 hold; and every fixed nonzero direction e in R^n (the paper writes the scalar drift
t^{-1/2}; in R^n it must be t^{-1/2} times a fixed nonzero vector; restricting e to unit vectors
or a basis vector is a harmless normalisation only if every nonzero direction is reachable by
scaling, otherwise a minor narrowing): with b'(t,theta,mu) := b(t,theta,mu) + t^{-1/2} e,
 (1) the system (b', sigma, h, f, g, xi_0) fails Assumption 2.2 (its origin value
     b'(.,0,delta_0) is not in L2(0,T;R^n));
 (2) it satisfies Assumptions 2.3, 2.4, 2.5 (with the same L, G, alpha, beta_1, beta_2);
 (3) the shifted system -- state shifted by s_t := (2 sqrt t e, 0, 0, 0), law argument
     translated by the same vector: b~(t,theta,mu) := b(t, theta + s_t, (. + s_t)_# mu)
     (= b'(t, theta + s_t, (.+s_t)_# mu) - t^{-1/2} e), likewise sigma~, h~, f~ with
     (theta + s_t, (.+s_t)_# mu), and g~(x,rho) := g(x + 2 sqrt T e, (. + 2 sqrt T e)_# rho),
     same xi_0 -- satisfies (2.3) and Assumptions 2.2-2.5;
 (4) the system (b', sigma, h, f, g, xi_0) has a solution in S (the paper's solution notion; its
     drift integrand is pathwise integrable but not square-integrable in time).
Quantifier order: the system and its constants first, then e, then the conclusions. Things that
would make it narrower: extra hypotheses on the system beyond (2.3)+2.2-2.5 (e.g. a margin,
m = n, specific coefficients), e restricted; broader: dropping 2.2 for the original system is
not possible (needed). Mismatched: shift with the wrong sign/constant (it must be 2 sqrt t,
the antiderivative of t^{-1/2}), translating the law argument not at all, or concluding
existence for the shifted system only and not for the system with the singular drift. The
hypotheses must be satisfiable (witness: e.g. Example 5.1(i), n = 1, e = 1). Check also that the
Lean solution notion admits a drift in L1 but not L2 in time (otherwise (4) is not the paper's
claim), and that (1) is not driven by a junk value at t = 0.
Comparison (verdict recorded 2026-10-19T05:48:15Z):
Comparison: Dissertation.PaperSpec.A.rem_uniq_translation (PaperSpec/A/Sec3Rem34.lean:96-135) against
my reading.

Hypotheses (Lean): standing basis (LevyDriver, 𝒢₀ independent, enlJoint), n, m, d >= 1, T > 0,
constants L, α, β₁, β₂, G, coefficients C, ξ₀, a direction e ≠ 0 in R^n, and JointBorel T C
((2.3)), Assumption22 C ξ₀, Assumption23 C L, G.rank = min m n (Assumption 2.4: full rank),
Assumption25 C G α β₁ β₂. These are exactly "(2.3) and Assumptions 2.2-2.5" in the printed form
(Spec/Assumptions.lean), with every nonzero direction e (my reading's preferred general form; no
unit-vector restriction). No extra hypothesis.

Conclusions (Lean), with C⁺ = C.addDrift (t ↦ (√t)⁻¹ e), i.e. b⁺ = b + t^{-1/2} e (0 at t ≤ 0, a
single null time in [0,T]), and C̃ = translatedCoeffs C (t ↦ 2√t e) T:
 (1) ∀ ξ, ¬ Assumption22 C⁺ ξ: C⁺ violates Assumption 2.2, for every initial datum, through the
     origin value (L2 taken over (0,T), so genuine). My (1). ✓
 (2) JointBorel C⁺, Assumption23 C⁺ with the same L, Assumption25 C⁺ with the same G, α, β₁, β₂
     (2.4 concerns G only and is unchanged). My (2). ✓
 (3) JointBorel C̃, Assumption22 C̃ ξ₀, Assumption23 C̃ L, Assumption25 C̃ G α β₁ β₂, where
     ψ̃(t,θ,μ) = ψ(t, θ + (2√t e,0,0,0), (· + (2√t e,0,0,0))_# μ) for ψ ∈ {b,σ,h,f} and
     g̃(x,ρ) = g(x + 2√T e, (· + 2√T e)_# ρ) (translateTuple shifts only the forward coordinate;
     lawP2 μ.law (translateTuple r_t) is the image law). That is exactly the paper's shifted
     system: the state shifted by 2√t e, the law argument translated accordingly, built from the
     original b (= b⁺ evaluated at the shifted point minus t^{-1/2} e). My (3). ✓
 (4) ∃ Θ = (X,Y,Z,U): Solution of C̃ from ξ₀, and (X + 2√t e, Y, Z, U) a Solution of C⁺ from
     ξ₀. So a solution of the system with the singular drift exists in S (in the reviewed
     Solution notion, which admits a drift that is integrable but not square-integrable in
     time), related to the shifted one by X ↦ X - 2√t e. My (4), with the correspondence made
     explicit. ✓
Quantifier order: system and constants, then e, then conclusions. ✓
Shift sign and constant: 2√t, the antiderivative of t^{-1/2}; X(C⁺) - 2√t e = X(C̃). ✓
Hypotheses can be met: the witness thm_cwp_hypotheses exhibits Example 5.1(i) (β₁ = β₂ = 1) on a
genuine basis satisfying (2.3) and Assumptions 2.2-2.5, and e = 1 ≠ 0 at n = 1.
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-19T05:48:52Z): The recorded review says "broader", and it points to a report filed under rem_uniq_initial. I record "faithful". Its hypotheses are exactly the standing setting, (2.3) and Assumptions 2.2-2.5, with a nonzero direction e. Its conclusions are the printed ones: Assumption 2.2 is violated and Assumptions 2.3-2.5 are kept; the shifted system satisfies (2.3) and 2.2-2.5; a solution exists. They add the explicit correspondence X ↦ X + 2√t e. The paper writes a scalar drift t^{-1/2} in R^n, which can only mean t^{-1/2} times a fixed vector, so quantifying over every nonzero e is the faithful general reading. Under a narrower reading of the paper (n = 1, or e fixed), the proposition is broader, with instance e = 1. Either way the verdict is in the "matches" group; no hypothesis is added and no case is lost.
