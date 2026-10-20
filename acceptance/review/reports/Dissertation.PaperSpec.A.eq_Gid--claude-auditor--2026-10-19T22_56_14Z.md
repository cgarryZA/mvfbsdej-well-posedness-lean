### A:eq:Gid: Dissertation.PaperSpec.A.eq_Gid
Pins: manuscript A None; project 6d403c197bfb10fe8808933c6e525ee0ae544fb1; hash ed839d34f480cba187a9b1634afe69c9 (pl-fp-v1:64566f0c7d4ee2abd8b2ace51e8dd3c5b880f8d31ae2680e8d78e2ccccf06870)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T22:56:14Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T22:47:21Z):
# Reading: spec eq_Gid ((4.19), expected G-energy identity, Step 1 of the proof of Lemma 4.3)

Paper: section 4, proof of Lemma 4.3, Step 1. Ito's product formula for <G dX_t, dY_t> gives the
pathwise identity (4.17); the five stochastic-integral terms have zero mean (BDG bounds (4.18),
supremum criterion; compensation formula for the fifth); taking expectations and dropping left
limits in the dt-integrals gives (4.19):
 E<G dX_T, dY_T> - E<G dxi_0, dY_0>
   = E int_0^T [ <lambda db_t + q^b_t, G^T dY_t> + <lambda dsigma_t + q^sigma_t, G^T dZ_t>_F
                 + int_E <lambda dh_t(e) + q^h_t(e), G^T dU_t(e)> nu(de)
                 + <-lambda df_t - q^f_t, G dX_t> ] dt.
 Implicit in "=" between expectations: the three expectations exist (E<G dX_T,dY_T> and
 E<G dxi_0,dY_0> are finite since dX, dY in S^2 and dxi_0 = dX_0; the dt-integrand is in
 L^1(dP x dt) by Cauchy-Schwarz: lambda dpsi + q in L^2 by Lipschitz + Theta^1-Theta^2 in S and
 square-integrable forcings; the nu-integral by Cauchy-Schwarz in L^2(nu)).

## Common setting: proof of Lemma 4.3 (lem:pert), section 4.3

Standing setting (section 2): filtered probability space (Omega,F,(F_t),P) with usual conditions,
horizon T>0, n,m,d>=1, d-dim Brownian motion W, independent Poisson random measure N on R_+ x E,
intensity dt nu(de), nu sigma-finite on countably generated (E,E) (infinite activity allowed, no
finiteness of nu), (F_t) = usual augmentation of the filtration of W, N and an independent F_0.
Ntilde = N - dt nu. H = R^n x R^m x R^{m x d} x L^2(nu;R^m). Coefficients b, sigma, h, f, g
deterministic, jointly Borel, with the signatures of section 2 (h valued in L^2(nu;R^n), Borel as
a map into L^2(nu;R^n)); g : R^n x P_2(R^n) -> R^m. Law flows mu_t, mu_t^- are the Borel
representatives of Lemma A.1 (agree with Law(Theta_t), Law(Theta_t^-) for a.e. t).

Hypotheses in force at this point of the proof (statement of Lemma 4.3):
 * Assumptions 2.5 (Lipschitz along diagonal, constant L, plus terminal Lipschitz (2.6)),
   2.6 (G full rank), 2.7 (terminal and interior G-monotonicity with alpha,beta1,beta2 and the
   sign conditions). NOT Assumption 2.4 (origin integrability), NOT xi_0 in L^2 a priori.
 * lambda_ in (0,1], lambda in [lambda_,1] (so lambda>0).
 * Theta^k = (X^k,Y^k,Z^k,U^k), k=1,2, solve the forced system (4.1) at parameter lambda, with
   F_0-measurable initial data xi_0^k and forcings q^k = (q^{b,k}, q^{sigma,k}, q^{h,k}, q^{f,k},
   q^{g,k}_T): q^b, q^sigma, q^f progressively measurable and in L^2(Omega x [0,T]); q^h
   predictable (P x E measurable) and in L^2(dP dt nu); q^g_T in L^2(Omega,F_T;R^m).
 * X^k, Y^k cadlag adapted with E int_0^T (|X^k|^2+|Y^k|^2) dt < infinity, X^k_T in
   L^2(Omega,F_T), Z^k in H^2_W (predictable, E int |Z|_F^2 < inf), U^k in H^2_N (predictable
   L^2(nu)-valued, E int ||U||^2 < inf).
 * Theta^1 - Theta^2 in S (E sup |dX|^2 + E sup |dY|^2 + E int (|dZ|^2+||dU||^2) < inf).
 "Solve (4.1)" means: both identities of (4.1) hold a.s. for every t in [0,T] (the paper's notion
 of solution, section 3), with h evaluated at the predictable tuple (Theta_s^-, mu_s^-); the
 integrals must exist (paper's stochastic integrals are the L^2 Ito / compensated Poisson ones
 of predictable square-integrable integrands, read through P x E-representatives (2.4)). A Lean
 solution concept requiring each coefficient process along each Theta^k to be square-integrable
 is a strengthening for the drift terms b, f (the paper's Remark 3.4 discusses drift not in L^2
 when Assumption 2.4 is dropped), but for sigma, h existence of the stochastic integral already
 forces it; flag if present.
 Notation: delta = (.)^1 - (.)^2, q := delta q (difference of forcings), dpsi_t =
 psi(t,Theta^1_t,mu^1_t) - psi(t,Theta^2_t,mu^2_t) for psi in {b,sigma,f}; dh_t at predictable
 tuples (Theta^{k,-}_t, mu^{k,-}_t); dg_T = g(X^1_T,Law(X^1_T)) - g(X^2_T,Law(X^2_T)).
 A statement may drop hypotheses that the step does not use (then it is broader; the printed
 instance is recovered by adding them). It must not add hypotheses the paper does not have at
 this point (e.g. Assumption 2.4, finite nu, L^2 initial data beyond what follows, continuity).

## What a faithful formal statement must contain
 * Setting/hypotheses of Lemma 4.3 above. Used here: the two solutions of (4.1) at lambda with
   their regularity, Theta^1 - Theta^2 in S, square-integrable forcings, Assumption 2.5 (to make
   lambda dsigma + q^sigma, lambda dh + q^h square-integrable, needed for zero means and for the
   integrability of the right side). G need only be a matrix here (full rank, monotonicity unused
   -> may be dropped, broader).
 * Conclusion: the identity of real numbers above, where E denotes genuine expectations
   (integrability of the three integrands must be part of the conclusion or derivable, since
   otherwise Lean's junk value 0 makes "=" a different statement), G^T acting on dY, dZ (on the
   left of R^{m x d}), pointwise on dU(e); <.,.>_F Frobenius; dh at the predictable tuples, db,
   dsigma, df at (Theta^k_t, mu^k_t); dxi_0 = xi_0^1 - xi_0^2; dY_0 the time-0 value. Using dY_t,
   dX_t (not left limits) inside the dt-integral is the paper's convention (equal dt x dP-a.e.).
 * The nu-integral of the pairing must be the L^2(nu) inner product <lambda dh_t + q^h_t,
   G^T dU_t>_{L^2(nu)} (any representative), integrated in t then expectation (or the joint
   integral over Omega x [0,T]; equal by Fubini given integrability).
 * Must hold with arbitrary sigma-finite nu (no finiteness of nu), arbitrary F_0.
 * Non-vacuity: needs an intended instance of two solutions of the forced system.
Comparison (verdict recorded 2026-10-19T22:54:01Z):
# Comparison: spec eq_Gid (Dissertation/PaperSpec/A/Sec4Difference.lean:211-282)

Note on the revision: rv.py prints "revision f598204"; claims.json and the Lean say 1f67672; I read
the vendored manuscript/paper/.

Hypotheses: the same binder list as eq_dX/eq_dY — exactly the hypotheses of Lemma 4.3 and the
standing ones (see shared notes). In particular Assumption 2.3 (needed for the integrability of the
right side) is present, Assumption 2.2 is absent as in Lemma 4.3.

## Shared findings on the Lemma 4.3 setting in the Lean (Sec4Difference.lean; Setting.lean)

(My reading used the wrong assumption numbers 2.5/2.6/2.7; the paper's numbering is
Assumption 2.2 integrability, 2.3 Lipschitz, 2.4 coupling matrix G, 2.5 monotonicity; (2.3) is
the joint Borel measurability display. The content is the same.)

Hypotheses common to the six Lemma 4.3 units, item by item:
* Standing setting: Ω, 𝒢₀ ≤ mΩ independent of ⨆_t D.filtration t, E countably generated, ν
  σ-finite (no finiteness), P probability, D : LevyDriver P d ν, filtration enlJoint 𝒢₀ D h𝒢₀
  (usual augmentation of ℱ^{W,N}_t ⊔ 𝒢₀); 0 < n, 0 < m, 0 < d, T > 0. Matches §2.
* JointBorel T C: the joint Borel measurability (2.3) on [0,T] × H × P₂(H) (W₂-Borel), h into
  L²(ν;ℝⁿ), g on ℝⁿ × P₂(ℝⁿ). Standing in §2. OK.
* Assumption23 L C (L ≥ 0, interior diagonal Lipschitz with the Hilbert-norm W₂ for a.e. t,
  terminal (2.6) for ℱ_T-measurable L² X_T); G.rank = min m n (full rank, Assumption 2.4 — c_G is
  then a definition); Assumption25 G α β₁ β₂ C (terminal monotonicity with integrability,
  interior (2.7) for a.e. t via Mono27At, Constants: α,β₁,β₂ ≥ 0, α+β₁>0, β₁+β₂>0, m<n ⇒ β₁>0,
  n<m ⇒ α,β₂>0). Assumption 2.2 is NOT assumed — matches Lemma 4.3.
* 0 < λ̲ ≤ 1, λ̲ ≤ λ ≤ 1. Matches.
* ξ₁, ξ₂ measurable for enlJoint at time 0 (ℱ₀-measurable), no integrability. Matches.
* PredForcing for q¹, q²: q^b, q^σ, q^f jointly and progressively measurable, finite energy on
  [0,T], vanishing off [0,T]; q^h jointly measurable, marked progressive and marked predictable
  (𝒫⊗ℰ), finite marked energy, vanishing off [0,T]; q^g strongly ℱ_T-measurable and L². Matches the
  forcing class of §4 (zero extension off [0,T] is a normalisation).
* WeakForcedSolution (k = 1, 2): ∃ γ representing h(s, Θ⁻_s, ·, Law Θ⁻_s) in L²(ν) for a.e. s,
  a.s. (jump_rep); PaperWeakTuple (X, Y adapted on [0,T], every path right-continuous on [0,T),
  left limits (WeakForcedSolution adds: for every ω) on (0,T], finite energy; Z predictable, U
  marked predictable, finite energies, vanishing off [0,T]); forcing; the forced drift/driver
  integrands jointly + progressively measurable with a.s. integrable paths on [0,T] (NOT L² —
  correct without Assumption 2.2); forced diffusion/jump integrands measurable with finite energy
  (existence of the L² stochastic integrals; for these, given Lipschitz and Θ ∈ ℍ_weak, finite
  energy is forced by the mere existence of the integral, so no narrowing); X_T ∈ L²; forward and
  backward identities of (4.1) a.s. simultaneously for all t ∈ [0,T], with a càdlàg version of the
  Brownian integral, the Poisson integral the library's càdlàg L² Itô–Lévy integral, the terminal
  value g(X_T, Law X_T) (true law), the coefficient processes evaluated at (Θ_s(ω), Law(Θ_s)) via
  driftProc/diffusionProc/driverProc, cut to [0,T].
  This is the paper's "Θ^k solves (4.1) with X^k,Y^k càdlàg adapted, E∫(|X|²+|Y|²)<∞,
  X_T ∈ L², Z ∈ H²_W, U ∈ H²_N".
* supSize(δΘ) < ⊤: E sup_{[0,T]}|δX|² + E sup|δY|² + Σ energies of δZ, δU < ∞, i.e.
  Θ¹ − Θ² ∈ ℍ. Matches.
* Laws: the Lean evaluates coefficients at the true law lawP2 P Θ_s at every s, where the paper uses
  the Borel representative μ_s of Lemma A.1; they agree for a.e. s (where Θ_s ∈ L²), and the
  coefficient processes only enter dt-, dW- and Ñ-integrals and dt-a.e. statements, so this is
  harmless (Lemma A.1, Step 3).
* Witness lem_pert_two_data_hypotheses: n = m = d = 1, ν = δ₀ on ℝ, T = 1, Example 5.1(i) affine
  system with β = 1 (JointBorel, Assumptions 2.3–2.5 with L = 1, α = β₁ = β₂ = 1, G = 1),
  λ̲ = λ = 1, zero forcings, data 0 and e₁, the two solutions given by Theorem 3.5 (thm_cwp),
  difference in ℍ via Theorem 3.1. A genuine instance with distinct solutions; the hypotheses can
  be met, the statements are not vacuous. It exercises neither nonzero forcings, λ < 1, nor
  infinite activity, which a witness need not do.

## The conclusion of eq_Gid against (4.19)
* Integrable (ω ↦ ⟨G δX_T, δY_T⟩) — via (G *ᵥ δX_T) ⬝ᵥ δY_T. OK.
* Integrable (ω ↦ ⟨G δξ₀, δY_0⟩) — via (G *ᵥ (ξ¹ − ξ²)) ⬝ᵥ δY_0. OK.
* Integrable on P ⊗ Leb|[0,T] of the integrand
  (λδb + q^b)·(Gᵀ δY_s) + Σ_j (λδσ + q^σ)_{·j}·(Gᵀ δZ_{·j,s}) + ∫_E (λδh(e) + q^h(e))·(Gᵀ δU_s(e)) ν(de)
  + (−λδf − q^f)·(G δX_s):
  - drift and driver at (Θ^k_s, Law Θ^k_s) (driftProc/driverProc), q = δq;
  - Σ_j over columns = the Frobenius pairing ⟨A, Gᵀ B⟩_F (Gᵀ acts on each column of δZ ∈ ℝ^{m×d});
  - δh at the predictable tuples via coeffJump(leftLimProc X^k, leftLimProc Y^k, Z^k, U^k), cut to
    [0,T]; the ν-integral is a Bochner integral, the integrand e ↦ … being ν-integrable for a.e.
    (ω,s) (lpRep gives an L²(ν) function at every (ω,s); q^h and δU are L²(ν) for a.e. (ω,s)), so the
    junk value can only occur on a dP⊗ds-null set, which does not affect the outer integral;
  - δY_s, δX_s (not left limits) in the drift multipliers — exactly as printed in (4.19) (the paper
    drops the left limits by its dt-integral convention).
  This is "the three expectations existing" (the third as a joint integral on Ω × [0,T]).
* Equality E⟨GδX_T,δY_T⟩ − E⟨Gδξ₀,δY_0⟩ = ∫_Ω ∫_{[0,T]} (integrand) ds dP — the iterated form of
  E∫_0^T[...]dt; with the asserted joint integrability it equals the joint integral (Fubini). OK.
* G is the m×n matrix acting by *ᵥ; Gᵀ by *ᵥ on ℝ^m vectors — same as the paper.
* The identity concerns genuine expectations (all integrands asserted integrable), so no junk value
  enters the equality.

## Hypotheses vs. those in force at (4.19)
Exactly those of Lemma 4.3 plus the standing ones; none added, none dropped (full rank and
Assumption 2.5 in force though unused at this step).

Verdict: faithful with representation choices.

## Coverage (claim A:eq:Gid, after show)
A:eq:Gid has a single clause (this unit). Its region is the display (4.19). The clause states the
identity and the existence of the three expectations (needed for the identity to be meaningful,
and established in the paper just before by the BDG/zero-mean argument and Cauchy–Schwarz). It
states nothing the passage does not claim. The surrounding Step-1 assertions — the pathwise
identity (4.17), the BDG bounds (4.18), "all five terms have zero expectation" — are other claims of
the inventory or proof steps outside this region; the clause does not need to state them. The
hypotheses are exactly those in force at that point of the proof of Lemma 4.3.
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless:
1. Pairings in coordinates: ⟨Gx, y⟩ as (G *ᵥ x) ⬝ᵥ y; the Frobenius pairing ⟨A, Gᵀ B⟩_F as the sum
   over the d columns of the dot products with Gᵀ applied to each column.
2. "E∫_0^T [...] dt" as the iterated integral ∫_Ω ∫_{[0,T]} with the integrand asserted integrable on
   Ω × [0,T] (P ⊗ Leb restricted to [0,T]); the iterated and joint integrals coincide.
3. δh at the predictable tuples through the canonical jointly measurable representative coeffJump,
   cut to [0,T]; the inner ν-integral is a Bochner integral whose integrand is ν-integrable for
   dP⊗ds-a.e. (ω,s), so its junk value is confined to a null set.
4. Coefficient processes at the true law Law(Θ^k_s) instead of the Borel law-flow representative
   (equal for a.e. s); processes and forcings extended by 0 off [0,T]; q = δq written as differences.
5. Solution notion and forcing class as for eq_dX (shared notes).
Disagreements with the author's review (shown 2026-10-19T22:56:09Z): Substantive disagreement: none. The author's reading (coordinate pairings, Frobenius as a sum over
columns with Gᵀ column-wise, Bochner expectations with the integrability of the two pairings and of
the integrand on Ω × [0,T] stated, E∫_0^T as the iterated integral, δh at the predictable tuples via
coeffJump, (4.17)/(4.18) left to their own claims) matches mine.

Minor difference of verdict label: the author records "faithful"; I record "faithful with
representation choices" (coordinates, iterated integral, canonical representative of δh with a
ν-integral that is junk only on a dP⊗ds-null set, true laws at every s instead of the Borel law-flow
representatives); all harmless.
Also noted: rv.py labels the paper revision f598204 while claims.json and the Lean say 1f67672.
