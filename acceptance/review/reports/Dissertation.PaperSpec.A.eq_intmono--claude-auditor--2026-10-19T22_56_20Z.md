### A:eq:intmono: Dissertation.PaperSpec.A.eq_intmono
Pins: manuscript A None; project 6d403c197bfb10fe8808933c6e525ee0ae544fb1; hash ed839d34f480cba14dbfddebc754cdd1 (pl-fp-v1:bd085372b14f8235abb19c17731ea25b112c46f5e35eaf09e1b97d41790ce7e4)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T22:56:20Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T22:47:31Z):
# Reading: spec eq_intmono ((4.20), insertion of interior monotonicity, Step 2 of Lemma 4.3)

Paper: section 4, proof of Lemma 4.3, Step 2. dh_t is evaluated at the predictable tuples, which
agree with (Theta^k_t, mu^k_t) for dt-a.e. t (Lemma A.1). Assumption 2.7 (interior inequality
(2.7)), applied at the diagonal input pair (Theta^1_t, mu^1_t), (Theta^2_t, mu^2_t) (diagonal for
a.e. t: Theta^k_t in L^2(Omega,F_t;H) for a.e. t by Fubini, mu^k_t the Borel law flow), times
lambda >= 0, gives for a.e. t:
 lambda E[ <db_t, G^T dY_t> + <dsigma_t, G^T dZ_t>_F + int_E <dh_t(e), G^T dU_t(e)> nu(de)
           + <-df_t, G dX_t> ]
   <= -lambda beta1 E[ |G^T dY_t|^2 + |G^T dZ_t|_F^2 + ||G^T dU_t||^2 ] - lambda beta2 E|G dX_t|^2.
 The left expectation exists (integrable integrand at a.e. t: dpsi_t in L^2 by Lipschitz,
 dTheta_t in L^2 for a.e. t).

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
 * Setting/hypotheses of Lemma 4.3. Used: Assumption 2.7 interior part with beta1, beta2 (for a.e.
   t and all diagonal pairs at t), lambda >= 0 (from lambda in [lambda_,1]), the solutions'
   regularity (so that Theta^k_t is a diagonal input for a.e. t), Lemma A.1 (predictable tuples vs
   tuples), Lipschitz for integrability.
 * Conclusion: for a.e. t in [0,T] (Lebesgue), the inequality above, with dh_t at the predictable
   tuples (Theta^{k,-}_t, mu^{k,-}_t) -- hence the step genuinely uses dh_t^- = dh_t a.e. -- and
   the left expectation existing (integrability as part of the conclusion, or derivable).
   Quantifier: "for a.e. t" outside, constants beta1,beta2,lambda fixed before.
 * The law argument must be the law flow (Borel representative mu^k_t = Law(Theta^k_t) a.e. t,
   mu^{k,-}_t for h); the diagonal input must be over the standing basis with F_t-measurability.
 * Non-vacuity: needs an intended instance satisfying Assumption 2.7 together with two solutions
   of (4.1).
Comparison (verdict recorded 2026-10-19T22:54:32Z):
# Comparison: spec eq_intmono (Dissertation/PaperSpec/A/Sec4Difference.lean:284-357)

Note on the revision: rv.py prints "revision f598204"; claims.json and the Lean say 1f67672; I read
the vendored manuscript/paper/.

Hypotheses: the same binder list as eq_dX — exactly those of Lemma 4.3 and the standing ones (see
shared notes); Assumption 2.5 (with β₁, β₂) is present and is what this step uses; λ ≥ λ̲ > 0.

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

## The conclusion of eq_intmono against (4.20)
∀ᵐ t ∈ [0,T] (Lebesgue on Icc 0 T):
* Integrable in ω of ⟨δb_t, Gᵀ δY_t⟩ + ⟨δσ_t, Gᵀ δZ_t⟩_F + ∫_E ⟨δh_t(e), Gᵀ δU_t(e)⟩ ν(de)
  + ⟨−δf_t, G δX_t⟩, where
  - δb_t, δσ_t, δf_t = ψ(t, Θ¹_t(ω), Law Θ¹_t) − ψ(t, Θ²_t(ω), Law Θ²_t), Θ^k_t = tupleAt (X, Y, the
    m×d matrix of Z, the L²(ν) class of U_t(ω,·));
  - δh_t = h(t, Θ^{1,−}_t(ω), Law Θ^{1,−}_t) − h(t, Θ^{2,−}_t(ω), Law Θ^{2,−}_t) — at the predictable
    tuples (left limits of X, Y; Z, U unchanged), as printed ("δh at the predictable tuples");
  - Gᵀ via GX Gᵀ / GZ Gᵀ (column-wise) / mark-wise inside the ν-integral; G δX via GX G.
  This is "the expectation on the left existing". OK.
* λ · E[pairing] ≤ −λβ₁ E[|GᵀδY_t|² + |GᵀδZ_t|²_F + ‖GᵀδU_t‖²_{L²(ν)}] − λβ₂ E|GδX_t|² (‖GᵀδU‖ via
  GU Gᵀ ν, the L²(ν) norm). Exactly (4.20). OK.
* Laws: the true laws Law(Θ^k_t), Law(Θ^{k,−}_t) at the given t, where the paper uses the Borel law
  flow μ^k_t, μ^{k,−}_t; they agree for a.e. t, and the conclusion is a.e. in t, so the two
  statements are equivalent.
* Junk values: the quadratic expectations are Bochner integrals of squares of L² variables for
  a.e. t (δΘ_t ∈ L² for a.e. t since Θ¹−Θ² ∈ ℍ); the uLift junk (0 when U_t(ω,·) ∉ L²(ν)) occurs only
  on a dt⊗dP-null set. No junk value can change the a.e.-in-t statement.
* As in the paper the step genuinely contains the identification of δh at the predictable tuples
  with δh at the tuples for a.e. t (Lemma A.1): the left side uses the former, while Assumption 2.5
  is imposed at diagonal inputs (Θ^k_t, Law Θ^k_t).

## Hypotheses vs. those in force at (4.20)
Exactly those of Lemma 4.3 plus the standing ones; none added, none dropped.

Verdict: faithful with representation choices.

## Coverage (claim A:eq:intmono, after show)
A:eq:intmono has a single clause (this unit), covering the display (4.20) together with the
existence of the left expectation and the evaluation of δh at the predictable tuples; the
introductory sentence of Step 2 (agreement of predictable tuples and tuples for a.e. t; application
of Assumption 2.5 at the common input pair) is the justification, and is absorbed into the clause
as stated (left side at predictable tuples, a.e. t). Nothing beyond the passage is claimed; the
hypotheses are exactly those in force at that point of the proof of Lemma 4.3.
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless:
1. Laws at the given time are the true laws Law(Θ^k_t), Law(Θ^{k,−}_t) (lawP2) rather than the Borel
   law-flow representatives μ^k_t, μ^{k,−}_t of Lemma A.1; they agree for a.e. t and the statement is
   for a.e. t.
2. The tuple Θ_t is tupleAt: coordinates of X, Y, the m×d matrix of Z and the L²(ν) class (uLift) of
   U_t(ω,·), with the junk class 0 when U_t(ω,·) ∉ L²(ν), which happens only on a dt⊗dP-null set.
3. Gᵀ on δZ column-wise (Kronecker Gᵀ⊗I_d), on δU mark-wise; ‖GᵀδU‖ as the L²(ν) norm of GU Gᵀ ν δU.
4. "The expectation on the left existing" is the integrability of the pairing in ω at a.e. t.
5. Solution notion and forcing class as for eq_dX (shared notes).
Disagreements with the author's review (shown 2026-10-19T22:56:14Z): Substantive disagreement: none. The author's reading (a.e. t; integrability of the pairing stated;
the integrand of (2.7) with h at the predictable tuples; laws as lawP2 of the tuples and of the
predictable tuples rather than fixed Borel versions, equal for a.e. t; right side as in Mono27At,
times λ) is the one I reached independently.

Minor difference of verdict label: the author records "faithful"; I record "faithful with
representation choices" (true laws instead of the Borel law flow; tupleAt with the junk L²(ν)
class 0 only on a dt⊗dP-null set; Gᵀ column-wise on δZ and mark-wise on δU); all harmless.
Also noted: rv.py labels the paper revision f598204 while claims.json and the Lean say 1f67672.
