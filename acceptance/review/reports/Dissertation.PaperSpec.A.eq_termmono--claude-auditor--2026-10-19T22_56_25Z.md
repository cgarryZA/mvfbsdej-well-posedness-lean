### A:eq:termmono: Dissertation.PaperSpec.A.eq_termmono
Pins: manuscript A None; project 6d403c197bfb10fe8808933c6e525ee0ae544fb1; hash ed839d34f480cba1ea261f16df305b5f (pl-fp-v1:f0e54f787457e91b59451da15a4737f07e9627df9464a515cf14166b9fd0f7f2)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T22:56:25Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T22:47:40Z):
# Reading: spec eq_termmono ((4.21), terminal monotonicity, Step 2 of Lemma 4.3)

Paper: section 4, proof of Lemma 4.3, Step 2, display (4.21):
 E<G dX_T, dY_T> = lambda E<G dX_T, dg_T> + E<G dX_T, q^g_T>
                 >= lambda alpha E|G dX_T|^2 - |E<G dX_T, q^g_T>|.
 First equality: dY_T = lambda dg_T + q^g_T a.s. ((4.16)) and linearity of E (needs
 integrability: dX_T, dY_T in L^2 since Theta^1-Theta^2 in S; dg_T in L^2 by (2.6),(2.9) since
 X^k_T in L^2; q^g_T = delta q^g_T in L^2). Inequality: terminal G-monotonicity of Assumption 2.7
 applied to X^1_T, X^2_T in L^2(Omega,F_T;R^n) (with the induced laws), multiplied by lambda >= 0,
 and x >= -|x|.

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
 * Setting/hypotheses of Lemma 4.3. Used: the backward terminal condition of (4.1) for both
   solutions, X^k_T in L^2(F_T), Theta^1-Theta^2 in S (dX_T, dY_T in L^2), q^{g,k}_T in L^2,
   terminal Lipschitz (2.6) for integrability of dg_T, terminal monotonicity with alpha, lambda>=0.
 * Conclusion: both the equality and the inequality (a chain), with dg_T = g(X^1_T,Law(X^1_T)) -
   g(X^2_T,Law(X^2_T)), q^g_T = q^{g,1}_T - q^{g,2}_T, G dX_T in R^m paired with vectors in R^m,
   and the expectations existing (integrability stated or derivable; with Lean's Bochner junk the
   equality would otherwise be a different statement).
 * Non-vacuity: intended instance with terminal monotonicity and two solutions.
Comparison (verdict recorded 2026-10-19T22:54:50Z):
# Comparison: spec eq_termmono (Dissertation/PaperSpec/A/Sec4Difference.lean:359-406)

Note on the revision: rv.py prints "revision f598204"; claims.json and the Lean say 1f67672; I read
the vendored manuscript/paper/.

Hypotheses: the same binder list as eq_dX — exactly those of Lemma 4.3 and the standing ones (see
shared notes). The terminal half of Assumption 2.5 (with α, over ℱ_T-measurable L² X_T, X'_T, with
integrability of the pairing) and the terminal Lipschitz (2.6) are present.

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

## The conclusion of eq_termmono against (4.21)
* Integrable: ⟨G δX_T, δY_T⟩, ⟨G δX_T, δg_T⟩ with δg_T = g(X¹_T, Law X¹_T) − g(X²_T, Law X²_T)
  (terminalVal, the true induced terminal laws, as in §2), and ⟨G δX_T, q^g_T⟩ with q^g = q^{g,1} −
  q^{g,2}. "The expectations existing". OK.
* E⟨GδX_T, δY_T⟩ = λ E⟨GδX_T, δg_T⟩ + E⟨GδX_T, q^g_T⟩. OK (first line of (4.21)).
* λ α E|GδX_T|² − |E⟨GδX_T, q^g_T⟩| ≤ λ E⟨GδX_T, δg_T⟩ + E⟨GδX_T, q^g_T⟩, with |GδX_T|² written as
  (GδX_T)·(GδX_T). Together with the equality this is the chain of (4.21). OK.
* Pairings in coordinates, (G *ᵥ x) ⬝ᵥ y — symmetric, so ⟨δg_T, GδX_T⟩ of Assumption 2.5 is the same
  quantity. No junk value: every integrand is asserted integrable.

## Hypotheses vs. those in force at (4.21)
Exactly those of Lemma 4.3 plus the standing ones; none added, none dropped.

Verdict: faithful with representation choices.

## Coverage (claim A:eq:termmono, after show)
A:eq:termmono has a single clause (this unit) covering the display (4.21) — the equality, the
inequality, and the existence of the expectations that the display presupposes. Nothing beyond the
passage is claimed; the hypotheses are exactly those in force at that point of the proof of
Lemma 4.3.
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless:
1. Pairings and norms in coordinates: ⟨Gx, y⟩ = (G *ᵥ x) ⬝ᵥ y and |Gx|² = (G *ᵥ x) ⬝ᵥ (G *ᵥ x).
2. The chain "= … ≥ …" is stated as the equality together with the inequality for the middle
   expression; "the expectations existing" as integrability of the three pairings.
3. δg_T uses terminalVal, i.e. g at X^k_T and the true law Law(X^k_T) (the paper's induced terminal
   law); q^g_T is the difference of the two terminal forcings.
4. Solution notion and forcing class as for eq_dX (shared notes).
Disagreements with the author's review (shown 2026-10-19T22:56:20Z): Substantive disagreement: none. The author's reading (the chain as the conjunction of the equality
and the inequality for the middle member; δg_T through terminalVal with the induced laws; q^g = δq^g;
|GδX_T|² as a dot product; integrability of the three pairings stated) is the same as mine.

Minor difference of verdict label: the author records "faithful"; I record "faithful with
representation choices" (coordinates, the chain split into two conjuncts, terminalVal for g at the
true law); all harmless.
Also noted: rv.py labels the paper revision f598204 while claims.json and the Lean say 1f67672.
