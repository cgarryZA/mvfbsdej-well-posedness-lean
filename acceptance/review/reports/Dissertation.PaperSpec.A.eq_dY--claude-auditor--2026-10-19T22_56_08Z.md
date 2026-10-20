### A:eq:dY: Dissertation.PaperSpec.A.eq_dY
Pins: manuscript A None; project 6d403c197bfb10fe8808933c6e525ee0ae544fb1; hash ed839d34f480cba1cc37dd9a0d2b35ad (pl-fp-v1:4262354b615f8d58d13f35be27f298bee36ad283ce203e0b749342a59c21b06d)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T22:56:08Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T22:47:07Z):
# Reading: spec eq_dY ((4.16), backward difference equation in the proof of Lemma 4.3)

Paper: section 4, proof of Lemma 4.3, display (4.16):
 d dY_t = -(lambda df_t + q^f_t) dt + dZ_t dW_t + int_E dU_t(e) Ntilde(dt,de),
 dY_T = lambda dg_T + q^g_T,
 i.e. in integrated (backward) form, a.s. for every t in [0,T],
 dY_t = lambda dg_T + q^g_T + int_t^T (lambda df_s + q^f_s) ds - int_t^T dZ_s dW_s
        - int_t^T int_E dU_s(e) Ntilde(ds,de),
 and dY_T = lambda dg_T + q^g_T a.s. Here dg_T = g(X^1_T, Law(X^1_T)) - g(X^2_T, Law(X^2_T))
 (induced terminal laws), q = delta q. Difference of the two backward equations of (4.1).

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
 * Setting/hypotheses above (unused ones may be dropped -> broader).
 * Conclusion: both identities, a.s. (null set independent of t, or per t; flag which), with
   dZ = Z^1 - Z^2 integrated against W (Ito), dU = U^1 - U^2 against Ntilde (read through a
   P x E-representative), df at (Theta^k_s, mu^k_s), dg_T with the laws of X^k_T (the true laws
   Law(X^k_T), not a Borel-flow representative -- at the fixed time T the paper uses the induced
   law), lambda the parameter, q^g_T, q^f the forcing differences.
 * dY_T = lambda dg_T + q^g_T: in the paper this is the t=T instance of the backward identity
   (integrals over [T,T] vanish); stating it separately is fine.
 * Non-vacuity as for (4.15).
Comparison (verdict recorded 2026-10-19T22:53:20Z):
# Comparison: spec eq_dY (Dissertation/PaperSpec/A/Sec4Difference.lean:144-209)

Note on the revision: rv.py prints "revision f598204"; claims.json and the Lean say 1f67672; I read
the vendored manuscript/paper/.

Hypotheses: literally the same binder list as eq_dX (see the shared notes below), i.e. exactly
the hypotheses of Lemma 4.3 plus the standing ones.

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

## The conclusion of eq_dY against (4.16)
For every coordinate k of the backward component:
* ∀ᵐ ω, s ↦ λ(driverProc¹ − driverProc²)_k + (q^{f,1} − q^{f,2})_k is integrable on [0,T]
  (existence of the ds-integral; the Bochner ∫ over Icc t T cannot be junk).
* ∀ᵐ ω, δY_{k,T} = λ(g(X¹_T, Law X¹_T) − g(X²_T, Law X²_T))_k + (q^{g,1} − q^{g,2})_k: the terminal
  condition δY_T = λ δg_T + q^g_T with the induced (true) terminal laws, as in §2's δg_T. OK.
* ∃ the measurability / progressive measurability / finite global energy of each column of
  δZ_k = Z¹_k − Z²_k and the joint measurability / marked progressive measurability / finite marked
  energy of δU_k (the conditions of the library's L² integrals), and
* ∀ t ∈ [0,T], ∀ᵐ ω: δY_{k,t} = λ δg_{T,k} + q^g_{T,k} + ∫_{[t,T]} (λ δf + q^f)_k ds
  − (∫_0^T − ∫_0^t) δZ_k dW − (∫_0^T − ∫_0^t)∫_E δU_k Ñ(ds,de),
  i.e. the integrated backward form of (4.16) with ∫_t^T = ∫_0^T − ∫_0^t, df at (Θ^k_s, Law Θ^k_s),
  q = δq. OK. The per-t null set: as for eq_dX (the paper's own "almost surely for every t").
* δU is integrated directly (no coefficient representative is needed: U^k are marked predictable
  processes). OK.

## Hypotheses vs. those in force at (4.16)
Exactly those of Lemma 4.3 and the standing ones; none added, none dropped (Assumptions 2.4, 2.5
in force though unused by this step).

Verdict: faithful with representation choices.

## Coverage (claim A:eq:dY, after show)
A:eq:dY has a single clause (this unit) covering (4.16) in full: the backward differential equation
and the terminal value δY_T = λ δg_T + q^g_T, in integrated form, with the existence of the
integrals (implicit in the printed display). The other display of the shared region, (4.15), is
claim A:eq:dX. No clause states something the passage does not claim; the hypotheses are exactly
those in force at that point of the proof of Lemma 4.3.
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless:
1. Coordinatewise statement (each k; the Brownian integral as Σ_j of 1-D integrals of the (k,j)
   entries of δZ).
2. "Almost surely at every t" as ∀ t ∈ [0,T], ∀ᵐ ω (the paper's own phrasing of its solution
   notion; equivalent with càdlàg versions); the terminal identity stated a.s. separately.
3. ∫_t^T of the stochastic integrals written as the difference of the library integrals at T and t;
   ∫_t^T ds as the Bochner integral over [t,T] with the a.s. path integrability asserted.
4. Coefficient processes at the true law Law(Θ_s) rather than the Borel law-flow representative (equal
   for a.e. s; only time-integrated quantities enter); terminal function at the true law Law(X_T),
   which is the paper's induced law.
5. Processes and forcings extended by 0 off [0,T]; solution notion as for eq_dX (the integrals of
   (4.1) must exist; drift/driver only pathwise integrable, as Lemma 4.3 without Assumption 2.2
   requires).
Disagreements with the author's review (shown 2026-10-19T22:56:03Z): Substantive disagreement: none. The author's review (shared with eq_dX) reads (4.16) as the
integrated backward identity from T, per t almost surely, with ∫_t^T of the stochastic integrals as
the difference of the library integrals at T and t, the driver pathwise integrable, and
δY_T = λ δg_T + q^g_T stated separately with the true terminal laws — the same reading as mine.

Minor difference of verdict label: the author records "faithful"; I record "faithful with
representation choices" (coordinatewise statement, per-t null set, ∫_t^T written as a difference,
coefficient laws as the true laws at every s rather than the Borel law-flow representative, zero
extension off [0,T]); all harmless.
Also noted: rv.py labels the paper revision f598204 while claims.json and the Lean say 1f67672.
