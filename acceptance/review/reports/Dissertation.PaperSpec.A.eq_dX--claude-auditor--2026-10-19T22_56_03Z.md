### A:eq:dX: Dissertation.PaperSpec.A.eq_dX
Pins: manuscript A None; project 6d403c197bfb10fe8808933c6e525ee0ae544fb1; hash ed839d34f480cba17f8ea34acd5ecf0b (pl-fp-v1:e1da92e85386b7e899dfc70abdf3b04872075b859d9b5e3349f7f96cf025caf7)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T22:56:03Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T22:46:59Z):
# Reading: spec eq_dX ((4.15), forward difference equation in the proof of Lemma 4.3)

Paper: section 4, proof of Lemma 4.3, display (4.15):
 d dX_t = (lambda db_t + q^b_t) dt + (lambda dsigma_t + q^sigma_t) dW_t
          + int_E (lambda dh_t(e) + q^h_t(e)) Ntilde(dt,de),
 with q = delta q and dX_0 = dxi_0 (used in Step 1 and Step 3), i.e. in integrated form
 dX_t = dxi_0 + int_0^t (lambda db + q^b) ds + int_0^t (lambda dsigma + q^sigma) dW
        + int_0^t int_E (lambda dh + q^h) Ntilde(ds,de),  a.s., for every t in [0,T].
 It is the difference of the two forward equations of (4.1): linearity of the Lebesgue, Ito and
 compensated Poisson integrals.

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
 * Setting and all hypotheses above (it may omit those not used: Assumptions 2.6, 2.7, Theta^1 -
   Theta^2 in S, possibly the Lipschitz assumption; omission = broader, fine).
 * Conclusion: almost surely, for every t in [0,T] (a single null set independent of t is the
   paper's notion; "for every t, a.s." is weaker -- since both sides are cadlag it is equivalent
   in the paper, but a Lean statement giving only "for every t, a.s." is acceptable only if it
   is what (4.15) as an "equation" claims; the paper's solution notion is a.s. for every t with
   the null set independent of t, so I expect either form; flag which), the identity above,
   with dxi_0 = xi_0^1 - xi_0^2, db, dsigma at (Theta^k_s, mu^k_s), dh at the predictable tuples
   (Theta^{k,-}_s, mu^{k,-}_s), q the differences of the forcings, lambda the parameter.
 * The stochastic integrals must be the paper's: Ito integral against the d-dim W of the
   R^{n x d}-valued integrand, compensated Poisson integral of the P x E-measurable
   representative of the L^2(nu;R^n)-valued integrand (independent of the representative; the
   clause name says the identity holds for every representative and one exists). Coordinatewise
   statement (each of the n coordinates) is an equivalent representation.
 * The integrals of the difference integrand must exist (they do: lambda dpsi + q is in L^2 by
   Lipschitz + Theta^1-Theta^2 in S, or simply as differences of existing integrals).
 * Non-vacuity: hypotheses (two solutions of the forced system) must be satisfiable by an
   intended instance (e.g. a witness with genuine solutions; trivial instances like lambda in
   range, zero coefficients and zero forcings/data giving zero solutions are weak but valid).
Comparison (verdict recorded 2026-10-19T22:52:54Z):
# Comparison: spec eq_dX (Dissertation/PaperSpec/A/Sec4Difference.lean:65-142)

Note on the revision: rv.py prints "revision f598204"; claims.json and the Lean say 1f67672; I read
the vendored manuscript/paper/.

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

## The conclusion of eq_dX against (4.15)
For every coordinate i:
* (drift) ∀ᵐ ω, s ↦ λ(driftProc¹ − driftProc²)_i + (q^{b,1} − q^{b,2})_i is integrable on [0,T]:
  the existence of the dt-integral of (4.15). OK (the Bochner ∫ s in Icc 0 t cannot be junk).
* (diffusion) ∃ joint measurability, progressive measurability and finite global energy of each
  column j of λ δσ + q^σ (the hypotheses of the library's L² Itô integral). OK.
* (jump) ∃ H : Ω → ℝ → E → ℝ jointly measurable, marked progressive, finite marked energy, equal
  P ⊗ Leb|[0,T] ⊗ ν-a.e. to λ(jumpProc T coeffJump¹ − jumpProc T coeffJump²)_i + (q^{h,1} − q^{h,2})_i,
  where coeffJump is evaluated along (leftLimProc X^k, leftLimProc Y^k, Z^k, U^k) — δh at the
  predictable tuples (Θ^{k,−}_s, Law Θ^{k,−}_s) through the canonical jointly measurable
  representative lpRep of the L²(ν)-valued coefficient. And for EVERY such H the identity holds.
  This is exactly "the jump integral is that of every representative of the integrand, and one
  exists".
* (identity) ∀ t ∈ [0,T], ∀ᵐ ω: δX_{i,t} = δξ₀_i + ∫_{[0,t]} (λ δb + q^b)_i ds
  + Σ_j ∫_0^t (λ δσ + q^σ)_{ij} dW^j + ∫_0^t∫_E H Ñ(ds,de), with q = δq. This is the integrated form
  of (4.15) with δX_0 = δξ₀ (which the paper uses right after). The null set may depend on t: the
  paper's own solution notion is "almost surely for every t", upgraded to a t-independent null set
  only because both sides are càdlàg; the library's Brownian integral is an L² limit with no
  chosen càdlàg version, so the per-t form is the meaningful one, and with càdlàg versions it is
  equivalent. Representation choice, harmless.
* Coordinatewise statement, (i,j) entries for σ with Σ_j against the d coordinates of W: the same
  as the vector/matrix identity.

## Hypotheses vs. those in force at (4.15)
Exactly the hypotheses of Lemma 4.3 plus the standing ones (n,m,d ≥ 1, T > 0, (2.3)); nothing
added (in particular no Assumption 2.2, no L² initial data, no finite ν), nothing dropped. The
step itself uses only the two forced equations; Assumptions 2.4/2.5 are in force but unused.

Verdict: faithful with representation choices.

## Coverage (claim A:eq:dX, after show)
A:eq:dX has a single clause (this unit); its source region is the display "The difference
equations are (4.15)–(4.16)", shared with A:eq:dY, which states (4.16). The clause states the whole
of (4.15), in integrated form with the initial value δξ₀ (implicit in "dδX_t" and used in Steps 1
and 3), the existence of the three integrals, and representative-independence of the jump
integral — all implicit in the printed display and the conventions of §2 ((2.4)). Nothing is
stated that the passage does not claim. The hypotheses are exactly those in force at that point
of the proof of Lemma 4.3 (no more, no fewer). The neighbouring prose sentence of the same
paragraph ("for a.e. t each pair (Θ^k_t, μ^k_t) is a diagonal input ...") is not part of this
claim's region; it is used inside eq_intmono.
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless:
1. Coordinatewise statement (each i; the Brownian integral as Σ_j of 1-D integrals of the (i,j)
   entries) instead of the vector/matrix form.
2. "Almost surely at every t" is stated as ∀ t ∈ [0,T], ∀ᵐ ω — the paper's own phrasing of its
   solution notion; with càdlàg versions it is equivalent to one null set (the library Brownian
   integral has no fixed càdlàg version, so the per-t form is the meaningful one).
3. Integrated form with δX_0 = δξ₀ for the differential notation of (4.15).
4. δh at the predictable tuples through the canonical jointly measurable representative coeffJump
   (lpRep of h(s, Θ⁻_s(ω), Law Θ⁻_s)), cut to [0,T]; the identity is asserted for every marked
   progressive, finite-energy H equal to it dP⊗ds⊗ν-a.e., and one such H is asserted to exist.
5. Coefficients are evaluated at the true law Law(Θ_s) (lawP2) at every s rather than at the Borel
   law-flow representative; they agree for a.e. s, and only time-integrated quantities enter.
6. Processes and forcings are extended by 0 off [0,T]; forcings carry joint measurability; the
   solution notion requires the integrals of (4.1) to exist (drift/driver pathwise integrable a.s.,
   diffusion/jump integrands of finite energy), which is the paper's tacit requirement and, for the
   stochastic integrands, no restriction given Lipschitz and Θ ∈ ℍ_weak.
Disagreements with the author's review (shown 2026-10-19T22:55:55Z): Substantive disagreement: none. The author's reading (integral form forward from 0 with
δX_0 = δξ₀, per-t almost-sure identity with the library integrals over enlJoint, δh at the
predictable tuples through coeffJump, existence of a representative and the identity for every
representative) is the one I reached independently, and the hypotheses are those of Lemma 4.3.
I also agree with the author's point that the representative formulation is needed because the
left limits at s = 0 read the paths before 0 (a null set of times).

Minor difference of verdict label: the author records "faithful"; I record "faithful with
representation choices" because several choices separate the formal text from the printed display
(coordinatewise statement; per-t null set; integrated form; coefficient laws taken as the true laws
Law(Θ_s) at every s instead of the Borel law-flow representatives of Lemma A.1, equal for a.e. s;
zero extension off [0,T]; the canonical representative coeffJump). All are harmless.
Also noted: rv.py labels the paper revision f598204 while claims.json and the Lean say 1f67672.
