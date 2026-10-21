### A:eq:coerc: Dissertation.PaperSpec.A.eq_coerc
Pins: manuscript A None; project 6d403c197bfb10fe8808933c6e525ee0ae544fb1; hash ed839d34f480cba1763b5cdd464a968d (pl-fp-v1:f806d1b2ace4d3a924ad457e49ebf8b627f9add329071827b08f75f1fdf329fe)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T22:56:33Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T22:47:53Z):
# Reading: spec eq_coerc ((4.22), coercivity bound, end of Step 2 of Lemma 4.3)

Paper: section 4, proof of Lemma 4.3, Step 2. With
 P  := E|dxi_0|^2 + E|q^g_T|^2 + E int_0^T (|q^b|^2 + |q^sigma|_F^2 + ||q^h||^2 + |q^f|^2) dt,
 N' := E|dX_T|^2 + E|dY_0|^2 + E int_0^T (|dX|^2 + |dY|^2 + |dZ|_F^2 + ||dU||^2) dt,
 K  := eta N' + (||G||^2/(4 eta)) P, eta > 0,
inserting (4.20) and (4.21) in (4.19) and rearranging, then Young with |G^T v| <= ||G|| |v|,
|G v| <= ||G|| |v| gives (4.22):
 lambda alpha E|G dX_T|^2 + lambda beta2 E int_0^T |G dX_t|^2 dt
   + lambda beta1 E int_0^T [ |G^T dY|^2 + |G^T dZ|_F^2 + ||G^T dU||^2 ] dt
 <= |E<G dxi_0, dY_0>| + |E<G dX_T, q^g_T>| + E int_0^T ( |<q^b, G^T dY>| + |<q^sigma, G^T dZ>_F| ) dt
    + E int_0^T ( | int_E <q^h(e), G^T dU(e)> nu(de) | + |<q^f, G dX>| ) dt
 <= K,
for every eta > 0 (eta is free; it is chosen later in Step 5). q = delta q. P and N' are finite
(Theta^1-Theta^2 in S, dxi_0 = dX_0, forcings square-integrable); this finiteness is implicit
(K is used as a real number). ||G|| = operator norm of G.

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
 * Setting/hypotheses of Lemma 4.3 (all of Assumptions 2.5-2.7 used: Lipschitz for
   integrability, monotonicity with alpha, beta1, beta2; lambda in [lambda_,1]; the two solutions
   with their regularity and Theta^1 - Theta^2 in S).
 * Conclusion: a chain of two inequalities (the middle term being the sum of the six absolute
   pairings, in exactly that form: the q^h pairing with the absolute value outside the nu-integral),
   the second for every eta > 0 (quantifier "for all eta > 0" inside, after the solutions), plus
   finiteness of P and N' (or their being real-valued as genuine expectations; with ENNReal/
   lintegral representations finiteness must be stated, with Bochner integrals integrability of
   the integrands must hold or be stated, otherwise junk 0 changes the meaning).
 * The left side uses the coercive blocks with lambda alpha, lambda beta2, lambda beta1;
   ||G|| the operator norm (or any norm satisfying |Gv|<=||G|||v| and |G^T v|<=||G|||v| -- using a
   different/larger constant would be weaker than printed; the paper's ||G|| is the operator norm,
   with ||G^T|| = ||G||).
 * Non-vacuity: intended instance with two solutions under Assumptions 2.5-2.7.
Comparison (verdict recorded 2026-10-19T22:55:41Z):
# Comparison: spec eq_coerc (Dissertation/PaperSpec/A/Sec4Difference.lean:408-494)

Note on the revision: rv.py prints "revision f598204"; claims.json and the Lean say 1f67672; I read
the vendored manuscript/paper/.

Hypotheses: the same binder list as eq_dX — exactly those of Lemma 4.3 and the standing ones (see
shared notes); α, β₁, β₂ are the constants of Assumption 2.5 (with Constants: all ≥ 0).

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

## The conclusion of eq_coerc against (4.22)
* N' ≠ ⊤, with N' = ∫⁻ |δX_T|² + ∫⁻ |δY_0|² + Σ_i energy(δX_i) + Σ_k energy(δY_k) + Σ_{k,j}
  energy(δZ_{kj}) + Σ_k markedEnergy(δU_k) on [0,T] = E|δX_T|² + E|δY_0|² + E∫_0^T(|δX|²+|δY|²+|δZ|²_F
  +‖δU‖²_{L²(ν)})dt (esq = Σ of squared coordinates; ‖δU‖² = Σ_k ∫_E |δU_k|² dν). Exactly the
  paper's N'. OK.
* P ≠ ⊤, P = dataSize(δξ₀, δq) = E|δξ₀|² + E|q^g_T|² + Σ energies of q^b, q^σ (entries), q^h,
  q^f — the paper's P (q = δq). OK.
* First inequality: λα E|GδX_T|² + λβ₂ E∫_{[0,T]} |GδX_s|² + λβ₁ E∫_{[0,T]}(|GᵀδY|² + Σ_j|GᵀδZ_{·j}|²
  + ∫_E |GᵀδU(e)|² ν(de)) ≤ |E⟨Gδξ₀,δY_0⟩| + |E⟨GδX_T,q^g_T⟩| + E∫(|⟨q^b,GᵀδY⟩| + |⟨q^σ,GᵀδZ⟩_F|)
  + E∫(|∫_E⟨q^h(e),GᵀδU(e)⟩ν(de)| + |⟨q^f,GδX⟩|). The six pairings, with the absolute value of the
  q^h pairing outside the ν-integral and of the q^σ pairing outside the Σ_j (Frobenius), exactly as
  printed. OK.
* Second inequality: ∀ η > 0, (six pairings) ≤ η·N' + ‖GX G‖²/(4η)·P, N' and P converted with
  toReal — faithful since both are asserted finite; ‖GX G‖ is the operator norm of x ↦ Gx between
  Euclidean spaces, the paper's ‖G‖. η is quantified after the solutions and only in this
  inequality (the first does not involve η), as in the paper (η is free, fixed in Step 5). OK.
* Junk values: all integrands are genuinely integrable under the hypotheses (squares of L²
  processes; products of L² forcings with L² differences), and the inner ν-integrals are ν-integrable
  for dP⊗ds-a.e. (ω,s). A junk 0 on the left could only weaken the first inequality, and none
  occurs. Expectations of the pairings at T and 0 are Bochner integrals of integrable functions
  (δX_T, δY_0, δξ₀ = δX_0, q^g in L²).

## Hypotheses vs. those in force at (4.22)
Exactly those of Lemma 4.3 plus the standing ones; none added, none dropped. (No constant is said
to depend on parameters here; η is arbitrary, ‖G‖ is explicit.)

Verdict: faithful with representation choices.

## Coverage (claim A:eq:coerc, after show)
A:eq:coerc has a single clause (this unit). Its region is the display (4.22); the clause states
both inequalities, with K = ηN' + ‖G‖²/(4η)P and the finiteness of N' and P that the definition of K
as a real number presupposes (N' and P are defined just above, in the same step). It states nothing
the passage does not claim. The hypotheses are exactly those in force at that point of the proof of
Lemma 4.3. Remark: the next sentence, "Each coercive block present on the left of (4.22) is
therefore at most K", lies outside this claim's region and is not stated by any clause I can see; it
is an immediate consequence (each block is nonnegative since λ, α, β₁, β₂ ≥ 0), so its omission is a
minor inventory gap at most.
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless:
1. N' and P as extended-nonnegative lintegrals/energies (esq = sum of squared coordinates, energies on
   [0,T], ‖δU‖² as the sum over coordinates of ∫_E |δU_k|² dν), asserted ≠ ⊤, and used through toReal in
   K; this is the paper's N', P and K exactly.
2. Expectations of the coercive blocks and of the six pairings as iterated Bochner integrals
   ∫_Ω ∫_{[0,T]}; all integrands are integrable under the hypotheses, so no junk value enters.
3. Frobenius pairings as sums over columns with Gᵀ applied column-wise; ‖GᵀδU‖² as ∫_E |GᵀδU(e)|² ν(de).
4. ‖G‖ is ‖GX G‖, the operator norm of x ↦ Gx between Euclidean spaces (the paper's ‖G‖, = ‖Gᵀ‖).
5. Solution notion and forcing class as for eq_dX (shared notes).
Disagreements with the author's review (shown 2026-10-19T22:56:25Z): Substantive disagreement about the proposition: none. The author's reading (N' and P as
extended-nonnegative quantities asserted finite and used through toReal; ‖G‖ = ‖GX G‖, the operator
norm; the six pairings in coordinates with the absolute values placed as printed; η quantified only
in the second inequality) matches mine.

Minor differences:
1. Verdict label: the author records "faithful"; I record "faithful with representation choices"
   (lintegral/energy representation of N' and P with toReal, iterated Bochner integrals, Frobenius as
   a column sum); all harmless.
2. Coverage: the author notes that the sentence after (4.22) ("Each coercive block present on the
   left of (4.22) is therefore at most 𝒦") "is a consequence and is not stated". I agree it is an
   immediate consequence (each block is ≥ 0 because λ, α, β₁, β₂ ≥ 0), but it is a mathematical
   assertion of the printed proof, outside the region of A:eq:coerc and, as far as I can see, of
   any other claim of the inventory; it is a minor inventory gap rather than a defect of this
   proposition.
Also noted: rv.py labels the paper revision f598204 while claims.json and the Lean say 1f67672.
