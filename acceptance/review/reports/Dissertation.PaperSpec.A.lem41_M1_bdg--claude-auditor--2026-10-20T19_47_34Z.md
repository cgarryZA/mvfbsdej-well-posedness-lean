### A:lem4.1:M2-infinite-activity: Dissertation.PaperSpec.A.lem41_M1_bdg
Pins: manuscript A None; project 53a4ee4fc8767ba8884b5732431dded9772b47df; hash ed839d34f480cba1732a2bccd942e938 (pl-fp-v1:865f356065a16f8c9afa6246a5164ee35c6a868e90ddcb773a08feb34ce825ca)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-20T19:47:34Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-20T19:41:21Z):
# Reading (locked before the Lean): spec Dissertation.PaperSpec.A.lem41_M1_bdg

Claim A:lem4.1:M2-infinite-activity, region sections/04-proof-wellposedness.tex lines 139-187
(the "Zero-mean terms" paragraph of the proof of Lemma 4.1, lem:bpbsde). The clause named for this
unit is the first link of the displayed chain for M¹ (lines 161-163).

## What the paper asserts at this point

- Setting (§2): standing Brownian-Poisson basis, horizon T > 0, m ≥ 1, ν σ-finite (ν(E) = ∞
  admitted), Ñ = N − dt ν.
- Hypotheses in force (Lemma 4.1): δY càdlàg adapted ℝ^m-valued; δZ ∈ H²_W, δU ∈ H²_N
  (predictable, E∫_0^T ‖δU_s‖²_{L²(ν)} ds < ∞, read through a P⊗E-measurable representative);
  (eq:dYlin) with δξ ∈ L²(F_T), φ ∈ L²(Ω×[0,T]); and, already shown in the "Membership" part,
  δY ∈ S²(0,T;ℝ^m).
- The object: M¹_t := ∫_0^t ∫_E e^s ⟨δY_{s−}, δU_s(e)⟩ Ñ(ds,de), a real-valued càdlàg local
  martingale (the integrand is predictable and only locally square-integrable: with δY ∈ S² and
  δU ∈ H²_N the product e^{2s}|δY_{s−}|²|δU_s(e)|² need not be dP⊗ds⊗ν-integrable, so M¹ is in
  general not an L²-martingale; the paper calls the three terms "local martingales").
- The assertion (first link, "BDG, Cauchy-Schwarz"): with c_BDG the one universal BDG constant
  (valid for càdlàg local martingales, at p = 1 and p = 2),
  E sup_{t≤T} |M¹_t| ≤ c_BDG E[(∫_0^T ∫_E e^{2s} |δY_{s−}|² |δU_s(e)|² N(ds,de))^{1/2}].
  This is BDG at p = 1 with [M¹]_T = ∫∫ e^{2s}⟨δY_{s−},δU_s(e)⟩² N(ds,de), followed by the pointwise
  Cauchy-Schwarz ⟨a,b⟩² ≤ |a|²|b|² under the N-integral. Both sides are in [0, ∞]; no finiteness
  is asserted by this link (finiteness comes from the later links).

## What a faithful formal statement must contain

1. The constant c_BDG universal: chosen before the probability space, T, m, ν, E, δY, δU (a form
   "there is c₀ > 0 such that for every c_BDG ≥ c₀ ..." with c₀ quantified first is equivalent,
   since the right-hand side is nonnegative). A constant chosen after T, ν or the processes would
   be weaker than the paper's "one universal constant".
2. For every standing setting, every δY càdlàg adapted (at least those of Lemma 4.1, broader is
   acceptable), every δU ∈ H²_N, and every process M¹ that is the local compensated integral of the
   predictable integrand e^s⟨δY_{s−}, δU_s(e)⟩ on [0,T] (not only in the case where that integrand
   is in L²(dP⊗ds⊗ν): restricting to that case would lose the case the paper is in).
3. The left side: E of the supremum of |M¹_t| over all t ∈ [0,T] (ℝ≥0∞-valued or as an integral
   of a measurable sup). The right side: c_BDG times E of the square root of the pathwise integral
   of e^{2s}|δY_{s−}|²|δU_s(e)|² against the random counting measure N(ω) on (0,T]×E (value in
   [0,∞]); δY_{s−} the left limit.
4. A statement with the BDG bracket ∫∫ e^{2s}⟨δY_{s−},δU_s(e)⟩² N on the right in place of the
   product would be a different (stronger-intermediate) quantity; the printed first link has the
   product |δY_{s−}|²|δU_s(e)|².
5. Witness: an instance with δY and δU nonzero (δU nonzero on a set of positive dP⊗ds⊗ν measure,
   δY nonzero) so the right side is not 0, ideally with ν infinite or at least a genuine Poisson
   measure.
Comparison (verdict recorded 2026-10-20T19:47:19Z):
# Comparison: spec Dissertation.PaperSpec.A.lem41_M1_bdg

Lean: Dissertation/PaperSpec/A/Sec4LocalMartingales.lean (`lem41_M1_bdg`). Paper: the first link
of the displayed chain for M¹ (sections/04-proof-wellposedness.tex lines 159-163), inside claim
A:lem4.1:M2-infinite-activity (lines 139-187, the "Zero-mean terms" paragraph of the proof of
Lemma 4.1).

## Item by item against the locked reading

1. **The constant.** `∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, c₀ ≤ c → ∀ {Ω} … ν … m d … T …`: c₀ is chosen
   before the probability space, the driver, ν, E, m, d, T and all processes, i.e. it is universal,
   and the bound is asserted for every c ≥ c₀. Since the right side is in [0, ∞], this is
   equivalent to the paper's "one universal constant c_BDG" valid for càdlàg local martingales.
   Matches (item 1 of my reading).
2. **Setting.** `LevyDriver` (d-dimensional Brownian motion and an independent Poisson random
   measure with σ-finite intensity ν on a countably generated E), `𝒢₀` independent of the driver,
   filtration `enlJoint 𝒢₀ D h𝒢₀` (usual augmentation of driver filtration ⊔ 𝒢₀); m, d ≥ 1, T > 0.
   ν(E) = ∞ is admitted. Matches §2.
3. **Hypotheses of Lemma 4.1.** δZ predictable, zero off [0, T], finite energy (H²_W); δU marked
   predictable (𝒫 ⊗ ℰ-measurable), zero off [0, T], finite marked energy (H²_N); δξ
   ℱ_T-measurable and in L²; φ jointly measurable with finite energy (L²(Ω × [0, T])); δY adapted
   on [0, T], right-continuous on [0, T) and with left limits on (0, T] for every ω (càdlàg
   adapted); (4.4) at every t ∈ [0, T] almost surely, with the L² Brownian and compensated
   integrals of the library written as differences at T and t. δY ∈ S², proved in the
   "Membership" part, is implied and rightly not assumed. These are the hypotheses in force.
4. **M¹.** `∀ M1, IsLocalCompensatedIntegral D.N (enlJoint …) … T H M1 → …` with
   `H ω s e = e^s Σ_k (if 0 < s then δY^k_{s−}(ω) else 0) δU^k_s(ω, e)`, i.e.
   e^s⟨δY_{s−}, δU_s(e)⟩. `IsLocalCompensatedIntegral` asks M1 adapted on [0, T], càdlàg on
   [0, T] for every ω, and a localising sequence τ_k (stopping times, nondecreasing, a.s.
   eventually ≥ T) whose cut-offs H 1_{s ≤ τ_k} have finite energy and whose L² compensated
   integrals agree with M1 at each t ∈ [0, T] a.s. on {t ≤ τ_k}. This is the local integral, not
   only the L² case (item 2 of my reading: no case lost). Every version of the paper's M¹ is
   indistinguishable on [0, T] from any M1 of this kind (agreement at each t a.s. plus right
   continuity), so the left side does not depend on the choice.
5. **Conclusion.** Left: `∫⁻ ω, ⨆ t ∈ [0, T], ‖M1 t ω‖₊ ∂P` = E sup_{t≤T} |M¹_t|. Right:
   `ofReal c * ∫⁻ ω, (∫⁻ over (0, T] × E of e^{2s} |δY_{s−}|² |δU_s(e)|² d(N ω))^{1/2} ∂P`, the
   pathwise integral against the counting measure N(ω), with |δY_{s−}|² = Σ_k (δY^k_{s−})² and
   |δU_s(e)|² = Σ_k (δU^k_s(e))²: the product form printed after the Cauchy-Schwarz inequality in
   ℝ^m, not the bracket ⟨·,·⟩² (item 4 of my reading). Matches.
6. **Truth.** BDG at p = 1 (Davis) for the càdlàg local martingale M¹ with M¹_0 = 0 and
   [M¹]_T = ∫∫ H² dN (H predictable), followed by ⟨a, b⟩² ≤ |a|²|b|²: true, and the clause is the
   printed link, neither broader nor narrower.

## Representation choices (each harmless)

- δY_{s−} is `Function.leftLim` of the path, replaced by 0 for s ≤ 0; at s = 0 the paper's value
  is immaterial (Lebesgue-null time set, N({0} × E) = 0 a.s., and the right-hand N-integral is
  over (0, T]). For s > T the integrand vanishes because δU does.
- Expectations are lower integrals in [0, ∞]; the constant enters as `ENNReal.ofReal c`, c ≥ c₀ > 0.
- Unknowns are coordinate families; the inner product is the coordinate sum.
- δZ, δU are extended by 0 off [0, T]; δY is càdlàg for every ω rather than almost surely (a
  null-set modification in the augmented filtration, which changes no quantity of the clause).
- The local integral is built from the library's L² compensated integral (defined for marked
  progressively measurable integrands of finite energy); here the integrand and its cut-offs are
  predictable (δU marked predictable, δY_{s−} left-continuous adapted, 1_{s ≤ τ_k} left-continuous),
  so it is the classical compensated integral and its bracket is ∫∫ H² dN.

## Coverage of claim A:lem4.1:M2-infinite-activity (lines 139-187)

Its nine clauses (claims.json): `lem41_M2_no_square_moment` (H²_N gives the quadratic integrand of
M² no square moments, ν ≠ 0), `lem41_jump_times` (with ν(E) = ∞ the jump times do not exhaust
[0, T]), `lem41_M2_integrand` (predictable, nonnegative), `lem41_M2_zero_mean` (L¹ bound by
e^T E∫‖δU‖², integrability of the Poisson integral and compensator, E[M²_T − M²_t] = 0),
`lem41_M2_martingale` (M² a martingale on [0, T], stronger than the printed "local martingale"),
`lem41_MW` (M^W local Itô integral, its BDG bound, finiteness, zero-mean increments), `lem41_M1`
(M¹ exists as a local compensated integral, composite bound, finiteness, zero-mean increments),
this clause (first link of the M¹ chain), and `lem41_M1_chain` (the later links: Cauchy-Schwarz
with sup|δY|, compensation formula (2.1), the L²(ν) norm). By their names they state every
mathematical assertion of the region: the three local martingales (the decomposition of the
terms of (4.5) belongs to A:eq:itoY2, per the scope note), the infinite-activity remark of line
151, the two BDG chains, the supremum criterion's conclusion for M^W and M¹, and the
compensation-formula argument for M². The remark "M² is handled through the compensation formula,
which asks only for integrability" is methodological. I reviewed only this clause's Lean; no
clause name states something the passage does not claim, the M² martingale clause being a
(true) strengthening. The hypotheses here are those of Lemma 4.1, in force at that point.

Witness: `Dissertation.Acceptance.A.lem_bpbsde_nonzero_hypotheses`
(Dissertation/Acceptance/A/WitnessLocal.lean) gives every Lemma 4.1 hypothesis at d = m = 1,
ν = δ₀ on ℝ, T = 1, δZ = δU = 1_{(0,1]}, φ = 0, δY = (càdlàg versions of) ∫_0^t dW + ∫_0^t∫ Ñ,
δξ = δY_1: an instance the paper intends (finite activity, a special case of the setting). With
δU ≠ 0 on (0, 1] and δY_{s−} ≠ 0 at the jump times of N with positive probability, the right
side is positive, so the clause does not read 0 ≤ 0. The witness itself does not exhibit a
process M1 satisfying `IsLocalCompensatedIntegral` for this integrand (the last premise of the
proposition); its existence under the same hypotheses is the first conjunct of the proposition
`lem41_M1`, which has the acceptance theorem `Dissertation.Acceptance.A.lem41_M1`. Together they
show the premises can be met non-degenerately; the witness alone would leave the M1 premise
unexhibited.

Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless:
1. δY_{s−} is the left limit of the path (`Function.leftLim`), set to 0 for s ≤ 0: the value at
   s = 0 is immaterial (Lebesgue-null time, N({0} × E) = 0 a.s., right-hand N-integral over
   (0, T]); for s > T the integrand vanishes since δU does.
2. Expectations are lower integrals in [0, ∞]; c_BDG enters as `ENNReal.ofReal c` for every
   c ≥ c₀, with c₀ > 0 quantified before everything else (a universal constant, as printed).
3. Coordinate families for the processes; ⟨·,·⟩ and |·|² are coordinate sums.
4. δZ, δU are extended by 0 off [0, T]; δY is càdlàg for every ω instead of almost surely (a
   null-set modification in the augmented filtration, changing no quantity of the clause).
5. "M¹ is the local compensated integral" is `IsLocalCompensatedIntegral`: càdlàg adapted on
   [0, T], equal up to localising stopping times exhausting [0, T] to the library's L²
   compensated integrals of the cut-offs. The integrand and its cut-offs are predictable, so this
   is the classical local integral, unique up to indistinguishability on [0, T], and the full
   local case (integrand not in L²(dP ⊗ ds ⊗ ν)) is covered.
The witness `lem_bpbsde_nonzero_hypotheses` exhibits the Lemma 4.1 hypotheses with δY, δU nonzero
(right side positive) but not an M1; existence of M1 there is the first conjunct of `lem41_M1`,
which has an acceptance theorem.
Disagreements with the author's review (shown 2026-10-20T19:47:27Z): none
