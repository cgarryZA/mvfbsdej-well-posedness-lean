# Reviews of the statements of paper A (well-posedness, at `1f67672`)

Each entry reads the manuscript passage and the proposition side by side. The marker records the
hash of the proposition reviewed; a change of the proposition reopens the entry. Each entry reads
the text of the manuscript at `1f67672` (`manuscript/`).

## Remark 2.6, (2.8): `Dissertation.PaperSpec.A.eq_coupling`

Manuscript (§2, Remark "Wasserstein bounds"): for two
diagonal inputs `(Θ, μ), (Θ', μ')` at the same time on the same probability space, the pair
`(Θ, Θ')` is a coupling of `(μ, μ')`, so
`W₂(μ, μ')² ≤ 𝔼[|δX|² + |δY|² + |δZ|²_F + ‖δU‖²_{L²(ν)}]`.

Proposition: for every probability space, every σ-finite `ν` on a countably generated `(E, ℰ)`,
all `n, m, d`, and all `Θ, Θ' : Ω → H` in `L²`,
`w2H (lawP2 P Θ) (lawP2 P Θ')² ≤ ∫ (‖δX‖² + ‖δY‖² + ‖δZ‖² + ‖δU‖²) dP`.

Correspondence:

* `H = ℝⁿ × ℝᵐ × ℝ^{m×d} × L²(ν; ℝᵐ)` is `TupleH ν n m d`; the `m × d` channel is
  `EuclideanSpace ℝ (Fin m × Fin d)`, whose norm is the Frobenius norm; the `U` channel is
  `Lp (EuclideanSpace ℝ (Fin m)) 2 ν` with its norm.
* `W₂` for the Hilbert norm of `H` is `w2H`: the 2-Wasserstein distance (infimum over couplings of
  the quadratic cost, `w2sq`, `IsCoupling`, `transportCostSq`) of the images under `toL2`, the
  identification of `H` with the `ℓ²` product of its channels.
* `μ = Law(Θ)` is `lawP2 P Θ`, the image measure for `Θ ∈ L²`.
* The proposition is broader than the printed claim: it holds for any two square-integrable
  tuples on one probability space, not only for two diagonal inputs at a common time. The printed
  claim is the instance at two diagonal inputs, which are square integrable (Definition 2.1).

Verdict: faithful (broader, printed claim an instance).

<!-- spec-review: Dissertation.PaperSpec.A.eq_coupling ed839d34f480cba17af7c36ae6c33114 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.eq_coupling--claude-reviewer--2026-10-17T12_12_10Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_coupling ed839d34f480cba17af7c36ae6c33114 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.eq_coupling--claude-auditor--2026-10-19T03_31_22Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_coupling ed839d34f480cba17af7c36ae6c33114 by=claude-auditor -->

## Remark 2.6, (2.9): `Dissertation.PaperSpec.A.eq_couplingT`

Manuscript: `W₂(ρ, ρ')² ≤ 𝔼|X_T − X'_T|²` for the induced terminal laws `ρ = Law(X_T)`,
`ρ' = Law(X'_T)`, "the `X`-marginal case of (2.8) at time `T`".

Proposition: for every probability space, all `n` and all `X, X' : Ω → ℝⁿ` in `L²`,
`w2P (lawP2 P X) (lawP2 P X')² ≤ ∫ ‖X − X'‖² dP`, with `w2P` the 2-Wasserstein distance of the
Euclidean norm on `P₂(ℝⁿ)`.

Correspondence: `X_T, X'_T ∈ L²(Ω, ℱ_T; ℝⁿ)` in the manuscript; the proposition asks square
integrability only, so it is broader, and the printed claim is its instance at `ℱ_T`-measurable
terminal values.

Verdict: faithful (broader, printed claim an instance).

<!-- spec-review: Dissertation.PaperSpec.A.eq_couplingT ed839d34f480cba1b0b3c75b14edd5d3 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/Dissertation.PaperSpec.A.eq_couplingT--claude-reviewer--2026-10-17T12_12_34Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_couplingT ed839d34f480cba1b0b3c75b14edd5d3 by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.eq_couplingT--claude-auditor--2026-10-19T03_34_37Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_couplingT ed839d34f480cba1b0b3c75b14edd5d3 by=claude-auditor -->

## Theorem 3.1: `Dissertation.PaperSpec.A.thm_stab`

Manuscript (§3, Theorem `thm:stab`): system 1 satisfies
Assumptions 2.2–2.5 with `L, α, β₁, β₂` and `G`; system 2 satisfies Assumptions 2.2–2.3 with its
own Lipschitz constant; `Θᵏ ∈ ℍ` solves (1.1) for system `k`; then (3.1) holds with `δψ` along
`(Θ²_t, μ²_t)` for `ψ ∈ {b, σ, f}`, `δh` along `(Θ²⁻_t, μ²⁻_t)` and `δ̂g_T` at `(X²_T, Law X²_T)`,
and `C_stab` depends only on `T, L, ‖G‖, c_G, α, β₁, β₂` (and the universal BDG constant), not on
system 2, the dimensions or `ν(E)`.

Proposition: `∃ C_stab : ℝ⁷ → ℝ`, then for every stochastic basis of §2 (`enlJoint`), all
`n, m, d ≥ 1`, `T > 0`, all constants, `G`, both systems and data, the hypotheses, and all
`Θ¹, Θ²` with `Solution`, `supSize(δΘ) ≤ C_stab(T, L, ‖G‖, s_min(G)⁻², α, β₁, β₂) · dataSize(…)` in
`[0, ∞]`.

Correspondence:

* Quantifier order: `C_stab` is chosen before the basis, `n, m, d`, `ν`, the systems and the
  solutions, as a function of the seven printed parameters; hence it depends on nothing else, as
  printed. The universal BDG constant is a fixed number and needs no argument.
* Hypotheses: (2.3) is `JointBorel` for both systems (the paper's standing measurability);
  Assumption 2.2 `Assumption22`, 2.3 `Assumption23` (with `L` for system 1 and `L₂` for system 2),
  2.4 `G.rank = min m n`, 2.5 `Assumption25` for system 1. The standing setting (`n, m, d ≥ 1`,
  `T > 0`, the driver, `𝒢₀` independent of it) is as in §2.
* Solutions: `Solution` (the solution notion of §3, reviewed with its representation choices in
  `definitions.md`).
* Conclusion: `supSize` of the differences is the left side of (3.1); `dataSize` with the
  differences named above is its right side (`δh` through `coeffJump` along
  `(leftLimProc X², leftLimProc Y², Z², U²)`, which represents `h(t, Θ²⁻_t, ·, μ²⁻_t)`). The
  inequality in `[0, ∞]` implies the printed one when its right side is finite and says nothing
  false when it is infinite.
* The paragraph after the theorem (the companion bound with the roles exchanged, the
  shared-interior case, the minimal hypotheses on system 2) is stated separately, as
  `thm_stab_companion`, `thm_stab_data` and `thm_stab_minimal`.

Witness: `Dissertation.Acceptance.A.thm_stab_nonzero_hypotheses`. Over a probability space
carrying a Lévy driver with `d = 1` and `ν = δ₀` on `ℝ` (`LevyDriver.exists`), with `𝒢₀ = ⊥`
(independent of everything, `indep_bot_left`), `n = m = 1` and `T = 1`, both systems are
Example 5.1(i) with `β₁ = β₂ = 1`, `σ_c = 0`, `h_c = 0`, and the initial data are `ξ¹ ≡ e₁` and
`ξ² ≡ 0`; the manuscript allows any `σ_c ∈ ℝ`, `h_c ∈ L²(ν)`, `ξ₀ ∈ L²(ℱ₀)` and `β₁, β₂ > 0`
there. The witness states (2.3), Assumptions 2.2 (for `ξ¹`), 2.3 (`L = 1`), 2.4 (`G = 1`, rank
`1 = min 1 1`) and 2.5 (`α = β₁ = β₂ = 1`) for system 1; system 2 is the same system, so its (2.3)
and Assumption 2.3 (`L₂ = 1`) are those of system 1, and Assumption 2.2 for `ξ²` is stated; a
`Solution` of each (from Theorem 3.5, `Dissertation.Acceptance.A.thm_cwp`); and the two sides of
(3.1) at the instance: `dataSize = 1`, as only the initial data differ (the coefficient
differences vanish because the systems coincide), and `supSize ≥ 1`, from `X¹_0 − X²_0 = e₁`
almost surely (`Solution.X_zero_ae`). Both sides of (3.1) are therefore positive at the instance.
The positivity hypotheses `0 < n, m, d, T` hold at `1`. The earlier witness `thm_stab_hypotheses`
(Example 5.1(i) with `β = 1` against `β = 2`, both from the initial datum `0`) remains a theorem
but is no longer linked: both of its solutions are zero, so the differences evaluated along
solution 2 and the error vanish and (3.1) reads `0 ≤ 0` there. The statement of this review that
it was not a trivial instance was wrong.

Verdict: faithful.

<!-- spec-review: Dissertation.PaperSpec.A.thm_stab ed839d34f480cba16bc55062de98e587 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/Dissertation.PaperSpec.A.thm_stab--claude-reviewer--2026-10-17T16_05_53Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.thm_stab ed839d34f480cba16bc55062de98e587 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.thm_stab--claude-auditor--2026-10-19T03_36_54Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.thm_stab ed839d34f480cba16bc55062de98e587 by=claude-auditor -->

## Theorem 3.3: `Dissertation.PaperSpec.A.thm_uniq`

Manuscript (§3, Theorem `thm:uniq`): under Assumptions 2.3–2.5,
(1.1) has at most one solution. More precisely, if `Θ¹, Θ² ∈ ℍ_weak` satisfy (1.1) with the same
initial condition, then `Θ¹ = Θ²`. Furthermore, `Θ¹ − Θ² ∈ ℍ`.

Proposition: for every stochastic basis of §2 (`enlJoint`), all `n, m, d ≥ 1`, `T > 0`, all
`L, α, β₁, β₂`, `G` and coefficients `C`, under (2.3) and Assumptions 2.3–2.5, for every initial
datum `ξ₀` and all `Θ¹, Θ²` with `WeakSolution` for `ξ₀`: `X¹, X²` and `Y¹, Y²` are
indistinguishable on `[0, T]`, the energies of `Z¹ − Z²` and `U¹ − U²` on `[0, T]` vanish, and
`supSize(Θ¹ − Θ²) < ∞`.

Correspondence:

* Hypotheses: Assumptions 2.3–2.5 as for Theorem 3.1, and the standing measurability (2.3);
  Assumption 2.2 is not assumed, as printed, so `ξ₀ : Ω → ℝⁿ` is arbitrary and the coefficient
  processes need not be square integrable along a tuple (see the reading recorded for
  `PaperAdmissibleInt` in `definitions.md`).
* "`Θ¹, Θ² ∈ ℍ_weak` satisfy (1.1) with the same initial condition": `WeakSolution` for both, with
  the one `ξ₀`.
* "`Θ¹ = Θ²`": equality of classes of `ℍ_weak` (indistinguishability for `X, Y`; vanishing energy
  of the difference for `Z, U`, which vanish off `[0, T]`).
* "`Θ¹ − Θ² ∈ ℍ`": the difference is càdlàg adapted, resp. predictable, as a difference of two
  such processes, so the condition is the finiteness of its `ℍ` norm, `supSize` (reviewed with
  Theorem 3.1). It follows from `Θ¹ = Θ²`; it is stated because it is printed.
* "(1.1) has at most one solution": the instance at two solutions in `ℍ`, since a solution is a
  weak solution (`PaperSolution.toWeakInt`, with the càdlàg paths unchanged); it is also the
  uniqueness clause of `thm_cwp`.

Witness: `Dissertation.Acceptance.A.thm_uniq_hypotheses`: at the instance of the Theorem 3.5
witness (Example 5.1(i), `β₁ = β₂ = 1`, `n = m = d = 1`, `ν = δ₀`, `T = 1`), (2.3) and
Assumptions 2.3–2.5 in the order of the proposition, and two tuples with `WeakSolution` for the
datum `0` (both the solution of Theorem 3.5, as the hypotheses of a true uniqueness statement can
only be met by equal tuples).

Verdict: faithful, with the reading of "satisfies (1.1)" by `L²` stochastic integrals recorded in
`definitions.md`.

<!-- spec-review: Dissertation.PaperSpec.A.thm_uniq ed839d34f480cba1b8815741b34ba4e5 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/Dissertation.PaperSpec.A.thm_uniq--claude-reviewer--2026-10-17T16_05_53Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.thm_uniq ed839d34f480cba1b8815741b34ba4e5 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.thm_uniq--claude-auditor--2026-10-19T03_35_38Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.thm_uniq ed839d34f480cba1b8815741b34ba4e5 by=claude-auditor -->

## Theorem 3.5: `Dissertation.PaperSpec.A.thm_cwp`, and its continuous dependence

Manuscript (§3, Theorem `thm:cwp`): for every horizon `T > 0`,
under Assumptions 2.2–2.5 the system (1.1) admits a solution `Θ = (X, Y, Z, U) ∈ ℍ`, unique by
Theorem 3.3 and depending continuously on the coefficients and data in the sense of the estimate
(3.1) of Theorem 3.1.

Proposition `thm_cwp`: for every stochastic basis of §2 (`enlJoint`), all `n, m, d ≥ 1`, `T > 0`,
all `L, α, β₁, β₂`, `G`, coefficients `C` and initial datum `ξ₀ : Ω → ℝⁿ`, under (2.3) and
Assumptions 2.2–2.5: there are `X, Y, Z, U` with `Solution`, and any two `Solution`s with this
datum have `X` and `Y` indistinguishable on `[0, T]`, and `𝔼 ∫_0^T |Z¹ − Z²|²_F dt = 0`,
`𝔼 ∫_0^T ‖U¹ − U²‖²_{L²(ν)} dt = 0`, coordinatewise.

Correspondence:

* Hypotheses: as for Theorem 3.1 (system 1): (2.3) `JointBorel`, Assumption 2.2 `Assumption22`
  with the initial datum (which carries `ξ₀ ∈ L²(Ω, ℱ₀; ℝⁿ)`), 2.3 `Assumption23` with `L`, 2.4
  `G.rank = min m n`, 2.5 `Assumption25`.
* "admits a solution `Θ ∈ ℍ`": the existential over `Solution`, the solution notion reviewed in
  `definitions.md` (paths càdlàg on `[0, T]`, `S²` bounds, predictable `Z, U` in `H²`, the
  identities of (1.1) almost surely at every time).
* "unique": equality in `ℍ`, whose elements are classes: `S²` identifies indistinguishable
  processes, `H²_W` and `H²_N` identify processes equal `dt ⊗ dP`-almost everywhere on `[0, T]`,
  which is the vanishing of the energies of the differences (`Z` and `U` vanish off `[0, T]`).
  The proposition asks uniqueness among solutions in `ℍ`, the class of the theorem; uniqueness
  in `ℍ_weak`, which the theorem cites, is Theorem 3.3's own claim (`A:thm:uniq`).
* "depending continuously on the coefficients and data in the sense of the estimate (3.1)": the
  second clause of the claim, the proposition `thm_stab` of Theorem 3.1, reviewed above. The
  manuscript names the sense, the estimate itself, so no separate continuity statement (a
  modulus, or continuity of a solution map in a topology) is read into it.

Witness: `Dissertation.Acceptance.A.thm_cwp_hypotheses`: at the instance of the Theorem 3.1
witness, system 1 (Example 5.1(i), `β₁ = β₂ = 1`, `σ_c = 0`, `h_c = 0`, datum `0`, `ν = δ₀`,
`n = m = d = 1`, `T = 1`, `G = 1`, `L = α = 1`) satisfies (2.3) and Assumptions 2.2–2.5, stated in
the order of the proposition.

Verdict: faithful.

<!-- spec-review: Dissertation.PaperSpec.A.thm_cwp ed839d34f480cba10deeabcd10e6e74d by=claude-author -->
Review by claude-reviewer: faithful (report `reports/Dissertation.PaperSpec.A.thm_cwp--claude-reviewer--2026-10-17T16_05_53Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.thm_cwp ed839d34f480cba10deeabcd10e6e74d by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.thm_cwp--claude-auditor--2026-10-19T03_34_53Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.thm_cwp ed839d34f480cba10deeabcd10e6e74d by=claude-auditor -->

## Proposition 3.8: `Dissertation.PaperSpec.A.prop_strict`

Manuscript (§3, Proposition `prop:strict`): let `n = m = 1`,
`d ≥ 1`, `G = 1`, fix `β₁ > 0`; for every `0 < ε < β₁` the drift (3.6)
`b(t, θ, μ) = −β₁ y + ε g₀(y − m_Y(μ))` is free-measure `W₂`-Lipschitz with constant `β₁ + ε`
and satisfies (3.7), `𝔼⟨δb, δY⟩ ≤ −(β₁ − ε) 𝔼|δY|²`, along all `(Θ, μ), (Θ', μ') ∈ 𝒟_t`; yet for
every `β ≥ 0` the pointwise bound `⟨δb, δy⟩ ≤ −β |δy|²` fails at a pair of free inputs with
`θ ∈ supp μ` and `θ' ∈ supp μ'`.

Proposition: for every σ-finite `ν` on a countably generated `(E, ℰ)`, every `d ≥ 1` and all
`β₁ > 0`, `0 < ε < β₁`: (i) `‖b(t, θ, μ) − b(t, θ', μ')‖ ≤ (β₁ + ε)(‖y − y'‖ + w2H μ μ')` at all
`t, θ, θ', μ, μ'`; (ii) on every probability space, for all `Θ, Θ' ∈ L²` and every `t`, the
pairing `⟨b(t, Θ, Law Θ) − b(t, Θ', Law Θ'), δY⟩` is integrable and its integral is at most
`−(β₁ − ε) ∫ ‖δY‖²`; (iii) for all `t` and `β ≥ 0` there are `θ, θ', μ, μ'` with `θ ∈ supp μ`,
`θ' ∈ supp μ'` and `¬ ⟨δb, δy⟩ ≤ −β ‖δy‖²`.

Correspondence:

* `b` is `clampDrift` (reviewed in `definitions.md`); `H = TupleH ν 1 1 d`; `G = 1` enters only
  as `⟨δb, G* δY⟩ = ⟨δb, δY⟩`.
* "free-measure `W₂`-Lipschitz with constant `β₁ + ε`": the term is not defined elsewhere in the
  paper; its proof shows `|δb| ≤ (β₁ + ε)(|δy| + W₂(μ, μ'))` at free inputs, which is clause
  (i), with `W₂` of the Hilbert norm of `H` (`w2H`, as in (2.8)). It implies the bound of
  Assumption 2.3 at free inputs, whose right side has `|δX| + |δY| + |δZ|_F + ‖δU‖ ≥ |δy|`.
* (3.7) "along all `(Θ, μ), (Θ', μ') ∈ 𝒟_t`": clause (ii) with `μ = lawP2 P Θ`. It is broader
  than printed: any probability space and any square-integrable `Θ, Θ'`, without
  `ℱ_t`-measurability; the printed claim is its instance on the standing basis. The integrability
  of the pairing is stated so that the Bochner integral is the expectation; `∫ ‖δY‖²` is finite
  for `Θ, Θ' ∈ L²`.
* "for every `β ≥ 0` … fails at a pair of free inputs with `θ ∈ supp μ`, `θ' ∈ supp μ'`": clause
  (iii), `supp` the support of the law (`Measure.support`); it holds at every `t`, as `b` does not
  depend on `t`.

Witness: `Dissertation.Acceptance.A.prop_strict_hypotheses` (`ν = δ₀` on `ℝ`, `d = 1`,
`β₁ = 2`, `ε = 1`); the hypotheses are numerical and the witness is immediate.

Verdict: faithful (clause (ii) broader, printed claim an instance).

<!-- spec-review: Dissertation.PaperSpec.A.prop_strict ed839d34f480cba1f1c48950c52ae4f4 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.prop_strict--claude-reviewer--2026-10-17T12_11_02Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.prop_strict ed839d34f480cba1f1c48950c52ae4f4 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.prop_strict--claude-auditor--2026-10-19T03_31_23Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.prop_strict ed839d34f480cba1f1c48950c52ae4f4 by=claude-auditor -->

## Corollary 3.6: `Dissertation.PaperSpec.A.cor_robust`, `cor_robust_wp`, `cor_robust_lip`

Manuscript (§3, Corollary `cor:robust`): let `m = n`, the
baseline `(b₀, σ₀, h₀, f₀, g)` with `ξ₀` satisfy Assumptions 2.2–2.5 with margin `c_diss > 0` in
the unweighted form (2.13); let the perturbations `p_b, p_σ, p_h, p_f` satisfy the corresponding
origin-integrability and diagonal Lipschitz conditions of Assumptions 2.2–2.3 and, for some
`c_pert ≥ 0`, (3.4). If `c_pert < c_diss`, the perturbed system satisfies, with the same `ξ₀`,
Assumptions 2.2–2.5 with the same `G, α, β₁, β₂` and margin `c_diss − c_pert`; by Theorems 3.1,
3.3 and 3.5 it is well-posed. If, in addition, the perturbations are independent of `θ` and
satisfy (3.5), then (3.4) holds with `c_pert = ‖G‖ L_p`.

Propositions: `cor_robust` (the assumptions of the perturbed system), `cor_robust_wp` (its
well-posedness), `cor_robust_lip` ((3.5) gives (3.4)).

Correspondence:

* Standing setting and `m = n`: as for Theorem 3.1, with `Coeffs ν n n d` and `G : n × n`.
* Baseline: (2.3) `JointBorel`, Assumptions 2.2–2.5 with `L₀, G, α, β₁, β₂`, and `Margin213`
  with `c_diss > 0`, the same `β₁, β₂` as in Assumption 2.5 (Remark 2.11 records the margin with
  the reduced constants; the corollary uses one set of constants).
* Perturbation: `OriginValues T p` (the origin values of Assumption 2.2 for `b, σ, h, f`),
  `LipInterior … L_p p` with `L_p ≥ 0` (the interior bound of Assumption 2.3; `p` has no terminal
  function), `PairingBound34 … c_pert p` with `c_pert ≥ 0`, and `c_pert < c_diss`.
* Reading recorded: the perturbed system satisfies the standing measurability (2.3)
  (`JointBorel T (C.perturb p)`). The corollary concludes well-posedness of the perturbed system,
  which Theorems 3.1–3.5 give under (2.3); the paper states no measurability of `p`, and (2.3) of
  the perturbed system is the standing hypothesis on the system it concludes about. Given (2.3)
  for the baseline it implies (2.3) for `b, σ, h, f` of `p` (`JointBorel.coeffBorelW2_of_perturb`).
* `cor_robust`'s conclusion: Assumption 2.2 with `ξ₀`; Assumption 2.3 with some constant (the
  paper names none; the proof's "Lipschitz constants add" gives `L₀ + L_p`); `G` of full rank
  (unchanged); Assumption 2.5 with the same `G, α, β₁, β₂`; (2.13) with margin
  `c_diss − c_pert`.
* `cor_robust_wp`: "well-posed by Theorems 3.1, 3.3 and 3.5": a solution in `ℍ` (`Solution`),
  uniqueness in `ℍ_weak` (`WeakSolution`, as Theorem 3.3), and (3.1) with the perturbed system as
  system `1` against every system `2` with (2.3) and Assumptions 2.2–2.3, with a function
  `C_stab` of `(T, L, ‖G‖, c_G, α, β₁, β₂)` chosen first and `L` any constant with which the
  perturbed system satisfies Assumption 2.3, as in Theorem 3.1 (the proof's `L₀ + L_p` is one);
  the `δh` of (3.1) along `Θ²⁻` as in `thm_stab`.
* `cor_robust_lip`: "if, in addition, … independent of `θ` and (3.5)": `TupleIndep` and `LawLip35`
  imply `PairingBound34` with `‖GX G‖ · L_p`, `‖GX G‖` the operator norm of `G`. The proposition
  drops the other hypotheses of the corollary, which the implication does not use, and holds on
  every filtered probability space; it is broader, the printed claim its instance. It keeps
  `n ≥ 1` and `T > 0`, under which (3.5) forces `L_p ≥ 0`.

Witnesses: `Dissertation.Acceptance.A.cor_robust_hypotheses` (for `cor_robust` and
`cor_robust_wp`): over a Lévy driver with `d = 1`, `ν = δ₀`, `𝒢₀ = ⊥`, `n = 1`, `T = 1`, the
baseline Example 5.1(i) with `β₁ = β₂ = 2`, `σ_c = 0`, `h_c = 0`, datum `0`, with `L₀ = 2`,
`G = 1`, `α = 1`, reduced constants `β₁ = β₂ = 1` and margin `c_diss = 1` (Remark 2.11), and the
feedback perturbation `p_b = ε y`, `p_σ = ε z`, `p_h = ε u`, `p_f = 0`, `ε = 1/2`, with
`L_p = c_pert = 1/2`; every hypothesis in the order of the propositions, the perturbed system's
(2.3) through its identification with Example 5.1(i) at `(3/2, 2)`
(`sys_two_perturb_feedback`). `Dissertation.Acceptance.A.cor_robust_lip_hypotheses`: the
perturbation of Example 5.4 (`ε = 1/4`, the profiles `min(|r|, 1)`, `Q(s) = min(|s₁|, 1)`, the
feature `min(‖u‖, 1)`, `w₀ = w₁ = v₀ = e₁`, `ĥ = 0`, reference laws `δ₀`), over a Lévy driver with
`d = 1`, `ν = δ₀`, `n = 1`, `T = 1`, depends on the tuple through its law only and satisfies (3.5)
with `L_p = 3/4`: a law-dependent perturbation of the kind the corollary is about.

Verdict: `cor_robust` and `cor_robust_wp` faithful, with the reading of the perturbed system's
measurability recorded; `cor_robust_lip` broader: it holds on every filtered probability space,
without the other hypotheses of the corollary, and the printed claim is its instance in the setting
of the corollary.

<!-- spec-review: Dissertation.PaperSpec.A.cor_robust ed839d34f480cba154326c82c977c8bd by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.cor_robust--claude-reviewer--2026-10-17T12_24_23Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.cor_robust ed839d34f480cba154326c82c977c8bd by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.cor_robust--claude-auditor--2026-10-19T03_36_02Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.cor_robust ed839d34f480cba154326c82c977c8bd by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.cor_robust_wp ed839d34f480cba16dd662e97e677716 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/Dissertation.PaperSpec.A.cor_robust_wp--claude-reviewer--2026-10-17T16_05_53Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.cor_robust_wp ed839d34f480cba16dd662e97e677716 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.cor_robust_wp--claude-auditor--2026-10-19T03_37_29Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.cor_robust_wp ed839d34f480cba16dd662e97e677716 by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.cor_robust_lip ed839d34f480cba14b18016daa0b4aac by=claude-author -->
Review by claude-reviewer: broader (report `reports/Dissertation.PaperSpec.A.cor_robust_lip--claude-reviewer--2026-10-17T16_03_52Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.cor_robust_lip ed839d34f480cba14b18016daa0b4aac by=claude-reviewer -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.cor_robust_lip--claude-auditor--2026-10-19T03_34_13Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.cor_robust_lip ed839d34f480cba14b18016daa0b4aac by=claude-auditor -->

## Assumption 2.4 (the bounds after "Then"): `Dissertation.PaperSpec.A.ass_G`

Manuscript (§2, Assumption `ass:G`): `G ∈ ℝ^{m×n}` has
full rank; `‖G‖` its operator norm, so `|Gv| ≤ ‖G‖ |v|` and `|G*v| ≤ ‖G‖ |v|`, and `s_min(G) > 0`
its smallest singular value; `c_G := s_min(G)⁻²`. Then `|x|² ≤ c_G |Gx|²` (`m ≥ n`),
`|y|² ≤ c_G |G*y|²` (`n ≥ m`); when `G*` is injective the second bound extends to
`|Z|²_F ≤ c_G |G*Z|²_F` and `‖U‖²_{L²(ν)} ≤ c_G ‖G*U‖²_{L²(ν)}`.

Scope decision: the assumption is the full rank of `G`, which every statement using it carries
as `G.rank = min m n`; the rest of the environment asserts consequences, stated as `ass_G`.

Proposition: for `m, n ≥ 1` and `G` with `G.rank = min m n`: `0 < sMin G`; the two operator-norm
bounds with `‖GX G‖`; the two coercivity bounds with `(sMin G ^ 2)⁻¹`; and, if the adjoint of
`GX G` is injective, the bounds for `Z ∈ ℝ^{m×d}` (every `d`, `GZ`) and `U ∈ L²(ν; ℝᵐ)` (every
measure `ν`, `GU`), with the adjoints of `GZ`, `GU` for `G*`.

Correspondence: `G*` is the adjoint (`Gᵀ` for real `G`); `GX, GZ, GU, sMin` are reviewed in
`definitions.md` (`sMin` is the smallest of the `min(m, n)` singular values, the square root of
the least eigenvalue of `GᵀG` or `GGᵀ`); `c_G = (sMin G ^ 2)⁻¹`. The `U` bound is asserted for
every measure `ν` on every measurable `E`, broader than the standing σ-finite `ν`.

Witness: `Dissertation.Acceptance.A.ass_G_hypotheses` (`m = n = 1`, `G = 1`).

Verdict: faithful (the `U` clause broader, the printed claim an instance).

<!-- spec-review: Dissertation.PaperSpec.A.ass_G ed839d34f480cba1654da9b84ef073af by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.ass_G--claude-reviewer--2026-10-17T12_05_30Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ass_G ed839d34f480cba1654da9b84ef073af by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.ass_G--claude-auditor--2026-10-19T03_31_21Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ass_G ed839d34f480cba1654da9b84ef073af by=claude-auditor -->

## Remark 2.6, (2.10): `Dissertation.PaperSpec.A.eq_lipfun`

Manuscript: for a separable Hilbert space `K` and `φ̄ : H → K` Lipschitz, the law functional
`μ ↦ ∫_H φ̄ dμ` is `W₂`-Lipschitz with the same constant,
`|∫_H φ̄ dμ − ∫_H φ̄ dμ'|_K ≤ Lip(φ̄) W₂(μ, μ')`.

Proposition: for every σ-finite `ν` on a countably generated `(E, ℰ)`, all `n, m, d`, every
separable Hilbert space `K` (`InnerProductSpace ℝ K`, complete, separable), every `φ : H → K`
and `L ≥ 0` with `‖φ θ − φ θ'‖ ≤ L ‖θ − θ'‖_H` (`‖toL2 θ − toL2 θ'‖`, the Hilbert norm of `H`),
and all `μ, μ' ∈ P₂(H)`: `‖∫ φ dμ − ∫ φ dμ'‖ ≤ L · w2H μ μ'`.

Correspondence: `Lip(φ̄)` is the least `L`; the proposition holds for every Lipschitz constant,
the printed claim its instance at the least one. `|·|_H` is the Hilbert norm (as in (2.8)); the
integrals are Bochner integrals, which exist since `φ` has linear growth and `μ, μ'` finite second
moments. `W₂` is `w2H`, reviewed with (2.8).

Witness: `Dissertation.Acceptance.A.eq_lipfun_hypotheses` (the projection `θ ↦ y` into `ℝ¹`,
`L = 1`).

Verdict: faithful.

<!-- spec-review: Dissertation.PaperSpec.A.eq_lipfun ed839d34f480cba187b5540277706218 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/Dissertation.PaperSpec.A.eq_lipfun--claude-reviewer--2026-10-17T16_03_52Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_lipfun ed839d34f480cba187b5540277706218 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.eq_lipfun--claude-auditor--2026-10-19T03_34_14Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_lipfun ed839d34f480cba187b5540277706218 by=claude-auditor -->

## Remark 2.6, (2.11): `Dissertation.PaperSpec.A.eq_margproj`

Manuscript: marginal projection `P₂(H) → P₂(L²(ν))`, `μ ↦ μ^U`, is 1-Lipschitz for `W₂`:
`W₂(μ^U, μ'^U) ≤ W₂(μ, μ')`.

Proposition: for every σ-finite `ν` on a countably generated `(E, ℰ)`, all `n, m, d` and all
`μ, μ' ∈ P₂(H)`: `w2P μ.margU μ'.margU ≤ w2H μ μ'`.

Correspondence: `μ^U` is `margU` (reviewed in `definitions.md`); `W₂` on `P₂(L²(ν; ℝᵐ))` is
`w2P` of the `L²(ν)` norm, and on `P₂(H)` it is `w2H` of the Hilbert norm. The statement has no
hypotheses beyond the standing setting.

Verdict: faithful.

<!-- spec-review: Dissertation.PaperSpec.A.eq_margproj ed839d34f480cba1c19abbad6d02050c by=claude-author -->
Review by claude-reviewer: faithful (report `reports/Dissertation.PaperSpec.A.eq_margproj--claude-reviewer--2026-10-17T16_03_52Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_margproj ed839d34f480cba1c19abbad6d02050c by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.eq_margproj--claude-auditor--2026-10-19T03_34_37Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_margproj ed839d34f480cba1c19abbad6d02050c by=claude-auditor -->

## Lemma 4.1: `Dissertation.PaperSpec.A.lem_bpbsde`

Manuscript (§4, Lemma `lem:bpbsde`): let `δY` be a càdlàg
adapted process and `δZ ∈ H²_W`, `δU ∈ H²_N` satisfy
`δY_t = δξ + ∫_t^T φ_s ds − ∫_t^T δZ_s dW_s − ∫_t^T ∫_E δU_s(e) Ñ(ds, de)` with
`δξ ∈ L²(ℱ_T)` and `φ ∈ L²(Ω × [0, T])`. Then `δY ∈ S²(ℝᵐ)`, and there is a constant `C_BP`,
depending only on `T` and `c_BDG`, with
`𝔼 sup_{t ≤ T} |δY_t|² + 𝔼 ∫_0^T (|δZ_s|²_F + ‖δU_s‖²_{L²(ν)}) ds
  ≤ C_BP (𝔼|δξ|² + 𝔼 ∫_0^T |φ_s|² ds)`.

Proposition: `∃ C_BP : ℝ → ℝ`, then for every stochastic basis of §2 (`enlJoint`), `m, d ≥ 1`,
`T > 0`, and `δξ, φ, δY, δZ, δU` with the hypotheses below, `supSize`-type left side `< ∞` and
`≤ C_BP(T) · (𝔼|δξ|² + Σ_k 𝔼 ∫_0^T |φ^k_s|² ds)` in `[0, ∞]`.

Correspondence:

* `C_BP`: chosen before everything, as a function of `T`; `c_BDG` is a universal number, not a
  parameter, so "depending only on `T` and `c_BDG`" is a function of `T` alone. It does not depend
  on `m`, `d`, `ν` or the basis.
* `δY`: `ℝᵐ`-valued (the conclusion `δY ∈ S²(ℝᵐ)`), coordinate processes adapted at every
  `t ∈ [0, T]` with every path right-continuous on `[0, T)` with left limits on `(0, T]`. A process
  càdlàg almost surely has an indistinguishable everywhere-càdlàg version (R11), and the
  conclusion is invariant under indistinguishability, so asking every path loses nothing.
* `δZ ∈ H²_W`, `δU ∈ H²_N`: predictable, resp. marked predictable, finite energy on `[0, T]`, zero
  off `[0, T]` (the normal form of R11).
* `δξ ∈ L²(ℱ_T)`: `ℱ_T`-measurable and square integrable.
* `φ ∈ L²(Ω × [0, T])`: each coordinate jointly measurable with finite energy on `[0, T]`; no
  progressive measurability is asked, as printed (the paper adds progressive measurability
  explicitly where it means it, e.g. for the forcings of (4.1)). The proof takes a progressive
  version of `φ` (`BrownianPoisson.exists_progressive_ae_eq`, from the adaptedness of `∫_0^t φ`
  and the Lebesgue differentiation theorem).
* The equation: for every `t ∈ [0, T]`, almost surely, with the canonical integrals of `δZ` and
  `δU` over `enlJoint`, `∫_t^T` as the difference of the values at `T` and at `t`, and
  `∫_t^T φ_s ds` over `[t, T]`.
* Conclusion: `𝔼 sup_{t ≤ T} |δY_t|² < ∞` is `δY ∈ S²(ℝᵐ)` given the càdlàg adapted paths; the
  estimate with `|δY_t|² = Σ_k |δY^k_t|²` (`esq`), `|δZ|²_F = Σ_{k,j}`, `‖δU‖² = Σ_k`.

Witness: `Dissertation.Acceptance.A.lem_bpbsde_hypotheses`: over a Lévy driver with `d = 1`,
`ν = δ₀`, `𝒢₀ = ⊥`, `T = 1`, the backward component `(Y, Z, U)` of the solution of Theorem 3.5 for
Example 5.1(i) (`β₁ = β₂ = 1`), with `δξ = g(X_T, Law X_T)` and `φ` the driver process, meets
every hypothesis, in the order of the proposition: the lemma's intended use.

Verdict: faithful.

<!-- spec-review: Dissertation.PaperSpec.A.lem_bpbsde ed839d34f480cba1202e3ec284da1f15 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.lem_bpbsde--claude-reviewer--2026-10-17T12_23_54Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.lem_bpbsde ed839d34f480cba1202e3ec284da1f15 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.lem_bpbsde--claude-auditor--2026-10-19T03_35_50Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.lem_bpbsde ed839d34f480cba1202e3ec284da1f15 by=claude-auditor -->

## Lemma 4.2: `Dissertation.PaperSpec.A.lem_small`

Manuscript (§4, Lemma `lem:small`): under Assumptions
2.2–2.3 there is `λ* ∈ (0, 1]`, depending only on `T`, `L` and `c_BDG`, such that `WP(λ)` holds
for every `λ ∈ [0, λ*]`.

Proposition: `∃ λ* : ℝ → ℝ → ℝ`, then in the standing setting, for `T > 0`, under (2.3) and
Assumptions 2.2 (datum `ξ₀`) and 2.3 (constant `L`): `0 < λ*(T, L) ≤ 1` and `WP(λ)` for every
`λ ∈ [0, λ*(T, L)]`.

Correspondence: `λ*` is a function of `(T, L)` chosen first (`c_BDG` is a universal number); its
bounds are asserted in the situation of the lemma. `WP` is reviewed in `definitions.md`.

Witness: `Dissertation.Acceptance.A.thm_cwp_hypotheses` (Example 5.1(i): (2.3) and
Assumptions 2.2–2.5, a superset of the hypotheses here).

Verdict: faithful.

<!-- spec-review: Dissertation.PaperSpec.A.lem_small ed839d34f480cba12f6a12214671fd14 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.lem_small--claude-reviewer--2026-10-17T12_26_58Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.lem_small ed839d34f480cba12f6a12214671fd14 by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.lem_small--claude-auditor--2026-10-19T03_37_18Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.lem_small ed839d34f480cba12f6a12214671fd14 by=claude-auditor -->

## Lemma 4.3: `Dissertation.PaperSpec.A.lem_pert`

Manuscript (Lemma `lem:pert`): under Assumptions 2.3–2.5, for `λ̲ ∈ (0, 1]` and
`λ ∈ [λ̲, 1]`, let `Θ¹, Θ²` solve (4.1) at `λ` with `ℱ₀`-measurable initial data `ξ₀^k` and
forcings `q^k`, where `X^k, Y^k` are càdlàg adapted with `𝔼 ∫_0^T (|X^k|² + |Y^k|²) dt < ∞`,
`X^k_T ∈ L²(Ω, ℱ_T)`, `Z^k ∈ H²_W`, `U^k ∈ H²_N`, and `Θ¹ − Θ² ∈ ℍ`. Then (4.14) holds with
`C_B` depending only on `T, L, ‖G‖, c_G, α, β₁, β₂, λ̲` and `c_BDG`.

Proposition: `∃ C_B` of these eight arguments; in the standing setting, for `T > 0`, under (2.3)
and Assumptions 2.3–2.5, for `0 < λ̲ ≤ 1`, `λ̲ ≤ λ ≤ 1`, `ℱ₀`-measurable `ξ₁, ξ₂`, forcings
`q¹, q²` of the class of (4.1) (`PredForcing`), `WeakForcedSolution`s `Θ¹, Θ²` and
`supSize(Θ¹ − Θ²) < ∞`: `supSize(Θ¹ − Θ²) ≤ C_B(T, L, ‖G‖, s_min(G)⁻², α, β₁, β₂, λ̲) ·
dataSize(δξ₀, δq^b, δq^σ, δq^h, δq^f, δq^g)`.

Correspondence:

* The class of `Θ^k`: `WeakForcedSolution` (`ℍ_weak`, `X_T ∈ L²`, the integrals of (4.1) along
  `Θ^k` existing; reading R15), reviewed in `definitions.md`.
* `ℱ₀`-measurable data: measurable for the time-`0` field of `enlJoint` (R4); no square
  integrability of `ξ₀^k` is asked, as printed.
* `Θ¹ − Θ² ∈ ℍ`: the finiteness of `supSize` of the difference (the càdlàg adaptedness and
  predictability of the difference are inherited). The proof does not use it.
* (4.14): `supSize` and `dataSize` (reviewed with Theorem 3.1) with the differences of the data.

Witness: `Dissertation.Acceptance.A.lem_pert_two_data_hypotheses`: at Example 5.1(i),
`λ̲ = λ = 1` and zero forcings, the solutions of Theorem 3.5 from the initial data `0` and `e₁`
as solutions of (4.1) in `ℍ_weak`; their difference lies in `ℍ` (by Theorem 3.1), and the data
size on the right of (4.14) is `𝔼|δξ₀|² = 1`, so the estimate is exercised with distinct
solutions.

Verdict: faithful.

<!-- spec-review: Dissertation.PaperSpec.A.lem_pert ed839d34f480cba1eefcd4522364d865 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.lem_pert--claude-reviewer--2026-10-17T12_26_32Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.lem_pert ed839d34f480cba1eefcd4522364d865 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.lem_pert--claude-auditor--2026-10-19T03_38_06Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.lem_pert ed839d34f480cba1eefcd4522364d865 by=claude-auditor -->

## (4.25), the Young bound in Step 4 of the proof of Lemma 4.3: `Dissertation.PaperSpec.A.eq_bwdyoung`

Manuscript (proof of Lemma `lem:pert`, Step 4, lines 726–733): "By Assumption 2.3, the coupling
bound (2.8), and Young's inequality, for every `0 < ε ≤ 1`,
`2 𝔼⟨δY_s, λ δf_s + q^f_s⟩ ≤ (C/ε) 𝔼|δY_s|² + ε 𝔼(|δZ_s|²_F + ‖δU_s‖²_{L²(ν)})
+ (C/ε) 𝔼(|δX_s|² + |q^f_s|²)`, with `C` independent of `ε`." In this proof `q` stands for the
difference `δq` of the forcings ("The difference equations below involve the forcings only through
`δq`, which we therefore write simply as `q`"), `δf_s = f(s, Θ¹_s, μ¹_s) − f(s, Θ²_s, μ²_s)` with
`μ^k_s = Law(Θ^k_s)`, and `C` follows the convention of §4: a positive constant depending only on
`T, L, ‖G‖, c_G, α, β₁, β₂` and `c_BDG`. The next display inserts (4.25) under
`∫_t^T e^{κs} … ds`, and the proof then takes `ε < 1`.

Proposition: `∃ K` of `(T, L, ‖G‖, c_G, α, β₁, β₂, λ̲)` such that, in the standing setting and
under the hypotheses of Lemma 4.3 (those of `lem_pert`: `T > 0`, (2.3), Assumptions 2.3–2.5 with
`L, α, β₁, β₂` and a full-rank `G`, `0 < λ̲ ≤ 1`, `λ̲ ≤ λ ≤ 1`, `ℱ₀`-measurable `ξ₁, ξ₂`, forcings
`q¹, q²` of the class of (4.1), `WeakForcedSolution`s `Θ¹, Θ²` and `supSize(Θ¹ − Θ²) < ∞`), for
every `ε` with `0 < ε ≤ 1`, at almost every `s ∈ [0, T]`,
`ofReal(2 ∫ ∑_k δY_{k,s} (λ δf_{k,s} + δq^f_{k,s}) dP) ≤ ofReal(C/ε) ∫⁻ |δY_s|² dP
+ ofReal(ε) ∫⁻ (|δZ_s|²_F + ‖δU_s‖²) dP + ofReal(C/ε) ∫⁻ (|δX_s|² + |δq^f_s|²) dP`
with `C = K(T, L, ‖G‖, s_min(G)⁻², α, β₁, β₂, λ̲)` and `δf_s` the difference of the `driverProc`s.

Readings:

* The hypotheses are those in force at Step 4, the hypotheses of Lemma 4.3, written as in
  `lem_pert`: the class `WeakForcedSolution` (`ℍ_weak` with `X_T ∈ L²` and the integrals of (4.1)
  along `Θ^k` existing, reviewed in `definitions.md`); `ℱ₀`-measurability as measurability for
  the time-`0` field of `enlJoint`; `Θ¹ − Θ² ∈ ℍ` as the finiteness of `supSize`;
  `c_G = s_min(G)⁻²`. The sentence cites Assumption 2.3 and (2.8) only; the other hypotheses
  of Lemma 4.3 are in force at Step 4, and keeping them makes the reading weaker than a bound
  under Assumption 2.3 alone. The proof below uses Assumptions 2.3 and 2.5.
* The constant: `K` is chosen before everything else, so `C` is fixed before `ε` and independent
  of it, as printed. Its arguments are the broadest dependence the text allows: the §4 convention
  lists `T, L, ‖G‖, c_G, α, β₁, β₂` (`c_BDG` is a universal constant), and `λ̲` is added because
  the constant `C_B` of Lemma 4.3 depends on it. The constant the proof gives depends on `L`
  alone, so the bound holds under any narrower dependence the text could mean.
* The time: (4.25) is printed at a time `s` and used under `∫_t^T … ds`; the proposition asks it at
  almost every `s ∈ [0, T]` (Lebesgue), the weaker conclusion. Under `∫_t^T … ds`, which is how
  the proof uses it, the two readings give the same bound.
* The expectations: `𝔼⟨δY_s, λ δf_s + q^f_s⟩` is the Bochner integral of
  `∑_k (Y¹_{k,s} − Y²_{k,s})(λ (f¹ − f²)_{k,s} + (q^{f,1} − q^{f,2})_{k,s})`, read in `[0, ∞]`
  through `ENNReal.ofReal`, its positive part; the right side is in `[0, ∞]` (lower integrals of
  `esq`, `∑_k esq` for `|·|²_F`, `∑_k ∫⁻ |δU_k(e)|² ν(de)` for `‖·‖²_{L²(ν)}`). Harmless: when the
  right side is finite the extended inequality is the real one (a negative left side satisfies
  both); when it is infinite the printed inequality says nothing; a pairing that is not integrable
  (undefined in the paper) is read as `0`.
* `ofReal(C/ε)` reads a negative `C` as `0`; since `K` is existential and the right side grows
  with `C`, this is the reading with `C ≥ 0`, equivalent to the paper's positive `C`.
* `δf_s` is `driverProc P T C X¹ Y¹ Z¹ U¹ k ω s − driverProc P T C X² Y² Z² U² k ω s`: coordinate
  `k` of `f(s, Θ^k_s(ω), Law(Θ^k_s))` for `s ∈ [0, T]` (reviewed in `definitions.md`); `δq^f_s` is
  `qf₁ − qf₂`, as the proof's convention `q = δq` says.

Proof: `K = 2 (10 (2L)²) + 3`, a function of `L` alone, within the allowed dependence: at almost
every `s`, Young's inequality with weight `a = (2K' + 2)/ε` and the expected Lipschitz bound (3.2)
with `K' = 10 (2L)²` (`PairDiff.ae_backwardYoung_le`,
`PaperWeakSolutionForcedInt.ae_backwardYoung_le`); the terms `ε 𝔼|δX_s|²` and `ε 𝔼|δY_s|²` that
Young's inequality leaves are at most `(1/ε)` times the same expectations because `ε ≤ 1`. The
proof of Lemma 4.3 in the implementation does not use (4.25) (`Stability/BackwardEnergy.lean`).

Witness: `Dissertation.Acceptance.A.lem_pert_two_data_hypotheses`, the hypotheses of Lemma 4.3,
which are those of (4.25): at Example 5.1(i) over a Lévy driver with `d = 1`, `ν = δ₀`,
`𝒢₀ = ⊥`, `n = m = 1`, `T = 1`, the system with (2.3) and Assumptions 2.3–2.5 at `L = 1`,
`G = 1`, `α = β₁ = β₂ = 1`; `λ̲ = λ = 1`; the zero forcing; the initial data `0` and `e₁`; the
solutions of Theorem 3.5 from them, `WeakForcedSolution`s with `supSize(Θ¹ − Θ²) < ∞`.

Verdict: faithful.

<!-- spec-review: Dissertation.PaperSpec.A.eq_bwdyoung ed839d34f480cba13db23656421cf5a0 by=claude-author -->

## Lemma 4.4: `Dissertation.PaperSpec.A.lem_cont`

Manuscript (Lemma `lem:cont`): under Assumptions 2.2–2.5, with `λ*` the threshold of Lemma 4.2,
there is `ζ₀ > 0`, depending only on `T, L, ‖G‖, c_G, α, β₁, β₂, λ*` and `c_BDG`, such that if
`λ₀ ∈ [λ*, 1]` and `WP(λ₀)` holds, then `WP(λ₀ + ζ)` holds for every `ζ ∈ [0, ζ₀]` with
`λ₀ + ζ ≤ 1`.

Proposition: `∃ ζ₀` of the eight arguments; in the standing setting, for `T > 0`, under (2.3) and
Assumptions 2.2–2.5, for every `λ* ∈ (0, 1]`: `ζ₀(…, λ*) > 0` and the continuation step.

Correspondence: the proposition is broader than printed: it holds for every `λ* ∈ (0, 1]`, not
only the threshold of Lemma 4.2; the printed claim is its instance at that threshold (which lies
in `(0, 1]` by `lem_small`). The positivity of `ζ₀` is asserted in the situation of the lemma.

Witness: `Dissertation.Acceptance.A.lem_cont_hypotheses`: the hypotheses of the lemma at Example
5.1(i) (the instance of `thm_cwp_hypotheses`, with the datum `0`), together with `λ*` and `λ₀` both
equal to the constant `λ*(1, 1) ∈ (0, 1]` of Lemma 4.2, and `WP(λ₀)` there (from `lem_small`), so
the premise of the continuation step is met and the step is exercised.

Verdict: broader: `λ*` ranges over all of `(0, 1]`; the printed claim is its instance at the
threshold of Lemma 4.2.

<!-- spec-review: Dissertation.PaperSpec.A.lem_cont ed839d34f480cba15f6eb38f12c8d372 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.lem_cont--claude-reviewer--2026-10-17T12_25_19Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.lem_cont ed839d34f480cba15f6eb38f12c8d372 by=claude-reviewer -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.lem_cont--claude-auditor--2026-10-19T03_35_26Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.lem_cont ed839d34f480cba15f6eb38f12c8d372 by=claude-auditor -->

## Example 5.1(i): `Dissertation.PaperSpec.A.ex_concrete_i_ham`, `ex_concrete_i`, `ex_concrete_i_pairing`, `ex_concrete_i_wp`

Manuscript (§5, Example `ex:concrete`, part (i)): `n = m = d = 1`,
`G = 1`, `ν` σ-finite, `ξ₀ ∈ L²(Ω, ℱ₀; ℝⁿ)`, `σ_c ∈ ℝ`, `h_c ∈ L²(ν)`, `β₁, β₂ > 0`. The
Hamiltonian `H` of the control problem is strictly convex in the controls with pointwise minimiser
`a^{b*} = −β₁ y`, `a^{σ*} = −β₁ z`, `a^{h*} = −β₁ u`, "so by the stochastic maximum principle
for jump diffusions [TangLi]" the optimality system is (1.1) with `b = −β₁ y`, `σ = σ_c − β₁ z`,
`h = h_c − β₁ u`, `f = β₂ x`, `g(x, ρ) = x`. Assumptions 2.2 and 2.3 hold with
`L = max{β₁, β₂, 1}`; Assumption 2.4 with `c_G = 1`; the interior and terminal pairings of (2.7)
evaluate exactly to `−β₁ 𝔼[|δY|² + |δZ|²_F + ‖δU‖²] − β₂ 𝔼|δX|²` and `𝔼|δX_T|²`; Assumption 2.5
holds with equality and `α = 1`, "so Theorem 3.5 yields well-posedness"; the identity carries any
margin `0 < c < min{β₁, β₂}` (Remark 2.11), unweighted with the same constant since `c_G = 1`; and
`∫_E ⟨δh(e), δU(e)⟩ ν(de) = −β₁ ‖δU‖²`.

Propositions:

* `ex_concrete_i_ham`: for every measure `ν`, `β₁ > 0`, `β₂`, `σ_c`, `h_c` and `(x, y, z, u)`, the
  function `H` on `ℝ × ℝ^{1×1} × L²(ν)`, written as printed (the `ν`-integral of the pointwise
  products), is `StrictConvexOn` the whole space and is minimised at `(−β₁ y, −β₁ z, −β₁ u)`.
* `ex_concrete_i`: in the standing setting with `n = m = d = 1`, for `T > 0`, `β₁, β₂ > 0`,
  `σ_c`, `h_c` and `ξ₀` strongly measurable for the time-`0` field of `enlJoint` and in `L²`:
  (2.3), Assumption 2.2 (datum `ξ₀`), Assumption 2.3 with `max (max β₁ β₂) 1`,
  `rank 1 = min 1 1`, `(sMin 1 ^ 2)⁻¹ = 1`, and Assumption 2.5 with `G = 1`, `α = 1`, `β₁, β₂`.
* `ex_concrete_i_pairing`: in the same setting, for every `t` and all pairs of `𝒟_t`, the
  expectation of `pairing27 1` equals `−β₁ ∫ (|δY|² + |δZ|² + ‖δU‖²) − β₂ ∫ |δX|²`; for
  `X_T, X'_T ∈ L²(ℱ_T)`, `𝔼⟨δg_T, δX_T⟩ = 𝔼|δX_T|²`; for every `0 < c < min β₁ β₂`,
  `Margin213` with `(β₁ − c, β₂ − c)` and margin `c`; and the jump identity at all points, laws
  and times.
* `ex_concrete_i_wp`: in the same setting, the conclusion of Theorem 3.5 (as in `thm_cwp`) for the
  affine system and the datum `ξ₀`.

Correspondence:

* The coefficients are `affineCoeffs β₁ β₂ σ_c h_c` (reviewed in `definitions.md`); `σ_c ∈ ℝ` is
  a point of `ℝ^{1×1}` and `(σ_c + a^σ) z` its Frobenius pairing.
* "Assumption 2.4 holds with `c_G = 1`": the full rank of `G = 1` and `c_G = s_min(1)⁻² = 1`. "Both
  rank branches of Assumption 2.5 are available" is the admissibility of the constants, part of
  `Assumption25`.
* The pairings are stated for every `t`, not only almost every `t ∈ [0, T]` (the coefficients do
  not depend on `t`). The expectation of the interior pairing is a Bochner integral; its integrand
  is pointwise equal to the integrable right-hand side, and its integrability is also part of
  `Assumption25` in `ex_concrete_i`.
* The margin: Remark 2.11 turns a bound with constants `β̄₁, β̄₂` into (2.12) with
  `β_i = β̄_i − c` and margin `c`; at `G = 1` the unweighted (2.13) (`Margin213`, reviewed with
  Corollary 3.6) has the same constant, which is what the example asserts.
* The jump identity is printed without expectation; it is stated pointwise, at all points
  `θ, θ'`, laws `μ, μ'` and times `t`, with `δh(e), δU(e)` the differences of the representatives.
* Not formalised: the step "by the stochastic maximum principle [TangLi] the optimality system is
  (1.1)" is a statement about cited work; the proposition covers the Hamiltonian's convexity and
  minimiser, and the system itself is the definition `affineCoeffs`. The interpretation of
  `β₁, β₂` is exposition.

Witness: `Dissertation.Acceptance.A.ex_concrete_hypotheses` (the standing setting with `ν = δ₀`,
`𝒢₀ = ⊥` and the datum `0`; `T = 1`, `β₁ = β₂ = 1`). `ex_concrete_i_ham` has only `β₁ > 0`.

* "Unweighted with the same constant here because `G = 1` gives `c_G = 1`": at `G = 1`,
  `c_G = 1`, so by Remark 2.11 the unweighted margin has the same constant.

Verdict: `ex_concrete_i` and `ex_concrete_i_wp` faithful; `ex_concrete_i_ham` broader: it holds for
every measure `ν`, σ-finite or not, and every real `β₂`, and the printed claim is its instance at a
σ-finite `ν` and `β₂ > 0`; `ex_concrete_i_pairing` broader: the pairings hold at every `t`, the
printed claim being its instance at almost every `t ∈ [0, T]`.

<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_i_ham ed839d34f480cba1cf9f26355b828c6a by=claude-author -->
Review by claude-reviewer: broader (report `reports/Dissertation.PaperSpec.A.ex_concrete_i_ham--claude-reviewer--2026-10-17T12_16_01Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_i_ham ed839d34f480cba1cf9f26355b828c6a by=claude-reviewer -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.ex_concrete_i_ham--claude-auditor--2026-10-19T03_31_21Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_i_ham ed839d34f480cba1cf9f26355b828c6a by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_i ed839d34f480cba1d2f6e8919288ad6b by=claude-author -->
Review by claude-reviewer: faithful (report `reports/Dissertation.PaperSpec.A.ex_concrete_i--claude-reviewer--2026-10-17T12_13_03Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_i ed839d34f480cba1d2f6e8919288ad6b by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.ex_concrete_i--claude-auditor--2026-10-19T03_36_52Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_i ed839d34f480cba1d2f6e8919288ad6b by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_i_pairing ed839d34f480cba1272d037d1e16e040 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/Dissertation.PaperSpec.A.ex_concrete_i_pairing--claude-reviewer--2026-10-17T16_05_52Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_i_pairing ed839d34f480cba1272d037d1e16e040 by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.ex_concrete_i_pairing--claude-auditor--2026-10-19T03_38_21Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_i_pairing ed839d34f480cba1272d037d1e16e040 by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_i_wp ed839d34f480cba13343e4213bb7f62d by=claude-author -->
Review by claude-reviewer: faithful (report `reports/Dissertation.PaperSpec.A.ex_concrete_i_wp--claude-reviewer--2026-10-17T16_05_52Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_i_wp ed839d34f480cba13343e4213bb7f62d by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.ex_concrete_i_wp--claude-auditor--2026-10-19T03_37_01Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_i_wp ed839d34f480cba13343e4213bb7f62d by=claude-auditor -->

## Example 5.1(i) with the drift (3.6): `Dissertation.PaperSpec.A.ex_concrete_i_clamp`, `ex_concrete_i_clamp_wp`

Manuscript (Example `ex:concrete`, end of part (i)): replacing the drift `−β₁ y` of the baseline
by (3.6) "leaves (2.7) intact with constants `(β₁ − ε, β₂)`, so Theorem 3.5 continues to apply".

Propositions: in the setting of `ex_concrete_i`, for `0 < ε < β₁`, the system
`clampAffineCoeffs β₁ β₂ ε σ_c h_c` satisfies (2.3), Assumption 2.2, Assumption 2.3 with some `L`,
`rank 1 = min 1 1`, and Assumption 2.5 with `G = 1`, `α = 1` and `(β₁ − ε, β₂)`
(`ex_concrete_i_clamp`); and it has the conclusion of Theorem 3.5 (`ex_concrete_i_clamp_wp`).

Correspondence: the range `0 < ε < β₁` is that of Proposition 3.8, where (3.6) is introduced, and
keeps `β₁ − ε > 0`. "Theorem 3.5 continues to apply" is read as its hypotheses holding
(`ex_concrete_i_clamp`) and hence its conclusion (`ex_concrete_i_clamp_wp`); the example names no
Lipschitz constant, so `L` is existential (Proposition 3.8 gives `β₁ + ε` for the drift).

Witness: `Dissertation.Acceptance.A.ex_concrete_hypotheses` (also `ε = 1/2 < β₁ = 1`).

Verdict: faithful.

<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_i_clamp ed839d34f480cba1f386f903a2799dd0 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/Dissertation.PaperSpec.A.ex_concrete_i_clamp--claude-reviewer--2026-10-17T12_14_00Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_i_clamp ed839d34f480cba1f386f903a2799dd0 by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.ex_concrete_i_clamp--claude-auditor--2026-10-19T03_38_15Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_i_clamp ed839d34f480cba1f386f903a2799dd0 by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_i_clamp_wp ed839d34f480cba14bccae170a8d514d by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.ex_concrete_i_clamp_wp--claude-reviewer--2026-10-17T12_15_11Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_i_clamp_wp ed839d34f480cba14bccae170a8d514d by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.ex_concrete_i_clamp_wp--claude-auditor--2026-10-19T03_38_30Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_i_clamp_wp ed839d34f480cba14bccae170a8d514d by=claude-auditor -->

## Example 5.1(ii): `Dissertation.PaperSpec.A.ex_concrete_ii_mean`, `ex_concrete_ii`, `ex_concrete_ii_pairing`

Manuscript (Example `ex:concrete`, part (ii)): `m_Ψ(μ) = ∫_H π_Ψ(θ) μ(dθ)`,
`𝔟(ρ) = ∫ x ρ(dx)`; `b = −2y − m_Y(μ)`, `σ = −2z − m_Z(μ)`, `h(e) = −2u(e) − m_U(μ)(e)`,
`f = 2x + m_X(μ)`, `g(x, ρ) = 2x + 𝔟(ρ)`, with `n = m = d = 1`, `G = 1`; `δm = (δm_X, δm_Y,
δm_Z, δm_U) = ∫ θ dμ − ∫ θ dμ'`. Claims: `|δm|_H ≤ W₂(μ, μ')`, `|𝔟(ρ) − 𝔟(ρ')| ≤ W₂(ρ, ρ')`,
`|δm_X| + |δm_Y| + |δm_Z|_F + ‖δm_U‖ ≤ 2 |δm|_H ≤ 2 W₂(μ, μ')`; "thus Assumption 2.3 holds with
`L = 2`"; `b, σ, h, f` vanish at `(0, δ₀)`, so Assumption 2.2 is immediate; along a diagonal pair
`m_Ψ(Law Θ) = 𝔼Ψ`, the four channel identities `𝔼⟨−δf, δX⟩ = −2 𝔼|δX|² − |𝔼 δX|²` (and for
`b, σ, h`), their sum, and `𝔼⟨δg_T, δX_T⟩ = 2 𝔼|δX_T|² + |𝔼 δX_T|²`; "Assumption 2.5 therefore
holds with `α = β₁ = β₂ = 2`"; for arbitrary σ-finite `ν`, including `ν(E) = ∞`.

Propositions:

* `ex_concrete_ii_mean`: for every σ-finite `ν` on a countably generated space and all
  `μ, μ' ∈ P₂(H)`, `ρ, ρ' ∈ P₂(ℝ)`: the channels of `tupleMean μ` are the four marginal means
  (Bochner integrals of the projections); `‖toL2 δm‖ ≤ w2H μ μ'`; the sum of the four channel norms
  of `δm` is at most `2 ‖toL2 δm‖`; `‖𝔟(ρ) − 𝔟(ρ')‖ ≤ w2P ρ ρ'`.
* `ex_concrete_ii`: in the standing setting with `n = m = d = 1`, for `T > 0` and `ξ₀ ∈ L²(ℱ₀)`:
  (2.3); `b, σ, h, f` vanish at `(t, 0, δ₀)` for every `t`; Assumption 2.2; Assumption 2.3 with
  `L = 2`; `rank 1 = min 1 1`; Assumption 2.5 with `G = 1` and `α = β₁ = β₂ = 2`.
* `ex_concrete_ii_pairing`: in the same setting, for every `t` and all pairs of `𝒟_t`:
  `tupleMean μ = 𝔼 Θ`; the four channel identities; the identity for `pairing27 1`; and the
  terminal identity for `X_T, X'_T ∈ L²(ℱ_T)`.

Correspondence:

* The coefficients are `meanFieldCoeffs ν 1 1`, with `tupleMean` and `barycentre` (reviewed in
  `definitions.md`); their channels are the printed `m_Ψ` by the first clause of
  `ex_concrete_ii_mean`. `|·|_H` is the Hilbert norm (`toL2`), `W₂` is `w2H` on `P₂(H)` and `w2P`
  on `P₂(ℝ)`.
* `2 |δm|_H ≤ 2 W₂(μ, μ')` is twice the first bound and is not restated.
* The example asserts (2.3) only through "meeting every assumption" in the section's opening; the
  proposition includes it.
* The inequalities `≤ −2 𝔼[…]` and `≥ 2 𝔼|δX_T|²` drawn from the identities are Assumption 2.5
  with `α = β₁ = β₂ = 2`, in `ex_concrete_ii`.
* The comparison with [LiMin, Example 3.1, (H3.2) and Theorem 3.1] is a statement about cited work
  and is not formalised; the arbitrary σ-finite `ν`, including infinite mass, is the quantifier
  over `ν`.

Witness: `Dissertation.Acceptance.A.ex_concrete_hypotheses` (setting and datum `0`).
`ex_concrete_ii_mean` has no hypotheses beyond the σ-finite `ν` on a countably generated space.

Verdict: faithful ((2.3) and the pairings at every `t`: broader).

<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_ii_mean ed839d34f480cba1adb40add6e4f8112 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/Dissertation.PaperSpec.A.ex_concrete_ii_mean--claude-reviewer--2026-10-17T12_19_08Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_ii_mean ed839d34f480cba1adb40add6e4f8112 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.ex_concrete_ii_mean--claude-auditor--2026-10-19T03_31_21Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_ii_mean ed839d34f480cba1adb40add6e4f8112 by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_ii ed839d34f480cba1cba84bcbe1866633 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/Dissertation.PaperSpec.A.ex_concrete_ii--claude-reviewer--2026-10-17T12_18_31Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_ii ed839d34f480cba1cba84bcbe1866633 by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.ex_concrete_ii--claude-auditor--2026-10-19T03_34_14Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_ii ed839d34f480cba1cba84bcbe1866633 by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_ii_pairing ed839d34f480cba16aa5f84a4f3328b5 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/Dissertation.PaperSpec.A.ex_concrete_ii_pairing--claude-reviewer--2026-10-17T16_05_52Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_ii_pairing ed839d34f480cba16aa5f84a4f3328b5 by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.ex_concrete_ii_pairing--claude-auditor--2026-10-19T03_33_35Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_ii_pairing ed839d34f480cba16aa5f84a4f3328b5 by=claude-auditor -->

## Example 5.2: `Dissertation.PaperSpec.A.ex_brownian`

Manuscript (Example `ex:brownian`): remove the Poisson channel, so that the filtration is
generated by `W` and `ℱ₀` and the representation property is the Brownian one; delete the
`U`-coordinate, reducing `H` to `ℝⁿ × ℝᵐ × ℝ^{m×d}` ("merely setting `h ≡ 0` on a
Brownian–Poisson basis is not a reduction"). The assumptions reduce to `W₂`-Lipschitz joint-law
dependence of `(X, Y, Z)` under `G`-monotonicity, the condition of [BYZ, (A1)]; with no jump
channel the `U`-dissipativity constraint of Remark 2.10 is vacuous, so both rank branches of
Assumption 2.5 are available.

Proposition: in the standing setting with `ν = 0` (any `d`, any countably generated `E`):
(a) `enlJoint 𝒢₀ D = augFiltration (ℱ^W ⊔ 𝒢₀)₊ P`, the usual augmentation of the filtration
generated by `W` and `𝒢₀`; (b) every `u ∈ L²(0; ℝᵐ)` is `0`; (b') for all `μ, μ' ∈ P₂(H)`,
`w2P (projP2 μ) (projP2 μ') = w2H μ μ'`: `W₂` on `P₂(H)` is `W₂` on the laws of `(X, Y, Z)` in
`ℝⁿ × ℝᵐ × ℝ^{m×d}` with its Euclidean norm; (c) for `1 ≤ m < n`, `d ≥ 1`,
`T > 0` and `ξ₀ ∈ L²(ℱ₀)` there are `G` of full rank and coefficients whose jump coefficient
depends on `(t, θ, μ)` only through `(t, x)` (the additive form `h(t, x, e)` of Remark 2.10), with
(2.3) and Assumptions 2.2–2.5 for some `L, α, β₁, β₂` with `β₁ > 0`.

Correspondence:

* "Remove the Poisson channel" is read as the standing setting at `ν = 0`. Clause (a) shows that
  it is the Brownian basis of the example: the Poisson measure of intensity `0`
  vanishes almost surely, so its natural filtration consists of null and conull sets and
  disappears in the augmentation. Clause (b) is the deletion of the `U`-coordinate: `H` is
  `ℝⁿ × ℝᵐ × ℝ^{m×d} × {0}`, and the Poisson integrals and `U` vanish.
* "The assumptions reduce to `W₂`-Lipschitz joint-law dependence of `(X, Y, Z)`": clause (b') is
  the reduction of the distance in which Assumption 2.3 measures the law dependence; `projP2` is
  the image law under `(x, y, z, u) ↦ (x, y, z)` (reviewed in `definitions.md`).
* "Both rank branches are available": the branch `m ≥ n` does not depend on the jump channel
  (Example 5.1(i) is an instance at every `ν`); the branch `m < n` is the one Remark 2.10 closes at
  `ν ≠ 0` for jump coefficients of the additive form. Clause (c) exhibits it at `ν = 0` for every
  `1 ≤ m < n` with such a jump coefficient (every jump coefficient is `0` there); the proof uses
  the linear generator with `G` the diagonal matrix, `α = β₁ = 1`, `β₂ = 0`.
* Not formalised: the identification of the reduced assumptions with the condition of [BYZ, (A1)]
  (a statement about cited work). The remark that `h ≡ 0` on a Brownian–Poisson basis is not a
  reduction, which this review earlier set aside as exposition, is a statement about the
  representation property; it is `ex_brownian_not_h0`, and the branch `m > n` is
  `ex_brownian_rank_gt` (both reviewed below). The reduction itself (the
  assumptions and the solution notions at `ν = 0` coincide with their Brownian forms) and the
  Brownian representation property are `ex_brownian_reduction` and `ex_brownian_prp`, reviewed
  below.

Witness: `Dissertation.Acceptance.A.ex_brownian_hypotheses` (a Lévy driver with `ν = 0` on `ℝ`,
`d = 1`, `𝒢₀ = ⊥`, `m = 1 < n = 2`, datum `0`).

Verdict: faithful.

<!-- spec-review: Dissertation.PaperSpec.A.ex_brownian ed839d34f480cba13b36df98cbfaee33 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.ex_brownian--claude-reviewer--2026-10-17T12_10_35Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_brownian ed839d34f480cba13b36df98cbfaee33 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.ex_brownian--claude-auditor--2026-10-19T03_34_12Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_brownian ed839d34f480cba13b36df98cbfaee33 by=claude-auditor -->

## Example 5.3: `Dissertation.PaperSpec.A.ex_expfunc`, `ex_expfunc_limin`, `ex_expfunc_jump`

Manuscript (Example `ex:expfunc`): `φ̄ : [0, T] × H × H → ℝᵏ` measurable and Lipschitz in
`(θ, θ')` uniformly in `t`, and `φ(t, θ, μ) = ∫_H φ̄(t, θ, θ') μ(dθ')`: at fixed `t, θ` this is the
Bochner mean of `φ̄(t, θ, ·)`, whose Lipschitz constant is at most `Lip(φ̄)`, so (2.10) supplies
the law-dependence component of Assumption 2.3. For the independent-copy interactions of [LiMin],
with `ψ̄` Lipschitz in all arguments but `t`, and `φ̄(t, θ, θ') = ∫_E ψ̄(t, x, y, z, u(e), x', y',
z', u'(e)) ν(de)`: the integral is finite at every `(θ, θ')`; with a constant finite when
`ν(E) < ∞`, `|φ̄(t, θ₁, θ₁') − φ̄(t, θ₂, θ₂')| ≤ Lip(ψ̄) max{ν(E), ν(E)^{1/2}} (|θ₁ − θ₂|_H +
|θ₁' − θ₂'|_H)`; the functional is well defined on equivalence classes. The jump coefficient
embeds through the Nemytskii map `[𝐇_t(θ, θ')](e) = h̄(t, x, y, z, u(e), x', y', z', u'(e), e)`,
again well defined on classes; assumed jointly Borel, Lipschitz into `L²(ν)` with constant `C`
and with `∫_0^T ‖𝐇_t(0, 0)‖² dt < ∞`, (2.10) applies with `K = L²(ν; ℝⁿ)` to
`h(t, θ, μ) = ∫_H 𝐇_t(θ, θ') μ(dθ')`.

Propositions:

* `ex_expfunc`: for σ-finite `ν` on a countably generated space, all `n, m, d, k`, `φ̄` into
  `ℝᵏ` jointly measurable on `ℝ × H × H` with `‖φ̄(t, θ₁, θ₁') − φ̄(t, θ₂, θ₂')‖ ≤
  L (‖toL2 θ₁ − toL2 θ₂‖ + ‖toL2 θ₁' − toL2 θ₂'‖)`, `L ≥ 0`: for every `t, θ`, `φ̄(t, θ, ·)` is
  `L`-Lipschitz for the Hilbert norm, and `‖∫ φ̄(t, θ, ·) dμ − ∫ φ̄(t, θ, ·) dμ'‖ ≤ L · w2H μ μ'`.
* `ex_expfunc_limin`: for a finite `ν`, `ψ̄ : ℝ × B × B → ℝᵏ` (`B = ℝⁿ × ℝᵐ × ℝ^{m×d} × ℝᵐ`)
  with `‖ψ̄(t, a, a') − ψ̄(t, b, b')‖ ≤ Lip ((Σ ‖aᵢ − bᵢ‖²)^{1/2} + (Σ ‖a'ᵢ − b'ᵢ‖²)^{1/2})`,
  `Lip ≥ 0`: at every `t`, the integrand is `ν`-integrable at all `θ, θ'`; the Lipschitz bound
  with constant `Lip · max(ν.real univ, √(ν.real univ))`; and the integral with representatives
  `v =ᵐ u`, `v' =ᵐ u'` equals the one with `u, u'`.
* `ex_expfunc_jump`: for σ-finite `ν` on a countably generated space and `h̄ : ℝ × B × B × E →
  ℝⁿ`: representatives `v =ᵐ u`, `v' =ᵐ u'` give Nemytskii maps equal `ν`-a.e.; and every
  `𝐇 : ℝ × H × H → L²(ν; ℝⁿ)` representing the Nemytskii map and Lipschitz with constant `C ≥ 0`
  gives `‖∫ 𝐇_t(θ, ·) dμ − ∫ 𝐇_t(θ, ·) dμ'‖_{L²(ν)} ≤ C · w2H μ μ'`.

Correspondence:

* "Lipschitz in `(θ, θ')`" is read as the sum form printed for `φ̄` in the [LiMin] display, with
  `|·|_H` the Hilbert norm (`toL2`); `Lip(φ̄)` is any Lipschitz constant, the least one an
  instance. The target `ℝᵏ` is `EuclideanSpace ℝ (Fin k)`; the diffusion kernel with values in
  `ℝ^{n×d}` is the instance `k = nd`.
* The Euclidean norm on each argument block `(x, y, z, u(e))` is written out as the square root
  of the sum of the four squared channel distances. With it the printed constant is exact; for
  the sum of the channel norms it would be twice as large.
* The finiteness "at every `(θ, θ')`" is the integrability of the integrand; the intermediate
  bound `∫ (|u| + |u'|) dν ≤ ν(E)^{1/2}(‖u‖ + ‖u'‖)` and the origin term are steps of its proof.
  The square-integrable origin values of `ψ̄` and the joint Borel measurability and origin
  integrability of `𝐇` serve Assumptions 2.2 and 2.3 of the full coefficient system, which the
  example leaves to that system ("imposed on the full coefficient system"); the propositions do
  not assume them, so they are broader.
* "Well defined on equivalence classes" is independence of the representatives of `u, u'`.
* Not formalised: that the class contains the interactions of [LiMin] and that their Lévy
  measure is the `ν` of the setting (statements about cited work).

Witnesses: `Dissertation.Acceptance.A.ex_expfunc_hypotheses`, `ex_expfunc_limin_hypotheses`,
`ex_expfunc_jump_hypotheses`, at `ν = δ₀` on `ℝ`, `n = m = d = k = 1` and the interaction kernel
`x − x'` (for the jump coefficient through the library's Nemytskii class, with constant
`max(1, ν(E)^{1/2})`).

* "Lipschitz in all arguments except `t`" names no norm on the argument blocks; the propositions
  take the Euclidean norm on each block. Another norm on these finite-dimensional blocks changes
  the Lipschitz constant by a fixed factor: a representation choice.

Verdict: `ex_expfunc` faithful with representation choices (the sum form of the Lipschitz condition,
with the Hilbert norm of `H`). `ex_expfunc_limin` and `ex_expfunc_jump` broader, with the block norm
as representation choice: they do not assume the square-integrable origin values of `ψ̄`, nor the
joint Borel measurability and the origin integrability `∫_0^T ‖𝐇_t(0, 0)‖² dt < ∞` of `𝐇` (no
measurability of `ψ̄` or `h̄` either), which the example imposes for the full coefficient system;
the printed claims are their instances at kernels with those properties.

<!-- spec-review: Dissertation.PaperSpec.A.ex_expfunc ed839d34f480cba1c0ebc41bbfe679cc by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.ex_expfunc--claude-reviewer--2026-10-17T12_20_36Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_expfunc ed839d34f480cba1c0ebc41bbfe679cc by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.ex_expfunc--claude-auditor--2026-10-19T03_34_12Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_expfunc ed839d34f480cba1c0ebc41bbfe679cc by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_expfunc_limin ed839d34f480cba1dc8d682dbdc81fa7 by=claude-author -->
Review by claude-reviewer: broader (report `reports/Dissertation.PaperSpec.A.ex_expfunc_limin--claude-reviewer--2026-10-17T16_03_52Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_expfunc_limin ed839d34f480cba1dc8d682dbdc81fa7 by=claude-reviewer -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.ex_expfunc_limin--claude-auditor--2026-10-19T03_34_13Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_expfunc_limin ed839d34f480cba1dc8d682dbdc81fa7 by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_expfunc_jump ed839d34f480cba1e622a1683bfc9f0d by=claude-author -->
Review by claude-reviewer: broader (report `reports/Dissertation.PaperSpec.A.ex_expfunc_jump--claude-reviewer--2026-10-17T16_03_52Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_expfunc_jump ed839d34f480cba1e622a1683bfc9f0d by=claude-reviewer -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.ex_expfunc_jump--claude-auditor--2026-10-19T03_31_22Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_expfunc_jump ed839d34f480cba1e622a1683bfc9f0d by=claude-auditor -->

## Remarks 2.7–2.9: `Dissertation.PaperSpec.A.rem_diag_mono`, `rem_diag_mono_converse`, `rem_intrinsic_uniform`, `rem_intrinsic_coupling`, `rem_intrinsic_basis`

Manuscript: Remark 2.7 (`rem:G-pairing`) explains the role of the full-rank `G`; its mathematical
content, `G`-coercivity controlling the forward variables when `m ≥ n` and the backward ones when
`n ≥ m`, is the bounds of Assumption 2.4 (claim `A:ass:G`, proposition `ass_G`), so the claim is
recorded as a duplicate of `A:ass:G`. Remark 2.8 (`rem:diag-mono`): the pointwise form of (2.7)
gives Assumption 2.5 by taking expectations, and the converse fails (Proposition 3.8); Examples
5.1(i) and 5.4 verify Assumption 2.5 exactly and perturbatively. Remark 2.9 (`rem:intrinsic`): for
`t > 0`, `ℱ_t` supports a uniform variable, a function of `W¹_t`; every coupling of two laws in
`P₂(H)` is the joint law of two `ℱ_t`-measurable inputs (Kallenberg, Lemma 4.22); so Assumptions
2.3 and 2.5 are properties of the coefficients, not of the basis; no richness of `ℱ_0` is needed;
the proofs use only the expected diagonal form.

Propositions:

* `rem_diag_mono` — Remark 2.8, first half, under (2.3): the pointwise inequality at almost
  every `t`, all points and laws, gives at almost every `t` and all inputs of `𝒟_t` that the
  positive part of the pairing has finite expectation (so the expectation of the pairing exists in
  `[−∞, ∞)`) and that, when the pairing is integrable, its expectation satisfies (2.7); and, if
  Assumption 2.3 holds with some `L`, (2.7) in the form of Assumption 2.5 (`Mono27At`, the
  expectation of the pairing existing) at almost every `t`.
* `rem_diag_mono_converse` — Remark 2.8, second half: at `n = m = d = 1` and every `T > 0`, the
  system of Proposition 3.8 (Example 5.1(i) with the drift (3.6), `β₁ = 2`, `β₂ = 1`, `ε = 1`)
  satisfies (2.3), Assumption 2.3 and Assumption 2.5 at `G = 1`, and for no `β ≥ 0`, `β'` the
  pointwise inequality.
* `rem_intrinsic_uniform`, `rem_intrinsic_coupling` — Remark 2.9, the uniform variable
  `Φ(W¹_t / √t)` and the realisation of couplings, over `enlJoint 𝒢₀ D h𝒢₀`, `d ≥ 1`, `t > 0`.
* `rem_intrinsic_basis` — Remark 2.9, "intrinsic": for two standing bases with the same `ν`, `d ≥ 1`
  and any `𝒢₀, 𝒢₀'` (no condition on `ℱ_0`), coefficients with (2.3) and `T > 0`, Assumption 2.3
  with a constant `L` holds over one exactly when over the other, and so does Assumption 2.5 with
  given `G, α, β₁, β₂`.

Correspondence:

* (2.7), (2.12), (2.13) are read with the expectation of the pairing existing (`Mono27At`,
  `Margin212`, `Margin213`). The printed step of Remark 2.8 ("taking expectations") holds without
  further hypotheses in the extended reading: the positive part of the pairing is bounded by the
  integrable right-hand side, so its expectation exists in `[−∞, ∞)`, and it is `−∞` exactly when
  the pairing is not integrable. The first conjunct of `rem_diag_mono` states this reading with
  only (2.3) standing. The second gives Assumption 2.5's own form, which asks the pairing to be
  integrable; that needs a growth bound, supplied by Assumption 2.3, which holds wherever
  Assumption 2.5 is used: without one the pairing need not be integrable (`b = −y − y³` along
  `Y ∈ L² \ L⁴`). So the proposition is the printed claim in the extended reading together with
  its form under Assumption 2.3, and is broader than either reading alone.
* Remark 2.9's basis independence is unconditional given (2.3), for Assumption 2.3 and for
  Assumption 2.5 with the integrability of its pairings, which is also a property of the joint law
  of the inputs. Without (2.3) an integrand on `H × H` need not be measurable for a coupling, which
  is why (2.3) is assumed, as it is standing in the paper. "The proofs use only the expected diagonal
  form" is a statement about the proofs, not formalised.

Witnesses: `Dissertation.Acceptance.A.rem_affine_hypotheses` (Example 5.1(i) with `β₁ = β₂ = 1`
over a Lévy driver with `d = 1`, `ν = δ₀ ≠ 0`, `𝒢₀ = ⊥`, `T = 1`: (2.3), Assumption 2.3, the
pointwise condition, Assumption 2.5 with `G = 1`, and `0 < 1/2 < 1`); `rem_coupling_hypotheses`
(`δ_{(0,0)}` couples `δ₀` with itself); `ex_concrete_hypotheses`, `ex_brownian_hypotheses`.

Verdict: `rem_diag_mono` and `rem_diag_mono_converse` faithful, with the readings listed (both
readings of (2.7) in Remark 2.8). `rem_intrinsic_uniform`, `rem_intrinsic_coupling` and
`rem_intrinsic_basis` broader: none assumes `𝒢₀` independent of the driver (the standing `hind₀`),
so they hold over `enlJoint 𝒢₀ D h𝒢₀` for every `𝒢₀`, the first two at every `t > 0` (and
`rem_intrinsic_uniform` for every σ-finite `ν`, countably generated or not); the printed claims are
their instances over the standing basis, with `𝒢₀` independent of the driver.

<!-- spec-review: Dissertation.PaperSpec.A.rem_diag_mono ed839d34f480cba146c1633f8e03b86c by=claude-author -->
Review by claude-reviewer: broader (report `reports/Dissertation.PaperSpec.A.rem_diag_mono--claude-reviewer--2026-10-17T16_05_52Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.rem_diag_mono ed839d34f480cba146c1633f8e03b86c by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.rem_diag_mono--claude-auditor--2026-10-19T03_34_01Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.rem_diag_mono ed839d34f480cba146c1633f8e03b86c by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.rem_diag_mono_converse ed839d34f480cba14b5e4594e14d9dc7 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/Dissertation.PaperSpec.A.rem_diag_mono_converse--claude-reviewer--2026-10-17T16_05_52Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.rem_diag_mono_converse ed839d34f480cba14b5e4594e14d9dc7 by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.rem_diag_mono_converse--claude-auditor--2026-10-19T03_36_03Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.rem_diag_mono_converse ed839d34f480cba14b5e4594e14d9dc7 by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.rem_intrinsic_uniform ed839d34f480cba13b7a9a5f65a5b218 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/Dissertation.PaperSpec.A.rem_intrinsic_uniform--claude-reviewer--2026-10-17T16_03_52Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.rem_intrinsic_uniform ed839d34f480cba13b7a9a5f65a5b218 by=claude-reviewer -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.rem_intrinsic_uniform--claude-auditor--2026-10-19T03_31_22Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.rem_intrinsic_uniform ed839d34f480cba13b7a9a5f65a5b218 by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.rem_intrinsic_coupling ed839d34f480cba1ff8eb9ca359fa48b by=claude-author -->
Review by claude-reviewer: faithful (report `reports/Dissertation.PaperSpec.A.rem_intrinsic_coupling--claude-reviewer--2026-10-17T16_03_53Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.rem_intrinsic_coupling ed839d34f480cba1ff8eb9ca359fa48b by=claude-reviewer -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.rem_intrinsic_coupling--claude-auditor--2026-10-19T03_36_39Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.rem_intrinsic_coupling ed839d34f480cba1ff8eb9ca359fa48b by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.rem_intrinsic_basis ed839d34f480cba132c02ed3a09a0eba by=claude-author -->
Review by claude-reviewer: broader (report `reports/Dissertation.PaperSpec.A.rem_intrinsic_basis--claude-reviewer--2026-10-17T16_05_52Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.rem_intrinsic_basis ed839d34f480cba132c02ed3a09a0eba by=claude-reviewer -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.rem_intrinsic_basis--claude-auditor--2026-10-19T03_34_37Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.rem_intrinsic_basis ed839d34f480cba132c02ed3a09a0eba by=claude-auditor -->

## The displays (1.1), (2.3), (4.1)

The displays (1.1), (2.3) and (4.1) define objects and are recorded with scope `definition`: (1.1)
is the system whose solutions in the space `ℍ` of Section 3 are `Dissertation.PaperSpec.A.Solution`;
(2.3) is the joint Borel measurability `Dissertation.WellPosedness.Spec.JointBorel`; (4.1) is the
forced system whose solutions are `Dissertation.PaperSpec.A.ForcedSolution`. These definitions are
reviewed in `definitions.md`.

Verdict: faithful.

## Section 2, the setting: `Dissertation.PaperSpec.A.sec2_separable`, `sec2_infinite_activity`, `eq_compid`, `eq_zeromean`, `sec2_prp`, `sec2_hborel`

Manuscript (§2, `sec:main-assumptions`): `ν` σ-finite on a countably generated `(E, ℰ)`, "so that
`L²(ν; ℝʲ)` is separable for every `j ≥ 1`" (`A:sec2:separable-L2nu`); the infinite-activity
regime, "in which `N` has infinitely many atoms on every nondegenerate time interval"
(`A:sec2:infinite-activity-atoms`); the compensation formula (2.1) for predictable `ψ ≥ 0`, in
`[0, ∞]` (`A:eq:compid`); the zero mean (2.2) of the compensated integral whenever
`𝔼 ∫_0^T ∫_E |ψ| ν(de) ds < ∞` (`A:eq:zeromean`); the predictable representation property of the
filtration of `W` and `N`, passed to the independent initial enlargement by `ℱ₀`: every
square-integrable `(ℱ_t)`-martingale is `M_0 + ∫ Z dW + ∫∫ U dÑ` for every `t ∈ [0, T]`, with
`M_0` `ℱ₀`-measurable and `(Z, U)` predictable square integrable, unique up to null sets
(`A:sec2:prp`); and the paragraph after (2.3): joint pointwise measurability of
`(t, θ, e, μ) ↦ h(t, θ, e, μ)` gives (2.3), "by Tonelli" and the Pettis theorem
(`A:sec2:hborel-derivation`).

Propositions:

* `sec2_separable` — for `ν` σ-finite on a countably generated space and `j ≥ 1`,
  `L²(ν; ℝʲ)` is separable.
* `sec2_infinite_activity` — for a Lévy driver with `ν(E) = ∞`, almost surely
  `N((s, t] × E) = ∞` for all `0 ≤ s < t`.
* `eq_compid` — over the filtration of §2 (`enlJoint`, `ℱ₀ = 𝒢₀` independent of the driver), for
  `ψ : Ω × ℝ × E → [0, ∞]` measurable for the marked predictable σ-algebra and every `T`,
  `𝔼 ∫_{(0, T] × E} ψ dN = 𝔼 ∫_{(0, T]} ∫_E ψ ν(de) ds`.
* `eq_zeromean` — in the same setting, for real `ψ` measurable for the marked predictable
  σ-algebra with `𝔼 ∫_{(0, T]} ∫_E |ψ| ν(de) ds < ∞`,
  `𝔼 (∫_{(0, T] × E} ψ dN − ∫_{(0, T]} ∫_E ψ ν(de) ds) = 0`.
* `sec2_prp` — for `d ≥ 1`, `T > 0` and a real martingale `M` of the filtration of §2 with
  `M_t ∈ L²` for every `t`: some pair `(Z, U)` represents `M` on `[0, T]` (`RepresentsMart`:
  predictable, finite energy, vanishing off `[0, T]`, and `M_t = M_0 + ∫_0^t Z dW + ∫_0^t ∫ U dÑ`
  almost surely for every `t ∈ [0, T]`, with the stochastic integrals of the solution notion); and
  any two representing pairs have differences of zero energy.
* `sec2_hborel` — for coefficients `C` and `H : ([0, T] × H × P₂(H)) × E → ℝⁿ` measurable for the
  Borel σ-algebra of `[0, T] × H × P₂(H)` (with `W₂` of the Hilbert norm) times `ℰ`, whose
  `e`-sections represent `C.h` in `L²(ν)`, the map `(t, θ, μ) ↦ h(t, θ, ·, μ)` is Borel
  measurable into `L²(ν; ℝⁿ)`.

Readings:

* "Infinitely many atoms" is read as `N((s, t] × E) = ∞`, the count of the integer-valued random
  measure on the interval; the library's Poisson random measure is a random measure with Poisson
  counts, without a representation as a sum of Dirac masses, so the atoms themselves are not
  formalised. The time intervals are those of `[0, ∞)`, on which `N` lives. The statement holds
  simultaneously for all intervals, almost surely.
* "Predictable `ψ`" in (2.1)–(2.2) is measurability for `markedPredictableSigma`, the σ-algebra
  `𝒫 ⊗ ℰ` generated by `F × (r, q] × B` with `F ∈ ℱ_r` (reviewed in `definitions.md`). The
  integral against `N` is over `(0, T] × E`; the integral in time over `(0, T]` (Lebesgue measure
  does not see the endpoint).
* In (2.2) the compensated integral of an integrand with `𝔼 ∫∫ |ψ| ν ds < ∞` is read pathwise as
  `∫ ψ dN − ∫∫ ψ ν ds`; by (2.1) both terms are finite almost surely. The `L²` compensated
  integral of the solution notion agrees with it when both exist; that agreement is not part of
  the claim.
* The predictable representation property is stated for real-valued martingales; a vector
  martingale is represented coordinatewise. "For every `t ∈ [0, T]`" is read as almost surely for
  each `t`; "unique up to null sets" as the energies of the differences of the integrands being
  zero, i.e. equality `dt ⊗ dP`-almost everywhere (resp. `dt ⊗ dP ⊗ ν`), among pairs representing
  `M` on `[0, T]`. `M_0` is `ℱ₀`-measurable because a martingale is adapted. The standing
  `d ≥ 1` and `T > 0` of the paper are hypotheses.
* In the paragraph after (2.3), "joint pointwise measurability" is measurability for
  `borel([0, T] × H × P₂(H)) ⊗ ℰ`; the proof goes through the distances
  `x ↦ ‖h(x) − y‖_{L²(ν)}`, measurable by Tonelli, and the separability of `L²(ν)`, in place of
  the paper's weak measurability and the Pettis theorem.

Witnesses: `sec2_infinite_activity_hypotheses` (Lebesgue measure on `ℝ` has infinite mass and
carries a Lévy driver). The following witnesses replace, for (2.1), (2.2), the representation
property and the paragraph after (2.3), the earlier ones
(`sec2_setting_hypotheses` with the zero martingale and `ψ = 0`, `sec2_hborel_hypotheses` with
`h = 0`), which exercised only zero conclusions and remain theorems; each is over a
Lévy driver with `d = 1`, `ν = δ₀` on `ℝ`, `𝒢₀ = ⊥`:

* `sec2_compensation_nonzero_hypotheses` (for `eq_compid` and `eq_zeromean`): the integrand
  `ψ_s(e) = 1_{(0, 1]}(s)`, as a real function and through `ofReal` as an `[0, ∞]`-valued one, is
  measurable for the marked predictable σ-algebra of the enlarged filtration; with `T = 1`,
  `𝔼 ∫_0^1 ∫ |ψ| dν ds = 1 < ∞` (the hypothesis of (2.2)), and both sides of (2.1) equal `1`
  (the right side computed, the left side `𝔼 N((0, 1] × ℝ)` from (2.1) itself). It does not
  state that the compensated integral of (2.2) is a nonzero random variable.
* `sec2_prp_nonzero_hypotheses` (for `sec2_prp`): `M_t = 𝔼[J | ℱ_t]` with `J = W_1 + Ñ((0, 1] × ℝ)`,
  the joint integral of `Z = U = 1_{(0, 1]}`, is a martingale of the enlarged filtration with
  `M_t ∈ L²` for every `t` (the hypotheses of the proposition, with `d = 1`, `T = 1`); `(Z, U)`
  represents `M` on `[0, 1]` (`RepresentsMart`), both energies equal `1`, and, by `sec2_prp`
  itself, every pair representing `M` agrees with `(Z, U)` up to null sets. With `𝒢₀ = ⊥` the
  initial enlargement is trivial at this instance; the ticket's variant with an independent
  Rademacher initial variable is not formalised.
* `sec2_hborel_nonzero_hypotheses` (for `sec2_hborel`): at `n = m = d = 1`, `T = 1`, Example 5.1(i)
  with `β₁ = 1`, `β₂ = 0`, `σ_c = h_c = 0` has `h(t, θ, μ) = −u`; the function
  `H((t, θ, μ), e) = −⟨e₁, u⟩_{L²(δ₀)} e₁`, with `e₁` the constant unit vector of `L²(δ₀; ℝ¹)`,
  is continuous in `(t, θ, μ)` and constant in `e`, hence measurable for
  `borel([0, 1] × H × P₂(H)) ⊗ ℰ`; it represents `h` `ν`-almost everywhere (through the inner
  product with `e₁`, not a point evaluation of the class `u`), and it is not the zero function.

Verdict: faithful, with the readings listed (in particular "atoms" as the count of `N`).

<!-- spec-review: Dissertation.PaperSpec.A.sec2_separable ed839d34f480cba1673cfd9d331f5aa6 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/Dissertation.PaperSpec.A.sec2_separable--claude-reviewer--2026-10-17T12_22_48Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.sec2_separable ed839d34f480cba1673cfd9d331f5aa6 by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.sec2_separable--claude-auditor--2026-10-19T03_34_36Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.sec2_separable ed839d34f480cba1673cfd9d331f5aa6 by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.sec2_infinite_activity ed839d34f480cba13a9f48f6bc72d40f by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.sec2_infinite_activity--claude-reviewer--2026-10-17T12_21_04Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.sec2_infinite_activity ed839d34f480cba13a9f48f6bc72d40f by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.sec2_infinite_activity--claude-auditor--2026-10-19T03_34_37Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.sec2_infinite_activity ed839d34f480cba13a9f48f6bc72d40f by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.eq_compid ed839d34f480cba1551f4f42ffdf2fa8 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.eq_compid--claude-reviewer--2026-10-17T12_11_27Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_compid ed839d34f480cba1551f4f42ffdf2fa8 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.eq_compid--claude-auditor--2026-10-19T03_31_22Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_compid ed839d34f480cba1551f4f42ffdf2fa8 by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.eq_zeromean ed839d34f480cba1ca027a9d4d1614c9 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.eq_zeromean--claude-reviewer--2026-10-17T12_15_00Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_zeromean ed839d34f480cba1ca027a9d4d1614c9 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.eq_zeromean--claude-auditor--2026-10-19T03_31_22Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_zeromean ed839d34f480cba1ca027a9d4d1614c9 by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.sec2_prp ed839d34f480cba1577f0ed2476fcdb5 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.sec2_prp--claude-reviewer--2026-10-17T12_22_12Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.sec2_prp ed839d34f480cba1577f0ed2476fcdb5 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.sec2_prp--claude-auditor--2026-10-19T03_34_14Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.sec2_prp ed839d34f480cba1577f0ed2476fcdb5 by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.sec2_hborel ed839d34f480cba1c7bf6ee7f1e38851 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/Dissertation.PaperSpec.A.sec2_hborel--claude-reviewer--2026-10-17T12_20_16Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.sec2_hborel ed839d34f480cba1c7bf6ee7f1e38851 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.sec2_hborel--claude-auditor--2026-10-19T03_31_21Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.sec2_hborel ed839d34f480cba1c7bf6ee7f1e38851 by=claude-auditor -->

## (2.4), the Fubini isometry: `Dissertation.PaperSpec.A.eq_fubiniiso`

Manuscript (§2, `eq:fubiniiso`): with `𝒫` the predictable σ-field on `Ω × [0, T]` under
`dt ⊗ dP`, `L²(𝒫; L²(ν)) ≅ L²(𝒫 ⊗ ℰ)` (HNVW, Propositions 1.2.24–1.2.25), "which supplies a
`𝒫 ⊗ ℰ`-measurable representative, unique up to `dt ⊗ dP ⊗ ν`-null sets; every Poisson integral
below, and every square-integrable `L²(ν)`-valued predictable integrand appearing in one, is read
through such a representative. In particular, a pointwise formula `u(e)` for `u ∈ L²(ν)` is
meaningful only when it descends to a well-defined element of `L²(ν)`". The paragraph
(`A:sec2:fubini-iso`) repeats the display with the reading convention and is recorded as a
duplicate of `A:eq:fubiniiso`.

Proposition `eq_fubiniiso`: for `μ` σ-finite on any measurable space `X`, `ν` σ-finite on a
countably generated `E` and `j ∈ ℕ`: a linear isometric equivalence
`Φ : L²(μ ⊗ ν; ℝʲ) ≃ L²(μ; L²(ν; ℝʲ))` with `Φ(g)(x) = g(x, ·)` in `L²(ν)` for `μ`-almost every
`x`; every `u ∈ L²(μ; L²(ν; ℝʲ))` has a measurable `g : X × E → ℝʲ` with `u(x) = g(x, ·)` for
almost every `x`; and two such measurable `g, g'` agree `μ ⊗ ν`-almost everywhere.

Readings:

* The proposition is stated for every σ-finite `(X, μ)`; the paper's instance is `X = Ω × [0, T]`
  with `𝒫` and `dt ⊗ dP` restricted to `𝒫`, a finite measure. The isometry is the paper's `≅`;
  the representative and its uniqueness are the following sentence.
* "Every Poisson integral … is read through such a representative" is the convention of the
  solution notion (`Solution` carries a representative `γ` of the jump coefficient), not a
  separate claim; "a pointwise formula `u(e)` … is meaningful only when it descends" is the same
  convention for formulas.
* The proof is the section map: Tonelli for the isometry, and the closed range containing the
  indicators of sets of finite measure times elements of `L²(ν)` for surjectivity, in place of
  the cited propositions.

Witnesses: none needed; the hypotheses (σ-finite measures, `E` countably generated) hold at every
instance of §2.

Verdict: broader: the proposition holds for every σ-finite `(X, μ)` and every `j`; the printed claim
is its instance at `X = Ω × [0, T]` with the predictable σ-field `𝒫` and `dt ⊗ dP`, `j = m` (or
`n`).

<!-- spec-review: Dissertation.PaperSpec.A.eq_fubiniiso ed839d34f480cba1f8905adfcaf41890 by=claude-author -->
Review by claude-reviewer: broader (report `reports/Dissertation.PaperSpec.A.eq_fubiniiso--claude-reviewer--2026-10-17T12_13_20Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_fubiniiso ed839d34f480cba1f8905adfcaf41890 by=claude-reviewer -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.eq_fubiniiso--claude-auditor--2026-10-19T03_31_21Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_fubiniiso ed839d34f480cba1f8905adfcaf41890 by=claude-auditor -->

## (2.5), the progressive coefficient processes: `Dissertation.PaperSpec.A.eq_coefmeas`

Manuscript (§2): "All coefficients are jointly Borel
measurable in their arguments ... Consequently, along any diagonal input, `(s, ω) ↦ ψ(s, Θ_s(ω),
μ_s)`, `ψ ∈ {b, σ, f}`, progressively measurable, `(s, ω, e) ↦ h(s, Θ_{s−}(ω), e, μ⁻_s)`,
predictable." The claims `A:sec2:coefmeas` (the paragraph) and `A:eq:coefmeas` (the display) are
the same statement.

Proposition `eq_coefmeas`: for any filtration and probability, coefficients satisfying (2.3)
(`JointBorel`) satisfy `CoeffRegular`: along every progressive tuple the drift, diffusion and
driver processes `ψ(s, Θ_s, Law Θ_s)` are jointly and progressively measurable, and the jump
coefficient has a jointly measurable, marked progressively measurable representative in `L²(ν)`.

Readings:

* "Along any diagonal input" is, as processes in `s`, along a progressive tuple with its own laws
  `μ_s = Law(Θ_s)`; the proposition takes every progressive tuple.
* The joint Borel measurability of the coefficients is the paragraph's hypothesis, (2.3).
* The predictable line of the display is `eq_coefmeas_jump`.

Witness: `Dissertation.Acceptance.A.thm_cwp_hypotheses` ((2.3) at Example 5.1(i)).

Verdict: broader: the proposition holds for every filtration and probability, along every
progressive tuple, and its jump part is the marked-progressive representative at `(Θ_s, μ_s)` of
`CoeffRegular`, not the predictable line of (2.5); the printed first line is its instance over the
standing basis along the tuples of the paper (diagonal inputs `Θ_s` with their laws).

<!-- spec-review: Dissertation.PaperSpec.A.eq_coefmeas ed839d34f480cba11ac3211646c24c86 by=claude-author -->
Review by claude-reviewer: broader (report `reports/Dissertation.PaperSpec.A.eq_coefmeas--claude-reviewer--2026-10-17T12_08_44Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_coefmeas ed839d34f480cba11ac3211646c24c86 by=claude-reviewer -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.eq_coefmeas--claude-auditor--2026-10-19T03_31_22Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_coefmeas ed839d34f480cba11ac3211646c24c86 by=claude-auditor -->

## (2.5), the predictable jump coefficient: `Dissertation.PaperSpec.A.eq_coefmeas_jump`

Manuscript (§2): the Fubini isometry (2.4) and "every Poisson
integral below ... is read through such a representative ... Consequently, along any diagonal
input, ... `(s, ω, e) ↦ h(s, Θ_{s−}(ω), e, μ⁻_s)`, predictable."

Proposition `eq_coefmeas_jump`: for coefficients satisfying (2.3), a predictable tuple `Θ` and a
Borel law flow `ρ : ℝ → P₂(H)` (Hilbert-norm `W₂`), the process `s ↦ 1_{[0,T]}(s) h(s, Θ_s, ρ_s)`
with values in `L²(ν; ℝⁿ)` is predictable.

Readings:

* The display's real-valued map of `(s, ω, e)` is read through (2.4): it is predictable as a map
  into `L²(ν)` and has a `𝒫 ⊗ ℰ`-measurable representative, which is `eq_fubiniiso`.
* The jump coefficient is evaluated at the predictable tuple `Θ⁻` and its law `μ⁻`, a
  deterministic flow; the proposition takes any predictable tuple and any Borel flow, cut off to
  the horizon. The Borel measurability of `s ↦ μ⁻_s` is part of Lemma A.1, not of (2.5).

Witness: `Dissertation.Acceptance.A.thm_cwp_hypotheses` ((2.3) at Example 5.1(i); a constant tuple
and a constant law flow are predictable and Borel).

Verdict: broader: the proposition holds for every filtration, every predictable tuple `Θ` and every
Borel law flow `ρ`; the printed claim is its instance over the standing basis at `Θ = Θ⁻` of a tuple
of the paper and `ρ = μ⁻`, the Borel flow of Lemma A.1, read through (2.4).

<!-- spec-review: Dissertation.PaperSpec.A.eq_coefmeas_jump ed839d34f480cba1e13c6b7ca8ccca73 by=claude-author -->
Review by claude-reviewer: broader (report `reports/Dissertation.PaperSpec.A.eq_coefmeas_jump--claude-reviewer--2026-10-17T16_03_52Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_coefmeas_jump ed839d34f480cba1e13c6b7ca8ccca73 by=claude-reviewer -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.eq_coefmeas_jump--claude-auditor--2026-10-19T03_34_12Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_coefmeas_jump ed839d34f480cba1e13c6b7ca8ccca73 by=claude-auditor -->

## Remark 3.2, the solution class: `Dissertation.PaperSpec.A.rem_cwp_class`

Manuscript (§3): "Let `Θ = (X, Y, Z, U) ∈ ℍ_weak` satisfy (1.1). Then
`Θ ∈ ℍ`. Indeed, the coefficients evaluated along `Θ` lie in `L²(dt ⊗ dP)` by
Assumptions 2.2–2.3, so Doob/BDG applied to the forward equation gives `𝔼 sup_{t≤T} |X_t|² < ∞`
... so Cauchy–Schwarz on the drift and Doob/BDG on the two martingales give
`𝔼 sup_{t≤T} |Y_t|² < ∞`."

Proposition `rem_cwp_class`: in the standing setting (the enlarged basis of a Lévy driver), for
`T > 0`, coefficients satisfying (2.3), Assumption 2.2 with initial datum `ξ₀` and Assumption 2.3
with a constant `L`, every tuple with `WeakSolution` (a tuple of `ℍ_weak` satisfying (1.1), the
drift and driver integrals pathwise) has `Solution` (it solves (1.1) in `ℍ`).

Readings:

* The remark states no hypotheses; its proof invokes Assumptions 2.2–2.3, and (2.3) is the
  standing measurability of §2. The proposition takes these three.
* "`Θ ∈ ℍ`" for a tuple satisfying (1.1) is `Solution`: the `S²` bounds of `ℍ` together with
  (1.1), its coefficient processes square integrable, which the remark's "Indeed" sentence
  establishes along the way.

Witness: `Dissertation.Acceptance.A.rem_cwp_class_hypotheses`: at Example 5.1(i) (2.3) and
Assumptions 2.2–2.3 hold and a tuple of `ℍ_weak` satisfies (1.1) (the solution of Theorem 3.5).

Verdict: faithful.

<!-- spec-review: Dissertation.PaperSpec.A.rem_cwp_class ed839d34f480cba1dac1a53237b9beb3 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.rem_cwp_class--claude-reviewer--2026-10-17T12_12_05Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.rem_cwp_class ed839d34f480cba1dac1a53237b9beb3 by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.rem_cwp_class--claude-auditor--2026-10-19T03_38_10Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.rem_cwp_class ed839d34f480cba1dac1a53237b9beb3 by=claude-auditor -->

## The paragraph after Theorem 3.1: `Dissertation.PaperSpec.A.thm_stab_companion`, `thm_stab_data`, `thm_stab_minimal`

Manuscript (§3): "If system 2 also satisfies Assumptions 2.4–2.5, with its
own coupling matrix and constants, exchanging the roles gives the companion bound with the
differences evaluated along solution 1 and the constant built from system 2's data. When the two
systems share the four interior coefficients, the bound gives continuous dependence on the initial
and terminal data. More minimally, the hypotheses on system 2 serve only to make the right-hand
side of (3.1) finite: the estimate holds whenever the displayed differences are
square-integrable."

Proposition `thm_stab_companion`: `∃ C_stab : ℝ⁷ → ℝ` such that, in the standing setting, if
system 1 satisfies (2.3) and Assumptions 2.2–2.3 with `L₁`, system 2 satisfies (2.3) and
Assumptions 2.2–2.5 with `L, α, β₁, β₂, G`, and `Θᵏ` has `Solution` for system `k`, then
`supSize(Θ¹ − Θ²) ≤ C_stab(T, L, ‖G‖, s_min(G)⁻², α, β₁, β₂) · dataSize(…)` with the coefficient
differences `ψ¹ − ψ²` along `Θ¹` (`δh` through `coeffJump` along the left limits of `Θ¹`) and
`δ̂g_T` at `(X¹_T, Law X¹_T)`.

Proposition `thm_stab_data`: under the hypotheses of `thm_stab`, and `C₂.b = C₁.b`,
`C₂.σ = C₁.σ`, `C₂.h = C₁.h`, `C₂.f = C₁.f`,
`supSize(Θ¹ − Θ²) ≤ C_stab · (𝔼|ξ¹ − ξ²|² + 𝔼|g¹(X²_T, Law X²_T) − g²(X²_T, Law X²_T)|²)`.

Proposition `thm_stab_minimal`: as `thm_stab`, with Assumptions 2.2–2.3 on system 2 dropped (it
keeps the standing measurability (2.3)), the inequality read in `[0, ∞]`.

Readings:

* Companion: "Assumptions 2.4–2.5 with its own coupling matrix and constants" for system 2,
  together with Assumptions 2.2–2.3 that Theorem 3.1 puts on it, is the hypothesis set of system
  1 in `thm_stab`; system 1 keeps what Theorem 3.1 puts on system 2, Assumptions 2.2–2.3 with its
  own constant `L₁`. The proposition drops Assumption 2.5 on system 1, which the exchange does not
  use, so it is weaker in hypotheses than the paragraph and implies it. The left side is written
  `Θ¹ − Θ²` (the norm makes the order immaterial). The constant is `C_stab` at system 2's
  parameters, the function of Theorem 3.1.
* Data: "share the four interior coefficients" is equality of `b, σ, h, f` as coefficient
  functions. The differences `δb, δσ, δh, δf` then vanish identically and the right side of (3.1)
  is `𝔼|δξ₀|² + 𝔼|δ̂g_T|²`, with `δ̂g_T` at `(X²_T, Law X²_T)` as in Theorem 3.1; "continuous
  dependence on the initial and terminal data" is this bound. Assumption 2.5 stays on system 1 and
  Assumptions 2.2–2.3 on system 2, as in Theorem 3.1.
* Minimal: "the estimate holds whenever the displayed differences are square-integrable" is read
  as (3.1) in `[0, ∞]` with no hypothesis on system 2 beyond (2.3) and the existence of its
  solution: when the differences are square-integrable the right side is finite and this is the
  printed estimate; otherwise it is infinite and the inequality holds trivially. The
  proposition is therefore at least as strong as the sentence. (2.3) on system 2 is kept: it is
  the standing measurability of §2, under which the displayed differences are processes at all
  (`δh` is read through `coeffJump`, which needs the Borel jump coefficient of system 2).
* `Solution` for system 2 is the solution notion of §3 (`definitions.md`); its drift energy is
  finite, which is stronger than membership of `ℍ` with the integrals pathwise. Remark 3.2
  (`rem_cwp_class`) shows the two agree under Assumptions 2.2–2.3; without them, as in
  `thm_stab_minimal`, the proposition covers the solutions of system 2 whose coefficient
  processes are square integrable.

Witness: `Dissertation.Acceptance.A.thm_stab_nonzero_hypotheses` for all three: one system,
Example 5.1(i) with `β₁ = β₂ = 1`, `σ_c = h_c = 0`, taken twice, with the initial data `e₁` and
`0`. For `thm_stab_companion` with the roles exchanged, system 2 of the proposition satisfies
Assumptions 2.2–2.5 with `L = 1`, `G = 1`, `α = β₁ = β₂ = 1` and system 1 satisfies (2.3) and
Assumptions 2.2–2.3 with `L₁ = 1`. For `thm_stab_data` the two systems share `b, σ, h, f` and the
initial data differ, the instance the paragraph describes. For `thm_stab_minimal` system 2
satisfies (2.3). In each the left side, symmetric in the two solutions, is at least `1`. The
earlier witness `thm_stab_hypotheses` had two zero solutions and is no longer
linked.

Verdict: `thm_stab_companion` broader: system 1 needs only (2.3) and Assumptions 2.2–2.3, and the
printed claim is its instance at a system 1 that also satisfies Assumptions 2.4–2.5, as in Theorem
3.1; `thm_stab_data` faithful; `thm_stab_minimal` faithful in the reading recorded (the inequality
in `[0, ∞]`).

<!-- spec-review: Dissertation.PaperSpec.A.thm_stab_companion ed839d34f480cba10ff3a550a92ccddf by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.thm_stab_companion--claude-reviewer--2026-10-17T12_19_01Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.thm_stab_companion ed839d34f480cba10ff3a550a92ccddf by=claude-reviewer -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.thm_stab_companion--claude-auditor--2026-10-19T03_37_17Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.thm_stab_companion ed839d34f480cba10ff3a550a92ccddf by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.thm_stab_data ed839d34f480cba1f26d5949b31ba63f by=claude-author -->
Review by claude-reviewer: faithful (report `reports/Dissertation.PaperSpec.A.thm_stab_data--claude-reviewer--2026-10-17T16_05_53Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.thm_stab_data ed839d34f480cba1f26d5949b31ba63f by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.thm_stab_data--claude-auditor--2026-10-19T03_37_06Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.thm_stab_data ed839d34f480cba1f26d5949b31ba63f by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.thm_stab_minimal ed839d34f480cba127494e1cb3f498aa by=claude-author -->
Review by claude-reviewer: faithful (report `reports/Dissertation.PaperSpec.A.thm_stab_minimal--claude-reviewer--2026-10-17T16_05_53Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.thm_stab_minimal ed839d34f480cba127494e1cb3f498aa by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.thm_stab_minimal--claude-auditor--2026-10-19T03_36_39Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.thm_stab_minimal ed839d34f480cba127494e1cb3f498aa by=claude-auditor -->

## The preamble of Section 5: `Dissertation.PaperSpec.A.sec5_limin`

Manuscript (§5): "the restrictive hypothesis is the dissipativity of
Assumption 2.5, ... which cannot be traded for Lipschitz continuity alone. The jump system of
[LiMin, Example 3.2] is linear, hence Lipschitz, and is shown there to admit no adapted solution on
the horizon `T = 3π/4`."

Proposition `sec5_limin`: in the standing setting with `d = 1` (any `ν`, `𝒢₀`, driver), on the
horizon `T = 3π/4`, the system `liMinCoeffs ν` (`n = m = d = 1`) satisfies (2.3), Assumption 2.2
with every deterministic initial datum and Assumption 2.3 with some constant; and for every
initial datum `ξ₀` with `𝔼 ξ₀ ≠ 0`, no tuple satisfies `WeakSolution` (a tuple of `ℍ_weak`
satisfying (1.1)).

Readings:

* "Linear, hence Lipschitz" is Assumption 2.3 (with constant `2`) together with (2.3) and the
  origin values of Assumption 2.2; the proposition states the three. Example 3.2 of Li and Min has
  a deterministic initial value, and Assumption 2.2 is stated for every deterministic datum.
* "Admit no adapted solution": the proposition excludes every tuple of `ℍ_weak` satisfying (1.1),
  which contains every `Solution`, so it is at least as strong as "no solution in `ℍ`". The
  exclusion is stated for initial data of nonzero mean, which contains the Li–Min initial value
  `x(0) = 1`. The condition cannot be dropped: from `ξ₀ = 0` the tuple `(W, 0, 0, 0)` satisfies
  (1.1) (the means vanish, so `b = f = g = 0` along it); this is not formalised.
* "Cannot be traded for Lipschitz continuity" is the conjunction: the hypotheses of Theorem 3.5
  other than Assumption 2.5 hold and the conclusion fails. The preamble does not assert that
  Assumption 2.5 fails for this system (it follows from Theorem 3.5 in contrapositive, and the
  implementation states it as `liMin_fails_assumption25`), so the proposition does not state it.
* `liMinCoeffs` is the system of Example 3.2 of Li and Min, reviewed in `definitions.md`.

Witness: `Dissertation.Acceptance.A.sec5_limin_hypotheses`: a probability space carrying a Lévy
driver with `d = 1` and `ν = δ₀` on `ℝ`, `𝒢₀ = ⊥` independent of it, and the initial datum
`ξ₀ ≡ 1` of mean `1`.

Verdict: broader: the proposition holds on every standing basis with `d = 1` and every σ-finite `ν`,
excludes every tuple of `ℍ_weak` satisfying (1.1), and does so from every initial datum of nonzero
mean; the printed claim (no adapted solution of the Li–Min system on `T = 3π/4`) is its instance at
the basis of the cited example and its initial value `x(0) = 1`, through the transcription
`liMinCoeffs` reviewed in `definitions.md`.

<!-- spec-review: Dissertation.PaperSpec.A.sec5_limin ed839d34f480cba132884b458e231942 by=claude-author -->
Review by claude-reviewer: broader (report `reports/Dissertation.PaperSpec.A.sec5_limin--claude-reviewer--2026-10-17T12_25_43Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.sec5_limin ed839d34f480cba132884b458e231942 by=claude-reviewer -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.sec5_limin--claude-auditor--2026-10-19T03_31_22Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.sec5_limin ed839d34f480cba132884b458e231942 by=claude-auditor -->

## Remark 3.7, general rank: `Dissertation.PaperSpec.A.rem_generalrank`, `rem_generalrank_wp`

Manuscript (§3): "The restriction to `m = n` reflects only the
unweighted bookkeeping: the same splitting of the pairing into baseline and perturbation
brackets, run in the weighted quantities of (2.12), gives the identical conclusion for arbitrary
`m, n` when the margin and (3.4) are both recorded in those quantities."

Propositions: `rem_generalrank` and `rem_generalrank_wp` are `cor_robust` and `cor_robust_wp`
(reviewed under Corollary 3.6) with `n, m ≥ 1` arbitrary, `G ∈ ℝ^{m×n}` of full rank, the
baseline's margin taken in (2.12) (`Margin212`, the weighted form)
instead of (2.13), the perturbation's pairing bound taken in `PairingBound34W` (the left side of
(3.4) bounded by `c_pert 𝔼[|Gᵀ δY|² + |Gᵀ δZ|²_F + ‖Gᵀ δU‖²_{L²(ν)} + |G δX|²]`) instead of
`PairingBound34`, and the margin of the perturbed system concluded in (2.12).

Readings:

* "The identical conclusion" is that of Corollary 3.6: the perturbed system satisfies
  Assumptions 2.2–2.5 with the same `G, α, β₁, β₂` and some Lipschitz constant, with the margin
  `c_diss − c_pert` (now in (2.12)), and is well-posed in the sense of Theorems 3.1, 3.3 and 3.5,
  the constant of (3.1) being that of Theorem 3.1. The two propositions state exactly these
  conclusions, with the hypotheses of Corollary 3.6 otherwise unchanged.
* "When the margin and (3.4) are both recorded in those quantities": `Margin212` for the margin,
  `PairingBound34W` for (3.4). `PairingBound34W` is a new definition of the specification layer,
  reviewed in `definitions.md`.
* Corollary 3.6's clause (3.5) ⇒ (3.4) is not part of the remark and has no weighted counterpart
  here.

Witness: `Dissertation.Acceptance.A.rem_generalrank_hypotheses`, the instance of
`cor_robust_hypotheses` (`n = m = 1`, `G = 1`, `ν = δ₀`, baseline Example 5.1(i) with
`β₁ = β₂ = 2`, feedback perturbation `ε = 1/2`), with (2.12) for the baseline at
`β₁ = β₂ = c_diss = 1` and the weighted (3.4) for the perturbation at `c_pert = 1/2`. At `G = 1`
the weighted and unweighted quantities coincide, so the witness shows the hypotheses can be met
but does not exhibit a case `m ≠ n`; an instance with `m ≠ n` is not formalised.

Verdict: faithful.

<!-- spec-review: Dissertation.PaperSpec.A.rem_generalrank ed839d34f480cba1bcd1d82734738c5b by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.rem_generalrank--claude-reviewer--2026-10-17T12_13_00Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.rem_generalrank ed839d34f480cba1bcd1d82734738c5b by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.rem_generalrank--claude-auditor--2026-10-19T03_36_13Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.rem_generalrank ed839d34f480cba1bcd1d82734738c5b by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.rem_generalrank_wp ed839d34f480cba118d1835a02488a97 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/Dissertation.PaperSpec.A.rem_generalrank_wp--claude-reviewer--2026-10-17T16_05_53Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.rem_generalrank_wp ed839d34f480cba118d1835a02488a97 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.rem_generalrank_wp--claude-auditor--2026-10-19T03_37_46Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.rem_generalrank_wp ed839d34f480cba118d1835a02488a97 by=claude-auditor -->

## Lemma A.1, the law flows: `Dissertation.PaperSpec.A.lem_lawflow`, `lem_lawflow_invariant`

Manuscript (Appendix A, Lemma `lem:lawflow`): "Let `X, Y` be càdlàg adapted and let `Z, U`
be fixed predictable versions, with `𝔼 ∫_0^T (|X_t|² + |Y_t|² + |Z_t|²_F + ∫_E |U_t(e)|² ν(de)) dt
< ∞`. Then the a.e.-defined maps `t ↦ Law(Θ⁻_t)` and `t ↦ Law(Θ_t)` admit Borel representatives,
unique up to Lebesgue-null sets of times, `μ⁻, μ : [0, T] → (P₂(H), W₂)`, `μ⁻_t = μ_t` for a.e.
`t`. Coefficient evaluations along these representatives are invariant, up to `dt ⊗ dP`-null
sets, under the choice of predictable representatives of `(Z, U)` and of the Borel
representatives."

Propositions: `lem_lawflow` (the Borel flows and their almost-everywhere agreement) and
`lem_lawflow_invariant` (uniqueness of the flows and invariance of coefficient evaluations).

Correspondence:

* Hypotheses: `CadlagPredTuple` (reviewed in `definitions.md`): `X, Y` adapted with càdlàg paths,
  `Z, U` predictable, each of finite energy on `[0, T]`: the printed integrability.
* "Admit Borel representatives `μ, μ⁻`": the canonical flows `s ↦ lawP2(Θ_s)` and
  `s ↦ lawP2(Θ⁻_s)` are measurable into `P₂(H)` with the Borel σ-algebra of `W₂`
  (`toP2WH`, the Hilbert-norm `W₂` of §2), and for a.e. `s` they are the laws `P ∘ Θ_s⁻¹`,
  `P ∘ (Θ⁻_s)⁻¹`. "`μ⁻_t = μ_t` for a.e. `t`": the last conjunct.
* "Unique up to Lebesgue-null sets": the first conclusion of `lem_lawflow_invariant`, any two
  flows representing the laws agree a.e.
* "Invariant ... under the choice of predictable representatives of `(Z, U)` and of the Borel
  representatives": the second conclusion, for an arbitrary coefficient `ψ(s, θ, μ)`, with the
  versions `Z = Z'` `dt ⊗ dP`-a.e. and `U = U'` `dt ⊗ dP ⊗ ν`-a.e.
* The invariance is stated for `Θ`; for `Θ⁻` it is the same statement applied to the left limits
  `leftLimProc X, leftLimProc Y`, since `X, Y` there are arbitrary.

Witnesses: `Dissertation.Acceptance.A.lem_lawflow_hypotheses` (the zero tuple on a one-point
space satisfies `CadlagPredTuple`) and `Dissertation.Acceptance.A.lem_lawflow_invariant_hypotheses`
(on a one-point space every tuple's law flow represents its laws).

Verdict: broader. `lem_lawflow` holds for every filtration and probability; `lem_lawflow_invariant`
takes arbitrary `X, Y` (no adaptedness or path regularity), arbitrary flows `ρ, ρ'` representing the
laws (not only Borel ones) and an arbitrary coefficient `ψ`, with no measurability. The printed
claims are their instances over the standing basis, at a tuple with `X, Y` càdlàg adapted and `Z, U`
predictable (`CadlagPredTuple`), the Borel flows of `lem_lawflow` and the coefficients of the
system.

<!-- spec-review: Dissertation.PaperSpec.A.lem_lawflow ed839d34f480cba1090c1a53f2a6cf7f by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.lem_lawflow--claude-reviewer--2026-10-17T12_27_30Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.lem_lawflow ed839d34f480cba1090c1a53f2a6cf7f by=claude-reviewer -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.lem_lawflow--claude-auditor--2026-10-19T03_36_15Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.lem_lawflow ed839d34f480cba1090c1a53f2a6cf7f by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.lem_lawflow_invariant ed839d34f480cba184c9d1f8d6f2b814 by=claude-author -->
Review by claude-reviewer: broader (report `reports/Dissertation.PaperSpec.A.lem_lawflow_invariant--claude-reviewer--2026-10-17T16_03_53Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.lem_lawflow_invariant ed839d34f480cba184c9d1f8d6f2b814 by=claude-reviewer -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.lem_lawflow_invariant--claude-auditor--2026-10-19T03_38_36Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.lem_lawflow_invariant ed839d34f480cba184c9d1f8d6f2b814 by=claude-auditor -->

## (4.2) and (4.3), the coefficient bounds: `Dissertation.PaperSpec.A.eq_coeffint`, `eq_termg`

Manuscript (§4): "By Assumptions 2.2–2.3, the coefficient processes
(2.5) along any `Θ ∈ ℍ` are square-integrable: for `ψ ∈ {b, σ, h, f}`, in the norms of
Assumption 2.3, `𝔼 ∫_0^T |ψ(s, Θ_s, μ_s)|² ds ≤ C 𝔼 ∫_0^T (|X_s|² + |Y_s|² + |Z_s|²_F +
‖U_s‖²_{L²(ν)} + |ψ(s, 0, δ_0)|²) ds` (4.2), by that Lipschitz bound together with the coupling
estimate (2.8) at `μ' = δ_0`. For the terminal function the analogous bound
`𝔼 |g(X_T, Law(X_T))|² ≤ C (𝔼 |X_T|² + |g(0, δ_0)|²)` (4.3) follows in the same way from (2.6)
and (2.9)." `C` depends only on `T, L, ‖G‖, c_G, α, β₁, β₂` and the BDG constant (the convention
of §4).

Propositions:

* `eq_coeffint`: `∃ K : ℝ → ℝ` such that, on every filtered probability space, if the interior
  bound of Assumption 2.3 (`LipInterior`) holds with `L` and `Θ_t` is `ℱ_t`-measurable and square
  integrable for a.e. `t ∈ [0, T]`, then for each of `b, σ, h, f` (Euclidean, Frobenius, `L²(ν)`
  and Euclidean norms), with `μ_s = Law(Θ_s)` (`lawP2`), the displayed inequality holds with
  `C = K(L)`, all integrals in `[0, ∞]`.
* `eq_termg`: `∃ K : ℝ → ℝ` such that, if `g` satisfies (2.6) (`LipTerminal`) with `L` and `X_T`
  is `ℱ_T`-measurable and square integrable, the displayed inequality holds with `C = K(L)`, in
  `[0, ∞]`.

Readings:

* The constant: `K` is chosen before everything else and depends on `L` only, which is within
  the convention that `C` depends only on the listed parameters. The proofs give
  `K(L) = 2 + 20 L²` and `2 + 8 L²`.
* "Along any `Θ ∈ ℍ`": a tuple of `ℍ` has `Θ_t` adapted and square integrable for a.e. `t`; the
  proposition assumes only this, so it covers `ℍ`. "Square-integrable" is the finiteness of the
  left side when the right side is finite; the right side is finite under Assumption 2.2 (origin
  values in `L²(0, T)`) and `Θ ∈ ℍ`, which the proposition does not need to assume since the
  inequality is read in `[0, ∞]`. The measurability of the coefficient processes, the other half
  of "the coefficient processes (2.5) ... are square-integrable", is (2.5) itself
  (`eq_coefmeas`).
* "In the norms of Assumption 2.3": the norms of `LipInteriorAt`, with the Hilbert-norm `W₂` on
  `P₂(H)` for the coupling (2.8).
* The displays write `h(s, Θ_s, μ_s)`; the proposition evaluates `h` there, as printed.

Witness: `Dissertation.Acceptance.A.thm_cwp_hypotheses` for both: at Example 5.1(i) Assumption 2.3
holds with `L = 1` (its interior and terminal parts are `LipInterior` and `LipTerminal`), and the
zero tuple, constant in time, is adapted and square integrable at every `t`, as is `X_T = 0`.

Verdict: broader: `eq_coeffint` and `eq_termg` hold on every filtered probability space, for every
tuple with `Θ_t` `ℱ_t`-measurable and square integrable for almost every `t` (every `ℱ_T`-measurable
square-integrable `X_T`), with no assumption beyond the Lipschitz bound used (no Assumption 2.2, and
for `eq_termg` no mark space); the printed claims are their instances over the standing basis along
`Θ ∈ ℍ` (and its `X_T`) under Assumptions 2.2–2.3.

<!-- spec-review: Dissertation.PaperSpec.A.eq_coeffint ed839d34f480cba13c4b68e5e50bad34 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.eq_coeffint--claude-reviewer--2026-10-17T12_22_13Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_coeffint ed839d34f480cba13c4b68e5e50bad34 by=claude-reviewer -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.eq_coeffint--claude-auditor--2026-10-19T03_36_47Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_coeffint ed839d34f480cba13c4b68e5e50bad34 by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.eq_termg ed839d34f480cba171988e2e6de37794 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/Dissertation.PaperSpec.A.eq_termg--claude-reviewer--2026-10-17T16_03_52Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_termg ed839d34f480cba171988e2e6de37794 by=claude-reviewer -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.eq_termg--claude-auditor--2026-10-19T03_31_22Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_termg ed839d34f480cba171988e2e6de37794 by=claude-auditor -->

## Example 5.1(i), sharpness: `Dissertation.PaperSpec.A.ex_concrete_i_sharp`

Manuscript (§5): Example 5.1(i) states that the displayed identity
`𝔼[⟨δb, δY⟩ + ⟨δσ, δZ⟩_F + ⟨−δf, δX⟩ + ∫_E ⟨δh(e), δU(e)⟩ ν(de)]
= −β₁ 𝔼[|δY|² + |δZ|²_F + ‖δU‖²] − β₂ 𝔼|δX|²` is sharp for the constants `β₁, β₂`.

Proposition: in the standing setting with `n = m = d = 1` (any σ-finite `ν`, `ν = 0` included),
for `T > 0`, `β₁, β₂ > 0`, `σ_c`, `h_c` and constants `β₁', β₂'`: if (2.7) (`Mono27At`, the
printed interior inequality with its integrability) holds for the coefficients of Example 5.1(i)
with `G = 1` and `β₁', β₂'` at almost every `t ∈ [0, T]`, then `β₁' ≤ β₁` and `β₂' ≤ β₂`.

Readings:

* "Sharp for the constants `β₁, β₂`": no larger constant satisfies the interior inequality, which
  is the proposition. The terminal constant `α = 1` is not part of the sentence.
* The proof tests two deterministic tuples at a time of positive measure: `δY = 1` with the other
  channels equal gives `β₁' ≤ β₁`; `δX = 1` gives `β₂' ≤ β₂` (`not_diagonalMonotone_affine_of_lt`).
  Constant tuples are diagonal inputs on every basis, so no richness of the noise is used, and
  `ν = 0` is covered.

Witness: `Dissertation.Acceptance.A.ex_concrete_hypotheses`: at its instance Assumption 2.5 holds
with the system's own `β₁, β₂`, so (2.7) holds with `β₁' = β₁`, `β₂' = β₂`.

Verdict: faithful.

<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_i_sharp ed839d34f480cba19df1faec1593a821 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/Dissertation.PaperSpec.A.ex_concrete_i_sharp--claude-reviewer--2026-10-17T12_17_25Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_i_sharp ed839d34f480cba19df1faec1593a821 by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.ex_concrete_i_sharp--claude-auditor--2026-10-19T03_36_07Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_i_sharp ed839d34f480cba19df1faec1593a821 by=claude-auditor -->

## Example 5.2, two further clauses: `Dissertation.PaperSpec.A.ex_brownian_not_h0`, `ex_brownian_rank_gt`

Manuscript (Example `ex:brownian`): "Merely setting `h ≡ 0` on a Brownian–Poisson basis is not a
reduction, since the backward Poisson integral and its integrand `U` persist in the
representation." … "With no jump channel the `U`-dissipativity constraint of Remark 2.10 is
vacuous, so both rank branches of Assumption 2.5 are available."

Propositions:

* `ex_brownian_not_h0`: in the standing setting (any `𝒢₀` independent of the driver, `E`
  countably generated, `ν` σ-finite), with `d ≥ 1` and `ν ≠ 0`, for every `T > 0` there is a
  martingale `M` of the filtration of §2 with `M_t ∈ L²` for every `t` such that no `Z` makes
  `(Z, 0)` represent `M` on `[0, T]` (`RepresentsMart` with `U = 0`).
* `ex_brownian_rank_gt`: in the standing setting with `ν = 0`, for `1 ≤ n < m`, `d ≥ 1`,
  `T > 0` and `ξ₀ ∈ L²(ℱ₀)` there are `G ∈ ℝ^{m×n}` of full rank, coefficients, and `L, α, β₁, β₂`
  with (2.3) and Assumptions 2.2–2.5, and `β₂ > 0`.

Correspondence:

* "`h ≡ 0` is not a reduction, since the backward Poisson integral and its integrand persist":
  the representation property of a Brownian–Poisson basis is not the Brownian one, whatever the
  coefficients, because some square-integrable martingale needs a nonzero `U`. The proposition
  is about the basis and not about the solutions of any particular system with `h = 0`; this is
  the content the sentence gives as its reason. The proof takes `A` with `0 < ν(A) < ∞`, the
  martingale `M_t = 𝔼[Ñ((0, T] × A) | ℱ_t]`, represented by `(0, 1_{(0, T] × A})`, and the
  uniqueness clause of the representation property (`sec2_prp`): a representation `(Z, 0)`
  would give `ν(A) T = 0`.
* "Both rank branches are available": the branch `m < n` is the last clause of `ex_brownian`; the
  branch `m > n` is `ex_brownian_rank_gt`, exhibited for every `1 ≤ n < m` by the linear
  generator `b = σ = h = 0`, `f(t, θ, μ) = G x`, `g(x, ρ) = G x` with `G` the diagonal matrix,
  `α = 1`, `β₁ = 0`, `β₂ = 1` (the admissible constants of the branch `m > n` require `α > 0`
  and `β₂ > 0`). The square case is Example 5.1(i).
* The jump coefficient in `ex_brownian_rank_gt` is an element of `L²(0; ℝᵐ) = {0}`, so no
  additive-form condition is needed.

Witnesses: `Dissertation.Acceptance.A.ex_brownian_not_h0_hypotheses` (a Lévy driver with `d = 1`
and `ν = δ₀ ≠ 0` on `ℝ`, `𝒢₀ = ⊥`); `Dissertation.Acceptance.A.ex_brownian_rank_gt_hypotheses`
(a Lévy driver with `ν = 0` on `ℝ`, `d = 1`, `𝒢₀ = ⊥`, `n = 1 < m = 2`, datum `0`).

Verdict: faithful for the two clauses stated; the reduction of the assumptions and the solution
notions to their Brownian forms is an open clause.

<!-- spec-review: Dissertation.PaperSpec.A.ex_brownian_not_h0 ed839d34f480cba13fa0ef4acc9fb310 by=claude-author -->
Review by claude-reviewer: faithful (report `reports/Dissertation.PaperSpec.A.ex_brownian_not_h0--claude-reviewer--2026-10-17T12_11_37Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_brownian_not_h0 ed839d34f480cba13fa0ef4acc9fb310 by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.ex_brownian_not_h0--claude-auditor--2026-10-19T03_34_13Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_brownian_not_h0 ed839d34f480cba13fa0ef4acc9fb310 by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_brownian_rank_gt ed839d34f480cba154d947c79143fab0 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.ex_brownian_rank_gt--claude-reviewer--2026-10-17T16_05_52Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_brownian_rank_gt ed839d34f480cba154d947c79143fab0 by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.ex_brownian_rank_gt--claude-auditor--2026-10-19T03_37_10Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_brownian_rank_gt ed839d34f480cba154d947c79143fab0 by=claude-auditor -->

## Example 5.2, the reduction to the Brownian forms: `Dissertation.PaperSpec.A.ex_brownian_reduction`, `ex_brownian_prp`

Manuscript (Example `ex:brownian`): "Remove the Poisson channel from the stochastic basis, so that
the filtration is generated by `W` and `ℱ₀` and the representation property is the Brownian one.
Delete the `U`-coordinate from the tuple, reducing `H` to `ℝⁿ × ℝᵐ × ℝ^{m×d}`. […] The
assumptions reduce to `W₂`-Lipschitz joint-law dependence of `(X, Y, Z)` under `G`-monotonicity,
the condition imposed in [BYZ, (A1)] with rectangular full-rank `G`."

Propositions:

* `ex_brownian_reduction`: in the standing setting with `ν = 0` (any `𝒢₀` independent of the
  driver, `E` countably generated, any `d`), for all `n, m`, every `T` and every coefficient
  system `C : Coeffs 0 n m d`, with `ℱ^B = enlBrownian 𝒢₀ D.W h𝒢₀` (the usual augmentation of
  the filtration generated by `W` and `𝒢₀`):
  (a) for every `L`, `Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L C ↔ BrownianAssumption23 ℱ^B P T L C`,
  and for every `t, L`, `LipInteriorAt (enlJoint …) P t L C ↔ BrownianLipInteriorAt ℱ^B P t L C`;
  (b) for every `t, G, β₁, β₂`, `Mono27At (enlJoint …) P t G β₁ β₂ C ↔ BrownianMonoAt ℱ^B …`
  ((2.7) at each time), and for every `G, α, β₁, β₂`,
  `Assumption25 (enlJoint …) P T G α β₁ β₂ C ↔ BrownianAssumption25 ℱ^B P T G α β₁ β₂ C`;
  (c) for all `ξ₀, X, Y, Z, U`, `Solution D h𝒢₀ hind₀ T C ξ₀ X Y Z U` holds if and only if every
  coordinate `U_k` is marked predictable for `ℱ^B` (and `ν = 0`), vanishes off `[0, T]` and has
  marked energy `0`, and `BrownianSolution D.W h𝒢₀ _ T C ξ₀ X Y Z` holds; and likewise
  `WeakSolution … ↔ (the same conditions on U) ∧ BrownianWeakSolution …`.
* `ex_brownian_prp`: in the standing setting with `ν = 0`, for `d ≥ 1`, `T > 0` and a real
  martingale `M` of `ℱ^B` with `M_t ∈ L²` for every `t`: some `Z` represents `M` on `[0, T]`
  (`RepresentsMartBrownian`: predictable for `ℱ^B`, finite energy, vanishing off `[0, T]`, and
  `M_t = M_0 + ∫_0^t Z dW` almost surely for every `t ∈ [0, T]`), and any two representing `Z`
  have differences of zero energy.

Correspondence:

* "Remove the Poisson channel" is read, as in the review of `ex_brownian`, as the standing setting
  at `ν = 0`. "The filtration is generated by `W` and `ℱ₀`" is `ℱ^B`: `enlBrownian 𝒢₀ W h𝒢₀` is
  `augFiltration (ℱ^W ⊔ 𝒢₀)₊ P`, the expression of clause (a) of `ex_brownian`, which states that
  it equals the filtration `enlJoint 𝒢₀ D h𝒢₀` of §2 at `ν = 0`. Every Brownian form is stated
  over `ℱ^B` and involves only `W`, `𝒢₀` and `P`; the Brownian integrals take as their proof
  argument `isBrownianFiltration_enlBrownian` (each coordinate of `W` is a Brownian motion for
  `ℱ^B`), whose identity does not affect the meaning.
* "Delete the `U`-coordinate, reducing `H` to `ℝⁿ × ℝᵐ × ℝ^{m×d}`": at `ν = 0` the tuple space
  `TupleH 0 n m d` has the jump channel `L²(0; ℝᵐ) = {0}` (clause (b) of `ex_brownian`) and is
  identified with `ℝⁿ × ℝᵐ × ℝ^{m×d}` by `projB` (`liftB_projB`); a coefficient system at `ν = 0`
  is a function of `(t, x, y, z)` and of a law on `H`, which `projP2` (isometric for `W₂`, clause
  (b') of `ex_brownian`) identifies with the law of `(X, Y, Z)`; its jump coefficient takes values
  in `L²(0; ℝⁿ) = {0}`. The Brownian forms are the paper's own notions applied to the same `C`
  with every term of the `U`-coordinate and of `h` deleted: none of them mentions `C.h`, `δU`,
  the jump pairing, `‖Gᵀ δU‖²`, a jump integrand `γ` or a compensated Poisson integral. The
  diagonal inputs keep the type `Ω → TupleH 0 n m d`, whose last channel is `{0}`.
* "The assumptions reduce to `W₂`-Lipschitz joint-law dependence of `(X, Y, Z)`":
  `BrownianLipInteriorAt` is `LipInteriorAt` with `‖δh‖_{L²(ν)}` and `‖δU‖_{L²(ν)}` deleted and
  `w2H μ μ'` replaced by `w2P (projP2 μ) (projP2 μ')`, the `W₂` distance of the laws of
  `(X, Y, Z)` in `ℝⁿ × ℝᵐ × ℝ^{m×d}` with its Euclidean norm (`ReducedTuple`);
  `BrownianAssumption23` is `L ≥ 0`, `BrownianLipInteriorAt` for almost every `t ∈ [0, T]`, and
  the terminal bound (2.6), which has no jump term, unchanged (`LipTerminal`). The proof: at
  `ν = 0` every element of `L²(0; F)` has norm `0`, and `w2P_projP2`.
* "under `G`-monotonicity": `brownianPairing` is `pairing27` without
  `∫_E ⟨δh(e), Gᵀ δU(e)⟩ ν(de)`; `BrownianMonoAt` is `Mono27At` with this pairing (the
  integrability conjunct included) and `‖Gᵀ δU‖²_{L²(ν)}` deleted from the right side;
  `BrownianAssumption25` is the terminal inequality of Assumption 2.5 (copied from the field
  `terminal`; no jump term), `BrownianMonoAt` for almost every `t ∈ [0, T]`, and the admissible
  constants `Constants n m α β₁ β₂`, unchanged. "With rectangular full-rank `G`" is Assumption
  2.4 (`G.rank = min m n`), which has no jump term and is not restated. With the jump terms gone,
  the `U`-dissipativity of Remark 2.10 disappears from (2.7); the branches of the constants are
  `ex_brownian` and `ex_brownian_rank_gt`.
* "The solution notions" are read as the two of §3 formalised in `Setting`: `Solution` (in `ℍ`)
  and `WeakSolution` (satisfying (1.1) in `ℍ_weak`). `BrownianPaperSolution` is `PaperSolution`
  with the fields of `U` (`U_pred`, `U_vanish`, `U_sq`) and of the representative of the jump
  coefficient (`γ_meas`, `γ_prog`, `γ_sq`, `jump_rep`) deleted, the coefficient processes
  `driftProc`, `diffusionProc`, `driverProc` evaluated along `Θ_s = (X_s, Y_s, Z_s, 0)` (the only
  tuple with the given `X, Y, Z` at `ν = 0`), the compensated Poisson integrals deleted from `fwd`
  and `bwd`, and a `d`-dimensional Brownian motion `W` over a filtration carrying it in place of
  the driver. `BrownianPaperWeakSolution` is `PaperWeakSolutionInt` (`PaperWeakTuple`,
  `PaperAdmissibleInt`, `XT_sq`, `fwd`, `bwd`) with the same deletions. `BrownianSolution` and
  `BrownianWeakSolution` apply them over `ℱ^B`, with the conjuncts of `Solution` and
  `WeakSolution` on the left limits of every path. The identities are
  `X_t = ξ₀ + ∫_0^t b(s, Θ_s, μ_s) ds + ∫_0^t σ(s, Θ_s, μ_s) dW_s` and
  `Y_t = g(X_T, Law X_T) + ∫_t^T f(s, Θ_s, μ_s) ds − ∫_t^T Z_s dW_s`: (1.1) without the
  compensated Poisson integrals.
* The deleted `U`: in (1.1) `U` is an element of `H²_N(0, T; L²(ν; ℝᵐ))`, which is `{0}` at
  `ν = 0`. The left side asks of the representative `U` what it asks at every `ν` (marked
  predictable, vanishing off `[0, T]`, finite marked energy). The right side keeps the first two,
  which are conditions on the representative and not on its class (the marked predictable
  σ-algebra is not the full product σ-algebra, also at `ν = 0`), and records that the marked
  energy, the squared norm in `L²(dt ⊗ dP ⊗ ν)`, is `0`, which is automatic at `ν = 0`
  (`markedEnergy_nu_zero`). So the solutions of (1.1) at `ν = 0` are the Brownian solutions
  `(X, Y, Z)` with `U = 0` in `H²_N`, every admissible representative of `0` allowed.
* "The representation property is the Brownian one": `ex_brownian_prp`, with
  `RepresentsMartBrownian` the Brownian form of `RepresentsMart` (`U` and the Poisson integral
  deleted, over `ℱ^B`), read as in the review of `sec2_prp` (almost surely for each `t`; unique up
  to `dt ⊗ dP`-null sets; `d ≥ 1` and `T > 0` hypotheses). The proof applies `sec2_prp` at `ν = 0`
  and the vanishing of the compensated Poisson integral at `ν = 0`.
* Broader than printed: `ex_brownian_reduction` holds for all `n, m, d` and every `T`; the printed
  claim, in the standing setting `n, m, d ≥ 1`, `T > 0`, is an instance. `ex_brownian_prp` keeps
  `d ≥ 1` and `T > 0`, as `sec2_prp` does.
* Disagreement and its resolution: the manuscript names no Brownian form of each notion, and the
  condition it cites, [BYZ, (A1)], is not in the repository. Each Brownian form is therefore
  written as the paper's own notion with the jump terms deleted, so that the reduction can be
  read against the printed definitions; the identification of the reduced assumptions with
  [BYZ, (A1)] (a statement about cited work) is not formalised.
* Not stated: Assumption 2.2 and (2.3), which the sentence does not mention (at `ν = 0` their jump
  components, `h(·, 0, ·, δ₀) ∈ L²(0, T; L²(0; ℝⁿ))` and the measurability of `h`, hold for every
  `C`); that every coefficient system on `ℝⁿ × ℝᵐ × ℝ^{m×d}` and its laws arises from some `C` at
  `ν = 0` (by composition with `projB` and `projP2`), which the example does not state; and the
  forced system (4.1), a device of the proof of §4.

Witnesses: `Dissertation.Acceptance.A.ex_brownian_reduction_hypotheses` (a Lévy driver with
`ν = 0` on `ℝ`, `d = 1`, `𝒢₀ = ⊥`; at `n = 1`, `m = 2`, `T = 1` and datum `0`, the linear
generator of `ex_brownian_rank_gt` has a solution of (1.1) in `ℍ` by `thm_cwp`, so that both
sides of (c) are met at an instance of the example);
`Dissertation.Acceptance.A.ex_brownian_prp_hypotheses` (the same driver, with `d = 1 > 0`,
`T = 1`, and the martingale `0` of `ℱ^B`, square integrable at every time).

Verdict: faithful, with "remove the Poisson channel" read as `ν = 0`, as in the review of
`ex_brownian`.

<!-- spec-review: Dissertation.PaperSpec.A.ex_brownian_reduction ed839d34f480cba16ec077c21383f1ee by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.ex_brownian_reduction--claude-reviewer--2026-10-17T16_05_53Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_brownian_reduction ed839d34f480cba16ec077c21383f1ee by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.ex_brownian_reduction--claude-auditor--2026-10-19T03_36_56Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_brownian_reduction ed839d34f480cba16ec077c21383f1ee by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_brownian_prp ed839d34f480cba1d54de82e0956a03e by=claude-author -->
Review by claude-reviewer: faithful (report `reports/Dissertation.PaperSpec.A.ex_brownian_prp--claude-reviewer--2026-10-17T16_03_52Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_brownian_prp ed839d34f480cba1d54de82e0956a03e by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.ex_brownian_prp--claude-auditor--2026-10-19T03_34_12Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_brownian_prp ed839d34f480cba1d54de82e0956a03e by=claude-auditor -->

## §3, the solution definition and the solution space: `Dissertation.PaperSpec.A.sec3_one_null_set`, `sec3_cadlag_versions`, `sec3_HH_inclusion`, `sec3_HH_definite`, `sec3_HH_norm`

Manuscript (§3, the paragraphs on `ℍ` and on solutions): the elements of `ℍ`
are equivalence classes (càdlàg components identified when indistinguishable, `Z` when equal
`dt ⊗ dP`-a.e., `U` when equal `dt ⊗ dP ⊗ ν`-a.e.); "under this identification `‖·‖_ℍ` is a norm
rather than a seminorm, and `(ℍ, ‖·‖_ℍ)` is a Banach space. Since
`𝔼 ∫_0^T |V_t|² dt ≤ T 𝔼 sup_{t ≤ T} |V_t|²`, the inclusion `ℍ ⊂ ℍ_weak` holds." A solution
satisfies both identities of (1.1) almost surely for every `t ∈ [0, T]`; "both sides of each
identity are càdlàg in `t`, so the exceptional null set may be taken independent of `t`."

Propositions:

* `sec3_one_null_set`: in the standing setting, for a tuple of `ℍ_weak` (`PaperWeakTuple`: adapted
  `X, Y` with every path right-continuous on `[0, T)`, predictable `Z, U`, finite energies) along
  which the integrals of (1.1) exist (`PaperAdmissibleInt`, with `γ` a representative of the jump
  coefficient), and any process `M` with almost surely right-continuous paths on `[0, T)` (the
  càdlàg version of the Brownian integral the identity uses): the forward identity
  `X_t = ξ₀ + ∫_0^t b + M_t + ∫_0^t ∫ γ Ñ` holds almost surely for each `t ∈ [0, T]` if and only
  if it holds off one null set for all `t ∈ [0, T]`; likewise the backward identity
  `Y_t = g + ∫_t^T f − (M_T − M_t) − (∫_0^T ∫ U Ñ − ∫_0^t ∫ U Ñ)`.
* `sec3_cadlag_versions`: for a tuple of `ℍ_weak` along which the integrals of (1.1) exist, as
  above, each coordinate of each of the four stochastic integrals of (1.1) (`∫ σ dW` and
  `∫∫ γ Ñ` of the forward identity, `∫ Z dW` and `∫∫ U Ñ` of the backward one, with the integrands
  and integrability proofs of `PaperWeakSolutionInt`) has a version `M`: adapted to the filtration
  of §2, equal almost surely to the integral at every `t ∈ [0, T]`, with every path
  right-continuous on `[0, T)` and with left limits on `(0, T]`.
* `sec3_HH_inclusion`: for `T ≥ 0` and `V` with values in `ℝⁿ`,
  `𝔼 ∫_0^T |V_t|² dt ≤ T 𝔼 sup_{t ≤ T} |V_t|²` in `[0, ∞]`, and a finite right side gives a
  finite energy of each coordinate (the `ℍ_weak` condition).
* `sec3_HH_definite`: for a tuple of `ℍ_weak`, `‖Θ‖²_ℍ` (`supSize`) is `0` if and only if `X`
  and `Y` are indistinguishable from `0` on `[0, T]`, `Z = 0` `dt ⊗ dP`-a.e. on `[0, T]`
  (`energyMeasure`) and `U = 0` `dt ⊗ dP ⊗ ν`-a.e. (`markedEnergyMeasure`).
* `sec3_HH_norm`: for tuples `Θ, Θ'` of `ℍ_weak` over the filtration of §2 and `c ∈ ℝ`, with
  `‖Θ‖_ℍ = supSize(Θ)^{1/2}` in `[0, ∞]` and the operations taken coordinatewise,
  `‖Θ + Θ'‖_ℍ ≤ ‖Θ‖_ℍ + ‖Θ'‖_ℍ` and `‖c Θ‖_ℍ = |c| ‖Θ‖_ℍ`.

Correspondence:

* "Both sides are càdlàg": the proof shows the right-continuity of each side and nothing else is
  needed: `X, Y` by `PaperWeakTuple` (every path); the drift and driver integrals by the
  integrability of almost every path on `[0, T]`; the compensated Poisson integrals by their
  almost sure càdlàg paths (`stochasticIntegral_cadlag`); `M` by hypothesis. The Brownian
  integral of the paper is an `L²` object; the identity is read with a càdlàg version, as the
  repository's solution notion `PaperWeakSolutionInt` does. The proposition does not assume `M` is
  that version, so it is broader.
* "Both sides of each identity are càdlàg in `t`" for the stochastic integrals is
  `sec3_cadlag_versions`. The Brownian integral of the library is an `L²` limit at each time
  without path regularity, and the compensated Poisson integral has càdlàg paths almost surely, so
  "càdlàg" is read as the existence of a version whose every path is càdlàg; the adaptedness of the
  version is a further conclusion, so the clause is broader. Its hypothesis is the class of
  `sec3_one_null_set`, which contains every solution.
* "`‖·‖_ℍ` is a norm rather than a seminorm" is `sec3_HH_definite` (definiteness on the identified
  classes) together with `sec3_HH_norm` (the triangle inequality and absolute homogeneity). Both
  are stated on `ℍ_weak` with the norm in `[0, ∞]`; `ℍ` is the part where it is finite, so they are
  broader. `ℍ_weak` being closed under the operations is not stated.
* "`(ℍ, ‖·‖_ℍ)` is a Banach space" (completeness) is `sec3_HH_complete`, reviewed in the next
  section.
* The inclusion `ℍ ⊂ ℍ_weak` is read as the energy condition of `ℍ_weak` for `X` and `Y`; the
  other conditions of `ℍ_weak` are those of `ℍ`.

Witness: `Dissertation.Acceptance.A.sec3_space_hypotheses` for `sec3_one_null_set` and
`sec3_HH_definite`: over a Lévy driver with `d = 1`, `ν = δ₀`, `𝒢₀ = ⊥`, `n = m = 1`, `T = 1`,
the solution of Example 5.1(i) (`β₁ = β₂ = 1`, `σ_c = h_c = 0`) from `ξ₀ ≡ e₁` gives a tuple of
`ℍ_weak` with the integrals of (1.1), with `X_0 = 1` almost surely (not the zero tuple).
`sec3_HH_inclusion` has no hypotheses beyond `T ≥ 0`.
`Dissertation.Acceptance.A.sec3_cadlag_versions_hypotheses` for `sec3_cadlag_versions`: over the
same driver, the tuple `X = Y = 1`, `Z = U = 1_{(0, 1]}` of `ℍ_weak`, along which the integrals of
(1.1) exist for the system of Example 5.1(i), with `Z` and `U` of energy `1` (nonzero integrands).
`Dissertation.Acceptance.A.sec3_HH_norm_hypotheses` for `sec3_HH_norm`: that tuple, taken for
both `Θ` and `Θ'`, with `‖Θ‖²_ℍ = 4`.

Verdict: faithful for `sec3_HH_inclusion`; broader for `sec3_one_null_set`,
`sec3_cadlag_versions`, `sec3_HH_definite` and `sec3_HH_norm`, each by the instantiation given
above.

<!-- spec-review: Dissertation.PaperSpec.A.sec3_one_null_set ed839d34f480cba1209a5aa6ac298690 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.sec3_one_null_set--claude-reviewer--2026-10-17T12_16_14Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.sec3_one_null_set ed839d34f480cba1209a5aa6ac298690 by=claude-reviewer -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.sec3_one_null_set--claude-auditor--2026-10-19T03_35_07Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.sec3_one_null_set ed839d34f480cba1209a5aa6ac298690 by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.sec3_HH_inclusion ed839d34f480cba130514b735af5f227 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.sec3_HH_inclusion--claude-reviewer--2026-10-17T12_15_35Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.sec3_HH_inclusion ed839d34f480cba130514b735af5f227 by=claude-reviewer -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.sec3_HH_inclusion--claude-auditor--2026-10-19T03_34_37Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.sec3_HH_inclusion ed839d34f480cba130514b735af5f227 by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.sec3_HH_definite ed839d34f480cba12b4c9985cfe528af by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.sec3_HH_definite--claude-reviewer--2026-10-17T12_14_59Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.sec3_HH_definite ed839d34f480cba12b4c9985cfe528af by=claude-reviewer -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.sec3_HH_definite--claude-auditor--2026-10-19T03_34_14Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.sec3_HH_definite ed839d34f480cba12b4c9985cfe528af by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.sec3_cadlag_versions ed839d34f480cba18328d3bafc39f8ed by=claude-author -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.sec3_cadlag_versions--claude-auditor--2026-10-19T05_49_14Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.sec3_cadlag_versions ed839d34f480cba18328d3bafc39f8ed by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.sec3_HH_norm ed839d34f480cba140aa5342c14a73fc by=claude-author -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.sec3_HH_norm--claude-auditor--2026-10-19T05_49_14Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.sec3_HH_norm ed839d34f480cba140aa5342c14a73fc by=claude-auditor -->

## §3, completeness of the solution space: `Dissertation.PaperSpec.A.sec3_HH_complete`

Manuscript (§3, the paragraph on `ℍ`): "Under this identification
`‖·‖_ℍ` is a norm rather than a seminorm, and `(ℍ, ‖·‖_ℍ)` is a Banach space."

Proposition `sec3_HH_complete`: in the standing setting, over `enlJoint 𝒢₀ D h𝒢₀`, let
`(X_j, Y_j, Z_j, U_j)` be tuples of `ℍ_weak` (`PaperWeakTuple`) with `supSize < ∞` (that is,
`‖·‖_ℍ < ∞`) such that for every `ε > 0` there is `N` with `supSize(Θ_j − Θ_k) < ε` for
`j, k ≥ N`. Then there is a tuple `(X, Y, Z, U)` of `ℍ_weak` with `supSize < ∞`, every path of
`X` and `Y` having left limits on `(0, T]` (so càdlàg, `PaperWeakTuple` giving right-continuity of
every path), and `supSize(Θ_j − Θ) → 0`.

Correspondence:

* `supSize` is `‖·‖²_ℍ`, the displayed squared norm; Cauchy and convergent for the square are the
  same as for the norm.
* The paper's elements are classes; completeness of the quotient is the statement that every
  Cauchy sequence of representatives has a representative limit, which is what is stated. The
  limit's càdlàg paths (every path, as `Solution` requires) are stronger than the almost sure left
  limits of `PaperWeakTuple`.
* The filtration is the one of §2, which contains the null sets at time `0`, so modifying a limit on
  a null set keeps it adapted.
* "`‖·‖_ℍ` is a norm" is reviewed under `sec3_HH_definite` and `sec3_HH_norm`; the closure of the
  quotient under the vector-space operations is not separately stated.

Witness: `Dissertation.Acceptance.A.sec3_HH_complete_hypotheses`: over a Lévy driver with
`d = 1`, `ν = δ₀`, `𝒢₀ = ⊥`, `n = m = 1`, `T = 1`, the constant sequence at the tuple
`X = Y = 1`, `Z = U = 1_{(0, 1]}` of `ℍ_weak`, with `‖Θ_j‖²_ℍ = 4`, is Cauchy. It shows the
hypotheses can be met by a nonzero tuple; a sequence that is not eventually constant is not
exhibited.

Verdict: faithful.

<!-- spec-review: Dissertation.PaperSpec.A.sec3_HH_complete ed839d34f480cba140502fce3ed6073c by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.sec3_HH_complete--claude-reviewer--2026-10-17T12_14_16Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.sec3_HH_complete ed839d34f480cba140502fce3ed6073c by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.sec3_HH_complete--claude-auditor--2026-10-19T03_34_22Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.sec3_HH_complete ed839d34f480cba140502fce3ed6073c by=claude-auditor -->

## §4, the horizon: `Dissertation.PaperSpec.A.sec4_horizon_not_contractive`

Manuscript (the introduction to §4): "The continuation
is in the coupling strength, not the horizon: shortening the horizon does not make the
frozen-coefficient map contractive, since the `(z, u)`-dependence of `σ, h` and the full-tuple law
coupling enter the contraction constant with no `T`-factor."

Proposition `sec4_horizon_not_contractive`: for every `T > 0`, `β₁ ≥ 1` and `β₂ > 0`, over
`enlJoint 𝒢₀ D h𝒢₀` for any Lévy driver with `d = 1` and `ν = 0` on a point: the system of
Example 5.1(i) with `σ_c = h_c = 0` satisfies (2.3), Assumption 2.2 with `ξ₀ = 0`,
Assumption 2.3 with `L = β₁ + β₂`, Assumption 2.4 with `G = 1` and Assumption 2.5 with `G = 1`,
`α = 1`; `BrownianFrozenStep` relates `0` to `0`; and there are a trial `(0, 0, Z, 0)` of `ℍ_weak`
with `Z = 1` on `[0, T]` and an output `(X', Y', Z', U')` of `ℍ_weak`, related by
`BrownianFrozenStep`, with `X' = Y' = −β₁ W` almost surely on `[0, T]`, `Z' = −β₁` and `U' = 0` on
`[0, T]`, `0 < ‖trial‖²_ℍ ≤ ‖output‖²_ℍ < ∞`.

Correspondence:

* "Does not make the frozen-coefficient map contractive" is read as: on every horizon there is a
  system satisfying the assumptions, with constants independent of `T`, for which `Φ₁` does not
  decrease the distance between two trials (`0` and `Θ`, whose images are `0` and `Θ̄`), so its
  Lipschitz constant on `ℍ` is at least `1` however small `T` is. `Φ₁` is the map of Lemma 4.2 at
  `λ = 1`, `q = 0` (`BrownianFrozenStep`).
* One example on one driver suffices for the negative statement. The example shows the
  `z`-dependence of `σ` entering with no `T`-factor; the `u`-dependence of `h` and the law coupling,
  the other reasons the sentence gives, are not separately exhibited.
* The output is related, not computed: the linear equations determine it up to the identification
  of `ℍ`, so the stated output is the image `Φ₁(Θ)`.

Witness: `Dissertation.Acceptance.A.sec4_horizon_hypotheses`: a probability space carrying a Lévy
driver with `d = 1` and `ν = 0` on a point, with `𝒢₀ = ⊥` and `T = β₁ = β₂ = 1`; the proposition
has no other hypotheses.

Verdict: faithful.

<!-- spec-review: Dissertation.PaperSpec.A.sec4_horizon_not_contractive ed839d34f480cba1fc081d81965ca7e6 by=claude-author -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.sec4_horizon_not_contractive--claude-reviewer--2026-10-17T12_08_17Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.sec4_horizon_not_contractive ed839d34f480cba1fc081d81965ca7e6 by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.sec4_horizon_not_contractive--claude-auditor--2026-10-19T03_35_41Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.sec4_horizon_not_contractive ed839d34f480cba1fc081d81965ca7e6 by=claude-auditor -->

## §4, the supremum criterion: `Dissertation.PaperSpec.A.sec4_supremum_criterion`

Manuscript (the preamble of §4, lines 30–37): "The maximal estimates use the
Burkholder–Davis–Gundy inequality in quadratic-variation form, at `p = 1` for the zero-mean
arguments and at `p = 2` for squared suprema ([HeWangYan], chapter on `H¹` and BMO; at `p = 2`
Doob's inequality gives the constant `4`), with one universal constant `c_BDG` valid at both
exponents; valid for càdlàg local martingales, the inequality covers the compensated-Poisson
martingales below without a separate jump statement. By localisation and dominated convergence, a
càdlàg local martingale whose running supremum is integrable has zero-mean increments (the
*supremum criterion* below)."

Uses. Proof of Lemma 4.1 (lines 1042–1043), for the local martingales `M^W_t = ∫_0^t e^s ⟨δY_{s−},
δZ_s dW_s⟩` and `M^1_t = ∫_0^t ∫_E e^s ⟨δY_{s−}, δU_s(e)⟩ Ñ(ds, de)`, after `𝔼 sup_{t ≤ T} |M^W_t| <
∞` and `𝔼 sup_{t ≤ T} |M^1_t| < ∞`: "These bounds put the running suprema of `M^W` and `M^1` in
`L¹`, so the supremum criterion gives `𝔼[M_T − M_t] = 0` for `M ∈ {M^W, M^1}`." Proof of Lemma 4.3
(lines 1482–1483), for the four stochastic integrals of (eq:bdg4), each of the form `∫_0^t`: "The
four suprema in (eq:bdg4) are therefore integrable, so the supremum criterion applies to those four
local martingales", and then "all five terms have zero expectation", that is `𝔼 M_T = 0` with `M_0 =
0`.

Proposition `sec4_supremum_criterion`: for every probability space `(Ω, P)`, every filtration `𝓕 =
(𝓕_t)_{t ≥ 0}` indexed by `ℝ≥0`, every process `M : ℝ≥0 → Ω → ℝ` and every `T ≥ 0`: if `M` is
adapted (`Adapted 𝓕 M`), almost every path of `M` is right-continuous with a left limit at every
`t`, `M` is a local martingale (`Locally (fun X => Martingale X 𝓕 P) 𝓕 M P`) and `∫⁻ sup_{u ≤ T}
‖M_u‖ₑ dP < ∞`, then `M_t` is integrable for every `t ≤ T` and `∫ (M_t − M_s) dP = 0` for all `s ≤ t
≤ T`.

Correspondence:

* Probability space and filtration: any filtered probability space with time `[0, ∞)`. The usual
  conditions and the Brownian–Poisson structure of §2 are not assumed, so the proposition is broader
  than its uses; the filtration of §2 (the usual augmentation of the one generated by `W`, `N` and
  `ℱ_0`, on `ℝ₊`) is an instance.
* Time interval. The local martingales of Lemmas 4.1 and 4.3 are integrals `∫_0^t` over `[0, T]`;
  the instance is the process stopped at `T` (`M_{t ∧ T}`, or the integral of an integrand vanishing
  after `T`), which is adapted, càdlàg and a local martingale on `[0, ∞)` exactly when the process
  is so on `[0, T]`, with the same running supremum over `[0, T]`.
* Values: real. Every local martingale the criterion is applied to is real-valued (each is an
  integral of an inner product). An `ℝⁿ`-valued reading follows componentwise.
* "Local martingale": `ProbabilityTheory.Locally` (Mathlib) unfolds to: there are maps `τ_k : Ω →
  [0, ∞]`, each a stopping time of `𝓕`, almost surely nondecreasing in `k` and tending to `∞`, such
  that every `M^{τ_k} 1_{τ_k > 0}` (`stoppedProcess` of `{ω | ⊥ < τ_k ω}.indicator (M ·)` at `τ_k`)
  is a martingale of `𝓕` under `P` (Mathlib's `Martingale`: strongly adapted with `𝔼[X_j | 𝓕_i] =
  X_i` a.s. for `i ≤ j`, which forces integrability, `Martingale.integrable`). This is the
  definition with the indicator `1_{τ_k > 0}` (as in Protter, Ch. I §6); a definition asking that
  `M^{τ_k}` itself be a martingale, or a uniformly integrable one, implies it, since `1_{τ_k > 0}`
  is bounded and `𝓕_0`-measurable. So the hypothesis is implied by every standard definition and is
  no stronger than the paper's. On a finite horizon "`τ_k ↑ T`" has to mean that the `τ_k` reach `T`
  (equivalently `τ_k ↑ ∞` once `τ_k` is set to `∞` on `{τ_k ≥ T}`): a sequence only approaching `T`
  from below localises `[0, T)`, and then the criterion fails at `t = T` (the deterministic `M =
  1_{[T, ∞)}` with `τ_k = T − 1/k` has every stopped process `0` and `𝔼[M_T − M_0] = 1`; not
  formalised). The proposition takes `τ_k → ∞`.
* "Càdlàg": almost every path right-continuous with left limits at every `t ≥ 0` (at `t = 0` the
  left-limit clause is vacuous). The every-path reading, the convention of
  `Dissertation.PaperSpec.A.Solution`, is an instance; under the usual conditions the two readings
  agree up to indistinguishability. The proof uses right-continuity only, to make `sup_{u ≤ T}
  |M_u|` almost everywhere measurable (it agrees a.s. with the supremum over a countable dense
  subset of `[0, T]` together with `T`).
* Adaptedness: `Adapted 𝓕 M`, each `M_t` `𝓕_t`-measurable; it is part of the definition of a local
  martingale, which the printed sentence presupposes.
* "Running supremum integrable": `∫⁻ ω, ⨆ u ≤ T, ‖M u ω‖ₑ ∂P < ∞`, i.e. `𝔼 sup_{u ≤ T} |M_u| < ∞`,
  the supremum taken in `[0, ∞]`, which is what the uses establish (`𝔼 sup_{t ≤ T} |M^W_t| < ∞`, `𝔼
  sup_{t ≤ T} |M^1_t| < ∞`, the four bounds of (eq:bdg4)). The sentence names no interval; under the
  reading `𝔼 sup_{t ≥ 0} |M_t| < ∞` the hypothesis holds for every `T`, so that reading is an
  instance (take `T = t`).
* "Zero-mean increments": `∫ (M_t − M_s) dP = 0` for `s ≤ t ≤ T`, together with the integrability of
  `M_t` for `t ≤ T`, without which the Bochner integral would be `0` by convention. Lemma 4.1 uses
  `(s, t) = (t, T)`: `𝔼[M_T − M_t] = 0`; Lemma 4.3 uses `(s, t) = (0, T)` with `M_0 = 0`: `𝔼 M_T =
  0`. The proposition does not assert that `M` is a martingale on `[0, T]` (true, by the same
  argument with conditional dominated convergence), since the sentence claims zero-mean increments
  only and the uses need no more.
* Not covered: the preceding sentence, that BDG at `p = 1` and `p = 2` holds for càdlàg local
  martingales with one constant for both exponents (Doob's `4` at `p = 2`), and so covers the
  compensated-Poisson martingales. That is a statement about the cited inequality of He, Wang and
  Yan, not part of the supremum criterion; it is not stated here.

Proof (for the reader; not part of the review): the printed one. Along the localising sequence,
`𝔼[M^{τ_k}_t 1_{τ_k > 0}] = 𝔼[M^{τ_k}_s 1_{τ_k > 0}]`; a.s. `τ_k → ∞`, so the two stopped values
equal `M_t`, `M_s` for large `k`; both are bounded by `sup_{u ≤ T} |M_u|`, which is integrable;
dominated convergence.

Witness: `Dissertation.Acceptance.A.sec4_supremum_criterion_hypotheses`: `Ω = Bool` with the
fair-coin law, the filtration trivial before time `1` and full from time `1`, `T = 2`, and `M_t = ξ
1_{t ≥ 1}` with `ξ(true) = 1`, `ξ(false) = −1`: `M` is adapted, every path is càdlàg with one jump
at `t = 1`, `M` is a martingale (so a local martingale, `τ_k = ∞`), `|M| ≤ 1`, and `M_2 ≠ M_0` on
every path. It is a single-jump martingale, not one of the stochastic integrals the paper applies
the criterion to; it shows that the hypotheses are met together by a process that moves and jumps.

Verdict: faithful. The proposition is broader than the printed claim (any filtration, almost surely
càdlàg paths, localisation with the indicator `1_{τ_k > 0}`); the printed claim, in the setting of
§2 and as used in Lemmas 4.1 and 4.3, is an instance.

<!-- spec-review: Dissertation.PaperSpec.A.sec4_supremum_criterion ed839d34f480cba1f588c2071f5242ff by=claude-author -->
Review by claude-reviewer: faithful (report `reports/Dissertation.PaperSpec.A.sec4_supremum_criterion--claude-reviewer--2026-10-17T16_03_52Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.sec4_supremum_criterion ed839d34f480cba1f588c2071f5242ff by=claude-reviewer -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.sec4_supremum_criterion--claude-auditor--2026-10-19T03_31_21Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.sec4_supremum_criterion ed839d34f480cba1f588c2071f5242ff by=claude-auditor -->

## Abstract: the claims it summarises (`A:abstract`)

Manuscript (abstract, at `1f67672`): "We prove existence, uniqueness, and stability for fully
coupled McKean–Vlasov forward–backward SDEs with jumps whose drift, diffusion, jump, and driver
coefficients may depend Lipschitz-continuously, in quadratic Wasserstein distance, on the joint law
of the full solution tuple `Θ = (X, Y, Z, U)` … The terminal function may depend
Lipschitz-continuously on `X_T` and its law. The system is driven by a Brownian motion and an
independent compensated Poisson random measure with arbitrary σ-finite intensity, so infinite jump
activity is admitted. Both the Lipschitz and monotonicity hypotheses are imposed only along
diagonal tuple–law pairs `(Θ, Law(Θ))`; we show that expected diagonal monotonicity is strictly
weaker than pointwise monotonicity. Under a jump-extended `G`-monotonicity condition we establish
an a priori continuous-dependence estimate, uniqueness, and existence on every prescribed finite
horizon, by monotone continuation in the coupling strength from a small-coupling base case. A
mean-field dealer-market example realises the `U`-law dependence non-perturbatively: its
interaction between valuation curves is monotone at every interaction strength and, in an explicit
specialisation, active along the solution; its mark measure has infinite activity."

Correspondence:

* "Existence, uniqueness, and stability", "an a priori continuous-dependence estimate,
  uniqueness, and existence on every prescribed finite horizon": `thm_stab`, `thm_uniq` and
  `thm_cwp` (reviewed above). Their hypotheses are (2.3) and Assumptions 2.2–2.5 along the
  diagonal inputs: the `W₂`-Lipschitz dependence of `b, σ, h, f` on the law of the full tuple and
  of `g` on `X_T` and its law, and the jump-extended `G`-monotonicity; they hold for every
  σ-finite `ν` on a countably generated space and every `T > 0`. "By monotone continuation … from
  a small-coupling base case" describes the proof and is not a separate claim.
* "Expected diagonal monotonicity is strictly weaker than pointwise monotonicity": `rem_diag_mono`
  (the pointwise condition gives Assumption 2.5) and `prop_strict` (the converse fails), reviewed
  above.
* "Arbitrary σ-finite intensity, so infinite jump activity is admitted": the quantifier over every
  σ-finite `ν` in the three theorems; that `ν(E) = ∞` is the infinite-activity regime is
  `sec2_infinite_activity` (reviewed above).
* The dealer market: "its interaction between valuation curves is monotone at every interaction
  strength" is `ex_dealer_mono`; "realises the `U`-law dependence non-perturbatively" is its
  well-posedness at every `ε ≥ 0` with no smallness condition, `ex_dealer_wp`; "in an explicit
  specialisation, active along the solution" is `ex_dealer_active`; "its mark measure has infinite
  activity" is `ex_dealer_marks` (`ν(E) = ∞`). The four are reviewed under Example 5.5.

Verdict: each clause is the proposition named, reviewed in its own section.

## Remark 2.10, the `β₁` dichotomy: `Dissertation.PaperSpec.A.rem_beta1_fibre`, `rem_beta1_dich`, `rem_beta1_zero`

Manuscript (§2, Remark `rem:beta1-dich`): "Suppose `ν ≠ 0`, so that `L²(ν) ≠ {0}`. Taking
`δX = δY = δZ = 0` and `δU` arbitrary in (2.7) reduces the interior pairing to
`𝔼 ∫_E ⟨δh(e), G* δU(e)⟩ ν(de) ≤ −β₁ 𝔼 ‖G* δU‖²_{L²(ν)}`, so `β₁ > 0` forces the jump coefficient
`h` to be strictly `U`-dissipative. A jump coefficient of the natural additive form `h = h(t, x, e)`
carries no `U`-feedback, so `δh = 0` while `δU` may be chosen with `G* δU ≠ 0`; the displayed bound
then forces `β₁ ≤ 0`, hence `β₁ = 0` as the constants are non-negative. Assumption 2.5 then
requires `m ≥ n` with `α, β₂ > 0`, the `G`-injective branch, and the `m < n` rank case is
available only for `U`-dissipative jump coefficients. The restriction is structural: it follows
from Assumption 2.5 itself, not from the estimates that exploit it. When `ν = 0` the fibre `L²(ν)`
is trivial, `δU = 0` identically, and the restriction disappears: this is the Brownian case of
Example 5.2, in which both rank branches remain available. The present uniform-coercivity theorem
does not cover the additive form when `m < n` and `ν ≠ 0`. Domination-monotonicity results for
Lévy-driven systems without mean-field dependence [XuTangMeng] show that uniform integrand
coercivity is not the only available solvability mechanism."

Propositions:

* `rem_beta1_fibre`: for `ν` σ-finite on any measurable space (countable generation is not assumed)
  and `m ≥ 1`, `L²(ν; ℝᵐ) ≠ {0}` when `ν ≠ 0`, and `L²(ν; ℝᵐ) = {0}` when `ν = 0`.
* `rem_beta1_dich`: in the standing setting, for `n, m ≥ 1`, `T > 0`, `ν ≠ 0`, `G ∈ ℝ^{m×n}` of
  full rank and coefficients satisfying Assumption 2.5 with `G, α, β₁, β₂`: (a) for almost every
  `t ∈ [0, T]` and all `(Θ, μ), (Θ', μ') ∈ 𝒟_t` whose `X, Y, Z` agree at every `ω`, the displayed
  bound; (b) if `h(t, θ, μ)` depends on `t` and the forward state `x` only (`h(t, θ, μ) =
  h(t, θ', μ')` whenever `θ` and `θ'` have the same `x`, at all `t` and all laws), then `β₁ = 0`,
  `n ≤ m`, `α > 0` and `β₂ > 0`; (c) if `m < n`, then `β₁ > 0` and `h` is not of that form.
* `rem_beta1_zero`: in the standing setting with `ν = 0`, `n = m ≥ 1`, `T > 0`, `β₁, β₂ > 0`,
  `σ_c` and `h_c`, the coefficients of Example 5.1(i) have a jump coefficient depending on `t` and
  `x` only and satisfy Assumption 2.5 with `G = I`, `α = 1` and the constants `β₁ > 0`, `β₂`.

Correspondence:

* The first sentence is `rem_beta1_fibre`'s first half, read with `m ≥ 1` (standing); its second
  half is "when `ν = 0` the fibre `L²(ν)` is trivial", so `δU = 0` identically.
* (a) is the second sentence: "taking `δX = δY = δZ = 0` and `δU` arbitrary" is a pair of
  diagonal inputs whose `X, Y, Z` coincide, with `U, U'` unrestricted; the pairing of (2.7) then
  reduces to its jump term, whose expectation exists as that of (2.7) does in Assumption 2.5. With
  `β₁ > 0`, (a) is the strict `U`-dissipativity of `h`.
* "The natural additive form `h = h(t, x, e)`" is read as: the element `h(t, θ, μ)` of
  `L²(ν; ℝⁿ)`, a function of the mark `e`, depends on `(t, θ, μ)` through `t` and `x` only, with no
  dependence on `y, z, u` or on the law. (b) is "the displayed bound then forces … `β₁ = 0` …
  Assumption 2.5 then requires `m ≥ n` with `α, β₂ > 0`".
* (c) is "the `m < n` rank case is available only for `U`-dissipative jump coefficients" and
  "the present uniform-coercivity theorem does not cover the additive form when `m < n` and
  `ν ≠ 0`": the admissible constants of Assumption 2.5 give `β₁ > 0` when `m < n`, so (a) is
  strict `U`-dissipativity there, and by (b) `h` is not additive, so Theorem 3.5, whose hypotheses
  include Assumption 2.5, never applies to it.
* `G` of full rank (Assumption 2.4, with which Assumption 2.5 is stated) and `n, m ≥ 1` (standing)
  supply a `δU` with `G* δU ≠ 0` once `ν ≠ 0`. "The restriction is structural" is the fact that the
  conclusions are drawn from Assumptions 2.4–2.5 alone.
* "The restriction disappears" at `ν = 0` is read as the failure of (b) there: an additive jump
  coefficient with `β₁ > 0`, which `rem_beta1_zero` exhibits at `n = m` (where (b) would force
  `β₁ = 0`). "Both rank branches remain available" is Example 5.2, whose clauses `ex_brownian`
  (the branch `m < n`, with an additive jump coefficient and `β₁ > 0`) and `ex_brownian_rank_gt`
  (the branch `m > n`) are recorded under this claim too and reviewed with Example 5.2.
* The last sentence is a statement about cited work.

Witnesses: `Dissertation.Acceptance.A.rem_affine_hypotheses` for `rem_beta1_fibre` and
`rem_beta1_dich`: over a Lévy driver with `d = 1` and `ν = δ₀ ≠ 0` on `ℝ`, `𝒢₀ = ⊥`, `T = 1`,
`n = m = 1`, `G = 1` of full rank, Example 5.1(i) with `β₁ = β₂ = 1`, `σ_c = 0`, `h_c = 0`
satisfies Assumption 2.5 with `α = 1`. The antecedents inside (b) and (c) (an additive `h`;
`m < n`) do not hold at this instance; the witness meets the hypotheses of the proposition, and
(a) is not vacuous there. `Dissertation.Acceptance.A.ex_brownian_hypotheses` for
`rem_beta1_zero`: a Lévy driver with `ν = 0` independent of `𝒢₀ = ⊥`, and `T = 1`.

Verdict: `rem_beta1_dich` and `rem_beta1_zero` faithful; `rem_beta1_fibre` broader, at every
measurable mark space, the printed claim its instance at the countably generated `E` of §2.

<!-- spec-review: Dissertation.PaperSpec.A.rem_beta1_fibre ed839d34f480cba1c9fa0ba4a3588e95 by=claude-author -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.rem_beta1_fibre--claude-auditor--2026-10-19T03_26_06Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.rem_beta1_fibre ed839d34f480cba1c9fa0ba4a3588e95 by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.rem_beta1_dich ed839d34f480cba1312ac03d25ff8ea1 by=claude-author -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.rem_beta1_dich--claude-auditor--2026-10-19T03_34_36Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.rem_beta1_dich ed839d34f480cba1312ac03d25ff8ea1 by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.rem_beta1_zero ed839d34f480cba10a600b0e388b329d by=claude-author -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.rem_beta1_zero--claude-auditor--2026-10-19T03_38_14Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.rem_beta1_zero ed839d34f480cba10a600b0e388b329d by=claude-auditor -->

## Remark 2.11, the dissipativity margin: `Dissertation.PaperSpec.A.rem_margin_reduce`, `rem_margin_unweighted`, `rem_margin_smaller`

Manuscript (§2, Remark `rem:margin`): (2.7) holds with margin `c > 0` if (2.12) holds, the bound
of (2.7) with the further term `−c 𝔼[|G* δY|² + |G* δZ|²_F + ‖G* δU‖² + |G δX|²]`. "Suppose the
interior pairing has been bounded with constants `β̄₁, β̄₂`. For every `0 < c < min{β̄₁, β̄₂}` the
same bound is (2.12) with the reduced constants `βᵢ := β̄ᵢ − c` and margin `c`: recording weaker
constants turns the difference into slack, which a perturbation raising the interior pairing by at
most the margin leaves intact. When `m = n` both `G` and `G*` are injective, so the bounds of
Assumption 2.4, applied channel by channel, give `c (|G* δY|² + |G* δZ|²_F + ‖G* δU‖² + |G δX|²)
≥ (c / c_G)(|δY|² + |δZ|²_F + ‖δU‖² + |δX|²)`. A margin `c` in (2.12) therefore yields the margin
`c / c_G`, which is smaller than `c` when `c_G > 1`, in the unweighted form, which with margin
`c > 0` reads (2.13)", whose margin term is `−c 𝔼[|δY|² + |δZ|²_F + ‖δU‖² + |δX|²]`.

Propositions:

* `rem_margin_reduce`: in the standing setting (any `n, m, d`, `G` and coefficients), if (2.7)
  (`Mono27At`) holds with `β̄₁, β̄₂` for almost every `t ∈ [0, T]`, then for every
  `0 < c < min{β̄₁, β̄₂}`, (2.12) (`Margin212`, reviewed in `definitions.md`) holds with the
  constants `β̄₁ − c, β̄₂ − c` and margin `c`.
* `rem_margin_unweighted`: in the standing setting with `m = n ≥ 1`, for `G` of full rank and
  `c > 0`, (2.12) with `β₁, β₂` and margin `c` gives (2.13) (`Margin213`) with the same constants
  and margin `c / c_G`, `c_G = s_min(G)⁻²`.
* `rem_margin_smaller`: for `n ≥ 1`, `G ∈ ℝ^{n×n}` of full rank with `c_G = s_min(G)⁻² > 1` and
  `c > 0`, `c / c_G < c`.

Correspondence:

* "The interior pairing has been bounded with constants `β̄₁, β̄₂`": (2.7) with these constants at
  almost every `t`, the expectation of the pairing existing, as in Assumption 2.5. "The same bound
  is (2.12)": the right-hand sides agree, `−(β̄₁ − c) A − (β̄₂ − c) B − c (A + B) = −β̄₁ A − β̄₂ B`
  with `A, B` the weighted quantities. The use of the slack by a perturbation is Corollary 3.6
  (`cor_robust`) and Remark 3.7 (`rem_generalrank`).
* The channel-by-channel bound is the inequality of Assumption 2.4 (`ass_G`) at `m = n`, where
  both branches hold; `c_G = s_min(G)⁻²` is the printed constant. "Yields the margin `c / c_G`" is
  `rem_margin_unweighted`, the implication from (2.12) with margin `c` to (2.13) with margin
  `c / c_G` and the same constants.
* "Which is smaller than `c` when `c_G > 1`" compares the two margins: `rem_margin_smaller`, in
  the setting of the sentence (`m = n`, `G` of full rank, `c_G = s_min(G)⁻²`, `c > 0`). The
  sentence makes no claim that the margin `c` fails in (2.13), and the proposition does not
  state one.

Witnesses: `Dissertation.Acceptance.A.rem_affine_hypotheses` for `rem_margin_reduce` (over a Lévy
driver with `d = 1`, `ν = δ₀`, `𝒢₀ = ⊥`, `T = 1`, Example 5.1(i) with `β₁ = β₂ = 1` satisfies
Assumption 2.5 at `G = 1`, whose interior part is (2.7) with `β̄₁ = β̄₂ = 1`, and
`0 < 1/2 < min{1, 1}`); `Dissertation.Acceptance.A.rem_margin_hypotheses` for
`rem_margin_unweighted` (the same system satisfies (2.12) at `G = 1` with the constants `1/2, 1/2`
and margin `1/2 > 0`; at `G = 1`, `c_G = 1`, so this witness meets the hypotheses without showing
the factor `c_G`); `Dissertation.Acceptance.A.rem_margin_smaller_hypotheses` for
`rem_margin_smaller` (`G = 1/2 ∈ ℝ^{1×1}`, of full rank, with `s_min(G) = 1/2`, so `c_G = 4 > 1`,
and `c = 1`).

Verdict: faithful.

<!-- spec-review: Dissertation.PaperSpec.A.rem_margin_reduce ed839d34f480cba15843e0ffe4756126 by=claude-author -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.rem_margin_reduce--claude-auditor--2026-10-19T03_34_35Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.rem_margin_reduce ed839d34f480cba15843e0ffe4756126 by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.rem_margin_unweighted ed839d34f480cba1ba4163c9b3d796bd by=claude-author -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.rem_margin_unweighted--claude-auditor--2026-10-19T03_34_35Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.rem_margin_unweighted ed839d34f480cba1ba4163c9b3d796bd by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.rem_margin_smaller ed839d34f480cba133faa12dcf2189f6 by=claude-author -->

## Remark 3.4, uniqueness without origin integrability: `Dissertation.PaperSpec.A.rem_uniq_initial`, `rem_uniq_singular`, `rem_uniq_translation`

Manuscript (§3, Remark `rem:uniq-no-integ`): "Remark 3.2 would place each tuple `Θ ∈ ℍ_weak`
satisfying (1.1) individually in `ℍ` if Assumption 2.2 were imposed. But the uniqueness only
requires Assumptions 2.3–2.5, as we only need to show that the difference `Θ¹ − Θ²` belongs to
`ℍ`, using only the Lipschitz control of coefficient differences. The proof of Theorem 3.5 uses
Assumption 2.2. Its initial-data condition `ξ₀ ∈ L²` is necessary for a solution in `ℍ`, since
`X₀ = ξ₀` and `𝔼 sup_{t≤T} |X_t|² < ∞`; the origin-value conditions are sufficient but not
necessary. For instance, adding the deterministic drift `t^{-1/2} ∉ L²(0, T)` to the `b` of a
system satisfying Assumptions 2.2–2.5 violates Assumption 2.2 and leaves Assumptions 2.3–2.5
unchanged, yet the shift `X ↦ X − 2√t`, applied to the state and translating the law argument
accordingly, returns a system satisfying Assumptions 2.2–2.5, so a solution still exists."

Clauses:

* The first sentence is `rem_cwp_class` (Remark 3.2) and "the uniqueness only requires
  Assumptions 2.3–2.5" is `thm_uniq` (Theorem 3.3), whose hypotheses are (2.3) and
  Assumptions 2.3–2.5, without Assumption 2.2, for tuples of `ℍ_weak`; both are reviewed above.
  "As we only need to show …" describes the proof. "The proof of Theorem 3.5 uses Assumption 2.2"
  describes a proof and is not a clause.
* "`ξ₀ ∈ L²` is necessary for a solution in `ℍ`": `rem_uniq_initial`: in the standing setting,
  `T ≥ 0`, a tuple with `WeakSolution` (a tuple of `ℍ_weak` satisfying (1.1)) whose forward
  component has `𝔼 sup_{t ≤ T} |X_t|² < ∞` has every coordinate of `ξ₀` in `L²`. A solution in
  `ℍ` is such a tuple; the proposition needs no assumption on the coefficients, as the printed
  argument (`X₀ = ξ₀` and the `S²` bound) uses none.
* "The origin-value conditions are sufficient but not necessary": sufficiency is Theorem 3.5.
  Non-necessity is an existence claim, and `rem_uniq_singular` gives one instance: with
  `𝒢₀ = ⊥`, `n = m = 1`, any `d`, every Lévy driver and every `T > 0`, the affine
  coefficients of Example 5.1(i) taken at `β₁ = 1`, `β₂ = 0`, `σ_c = 0`, `h_c = 0` (outside the
  example's `β₂ > 0`, and still satisfying Assumptions 2.2–2.5)
  with `t^{-1/2}` added to `b` satisfies (2.3) and Assumptions 2.3–2.5 (`L = 1`, `G = 1`,
  `α = β₁ = 1`, `β₂ = 0`), violates Assumption 2.2 for every initial datum, and from `ξ₀ = 0` has
  a solution in `ℍ` (`Solution`: `WeakSolution` with finite `𝔼 sup |X|²` and `𝔼 sup |Y|²`, the
  drift integral read pathwise, as for every solution; the drift `t^{-1/2}` has infinite energy,
  which the solution notion does not exclude).
* The "For instance" sentence, for an arbitrary system, is `rem_uniq_translation`: in the
  standing setting with `n, m, d ≥ 1` (those of Theorem 3.5), for `T > 0`, a system `C` with
  initial datum `ξ₀` satisfying (2.3) and Assumptions 2.2–2.5 (`L, α, β₁, β₂`, `G` of full rank)
  and a nonzero `e ∈ ℝⁿ`: `C⁺ = C.addDrift (t ↦ t^{-1/2} e)` satisfies (2.3), Assumption 2.3
  with `L` and Assumption 2.5 with `G, α, β₁, β₂`, and violates Assumption 2.2 for every initial
  datum; `C̃ = translatedCoeffs C (t ↦ 2√t e) T` satisfies (2.3) and Assumptions 2.2, 2.3, 2.5
  with the same constants and `ξ₀`; and there is `(X, Y, Z, U)` with `Solution` for `C̃` from
  `ξ₀` such that `(X + 2√t e, Y, Z, U)` has `Solution` for `C⁺` from `ξ₀`.

Correspondence for `rem_uniq_translation`:

* "The deterministic drift `t^{-1/2}`" is a vector drift in `ℝⁿ`; it is read along an arbitrary
  nonzero direction `e`, the printed shift `X ↦ X − 2√t` along the same direction.
  `addDrift` is reviewed under `rem_uniq_singular`; `translatedCoeffs` (with `translateTuple`)
  in `definitions.md`: it evaluates `b, σ, h, f` at the tuple and law translated by `r_t` in the
  forward coordinate and `g` at `x + r_T` and the translated terminal law, which is "applied to
  the state and translating the law argument accordingly".
* Assumption 2.4 concerns `G` alone and is unchanged by both operations; it is a hypothesis.
* "So a solution still exists" is `Solution` for the system with the singular drift. The
  proposition also names the translated solution and the translation back, which is the printed
  route.

Witnesses: `Dissertation.Acceptance.A.rem_uniq_hypotheses` for `rem_uniq_initial` and
`rem_uniq_singular`: over a probability space carrying a Lévy driver with `d = 1`, `ν = δ₀`,
`𝒢₀ = ⊥`, `T = 1`, the singular system has a `Solution` from `0`;
`Dissertation.Acceptance.A.thm_cwp_hypotheses` for `rem_uniq_translation`: a system
satisfying (2.3) and Assumptions 2.2–2.5 over a standing basis with `n = m = d = 1`, with which
any `e ≠ 0` meets the hypotheses.

Verdict: broader for `rem_uniq_initial` (its hypothesis asks of the tuple of `ℍ_weak` only the
`S²` bound of `X`; a solution in `ℍ` is an instance); faithful for `rem_uniq_singular` and
`rem_uniq_translation`.

<!-- spec-review: Dissertation.PaperSpec.A.rem_uniq_initial ed839d34f480cba1fa628ed6b5f5989d by=claude-author -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.rem_uniq_initial--claude-auditor--2026-10-19T03_34_35Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.rem_uniq_initial ed839d34f480cba1fa628ed6b5f5989d by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.rem_uniq_singular ed839d34f480cba1ba6232c9763ebb54 by=claude-author -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.rem_uniq_singular--claude-auditor--2026-10-19T05_49_14Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.rem_uniq_singular ed839d34f480cba1ba6232c9763ebb54 by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.rem_uniq_translation ed839d34f480cba13b68ad605862c311 by=claude-author -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.rem_uniq_translation--claude-auditor--2026-10-19T05_49_14Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.rem_uniq_translation ed839d34f480cba13b68ad605862c311 by=claude-auditor -->

## The paragraph after Corollary 3.6: `Dissertation.PaperSpec.A.cor_margin_channels`, `cor_margin_additive`, `cor_margin_finite`, `cor_margin_continuous`, `cor_margin_separate`, `cor_margin_findim`

Manuscript (§3, the paragraph after Corollary `cor:robust`): "The margin hypothesis is demanding in the jump channel:
by the reduction of Remark 2.10, a margin in (2.13) forces every channel of the baseline to be
strictly dissipative. When `ν ≠ 0`, an additive `h₀ = h₀(t, x, e)` therefore cannot serve as a
baseline. When, moreover, `L²(ν)` is infinite-dimensional, jump feedback entering through finitely
many functionals of `u` supplies no margin either, since finitely many continuous functionals
cannot separate the points of an infinite-dimensional space; a margin then needs feedback
dissipative on the whole of `L²(ν)`, as in Examples 5.1(i) and 5.5. If `L²(ν)` is
finite-dimensional, as when `ν` is carried by finitely many atoms, finitely many functionals can
determine `u` and the second obstruction disappears."

Propositions:

* `cor_margin_channels`: in the standing setting, (2.13) (`Margin213`) with `β₁, β₂, c` gives,
  for almost every `t ∈ [0, T]` and all `(Θ, μ), (Θ', μ') ∈ 𝒟_t` that differ in one channel only,
  the inequality of that channel: `𝔼⟨−δf, G δX⟩ ≤ −β₂ 𝔼|G δX|² − c 𝔼|δX|²`,
  `𝔼⟨δb, Gᵀ δY⟩ ≤ −β₁ 𝔼|Gᵀ δY|² − c 𝔼|δY|²`, `𝔼⟨δσ, Gᵀ δZ⟩_F ≤ −β₁ 𝔼|Gᵀ δZ|²_F − c 𝔼|δZ|²_F`
  and `𝔼∫_E ⟨δh(e), Gᵀ δU(e)⟩ ν(de) ≤ −β₁ 𝔼‖Gᵀ δU‖² − c 𝔼‖δU‖²`.
* `cor_margin_additive`: for `m ≥ 1`, `T > 0`, `ν ≠ 0`, `β₁ ≥ 0`, `c > 0`, if `h(t, θ, μ)` depends
  on `t` and `x` only, (2.13) fails.
* `cor_margin_finite`: for `T > 0`, `L²(ν; ℝᵐ)` infinite dimensional, `β₁ ≥ 0`, `c > 0` and a
  linear map `ℓ : L²(ν; ℝᵐ) → ℝᵏ`, if `h(t, (x, y, z, u), δ_{(x,y,z,u)})` depends on `u` only
  through `ℓ u`, (2.13) fails.
* `cor_margin_separate`: for every real normed space `H` that is not finite dimensional, every
  `k` and every continuous `F : H → ℝᵏ`, `F` is not injective.
* `cor_margin_continuous`: in the standing setting with `d ≥ 1`, for `T > 0`, with
  `L²(ν; ℝᵐ)` not finite dimensional, all `β₁ ≥ 0`, `β₂`, `G`, `c > 0`, coefficients `C`, `k` and
  maps `F_t : L²(ν; ℝᵐ) → ℝᵏ` continuous for every `t`: if
  `h(t, θ, μ) = h(t, θ', μ)` whenever `θ, θ'` share `x, y, z` and `F_t u = F_t u'`, for every law
  `μ`, then (2.13) (`Margin213`) fails.
* `cor_margin_findim`: for `m = n ≥ 1`, `L²(ν; ℝⁿ)` finite dimensional, `T > 0`, `β₁, β₂ ≥ 0`,
  `c > 0`: some injective linear `ℓ : L²(ν; ℝⁿ) → ℝᵏ` exists, and Example 5.1(i) with the
  constants `β₁ + c, β₂ + c`, whose jump coefficient depends on `u` only through `ℓ u`, satisfies
  (2.13) at `G = I` with `β₁, β₂` and the margin `c`.

Readings:

* "Strictly dissipative": the channel inequality with the extra `−c 𝔼|δ·|²`, `c > 0`; a strict
  inequality for nonzero differences follows. "Every channel": the four channels `X, Y, Z, U`.
  The proposition does not assume `c > 0` or `β₁, β₂ ≥ 0`; it is the reduction, valid for any
  constants.
* "An additive `h₀ = h₀(t, x, e)` cannot serve as a baseline": a baseline of Corollary 3.6 is a
  system with (2.13) for a margin `c_diss > 0` and admissible constants (`β₁ ≥ 0`); the
  proposition shows (2.13) fails for every such margin. "Additive" is the reading of
  Remark 2.10 (`rem_beta1_dich`): `h(t, θ, μ)` depends on `t` and `x` only, its value being an
  element `h₀(t, x, ·)` of `L²(ν)`. Dimensions are general `m, n`; Corollary 3.6 has `m = n`.
* "Jump feedback entering through finitely many functionals of `u`": `cor_margin_finite` takes
  `k` **linear** functionals `ℓ = (ℓ₁, …, ℓ_k)` (continuity not assumed), with the jump
  coefficient depending on `u` only through `ℓ u` along deterministic inputs, where the law is the
  Dirac mass of the input. This covers coefficients `H(t, x, y, z, ℓ u, π_# μ)` with
  `π(θ) = (x, y, z, ℓ u)`, law-free ones in particular. The printed "finitely many continuous
  functionals" also admits **nonlinear** continuous functionals, and law dependence reading more
  of `u` than `ℓ u` (for example the mean of the `U`-marginal in `L²(ν)`); `cor_margin_finite`
  covers neither, so it is narrower than the printed sentence. The general reading is
  `cor_margin_continuous`: `h` depends on `u` only through `F_t u`, at each fixed
  `(t, x, y, z, μ)`, the dependence on `x, y, z`, on the law and on `t` being otherwise
  arbitrary, with "continuous functionals" taken from the sentence's justification. The
  conclusion "supplies no margin" is the failure of (2.13) for every margin `c > 0`, with
  admissible `β₁ ≥ 0`, in both.
* "Since finitely many continuous functionals cannot separate the points of an
  infinite-dimensional space" is `cor_margin_separate`, with `F` the vector of the `k`
  functionals, possibly nonlinear.
* `d ≥ 1` in `cor_margin_continuous` is part of the standing setting of Theorem 3.5 (`thm_cwp`);
  with a law dependence allowed, two inputs that the functionals do not separate must carry the
  same law, which needs one nontrivial event at a positive time, supplied by a Brownian
  coordinate.
* "A margin then needs feedback dissipative on the whole of `L²(ν)`" summarises the jump
  inequality of `cor_margin_channels`, which holds for every `δU`; it is not stated separately.
* "Finitely many functionals can determine `u` and the second obstruction disappears" is read as:
  an injective `ℓ` into some `ℝᵏ` exists, and a coefficient whose jump feedback enters only
  through it carries a margin. The proposition exhibits Example 5.1(i), whose jump coefficient
  `h_c − (β₁ + c) u` is a function of `ℓ u` for injective `ℓ`. "As when `ν` is carried by finitely
  many atoms" is an instance of the hypothesis and is not restated.

Witnesses:

* `cor_margin_channels`: `Dissertation.Acceptance.A.cor_robust_hypotheses`, whose baseline
  (Example 5.1(i) with `β₁ = β₂ = 2`, `ν = δ₀`) satisfies (2.13) at `G = 1` with
  `β₁ = β₂ = c = 1`.
* `cor_margin_additive`: `Dissertation.Acceptance.A.cor_margin_additive_hypotheses`: a Lévy
  driver with `ν = δ₀ ≠ 0` and `d = 1`, `𝒢₀ = ⊥`, and Example 5.1(i) with `n = 1`, `β₁ = 0`,
  `β₂ = 1`, `σ_c = 0`, `h_c = 0`, whose jump coefficient depends on `t, x` only; `m = 1`, `T = 1`,
  `β₁ = 0`, `c = 1` meet the remaining hypotheses.
* `cor_margin_finite`: `Dissertation.Acceptance.A.cor_margin_finite_hypotheses`: a Lévy driver
  with `ν` Lebesgue measure on `ℝ` and `d = 1`, `𝒢₀ = ⊥`; `L²(ν; ℝ¹)` is infinite dimensional
  (`not_finiteDimensional_Lp_volume`); and `rankOneCoeffs`, with jump coefficient
  `h = −⟨φ, u⟩ φ` for `φ = 1_{[0,1]}`, depends on `u` only through the single functional
  `ℓ u = ⟨φ, u⟩`. `T = 1`, `β₁ = 0`, `c = 1` meet the remaining hypotheses.
* `cor_margin_continuous`: `Dissertation.Acceptance.A.cor_margin_continuous_hypotheses`: the
  driver and `L²(ν; ℝ¹)` of `cor_margin_finite_hypotheses`, and at every time and every law the
  jump coefficient of `rankOneCoeffs` depends on `u` only through the continuous functional
  `u ↦ ⟨φ, u⟩`; the same witness meets the hypotheses of `cor_margin_separate`
  (`L²(ν; ℝ¹)` infinite dimensional and the continuous map `u ↦ ⟨φ, u⟩` into `ℝ¹`).
* `cor_margin_findim`: `Dissertation.Acceptance.A.cor_margin_findim_hypotheses`: a Lévy driver
  with `ν = δ₀` and `d = 1`, `𝒢₀ = ⊥`, and `L²(δ₀; ℝ¹)` finite dimensional; `n = 1`, `T = 1`,
  `β₁ = β₂ = 0`, `c = 1`, `σ_c = 0`, `h_c = 0` meet the remaining hypotheses.

Verdict: `cor_margin_channels`, `cor_margin_additive` and `cor_margin_continuous` broader: they hold
for every `m`, `n`, coupling matrix `G` and coefficient system, with no assumption on the system
beyond the hypotheses stated (and `cor_margin_channels` for all constants `β₁, β₂, c`); the printed
claims are their instances at a baseline of Corollary 3.6 (`m = n`, Assumptions 2.2–2.5, admissible
constants, `c > 0`). `cor_margin_finite` is broader in the same way relative to its linear reading,
whose instance at such a baseline is the linear, Dirac-input case of the printed sentence; it is
narrower than the sentence, which `cor_margin_continuous` reads in general, so together they cover
it. `cor_margin_separate` and `cor_margin_findim` faithful, in the readings recorded.

<!-- spec-review: Dissertation.PaperSpec.A.cor_margin_channels ed839d34f480cba14127298d8cc156d9 by=claude-author -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.cor_margin_channels--claude-auditor--2026-10-19T03_34_36Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.cor_margin_channels ed839d34f480cba14127298d8cc156d9 by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.cor_margin_additive ed839d34f480cba19075028a95edf84d by=claude-author -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.cor_margin_additive--claude-auditor--2026-10-19T03_34_35Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.cor_margin_additive ed839d34f480cba19075028a95edf84d by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.cor_margin_finite ed839d34f480cba15e05ed8a37017606 by=claude-author -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.cor_margin_finite--claude-auditor--2026-10-19T03_34_36Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.cor_margin_finite ed839d34f480cba15e05ed8a37017606 by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.cor_margin_continuous ed839d34f480cba1bd840ffee2f6a13b by=claude-author -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.cor_margin_continuous--claude-auditor--2026-10-19T03_34_36Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.cor_margin_continuous ed839d34f480cba1bd840ffee2f6a13b by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.cor_margin_separate ed839d34f480cba1b90f9a7b02bff832 by=claude-author -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.cor_margin_separate--claude-auditor--2026-10-19T03_26_48Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.cor_margin_separate ed839d34f480cba1b90f9a7b02bff832 by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.cor_margin_findim ed839d34f480cba153b1b629e759bb45 by=claude-author -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.cor_margin_findim--claude-auditor--2026-10-19T03_34_36Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.cor_margin_findim ed839d34f480cba153b1b629e759bb45 by=claude-auditor -->

## Section 5, the overview paragraph (`A:sec5:overview`)

Manuscript (§5, second paragraph, at `1f67672`): "Example 5.1 exhibits two dissipative models
meeting every assumption exactly, both at arbitrary jump activity: (i) a law-free affine base, and
(ii) mean-field coefficients. Examples 5.2 and 5.3 recover the Brownian [BYZ] and the
expectation-functional [LiMin] subclasses as special cases. Example 5.4 then carries the law
dependence beyond those subclasses, to genuinely nonlinear functionals of the full tuple and of
the jump integrand, and Example 5.5, a non-perturbative full `U`-law model, is a mean-field dealer
market in which the law of the `L²(ν)`-valued jump integrand arises as a population law on
valuation curves and enters the jump response through a monotone crowding operator, so that
well-posedness holds at every interaction strength; in an explicit specialisation the interaction
is active along the solution. In Examples 5.4 and 5.5, we take `ν ≠ 0`."

Correspondence:

* Example 5.1: `ex_concrete_i` and `ex_concrete_ii` (reviewed above), over every σ-finite `ν`
  ("at arbitrary jump activity").
* Examples 5.2 and 5.3: `ex_brownian` and `ex_expfunc` (reviewed above); the identification with
  the conditions of the cited papers is a statement about cited work.
* "Genuinely nonlinear functionals of the full tuple and of the jump integrand", read as in
  Example 5.4 (law statistics that are no expectation functionals, beyond the subclass of
  Example 5.3): `ex_fulllaw_beyond_radial` for the full tuple and `ex_fulllaw_beyond_U_corr` for
  the jump integrand, the latter with `L²(ν) ≠ {0}`, which the last sentence ("we take `ν ≠ 0`")
  supplies; reviewed under Example 5.4. The cylindrical term (`ex_fulllaw_beyond_Q`) is a further
  functional of the jump integrand.
* Example 5.5: "a monotone crowding operator" is `ex_dealer_mono`, "well-posedness holds at every
  interaction strength" is `ex_dealer_wp`, and "in an explicit specialisation the interaction is
  active along the solution" is `ex_dealer_active`, reviewed under Example 5.5. The population law
  on valuation curves is the modelling description.
* "We take `ν ≠ 0`" is a standing hypothesis of Examples 5.4 and 5.5, not a claim.

Verdict: each clause is the proposition named, reviewed in its own section.

## Example 5.4, nonlinear law functionals: `Dissertation.PaperSpec.A.ex_fulllaw_lip`, `ex_fulllaw_pert`, `ex_fulllaw_wp`, `ex_fulllaw_beyond_radial`, `ex_fulllaw_beyond_U_corr`, `ex_fulllaw_beyond_Q`, `ex_fulllaw_affineQ`

Manuscript (§5, Example `ex:fulllaw`): fix `μ₀ ∈ P₂(H)`, `Λ₀ ∈ P₂(L²(ν))`, `ε > 0`,
`𝔮, 𝔮̃, 𝔮̂ : ℝ₊ → ℝ`, `Q : ℝᴶ → ℝ`, `φ_1, …, φ_J : L²(ν) → ℝ`, `w₀, w₁ ∈ ℝᵐ`, `v₀ ∈ ℝⁿ`,
`ĥ ∈ L²(ν; ℝⁿ)`, "with `𝔮, 𝔮̃, 𝔮̂, Q` and the features `φ_j` bounded and Lipschitz". The baseline
`(b₀, σ₀, h₀, f₀, g)` is as in Corollary 3.6 (`m = n`, Assumptions 2.2–2.5, a margin
`c_diss > 0` in (2.13)); "Example 5.1(i) supplies such a baseline". The perturbation adds
`ε 𝔮(W₂(μ, μ₀)) w₀ + ε Q(∫ φ_1 dμ^U, …, ∫ φ_J dμ^U) w₁` to `f`, `ε 𝔮̃(W₂(μ^U, Λ₀)) v₀` to `b` and
`ε 𝔮̂(W₂(μ^U, Λ₀)) ĥ(e)` to `h`; "the baseline is taken law-free for simplicity: a law-dependent
dissipative baseline works identically". The law functionals are (i) "a nonlinear radial
statistic of the full tuple law", (ii) the same for the `U`-marginal, and (iii) "the `Q`-term, a
nonlinear cylindrical functional of the `U`-marginal: finitely many integrals of arbitrary
bounded-Lipschitz features on the fibre `L²(ν)`, composed through the
nonlinear `Q`". "For nonconstant `𝔮, 𝔮̃, 𝔮̂`, the radial statistics lie beyond the expectation and
two-point-kernel jump-integrand interactions of the preceding examples, and beyond the linear
jump-integrand expectations of the cited models. The cylindrical term does so when `Q` is
non-affine on the attained range of the feature vector `(∫ φ_1 dμ^U, …, ∫ φ_J dμ^U)`: if
`Q(s) = a + ∑_j c_j s_j` there, the `Q`-term equals `∫_H (a + ∑_j c_j φ_j(u')) μ(dθ')`, an
expectation functional already covered by Example 5.3. All three are `W₂`-Lipschitz in `μ`", with the constants `Lip(𝔮)` (by the triangle
inequality), `Lip(𝔮̃)`, `Lip(𝔮̂)` (by (2.11)) and `L_Q := Lip(Q)(∑_j Lip(φ_j)²)^{1/2}` (by
(2.10)). The perturbations satisfy the
origin integrability of Assumption 2.2, are independent of `θ` and satisfy (3.5) with
`L_p := ε(|w₀| Lip(𝔮) + |v₀| Lip(𝔮̃) + |w₁| L_Q + ‖ĥ‖ Lip(𝔮̂))`, "hence the diagonal Lipschitz
condition of Assumption 2.3 as well. By (3.5) and Corollary 3.6, (3.4) holds with
`c_pert = ‖G‖ L_p`, so the perturbed system is well-posed, with margin `c_diss − ‖G‖ L_p`,
whenever" (5.1) `ε ‖G‖ (…) < c_diss`.

Propositions:

* `ex_fulllaw_lip`: for σ-finite `ν` on a countably generated space, profiles Lipschitz on `ℝ`
  with constants `Lip(𝔮), Lip(𝔮̃), Lip(𝔮̂) ≥ 0`, `Q` Lipschitz for the Euclidean norm with
  `Lip(Q) ≥ 0`, features `φ_j` Lipschitz with `Lip(φ_j)`, and all `μ₀, Λ₀, μ, μ'`: the four
  bounds, with `W₂` of the Hilbert norm on `P₂(H)` (`w2H`) and of the norm on `P₂(L²(ν))` (`w2P`).
* `ex_fulllaw_pert`: in the standing setting with `m = n ≥ 1`, `d ≥ 1`, `T > 0`, any `G`,
  `ε > 0` and the data of `ex_fulllaw_lip`: the perturbation `ex54Pert` is independent of the
  tuple (`TupleIndep`), has square-integrable origin values (`OriginValues`), satisfies (3.5)
  (`LawLip35`) and the interior bound of Assumption 2.3 (`LipInterior`) with `L_p`, and (3.4)
  (`PairingBound34`) with `‖G‖ L_p`, `‖G‖` the operator norm.
* `ex_fulllaw_wp`: with these data and a baseline `C` with datum `ξ₀` satisfying (2.3),
  Assumptions 2.2–2.5 (`L₀`, `G` of full rank, `α, β₁, β₂`) and (2.13) with `c_diss > 0`: under
  (5.1) the perturbed system `C.perturb (ex54Pert …)` satisfies (2.3), Assumption 2.2 with `ξ₀`,
  Assumption 2.3 with some `L`, Assumption 2.5 with the baseline's `G, α, β₁, β₂` and (2.13) with
  margin `c_diss − ‖G‖ L_p`, has a `Solution`, and any two `Solution`s are equal in `ℍ`.
* `ex_fulllaw_beyond_radial`: for σ-finite `ν`, `n ≥ 1`, a bounded Lipschitz profile `𝔮` not
  constant on `[0, ∞)` and every `μ₀`: no `φ : H → ℝ` integrable against every law of `P₂(H)` has
  `𝔮(W₂(μ, μ₀)) = ∫ φ dμ` for all `μ ∈ P₂(H)`.
* `ex_fulllaw_beyond_U_corr`: the same for `𝔮̃(W₂(μ^U, Λ₀))`, with `L²(ν; ℝᵐ) ≠ {0}`.
* `ex_fulllaw_beyond_Q`: for bounded Lipschitz features and a Lipschitz `Q` not affine on the
  attained range `{(∫ φ_j dμ^U)_j : μ ∈ P₂(H)}` of the feature vector, no `φ' : H → ℝ` integrable
  against every law of `P₂(H)` has `Q((∫ φ_j dμ^U)_j) = ∫ φ' dμ` for all `μ`.
* `ex_fulllaw_affineQ`: for Lipschitz features and `Q` affine on the attained range,
  `Q(s) = a + ∑_j c_j s_j` at every `s = (∫ φ_j dμ^U)_j`, the `Q`-term is
  `∫_H (a + ∑_j c_j φ_j(u')) μ(dθ')` for every `μ ∈ P₂(H)`.

Correspondence:

* The perturbation is `ex54Pert` (reviewed in `definitions.md`), with no `σ`-perturbation as
  printed, and the perturbed system is `Coeffs.perturb`. With `m = n` the directions lie in `ℝⁿ`.
  The profiles are functions on `ℝ`, Lipschitz on `ℝ`; only their values on `[0, ∞)` enter, and a
  Lipschitz function on `ℝ₊` extends to `ℝ` with the same constant (`r ↦ 𝔮(|r|)`): a
  representation choice. `Lip(Q)` is taken for the Euclidean norm of `ℝᴶ`, the norm for which
  `L_Q` is the printed constant.
* The bounds on the profiles, on `Q` and on the features are printed; `ex_fulllaw_lip`,
  `ex_fulllaw_pert` and `ex_fulllaw_wp` do not use them and do not assume them, so they are
  broader. The perturbation is constant in time, so its origin values lie in `L²(0, T)` on a finite
  horizon in any case.
* "Independent of `θ`" is `TupleIndep`; "the diagonal Lipschitz condition of Assumption 2.3" is
  the interior bound `LipInterior` (the perturbation has no terminal function), as in
  Corollary 3.6. "(3.4) holds with `c_pert = ‖G‖ L_p`" is the (3.5) clause of Corollary 3.6
  (`cor_robust_lip`) applied to this perturbation; `ex_fulllaw_pert` does not need `G` of full
  rank and is broader.
* Well-posedness: as in Corollary 3.6, the baseline is arbitrary (law-dependent baselines
  included, which "works identically"; its forward–backward coupling is unrestricted, as the
  example's last sentence says), with (2.13) at the constants of Assumption 2.5. "Well-posed, with
  margin `c_diss − ‖G‖ L_p`" is read as: the perturbed system satisfies the hypotheses of
  Theorems 3.1, 3.3 and 3.5 ((2.3) and Assumptions 2.2–2.5) and (2.13) with that margin, and has
  the conclusion of Theorem 3.5 (as in `thm_cwp`). The estimate (3.1) and the uniqueness in
  `ℍ_weak` follow from `thm_stab` and `thm_uniq` and are not restated. (5.1) is as printed.
* "Beyond the expectation and two-point-kernel jump-integrand interactions … and beyond the linear
  jump-integrand expectations" is read as: the statistic, a function of `μ` alone, is no
  expectation functional `μ ↦ ∫ φ dμ`. A two-point kernel of Example 5.3 at fixed `(t, θ)` is the
  expectation functional of `φ̄(t, θ, ·)`, and a linear jump-integrand expectation is that of a
  linear function of `u`, so the reading excludes all three. `φ` ranges over all functions
  integrable against every law of `P₂(H)`, not only Lipschitz kernels: broader.
* "For nonconstant `𝔮, 𝔮̃, 𝔮̂`": the profile is asked not to be constant on `[0, ∞)`, where it
  is evaluated. For `n ≥ 1`, `W₂(μ, μ₀)` takes every value in `[0, ∞)` (translates of `μ₀` along
  the `X`-channel), so the statistic is not constant. The `U`-marginal proposition serves `𝔮̃` (in
  `b`) and `𝔮̂` (in the jump coefficient); its hypothesis `L²(ν; ℝᵐ) ≠ {0}` is the `ν ≠ 0` that the
  overview of §5 takes in this example (with `m ≥ 1` standing), and it is necessary: when
  `L²(ν; ℝᵐ) = {0}` every `U`-marginal is `δ₀` and the statistic is constant.
* "The cylindrical term does so when `Q` is non-affine on the attained range" is
  `ex_fulllaw_beyond_Q`; the printed bound on `Q` is not used and not assumed (broader). The
  converse sentence "if `Q(s) = a + ∑_j c_j s_j` there, the `Q`-term equals … an expectation
  functional" is `ex_fulllaw_affineQ`, with the features Lipschitz (bounded is not needed), so the
  integrals exist. "Already covered by Example 5.3" is not a conjunct of the proposition: it follows
  from its Lipschitz hypothesis, under which the kernel `θ' ↦ a + ∑_j c_j φ_j(u')` is measurable and
  Lipschitz in `θ'` for `|·|_H` (with constant `∑_j |c_j| Lip(φ_j)`), so that `ex_expfunc` applies
  to it.
* "On the fibre `L²(ν)`": the claims hold for every `ν` of the standing setting (with
  `L²(ν) ≠ {0}` where stated).

Witnesses:

* `Dissertation.Acceptance.A.ex_fulllaw_hypotheses` for `ex_fulllaw_lip`, `ex_fulllaw_pert` and
  `ex_fulllaw_wp`: over a Lévy driver with `d = 1`, `ν = δ₀` on `ℝ`, `𝒢₀ = ⊥`, `n = 1`, `T = 1`,
  the baseline Example 5.1(i) with `β₁ = β₂ = 2` and datum `0` (`L₀ = 2`, `G = 1`,
  `α = β₁ = β₂ = 1`, margin `c_diss = 1`), the baseline the example names; `ε = 1/4`,
  `𝔮 = 𝔮̃ = 𝔮̂ = min{|·|, 1}`, `Q(s) = min{|s₁|, 1}`, `φ₁(u) = min{‖u‖, 1}`,
  `w₀ = w₁ = v₀ = e₁`, `ĥ = 0`, all Lipschitz constants `1`, so `L_p = 3/4` and (5.1) reads
  `3/4 < 1`. The jump direction `ĥ = 0` is an instance the example allows; the drift and driver
  perturbations are nonzero.
* `Dissertation.Acceptance.A.ex_fulllaw_beyond_hypotheses` for `ex_fulllaw_beyond_radial` and
  `ex_fulllaw_beyond_U_corr`: at `ν = δ₀` on `ℝ`, the unit vector `e₁ ≠ 0` of `L²(ν; ℝ)`, the
  profile `min{|r|, 1}` (bounded, `1`-Lipschitz, not constant on `[0, ∞)`) and the kernel `0`,
  integrable against every law; `n = 1` for the radial statistic.
* `Dissertation.Acceptance.A.ex_fulllaw_beyond_Q_hypotheses` for `ex_fulllaw_beyond_Q`: at
  `ν = δ₀` on `ℝ`, `J = 1`, `φ₁(u) = min{‖u‖, 1}` (bounded, `1`-Lipschitz) and
  `Q(s) = min{|s₁|, 1/2}` (`1`-Lipschitz), not affine on the attained range: at the Dirac laws
  with `U`-channel `0`, `e₁/2`, `e₁` the feature takes the values `0, 1/2, 1` and `Q` the values
  `0, 1/2, 1/2`.
* `Dissertation.Acceptance.A.ex_fulllaw_affineQ_hypotheses` for `ex_fulllaw_affineQ`: at
  `ν = δ₀` on `ℝ`, `J = 1`, the `1`-Lipschitz feature `φ₁(u) = min{‖u‖, 1}` and `Q(s) = s₁`,
  affine, with `a = 0`, `c₁ = 1`.

Verdict: broader, each with its instantiation; the profiles on `ℝ` and the Euclidean `Lip(Q)` are
representation choices. `ex_fulllaw_lip`, `ex_fulllaw_pert` and `ex_fulllaw_wp` drop the boundedness
of the profiles, of `Q` and of the features (`ex_fulllaw_pert` also takes any `G`, and
`ex_fulllaw_wp` any baseline of Corollary 3.6); the printed claims are their instances at bounded
data and, for `ex_fulllaw_wp`, at the baseline the example names or any other.
`ex_fulllaw_beyond_radial`, `ex_fulllaw_beyond_U_corr` and `ex_fulllaw_beyond_Q` exclude every
function integrable against every law of `P₂(H)`, not only the expectation and kernel interactions
of the preceding examples, at general dimensions (and `ex_fulllaw_beyond_Q` without the bound on
`Q`); the printed claims are their instances at `m = n` and the interactions of Examples 5.1–5.3.
`ex_fulllaw_affineQ` drops the boundedness of the features; the printed claim is its instance at
bounded Lipschitz features.

<!-- spec-review: Dissertation.PaperSpec.A.ex_fulllaw_lip ed839d34f480cba11fea7903ed24f9f8 by=claude-author -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.ex_fulllaw_lip--claude-auditor--2026-10-19T03_34_36Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_fulllaw_lip ed839d34f480cba11fea7903ed24f9f8 by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_fulllaw_pert ed839d34f480cba1e9dade95deb0a071 by=claude-author -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.ex_fulllaw_pert--claude-auditor--2026-10-19T03_34_36Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_fulllaw_pert ed839d34f480cba1e9dade95deb0a071 by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_fulllaw_wp ed839d34f480cba173d663ff51153197 by=claude-author -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.ex_fulllaw_wp--claude-auditor--2026-10-19T03_34_36Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_fulllaw_wp ed839d34f480cba173d663ff51153197 by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_fulllaw_beyond_radial ed839d34f480cba1fc87ff54d30df5ad by=claude-author -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.ex_fulllaw_beyond_radial--claude-auditor--2026-10-19T03_37_07Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_fulllaw_beyond_radial ed839d34f480cba1fc87ff54d30df5ad by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_fulllaw_beyond_U_corr ed839d34f480cba193f328d7c8c243ea by=claude-author -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.ex_fulllaw_beyond_U_corr--claude-auditor--2026-10-19T03_37_48Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_fulllaw_beyond_U_corr ed839d34f480cba193f328d7c8c243ea by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_fulllaw_beyond_Q ed839d34f480cba12be9f13eb8df21c1 by=claude-author -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.ex_fulllaw_beyond_Q--claude-auditor--2026-10-19T03_38_27Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_fulllaw_beyond_Q ed839d34f480cba12be9f13eb8df21c1 by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_fulllaw_affineQ ed839d34f480cba1b7c4d4b7307e74ea by=claude-author -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.ex_fulllaw_affineQ--claude-auditor--2026-10-19T03_37_37Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_fulllaw_affineQ ed839d34f480cba1b7c4d4b7307e74ea by=claude-auditor -->

## Example 5.5, the mean-field dealer market: `Dissertation.PaperSpec.A.ex_dealer_potential`, `ex_dealer_crowd`, `ex_dealer_coeffs`, `ex_dealer_ham`, `ex_dealer`, `ex_dealer_mono`, `ex_dealer_wp`, `ex_dealer_twopoint`, `ex_dealer_mean_corr`, `ex_dealer_not_mean_corr`, `ex_dealer_affine`, `ex_dealer_marks`, `ex_dealer_riccati`, `ex_dealer_inert`, `ex_dealer_spec_marks`, `ex_dealer_zero`, `ex_dealer_symm`, `ex_dealer_active`, `ex_dealer_depends`

Manuscript (§5, Example `ex:dealer`, at `1f67672`). The crowding correction
`A_λ(u) := ∫_{L²(ν)} ∇V(u − v) λ(dv)`, `V(w) := √(1 + ‖w‖²) − 1`, `λ ∈ P₂(L²(ν))`; "the potential
`V` is even and convex, with `∇V(w) = w / √(1 + ‖w‖²)`, `‖∇V(w)‖ ≤ 1`, `Lip(∇V) ≤ 1`". "Fix
`ε ≥ 0` and `h_x ∈ L²(ν)`, make the jump response of Example 5.1(i) exposure-sensitive, and tilt
it by the crowding correction: `b = −β₁ y`, `σ = σ_c − β₁ z`,
`h = h_c + h_x x − β₁ u − ε A_{μ^U}(u)`, `f = β₂ x + ⟨h_x, u⟩_{L²(ν)}`, `g(x, ρ) = x`, with `μ^U`
the `U`-marginal of the measure argument. … In the control problem the latter enters the
Hamiltonian as `⟨h_x x, u⟩_{L²(ν)}`, whose `x`-derivative is the added driver term
`⟨h_x, u⟩_{L²(ν)}`. At `ε = 0` and `h_x = 0` this is Example 5.1(i) verbatim." Assumptions
2.2–2.4: the origin value `h(·, 0, δ₀) = h_c` is unchanged, so Assumption 2.2 holds;
`‖A_λ(u) − A_λ'(u')‖ ≤ ‖u − u'‖ + W₂(λ, λ')` and (2.11) give Assumption 2.3 "with
`L = max{β₁ + ε + ‖h_x‖, β₂ + ‖h_x‖, 1}`"; joint Lipschitz continuity gives (2.3); Assumption 2.4
holds as in Example 5.1(i). Monotonicity at arbitrary `ε`: along `(Θ, μ), (Θ', μ') ∈ 𝒟_t`,
`𝔼⟨A_{μ^U}(U) − A_{μ'^U}(U'), U − U'⟩ ≥ 0`; "the exposure terms cancel between the jump and driver
channels, `⟨h_x δX, δU⟩ − ⟨h_x, δU⟩ δX = 0`", the interior bound
`𝔼[∫_E ⟨δh(e), δU(e)⟩ ν(de) + ⟨−δf, δX⟩] ≤ −β₁ 𝔼‖δU‖² − β₂ 𝔼|δX|²`, "and (2.7) holds with the
constants `α = 1, β₁, β₂` of Example 5.1(i) for every `ε ≥ 0` … Theorem 3.5 applies directly."
Beyond the mean: the two-point laws `λ₁ = ½(δ_{−w} + δ_w)`, `λ₂ = ½(δ_{−2w} + δ_{2w})` share their
mean, with `A_{λ₁}(w) = w / √5`, `A_{λ₂}(w) = ½(3/√10 − 1/√2) w`; "the correction is nonlinear in
the valuation curves, but affine in their population law:
`A_{sλ₁ + (1 − s)λ₂} = s A_{λ₁} + (1 − s) A_{λ₂}` for `s ∈ [0, 1]`. It is an expectation kernel in
the sense of Example 5.3, with `L²(ν)` in the role of `K`". Marks and activity:
`E = {−1, +1} × (0, 1]`, `ν(dς, dq) = c_ς q^{−1−ϱ} dq`, `c_ς > 0`, `0 < ϱ < 2`: `ν(E) = ∞`,
`∫ q² dν < ∞`, `h_c(ς, q) = ς q ∈ L²(ν)`. The interaction is active: "for `h_x = 0`, with `p` the
positive solution of `p' = β₁ p² − β₂`, `p(T) = 1`, the tuple `Y_t = p(t) X_t`,
`Z_t = p(t) σ_c / (1 + β₁ p(t))`, `U_t = p(t) h_c / (1 + β₁ p(t))` solves the system, so
`Law(U_t)` is a Dirac mass, `A_{Law(U_t)}(U_t) = ∇V(0) = 0`, and the same tuple solves it for every
`ε`." "Take `β₁ = 1`, `β₂ = ½`, `σ_c = 1`, `ξ₀ = 0`, `c_{±1} = (2 − ϱ)/2`, `h_c(ς, q) = ς q` and
`h_x(ς, q) = q`, so that `‖h_c‖ = ‖h_x‖ = 1` and `⟨h_c, h_x⟩ = 0`." The linear equation
`X⁰_t = ∫_0^t (−X⁰_s ds + ½ dW_s) + ½ ∫_0^t ∫_E (h_c(e) + h_x(e) X⁰_{s−}) Ñ(ds, de)` "has Lipschitz
coefficients, hence a unique solution `X⁰ ∈ S²(ℝ)`"; the tuple `Y⁰ = X⁰`, `Z⁰ = ½`,
`U⁰_t = ½(h_c + h_x X⁰_{t−})` solves the system at `ε = 0`; `𝔼 X⁰_t = 0`, `v' = −(7/4) v + ½`,
`𝔼‖U⁰_t − 𝔼U⁰_t‖² = v(t)/4 = (1/14)(1 − e^{−7t/4})`, so `Law(U⁰_t)` is not a Dirac mass for
`t ∈ (0, T]`; the symmetrised identity
`∫ ⟨A_λ(u), u⟩ λ(du) = ½ ∬ ‖u − v‖² / √(1 + ‖u − v‖²) λ(du) λ(dv)`, positive unless `λ` is a
Dirac mass; hence `A_{Law(U⁰_t)}(U⁰_t) ≠ 0` with positive probability for every `t ∈ (0, T]`;
for every `ε > 0`, `𝔼 ∫_0^T ‖ε A_{Law(U^ε_t)}(U^ε_t)‖² dt > 0`; "the solution therefore depends
on `ε`: if one tuple solved the system at two strengths, … the crowding correction [would]
vanish `dt ⊗ dP`-a.e."

Propositions (each in the standing setting with `n = m = d = 1` where a basis appears):

* `ex_dealer_potential`, `ex_dealer_crowd`, `ex_dealer_twopoint`, `ex_dealer_mean_corr`,
  `ex_dealer_marks`: the potential (even, convex, gradient `∇V`, `‖∇V‖ ≤ 1`, 1-Lipschitz, on
  `L²(ν)` for every `ν`); the crowding bound with `W₂` of `L²(ν)`; the two-point laws; no `Φ`
  with `A_λ(u) = Φ(∫ v λ(dv), u)` for all `λ, u` when `L²(ν) ≠ {0}`; the mark measure.
* `ex_dealer_coeffs`: `ex55Coeffs` at `ε = 0`, `h_x = 0` is `affineCoeffs`.
* `ex_dealer_ham`: the Hamiltonian of Example 5.1(i) with `⟨h_x x, u⟩` added has `x`-derivative
  `β₂ x + ⟨h_x, u⟩`, at every point and control.
* `ex_dealer`: for `T > 0`, `β₁, β₂ > 0`, `σ_c`, `h_c, h_x`, `ε ≥ 0`, `ξ₀ ∈ L²(Ω, ℱ₀)`:
  `h(t, 0, δ₀) = h_c`, (2.3), Assumption 2.2, Assumption 2.3 with the printed `L`, `G = 1` of full
  rank with `c_G = 1`.
* `ex_dealer_mono`: at every `t` and all pairs of `𝒟_t`, the crowding inequality; the exposure
  cancellation for all `δx ∈ ℝ`, `δu ∈ L²(ν)`; the interior bound; Assumption 2.5 with `G = 1`,
  `α = 1`, `β₁, β₂`.
* `ex_dealer_wp`: the conclusion of Theorem 3.5 for every `ε ≥ 0` and `h_x`.
* `ex_dealer_not_mean_corr`: when `L²(ν) ≠ {0}`, no `Φ` of the mean and `u`, and for some
  `λ ∈ P₂(L²(ν))` the map `u ↦ A_λ(u)` is not affine.
* `ex_dealer_affine`: the mixture identity for `λ₁, λ₂ ∈ P₂(L²(ν))`, `s ∈ [0, 1]`; for `μ ∈ P₂(H)`,
  `A_{μ^U}(u) = ∫_H 𝐇(u, u') μ(dθ')` with `𝐇(u, u') = ∇V(u − u')`; and
  `‖𝐇(u₁, u₁') − 𝐇(u₂, u₂')‖ ≤ |θ₁ − θ₂|_H + |θ₁' − θ₂'|_H`.
* `ex_dealer_riccati`: for `β₁, β₂, T > 0`, a `p` with `p' = β₁ p² − β₂` on `[0, T]`, `p(T) = 1`,
  `p > 0`; and any two solutions of `q' = β₁ q² − β₂`, `q(T) = 1`, on `[0, T]` agree there.
* `ex_dealer_inert`: for `h_x = 0` and such a `p`: a solution exists, and every solution has
  `Y_t = p(t) X_t` a.s. at each `t ∈ [0, T]`, `Z = p σ_c / (1 + β₁ p)` and
  `U = p h_c / (1 + β₁ p)` for `dt ⊗ dP` on `[0, T]`, the `U`-marginal of `Law(Θ⁻_s)` the Dirac
  mass at `p(s) h_c / (1 + β₁ p(s))` and the correction zero a.s. at a.e. `s`, and the tuple
  solves (1.1) at every `ε' ≥ 0`.
* `ex_dealer_spec_marks`: for `0 < ϱ < 2` and `ex55Marks ϱ`: `ς q, q ∈ L²(ν)`, both of square norm
  `1`, orthogonal.
* `ex_dealer_zero`: for the classes `h_c, h_x` of `ς q`, `q`: the linear equation `ex55Linear` has
  a solution with `𝔼 sup |X⁰|² < ∞` and left limits along every path; solutions are
  indistinguishable on `[0, T]`; for every solution, `Θ⁰` solves (1.1) at `β₁ = 1`, `β₂ = ½`,
  `σ_c = 1`, `ε = 0`, `ξ₀ = 0`; `𝔼 X⁰_t = 0`, `v = (2/7)(1 − e^{−7t/4})` on `[0, T]`,
  `v' = −(7/4) v + ½` on `(0, T)`; and on `(0, T]` the variance identity and that `Law(U⁰_t)` is no
  Dirac mass.
* `ex_dealer_symm`: the symmetrised identity for `λ ∈ P₂(L²(ν))` and positivity off Dirac masses.
* `ex_dealer_active`: in the specialisation, `P{A_{Law(U⁰_t)}(U⁰_t) ≠ 0} > 0` at every
  `t ∈ (0, T]`; and for every `ε > 0` and every solution at `ε`, the energy of `ε A` is positive.
* `ex_dealer_depends`: for `β₁, β₂ > 0` and `ε, ε' ≥ 0`, a tuple solving at `ε ≠ ε'` has the
  correction zero for `dt ⊗ dP`; in the specialisation, no tuple solves at two strengths
  `ε ≠ ε'` in `[0, ∞)`.

Correspondence:

* The setting is that of Example 5.1(i), which the example modifies: `n = m = d = 1`, `G = 1`,
  `ξ₀ ∈ L²(Ω, ℱ₀)`, `σ_c ∈ ℝ`, `h_c, h_x ∈ L²(ν)`, `β₁, β₂ > 0`, `ε ≥ 0`. The overview of §5 takes
  `ν ≠ 0` in this example. `ex_dealer_mean_corr` and `ex_dealer_not_mean_corr` assume `L²(ν) ≠ {0}`,
  which for σ-finite `ν` is equivalent to `ν ≠ 0` (`rem_beta1_fibre`: `ν ≠ 0` gives a nonzero
  element, and `ν = 0` makes `L²(ν) = {0}`), so they are at the printed generality.
  `ex_dealer_marks` and the specialisation (`ex_dealer_spec_marks`, `ex_dealer_zero`,
  `ex_dealer_active` and the second clause of `ex_dealer_depends`) are at the printed mark measure,
  and `ex_dealer_twopoint` asks a unit vector of `L²(ν)`, so `ν ≠ 0`. `ex_dealer`, `ex_dealer_mono`,
  `ex_dealer_wp` and `ex_dealer_inert`, and with them the other propositions not tied to the mark
  measure (`ex_dealer_crowd`, `ex_dealer_coeffs`, `ex_dealer_affine`, `ex_dealer_symm`, the first
  clause of `ex_dealer_depends`), hold for every σ-finite `ν` on a countably generated space,
  `ν = 0` included: broader, the printed claims their instances at `ν ≠ 0`. `ex_dealer_potential`
  holds for every measure `ν` on every measurable space, with none of the standing hypotheses on
  `E`, and `ex_dealer_ham` likewise for all real `β₁, β₂`: broader, the printed claims their
  instances in the setting of the example. The coefficients are `ex55Coeffs` (reviewed in
  `definitions.md`).
* `ex_dealer_ham`: "the latter enters the Hamiltonian as `⟨h_x x, u⟩`, whose `x`-derivative is the
  added driver term" is stated on the Hamiltonian of Example 5.1(i) (`ex_concrete_i_ham`) with that
  term added, whose full `x`-derivative is the driver `f = β₂ x + ⟨h_x, u⟩`. The control problem
  itself and the stochastic maximum principle are cited work (as for Example 5.1(i)).
* `ex_dealer`: the printed `L`; its interior part from the crowding bound and
  `‖h_x x − h_x x'‖ = ‖h_x‖ |x − x'|`, `|⟨h_x, u − u'⟩| ≤ ‖h_x‖ ‖u − u'‖`.
* `ex_dealer_mono`: the quantifier "for every `ε ≥ 0`" and constants free of `ε`; the inequalities
  at every `t`, not only almost every `t` (the coefficients do not depend on `t`): broader. The
  integrand of the crowding inequality is bounded by `2 ‖U − U'‖`, so its Bochner integral is
  the expectation. The `π ⊗ π` symmetrisation and "no auxiliary random variable on `Ω` is needed"
  describe the proof.
* "Nonlinear in the valuation curves" is read as: for some law the correction is not an affine
  function of `u`; "affine in their population law" as the mixture identity at `s ∈ [0, 1]`;
  "an expectation kernel in the sense of Example 5.3, with `L²(ν)` in the role of `K`" as the
  integral representation against the full measure argument with the kernel `∇V(u − u')`,
  Lipschitz in `(θ, θ')` for `|·|_H` (the hypotheses of `ex_expfunc` with `K = L²(ν)`). "Dependence
  nonlinear in the law itself is that of Example 5.4" is a cross-reference.
* `ex_dealer_riccati`, `ex_dealer_inert`: "the positive solution" is read as existence of a
  positive solution on `[0, T]` and uniqueness among solutions on `[0, T]` with `p(T) = 1`. "The
  tuple … solves the system" is read through Theorem 3.5: a solution exists, and every solution
  (all agree in `ℍ`, Theorem 3.3) has the printed `Y, Z, U`, `X` being the forward state of the
  system along them. `Z` and `U` are elements of `ℍ`, defined up to `dt ⊗ dP`-null sets, so their
  identities, the Dirac law and the vanishing of the correction are stated for almost every `s`;
  `Law(U_s)` is the `U`-marginal of `Law(Θ⁻_s)`, the argument of the jump coefficient in (1.1).
* `ex_dealer_marks`: the printed mark measure with its encodings: the sides as `Bool`, `true` for
  `+1`, so that `h_c(ς, q) = ς q` is `(if ς then 1 else −1) q`; the sizes as the subtype `(0, 1]` of
  `ℝ` with Lebesgue measure carried to it (`comap`); `ν` the measure with density
  `ofReal (c_ς q^{−1−ϱ})` against counting measure times that Lebesgue measure, the printed
  `c_ς q^{−1−ϱ} dq` with counting measure in `ς`; `ν(E) = ∞` as `ν univ = ∞`; `∫ q² dν < ∞` as a
  lower integral of `ofReal (q²)`; and `h_c ∈ L²(ν)` as `MemLp` of exponent `2`. The hypotheses
  `c_ς > 0`, `0 < ϱ < 2` are the printed ones, so the proposition is not broader.
* `ex_dealer_spec_marks`: the printed choices; `ex55Marks ϱ` is `dealerMarks` with
  `c_{±1} = (2 − ϱ)/2` (reviewed in `definitions.md`).
* `ex_dealer_zero`: "a unique solution `X⁰ ∈ S²(ℝ)`" is existence in `S²` with càdlàg-type paths
  and indistinguishability of any two solutions of `ex55Linear` (`ex55Linear` reviewed in
  `definitions.md`); "`Θ⁰ ∈ ℍ`" is part of `Solution`. The printed intermediate
  `v' = −2v + ¼ + ¼(‖h_c‖² + ‖h_x‖² v)`, the computation of `σ, h, f` along `Θ⁰` and "Itô's formula
  with (2.4)" are steps of the proof. `v' = −(7/4) v + ½` is stated on the open interval, where
  the two-sided derivative is defined.
* `ex_dealer_active`: "with positive probability" is `0 < P{…}`; the law in the first clause is the
  image of `P` under `U⁰_t`. The second clause holds for every solution at `ε`, not only the one of
  Theorem 3.5 (they agree by Theorem 3.3), and `Law(U^ε_t)` is read as in `ex_dealer_inert`. The
  contradiction argument is a step of the proof.
* `ex_dealer_depends`: "the solution therefore depends on `ε`" is the second clause; the
  conditional sentence is the first, stated for the constants of Example 5.5 (`β₁, β₂ > 0`,
  `ε, ε' ≥ 0`), every σ-finite `ν` and every initial datum; "subtracting the forward equations and
  the compensated-Poisson isometry" describes its proof.
* Not formalised: the dealer-market reading (requests for quotes, valuation curves, routing,
  quotes affine in the curve, the uncontrolled exposure change at an event, the small-ticket
  limit), which is modelling, and the finite-player inspiration (Cont and Xiong), which is cited
  work.

Witnesses: `Dissertation.Acceptance.A.ex_dealer_hypotheses` for `ex_dealer`, `ex_dealer_mono`,
`ex_dealer_wp`, `ex_dealer_coeffs`, `ex_dealer_ham`, `ex_dealer_potential` and `ex_dealer_crowd`
(the mark measure
of the example with `c_{±1} = 1/2`, `ϱ = 1`; a Lévy driver with `d = 1` on it; `𝒢₀ = ⊥`; the datum
`0`; `T = β₁ = β₂ = ε = 1`); `ex_dealer_unit_hypotheses` for `ex_dealer_twopoint`,
`ex_dealer_mean_corr`, `ex_dealer_not_mean_corr`, `ex_dealer_affine` and `ex_dealer_symm` (a unit
`h_c` on the same mark space); `ex_dealer_marks_hypotheses` for `ex_dealer_marks`;
`ex_dealer_inert_hypotheses` for `ex_dealer_riccati` and `ex_dealer_inert`; and
`ex_dealer_spec_hypotheses` for `ex_dealer_spec_marks`, `ex_dealer_zero`, `ex_dealer_active` and
`ex_dealer_depends` (`ϱ = 1`, a Lévy driver on `ex55Marks 1`, `𝒢₀ = ⊥`, `T = 1`, the classes of
`ς q` and `q`).
`ex_dealer_potential` has no hypotheses, so it needs no witness; the one linked
(`ex_dealer_hypotheses`) is not needed for it.

Verdict: broader, each with the instantiation above, for `ex_dealer`, `ex_dealer_mono`,
`ex_dealer_wp` and `ex_dealer_inert` (every σ-finite `ν`, `ν = 0` included, and the inequalities of
`ex_dealer_mono` at every `t`) and the other propositions not tied to the mark measure
(`ex_dealer_crowd`, `ex_dealer_coeffs`, `ex_dealer_affine`, `ex_dealer_symm`, `ex_dealer_depends`,
the last also for every initial datum); for `ex_dealer_ham` and `ex_dealer_potential` (every measure
`ν` on every measurable space, `ex_dealer_ham` for all real `β₁, β₂`); and for `ex_dealer_active`
(every solution). Faithful: `ex_dealer_twopoint`, `ex_dealer_mean_corr` and
`ex_dealer_not_mean_corr` (`L²(ν) ≠ {0}` being `ν ≠ 0`), `ex_dealer_marks` with the encodings
listed, `ex_dealer_riccati`, `ex_dealer_spec_marks` and `ex_dealer_zero`.

<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_potential ed839d34f480cba1c2e5952133294af3 by=claude-author -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.ex_dealer_potential--claude-auditor--2026-10-19T03_27_12Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_potential ed839d34f480cba1c2e5952133294af3 by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_crowd ed839d34f480cba1542ac74da98a0887 by=claude-author -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.ex_dealer_crowd--claude-auditor--2026-10-19T03_27_20Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_crowd ed839d34f480cba1542ac74da98a0887 by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_coeffs ed839d34f480cba17c7bbab57e15328e by=claude-author -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.ex_dealer_coeffs--claude-auditor--2026-10-19T03_27_20Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_coeffs ed839d34f480cba17c7bbab57e15328e by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_ham ed839d34f480cba18d97e926abe7317b by=claude-author -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.ex_dealer_ham--claude-auditor--2026-10-19T03_27_20Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_ham ed839d34f480cba18d97e926abe7317b by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer ed839d34f480cba1e2c74601c0086824 by=claude-author -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.ex_dealer--claude-auditor--2026-10-19T03_34_36Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer ed839d34f480cba1e2c74601c0086824 by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_mono ed839d34f480cba17aa9ad92a733a79a by=claude-author -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.ex_dealer_mono--claude-auditor--2026-10-19T03_34_36Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_mono ed839d34f480cba17aa9ad92a733a79a by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_wp ed839d34f480cba1382a433c842b2a2c by=claude-author -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.ex_dealer_wp--claude-auditor--2026-10-19T03_34_36Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_wp ed839d34f480cba1382a433c842b2a2c by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_twopoint ed839d34f480cba10e7a45835d5244c0 by=claude-author -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.ex_dealer_twopoint--claude-auditor--2026-10-19T03_27_19Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_twopoint ed839d34f480cba10e7a45835d5244c0 by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_mean_corr ed839d34f480cba18bab6ae8a6c6a027 by=claude-author -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.ex_dealer_mean_corr--claude-auditor--2026-10-19T03_27_19Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_mean_corr ed839d34f480cba18bab6ae8a6c6a027 by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_marks ed839d34f480cba140a65f520ffefa33 by=claude-author -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.ex_dealer_marks--claude-auditor--2026-10-19T03_27_26Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_marks ed839d34f480cba140a65f520ffefa33 by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_not_mean_corr ed839d34f480cba1d76cfc2366e08961 by=claude-author -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.ex_dealer_not_mean_corr--claude-auditor--2026-10-19T03_27_19Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_not_mean_corr ed839d34f480cba1d76cfc2366e08961 by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_affine ed839d34f480cba14f86326a4c8f6eab by=claude-author -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.ex_dealer_affine--claude-auditor--2026-10-19T03_27_20Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_affine ed839d34f480cba14f86326a4c8f6eab by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_riccati ed839d34f480cba122071b255b506300 by=claude-author -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.ex_dealer_riccati--claude-auditor--2026-10-19T03_27_19Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_riccati ed839d34f480cba122071b255b506300 by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_inert ed839d34f480cba141c76d0c8dddc879 by=claude-author -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.ex_dealer_inert--claude-auditor--2026-10-19T03_34_36Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_inert ed839d34f480cba141c76d0c8dddc879 by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_spec_marks ed839d34f480cba1efd7d1ab7e3204fd by=claude-author -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.ex_dealer_spec_marks--claude-auditor--2026-10-19T03_26_36Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_spec_marks ed839d34f480cba1efd7d1ab7e3204fd by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_zero ed839d34f480cba1fbee3842d146d0f8 by=claude-author -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.ex_dealer_zero--claude-auditor--2026-10-19T03_34_36Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_zero ed839d34f480cba1fbee3842d146d0f8 by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_symm ed839d34f480cba11753a45d7d37cdc6 by=claude-author -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.ex_dealer_symm--claude-auditor--2026-10-19T03_27_19Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_symm ed839d34f480cba11753a45d7d37cdc6 by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_active ed839d34f480cba11684a792fea39139 by=claude-author -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.ex_dealer_active--claude-auditor--2026-10-19T03_34_35Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_active ed839d34f480cba11684a792fea39139 by=claude-auditor -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_depends ed839d34f480cba1d5b82af653b55a54 by=claude-author -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.ex_dealer_depends--claude-auditor--2026-10-19T05_49_14Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_depends ed839d34f480cba1d5b82af653b55a54 by=claude-auditor -->

## Remark 5.6, the scope of the measure argument: `Dissertation.PaperSpec.A.rem_freelaw`

Manuscript (§5, Remark `rem:freelaw`): "The proofs consume the tuple law through a single
mechanism: the `W₂` term of Assumption 2.3, dominated at every use by the synchronous coupling
bound (2.8). The right-hand side of (2.8) carries `𝔼‖δU‖²` whether or not the measure argument
reads the `U`-marginal, because the coefficients depend on `u` pointwise — a dependence
Remark 2.10 makes unavoidable whenever `β₁ > 0` and `ν ≠ 0`: for `w ∈ L²(ν)` with `G* w ≠ 0` and a
symmetric sign `ξ` independent of the other components, the tuples with `U = ξ w` and `U' = −ξ w`
and equal other components have the same law, so coefficients reading `u` only through the law make
the left-hand side of (2.7) vanish, while its right-hand side is `−4 β₁ ‖G* w‖² < 0`. Nothing is
therefore gained by restricting the coefficients to the `(X, Y, Z)`-marginal law: with the
coupling bound taken in `H`, the estimates close at the full tuple law, and Example 5.5 exhibits that scope arising from
a routing mechanism rather than by construction."

The bound (2.8) is `eq_coupling` (reviewed above). The pointwise dependence is read here.

Proposition `rem_freelaw`: in the standing setting with `ν ≠ 0`, for `n, m, d ≥ 1`, `T > 0`, `G`
of full rank and coefficients satisfying Assumption 2.5 with `β₁ > 0`, for almost every
`t ∈ [0, T]` there are `(Θ, μ), (Θ', μ') ∈ 𝒟_t` with the same law `μ = μ'` and the same `X, Y, Z`
at every `ω`, at which `h(t, Θ, μ) ≠ h(t, Θ', μ')` with positive probability.

Correspondence:

* "The coefficients depend on `u` pointwise": the jump coefficient is not a function of
  `(t, x, y, z, μ)`. The proposition exhibits this along the diagonal, where the hypotheses live,
  at two inputs with one law: there every law term of a coefficient is the same and only the
  pointwise dependence on `u` differs, which is "whether or not the measure argument reads the
  `U`-marginal".
* "A dependence Remark 2.10 makes unavoidable whenever `β₁ > 0` and `ν ≠ 0`": under Assumption 2.5
  with `β₁ > 0` (and `G` of full rank, Assumption 2.4, with which it is stated) and `ν ≠ 0`. The
  proof applies the reduction of Remark 2.10 (`rem_beta1_dich`) to `U = B u₀` and `U' = −B u₀`,
  with `B = W¹_t − W¹_0` and `G* u₀ ≠ 0`, which have one law; `d ≥ 1` (standing) and `t > 0`
  supply the centred Gaussian `B`. This is the printed argument, with the symmetric random factor `B`
  in place of the sign `ξ`.
* "The proofs consume the tuple law through a single mechanism" and "nothing is therefore gained
  …" describe the proofs and are not formalised; the scope exhibited by Example 5.5 is the content
  of `ex_dealer`–`ex_dealer_wp`.

Witness: `Dissertation.Acceptance.A.rem_affine_hypotheses` (Example 5.1(i) with `β₁ = β₂ = 1`
over a Lévy driver with `d = 1`, `ν = δ₀ ≠ 0`, `𝒢₀ = ⊥`, `T = 1`, `n = m = 1`: Assumption 2.5 at
`G = 1`, of full rank, with `α = 1` and `β₁ = 1 > 0`).

Verdict: faithful.

<!-- spec-review: Dissertation.PaperSpec.A.rem_freelaw ed839d34f480cba105f02a9629cb6b98 by=claude-author -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.rem_freelaw--claude-auditor--2026-10-19T03_34_36Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.rem_freelaw ed839d34f480cba105f02a9629cb6b98 by=claude-auditor -->

## Remark 5.7, perturbative and non-perturbative law dependence (`A:rem:regimes`)

Manuscript (§5, Remark `rem:regimes`): "Example 5.4 shows that arbitrary nonlinear full-tuple law
dependence can be added when it is smaller than the dissipativity margin. Example 5.5 shows that a
`U`-law interaction nonlinear in the valuation curves can have arbitrary strength when its
geometry is itself monotone, and remain active along the solution."

The remark summarises the two examples; its clauses are propositions reviewed there:

* The first sentence is `ex_fulllaw_pert` (the added dependence satisfies (3.4) with
  `c_pert = ‖G‖ L_p`), `ex_fulllaw_wp` (well-posed when (5.1), `c_pert < c_diss`, holds) and
  `ex_fulllaw_beyond_radial` (the added dependence is no expectation functional), reviewed under
  Example 5.4. "Arbitrary" is read as in Example 5.4, its three families with arbitrary bounded
  Lipschitz profiles, features and outer function; for any `θ`-independent `W₂`-Lipschitz
  perturbation the statement is Corollary 3.6 with (3.5).
* "A `U`-law interaction nonlinear in the valuation curves" is `ex_dealer_not_mean_corr`: the
  crowding correction is no function of the mean of the `U`-law together with `u`, and for some
  law it is not affine in `u`, with `L²(ν) ≠ {0}` (the `ν ≠ 0` of the overview of §5).
* "Can have arbitrary strength when its geometry is itself monotone" is `ex_dealer_mono` and
  `ex_dealer_wp` (monotone and well-posed at every `ε ≥ 0`), and "remain active along the
  solution" is `ex_dealer_active`, reviewed under Example 5.5.

Verdict: covered by the clauses listed, each as reviewed under its example.

## Section 6, the conclusion (`A:conclusion`)

Manuscript (§6, at `1f67672`): "Theorems 3.1, 3.3 and 3.5 establish global well-posedness, with a
quantitative stability estimate, for fully coupled MV-FBSDEJ with `W₂`-dependence on the law of
the whole tuple, including the `L²(ν)`-valued jump integrand, at arbitrary σ-finite jump activity.
By Corollary 3.6, the well-posedness is robust, at `m = n`, under full-tuple-law perturbations
below the dissipativity margin. The Lipschitz and monotonicity assumptions are imposed only along
the diagonal inputs `(Θ_t, Law(Θ_t)) ∈ 𝒟_t`: Proposition 3.8 shows that expected diagonal
`G`-monotonicity is strictly weaker than its pointwise form (Remark 2.8). The monotonicity of
Assumption 2.5 is the principal structural assumption and is still coercive; in the `m < n` regime
with `ν ≠ 0` it forces strictly `U`-dissipative jump feedback (Remark 2.10). Relaxing that
coercivity, so that additive jump coefficients become admissible when `m < n`, and treating
domination-monotonicity conditions, developed for Brownian mean-field systems [ChenNie, TianYu,
WuHao] and for Lévy-driven systems without mean-field dependence [XuTangMeng], or conditional laws
under common noise, are the natural next questions."

Correspondence:

* The first sentence: `thm_stab`, `thm_uniq` and `thm_cwp`, over every σ-finite `ν`.
* The second: `cor_robust_wp`.
* The third: `prop_strict` and `rem_diag_mono`.
* The fourth: `rem_beta1_dich` (Remark 2.10, with `ν ≠ 0`), reviewed under Remark 2.10; "still
  coercive" is the admissibility of the constants in Assumption 2.5.
* The last sentence names open questions and cited work.

Verdict: each clause is the proposition named, reviewed in its own section.
