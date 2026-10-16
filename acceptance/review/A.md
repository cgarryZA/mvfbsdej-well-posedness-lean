# Reviews of the statements of paper A (well-posedness, `e939294`)

Each entry reads the manuscript passage and the proposition side by side. The marker records the
hash of the proposition reviewed; a change of the proposition reopens the entry.

## Remark 2.6, (2.8): `Dissertation.PaperSpec.A.eq_coupling`

Manuscript (`paper/sections/02-model-assumptions.tex`, Remark "Wasserstein bounds"): for two
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

## Remark 2.6, (2.9): `Dissertation.PaperSpec.A.eq_couplingT`

Manuscript: `W₂(ρ, ρ')² ≤ 𝔼|δX|²` for the induced terminal laws `ρ = Law(X_T)`,
`ρ' = Law(X'_T)`, "the `X`-marginal case of (2.8)".

Proposition: for every probability space, all `n` and all `X, X' : Ω → ℝⁿ` in `L²`,
`w2P (lawP2 P X) (lawP2 P X')² ≤ ∫ ‖X − X'‖² dP`, with `w2P` the 2-Wasserstein distance of the
Euclidean norm on `P₂(ℝⁿ)`.

Correspondence: `X_T, X'_T ∈ L²(Ω, ℱ_T; ℝⁿ)` in the manuscript; the proposition asks square
integrability only, so it is broader, and the printed claim is its instance at `ℱ_T`-measurable
terminal values.

Verdict: faithful (broader, printed claim an instance).

<!-- spec-review: Dissertation.PaperSpec.A.eq_couplingT ed839d34f480cba1b0b3c75b14edd5d3 by=claude-author -->

## Theorem 3.1: `Dissertation.PaperSpec.A.thm_stab`

Manuscript (`paper/sections/03-main-results.tex`, Theorem `thm:stab`): system 1 satisfies
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
it was not a trivial instance was wrong (GitHub #247).

Verdict: faithful.

<!-- spec-review: Dissertation.PaperSpec.A.thm_stab ed839d34f480cba16bc55062de98e587 by=claude-author -->

## Theorem 3.3: `Dissertation.PaperSpec.A.thm_uniq`

Manuscript (`paper/sections/03-main-results.tex`, Theorem `thm:uniq`): under Assumptions 2.3–2.5,
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

## Theorem 3.5: `Dissertation.PaperSpec.A.thm_cwp`, and its continuous dependence

Manuscript (`paper/sections/03-main-results.tex`, Theorem `thm:cwp`): for every horizon `T > 0`,
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

## Proposition 3.8: `Dissertation.PaperSpec.A.prop_strict`

Manuscript (`paper/sections/03-main-results.tex`, Proposition `prop:strict`): let `n = m = 1`,
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

## Corollary 3.6: `Dissertation.PaperSpec.A.cor_robust`, `cor_robust_wp`, `cor_robust_lip`

Manuscript (`paper/sections/03-main-results.tex`, Corollary `cor:robust`): let `m = n`, the
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
  `C_stab` of `(T, L, ‖G‖, c_G, α, β₁, β₂)` chosen first, `L` a Lipschitz constant of the
  perturbed system; the `δh` of (3.1) along `Θ²⁻` as in `thm_stab`.
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
(`sys_two_perturb_feedback`). `Dissertation.Acceptance.A.cor_robust_lip_hypotheses`: the constant
perturbation `p_σ = e₁₁` is independent of `θ` and satisfies (3.5) with `L_p = 1`.

Verdict: faithful, with the reading of the perturbed system's measurability recorded; the (3.5)
clause broader, the printed claim an instance.

<!-- spec-review: Dissertation.PaperSpec.A.cor_robust ed839d34f480cba154326c82c977c8bd by=claude-author -->
<!-- spec-review: Dissertation.PaperSpec.A.cor_robust_wp ed839d34f480cba1858a2d606d9d9c09 by=claude-author -->
<!-- spec-review: Dissertation.PaperSpec.A.cor_robust_lip ed839d34f480cba14b18016daa0b4aac by=claude-author -->

## Assumption 2.4 (the bounds after "Then"): `Dissertation.PaperSpec.A.ass_G`

Manuscript (`paper/sections/02-model-assumptions.tex`, Assumption `ass:G`): `G ∈ ℝ^{m×n}` has
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

## Lemma 4.1: `Dissertation.PaperSpec.A.lem_bpbsde`

Manuscript (`paper/sections/04-proof-wellposedness.tex`, Lemma `lem:bpbsde`): let `δY` be a càdlàg
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

## Lemma 4.2: `Dissertation.PaperSpec.A.lem_small`

Manuscript (`paper/sections/04-proof-wellposedness.tex`, Lemma `lem:small`): under Assumptions
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

## Lemma 4.3: `Dissertation.PaperSpec.A.lem_pert`

Manuscript (Lemma `lem:pert`): under Assumptions 2.3–2.5, for `λ̲ ∈ (0, 1]` and
`λ ∈ [λ̲, 1]`, let `Θ¹, Θ²` solve (4.1) at `λ` with `ℱ₀`-measurable initial data `ξ₀^k` and
forcings `q^k`, where `X^k, Y^k` are càdlàg adapted with `𝔼 ∫_0^T (|X^k|² + |Y^k|²) dt < ∞`,
`X^k_T ∈ L²(Ω, ℱ_T)`, `Z^k ∈ H²_W`, `U^k ∈ H²_N`, and `Θ¹ − Θ² ∈ ℍ`. Then (4.13) holds with
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
* (4.13): `supSize` and `dataSize` (reviewed with Theorem 3.1) with the differences of the data.

Witness: `Dissertation.Acceptance.A.lem_pert_hypotheses`: at Example 5.1(i), `λ̲ = λ = 1`, zero
forcing and datum `0`, the solution of Theorem 3.5 as a solution of (4.1) in `ℍ_weak`, taken
twice.

Verdict: faithful.

<!-- spec-review: Dissertation.PaperSpec.A.lem_pert ed839d34f480cba1eefcd4522364d865 by=claude-author -->

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

Witness: `Dissertation.Acceptance.A.thm_cwp_hypotheses` (Example 5.1(i)); the premise `WP(λ₀)` of
the continuation step is met at `λ₀ = λ*` by `lem_small`.

Verdict: faithful (broader, printed claim an instance).

<!-- spec-review: Dissertation.PaperSpec.A.lem_cont ed839d34f480cba15f6eb38f12c8d372 by=claude-author -->

## Example 5.1(i): `Dissertation.PaperSpec.A.ex_concrete_i_ham`, `ex_concrete_i`, `ex_concrete_i_pairing`, `ex_concrete_i_wp`

Manuscript (`paper/sections/05-examples.tex`, Example `ex:concrete`, part (i)): `n = m = d = 1`,
`G = 1`, `ν` σ-finite, `ξ₀ ∈ L²(Ω, ℱ₀; ℝⁿ)`, `σ_c ∈ ℝ`, `h_c ∈ L²(ν)`, `β₁, β₂ > 0`. The
Hamiltonian `H` of the control problem is strictly convex in the controls with pointwise minimiser
`a^{b*} = −β₁ y`, `a^{σ*} = −β₁ z`, `a^{h*} = −β₁ u`, "so by the stochastic maximum principle
for jump diffusions [TangLi]" the optimality system is (1.1) with `b = −β₁ y`, `σ = σ_c − β₁ z`,
`h = h_c − β₁ u`, `f = β₂ x`, `g(x, ρ) = x`. Assumptions 2.2 and 2.3 hold with
`L = max{β₁, β₂, 1}`; Assumption 2.4 with `c_G = 1`; the interior and terminal pairings of (2.7)
evaluate exactly to `−β₁ 𝔼[|δY|² + |δZ|²_F + ‖δU‖²] − β₂ 𝔼|δX|²` and `𝔼|δX_T|²`; Assumption 2.5
holds with equality and `α = 1`, "so Theorem 3.5 yields well-posedness"; the identity carries any
margin `0 < c < min{β₁, β₂}` (Remark 2.7), unweighted with the same constant since `c_G = 1`; and
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
* The margin: Remark 2.7 turns a bound with constants `β̄₁, β̄₂` into (2.12) with
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

Verdict: faithful (the pairings at every `t`, `β₂` arbitrary in `ex_concrete_i_ham`: broader).

<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_i_ham ed839d34f480cba1cf9f26355b828c6a by=claude-author -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_i ed839d34f480cba1d2f6e8919288ad6b by=claude-author -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_i_pairing ed839d34f480cba1272d037d1e16e040 by=claude-author -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_i_wp ed839d34f480cba13343e4213bb7f62d by=claude-author -->

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
<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_i_clamp_wp ed839d34f480cba14bccae170a8d514d by=claude-author -->

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
<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_ii ed839d34f480cba1cba84bcbe1866633 by=claude-author -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_ii_pairing ed839d34f480cba16aa5f84a4f3328b5 by=claude-author -->

## Example 5.2: `Dissertation.PaperSpec.A.ex_brownian`

Manuscript (Example `ex:brownian`): remove the Poisson channel, so that the filtration is
generated by `W` and `ℱ₀` and the representation property is the Brownian one; delete the
`U`-coordinate, reducing `H` to `ℝⁿ × ℝᵐ × ℝ^{m×d}` ("merely setting `h ≡ 0` on a
Brownian–Poisson basis is not a reduction"). The assumptions reduce to `W₂`-Lipschitz joint-law
dependence of `(X, Y, Z)` under `G`-monotonicity, the condition of [BYZ, (A1)]; with no jump
channel the `U`-dissipativity constraint of Remark 2.10 is vacuous, so both rank branches of
Assumption 2.5 are available. Remark 2.10 adds: "When `ν = 0` the fibre `L²(ν)` is trivial,
`δU = 0` identically, and the restriction disappears: this is the Brownian case of Example 5.2, in
which both rank branches remain available."

Proposition: in the standing setting with `ν = 0` (any `d`, any countably generated `E`):
(a) `enlJoint 𝒢₀ D = augFiltration (ℱ^W ⊔ 𝒢₀)₊ P`, the usual augmentation of the filtration
generated by `W` and `𝒢₀`; (b) every `u ∈ L²(0; ℝᵐ)` is `0`; (b') for all `μ, μ' ∈ P₂(H)`,
`w2P (projP2 μ) (projP2 μ') = w2H μ μ'`: `W₂` on `P₂(H)` is `W₂` on the laws of `(X, Y, Z)` in
`ℝⁿ × ℝᵐ × ℝ^{m×d}` with its Euclidean norm; (c) for `1 ≤ m < n`, `d ≥ 1`,
`T > 0` and `ξ₀ ∈ L²(ℱ₀)` there are `G` of full rank and coefficients whose jump coefficient
depends on `(t, θ, μ)` only through `(t, x)` (the additive form `h(t, x, e)` of Remark 2.10), with
(2.3) and Assumptions 2.2–2.5 for some `L, α, β₁, β₂` with `β₁ > 0`.

Correspondence:

* "The Brownian case" is the standing setting at `ν = 0`, the reading of Remark 2.10. Clause (a)
  shows that it is the Brownian basis of the example: the Poisson measure of intensity `0`
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
  `ex_brownian_rank_gt` (both reviewed below, GitHub #244). The reduction itself (the
  assumptions and the solution notions at `ν = 0` coincide with their Brownian forms) is an open
  clause.

Witness: `Dissertation.Acceptance.A.ex_brownian_hypotheses` (a Lévy driver with `ν = 0` on `ℝ`,
`d = 1`, `𝒢₀ = ⊥`, `m = 1 < n = 2`, datum `0`).

Verdict: faithful.

<!-- spec-review: Dissertation.PaperSpec.A.ex_brownian ed839d34f480cba13b36df98cbfaee33 by=claude-author -->

## Example 5.3: `Dissertation.PaperSpec.A.ex_expfunc`, `ex_expfunc_limin`, `ex_expfunc_jump`

Manuscript (Example `ex:expfunc`): `φ̄ : [0, T] × H × H → ℝᵏ` measurable and Lipschitz in
`(θ, θ')` uniformly in `t`, and `φ(t, θ, μ) = ∫_H φ̄(t, θ, θ') μ(dθ')`: at fixed `t, θ` this is the
Bochner mean of `φ̄(t, θ, ·)`, whose Lipschitz constant is at most `Lip(φ̄)`, so (2.10) supplies
the law-dependence component of Assumption 2.3. For the independent-copy interactions of [LiMin],
with `ψ̄` Lipschitz in all arguments but `t`, for the Euclidean norm on each argument block
`(x, y, z, u(e))`, `(x', y', z', u'(e))`, and `φ̄(t, θ, θ') = ∫_E ψ̄(t, x, y, z, u(e), x', y', z',
u'(e)) ν(de)`: the integral is finite at every `(θ, θ')`; with a constant finite when
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
* "Lipschitz for the Euclidean norm on each argument block" is written out as the square root
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

Verdict: faithful (the three propositions broader than printed, as listed).

<!-- spec-review: Dissertation.PaperSpec.A.ex_expfunc ed839d34f480cba1c0ebc41bbfe679cc by=claude-author -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_expfunc_limin ed839d34f480cba1dc8d682dbdc81fa7 by=claude-author -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_expfunc_jump ed839d34f480cba1e622a1683bfc9f0d by=claude-author -->

## Example 5.4: `Dissertation.PaperSpec.A.ex_fulllaw_lip`, `ex_fulllaw_pert`, `ex_fulllaw_wp`, `ex_fulllaw_affineQ`, `ex_fulllaw_beyond_radial`, `ex_fulllaw_beyond_U`, `ex_fulllaw_beyond_U_corr`, `ex_fulllaw_beyond_Q`

Manuscript (Example `ex:fulllaw`): fix `μ₀ ∈ P₂(H)`, `Λ₀ ∈ P₂(L²(ν))`, `ε > 0`, bounded Lipschitz
`𝔮, 𝔮̃, 𝔮̂ : ℝ₊ → ℝ`, `Q : ℝᴶ → ℝ`, `φ_j : L²(ν) → ℝ`, directions `w₀, w₁ ∈ ℝᵐ`, `v₀ ∈ ℝⁿ`,
`ĥ ∈ L²(ν; ℝⁿ)`; the baseline is as in Corollary 3.6 (`m = n`, Assumptions 2.2–2.5, a margin
`c_diss > 0` in (2.13); Example 5.1(i) supplies one); perturb `f` by
`ε 𝔮(W₂(μ, μ₀)) w₀ + ε Q(∫ φ_1 dμ^U, …, ∫ φ_J dμ^U) w₁`, `b` by `ε 𝔮̃(W₂(μ^U, Λ₀)) v₀` and `h` by
`ε 𝔮̂(W₂(μ^U, Λ₀)) ĥ`. Claims: (a) for nonconstant `𝔮, 𝔮̃, 𝔮̂` the radial statistics lie beyond
the expectation and two-point-kernel interactions of the preceding examples (and beyond the linear
jump-integrand expectations of the cited models); (b) the cylindrical term does so when `Q` is
non-affine on the attained range of the feature vector, and if `Q(s) = a + ∑ c_j s_j` there it is
the expectation functional `∫ (a + ∑ c_j φ_j(u')) μ(dθ')`; (c) all three statistics are
`W₂`-Lipschitz with constants `Lip(𝔮)`, `Lip(𝔮̃)`, `Lip(𝔮̂)`, `L_Q = Lip(Q)(∑ Lip(φ_j)²)^{1/2}`;
(d) the perturbations satisfy the origin integrability of Assumption 2.2, are independent of `θ`,
satisfy (3.5) with `L_p = ε(|w₀| Lip(𝔮) + |v₀| Lip(𝔮̃) + |w₁| L_Q + ‖ĥ‖ Lip(𝔮̂))`, hence the
diagonal Lipschitz condition of Assumption 2.3; (e) by Corollary 3.6, (3.4) holds with
`c_pert = ‖G‖ L_p`, and the perturbed system is well-posed, with margin `c_diss − ‖G‖ L_p`,
whenever (5.1) `ε ‖G‖ (…) < c_diss`.

Propositions:

* `ex_fulllaw_lip` — (c), for every σ-finite `ν` on a countably generated space, all `n, m, d, J`,
  Lipschitz data (with nonnegative constants) and all `μ₀, Λ₀, μ, μ'`.
* `ex_fulllaw_pert` — (d) and (3.4) of (e): in the standing setting with `m = n`, `T > 0`, `G`,
  `ε > 0` and Lipschitz data, `ex54Pert …` (the printed perturbation, reviewed in
  `definitions.md`) is `TupleIndep`, has `OriginValues`, satisfies `LawLip35` and `LipInterior`
  with `L_p` and `PairingBound34` with `‖GX G‖ L_p`.
* `ex_fulllaw_wp` — (e): under the baseline hypotheses of `cor_robust`, Lipschitz data, `ε > 0`
  and (5.1), the perturbed system `C.perturb (ex54Pert …)` satisfies (2.3), Assumption 2.2, some
  Assumption 2.3, Assumption 2.5 with the baseline's `G, α, β₁, β₂`, `Margin213` with margin
  `c_diss − ‖GX G‖ L_p`, and has a solution unique in `ℍ` (the conclusion of `thm_cwp`).
* `ex_fulllaw_affineQ` — (b), second half: for Lipschitz features and `Q` affine on the attained
  range, the `Q`-term equals `∫_H (a + ∑_j c_j φ_j(θ'.u)) μ(dθ')`.
* `ex_fulllaw_beyond_radial` — (a) for `𝔮`: for `n ≥ 1`, every bounded Lipschitz `𝔮` not constant
  on `[0, ∞)` and every `μ₀`, no `φ` integrable against every law of `P₂(H)` has
  `𝔮(W₂(μ, μ₀)) = ∫ φ dμ` for all `μ`.
* `ex_fulllaw_beyond_U` — (a) for `𝔮̃, 𝔮̂`, as printed: the same for `𝔮̃(W₂(μ^U, Λ₀))` at every
  σ-finite `ν` and `m ≥ 1`. **Refuted** by `ex_fulllaw_beyond_U_false`: at `ν = 0` the fibre
  `L²(ν)` is `{0}`, every `U`-marginal is `δ₀ = Λ₀`, and the statistic is the constant
  `𝔮̃(0)`, the expectation functional of a constant, for the bounded Lipschitz non-constant
  `𝔮̃(r) = min(|r|, 1)`.
* `ex_fulllaw_beyond_U_corr` — the corrected statement: the same with `L²(ν; ℝᵐ) ≠ {0}`.
* `ex_fulllaw_beyond_Q` — (b), first half: for bounded Lipschitz features and Lipschitz `Q` not
  affine on the attained range, the `Q`-term is no expectation functional.

Correspondence:

* The standing setting of §2 admits `ν = 0` (σ-finite), and the example fixes no condition on
  `ν`; its closing sentence of Remark 2.10 treats `ν = 0` as the Brownian case. The refutation is
  of the `U`-marginal sentence as printed; the manuscript edit is to add `ν ≠ 0` (REMEDIATION
  A1s). The full-law radial statistic and the cylindrical term are not affected.
* "Lie beyond the expectation … interactions" is read as: not an expectation functional
  `μ ↦ ∫ φ dμ` of the law, the form every such interaction takes at a fixed state. The kernel `φ`
  is only asked to be integrable against every law of finite second moment, which is broader than
  the Lipschitz kernels of Example 5.3, so the propositions are the stronger reading.
* The profiles are functions on `ℝ` with a global Lipschitz bound; they are applied to distances,
  so only their restriction to `[0, ∞)` enters, and "not constant" is asked on `[0, ∞)`. The
  boundedness of the data is assumed where the printed claim could depend on it (the "beyond"
  clauses); in `ex_fulllaw_lip`, `ex_fulllaw_pert`, `ex_fulllaw_wp` and `ex_fulllaw_affineQ` it is
  not assumed, so these are broader.
* (5.1) is written `ε ‖GX G‖ (…) < c_diss`, `‖GX G‖` the operator norm `‖G‖`.
* The clauses (a) for general `μ₀`, `Λ₀` and the first half of (b) are proved at the printed
  generality (2026-10-01): for (a), the mixtures `(1 − t) μ₀ + t δ_{R v}` realise every distance to
  the reference law by the intermediate value theorem, while affinity along mixtures would keep
  `𝔮(r)` within `2 t sup |𝔮|` of `𝔮(0)` (`not_affineAlongMixtures_of_radialProfile`, which uses
  the boundedness of the profile and not its Lipschitz constant); for (b), an expectation
  functional makes `Q` affine along the segments of the attained range, a convex set, hence equal
  there to an affine function (`exists_affine_eq_of_affine_segments`, finite dimension). The
  earlier library results for Dirac reference laws and for a two-point chord condition on `Q`
  (`radial_ne_integral`, `radialU_ne_integral`, `cylindrical_margU_ne_integral`) are special
  cases.
* Not formalised: the comparison with the linear jump-integrand expectations of the cited models,
  and the sentence on the trade against the weak-coupling route (statements about cited work and
  exposition).

Witnesses: `Dissertation.Acceptance.A.ex_fulllaw_hypotheses` (the baseline of Corollary 3.6's
instance, Example 5.1(i) with `β₁ = β₂ = 2`, margin `c_diss = 1`; `ε = 1/4`, profiles
`min(|r|, 1)`, `Q(s) = min(|s₁|, 1)`, `φ₁(u) = min(‖u‖, 1)`, unit directions, `ĥ = 0`, so
`L_p = 3/4 < 1`); `ex_fulllaw_affineQ_hypotheses` (`Q(s) = s₁`); `ex_fulllaw_beyond_hypotheses`
(a unit vector of `L²(δ₀)`, the profile `min(|r|, 1)`, the kernel `0`);
`ex_fulllaw_beyond_Q_hypotheses` (`Q(s) = min(|s₁|, 1/2)`, `φ₁(u) = min(‖u‖, 1)`, not affine on
the attained values `0, 1/2, 1`).

Verdict: faithful, with the printed `U`-marginal sentence refuted at `ν = 0` and corrected by
`ν ≠ 0`.

<!-- spec-review: Dissertation.PaperSpec.A.ex_fulllaw_lip ed839d34f480cba11fea7903ed24f9f8 by=claude-author -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_fulllaw_pert ed839d34f480cba1e9dade95deb0a071 by=claude-author -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_fulllaw_wp ed839d34f480cba173d663ff51153197 by=claude-author -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_fulllaw_affineQ ed839d34f480cba1b7c4d4b7307e74ea by=claude-author -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_fulllaw_beyond_radial ed839d34f480cba1fc87ff54d30df5ad by=claude-author -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_fulllaw_beyond_U ed839d34f480cba1e06f855614a9b4c6 by=claude-author -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_fulllaw_beyond_U_corr ed839d34f480cba193f328d7c8c243ea by=claude-author -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_fulllaw_beyond_Q ed839d34f480cba12be9f13eb8df21c1 by=claude-author -->

## Example 5.5: `Dissertation.PaperSpec.A.ex_dealer_potential`, `ex_dealer_crowd`, `ex_dealer_coeffs`, `ex_dealer`, `ex_dealer_mono`, `ex_dealer_wp`, `ex_dealer_twopoint`, `ex_dealer_not_mean`, `ex_dealer_not_mean_corr`, `ex_dealer_affine`, `ex_dealer_marks`

Manuscript (Example `ex:dealer`): the crowding correction `A_λ(u) = ∫ ∇V(u − v) λ(dv)`,
`V(w) = √(1 + ‖w‖²) − 1`, `λ ∈ P₂(L²(ν))`. Claims: (a) `V` is even and convex, with
`∇V(w) = w / √(1 + ‖w‖²)`, `‖∇V(w)‖ ≤ 1`, `Lip(∇V) ≤ 1`; (b) for `ε ≥ 0`, `h_x ∈ L²(ν)`:
`b = −β₁ y`, `σ = σ_c − β₁ z`, `h = h_c + h_x x − β₁ u − ε A_{μ^U}(u)`, `f = β₂ x + ⟨h_x, u⟩`,
`g(x, ρ) = x`; the Hamiltonian term `⟨h_x x, u⟩` has `x`-derivative `⟨h_x, u⟩`; at `ε = 0`,
`h_x = 0` this is Example 5.1(i) verbatim; (c) `h(·, 0, δ₀) = h_c`, Assumption 2.2 as in 5.1(i);
`‖A_λ(u) − A_λ'(u')‖ ≤ ‖u − u'‖ + W₂(λ, λ')`; with (2.11), Assumption 2.3 with
`L = max{β₁ + ε + ‖h_x‖, β₂ + ‖h_x‖, 1}`; (2.3); Assumption 2.4 as in 5.1(i); (d) for
`(Θ, μ), (Θ', μ') ∈ 𝒟_t`, `𝔼⟨A_{μ^U}(U) − A_{μ'^U}(U'), U − U'⟩ ≥ 0`; the exposure terms cancel;
`𝔼[∫_E ⟨δh, δU⟩ dν + ⟨−δf, δX⟩] ≤ −β₁ 𝔼‖δU‖² − β₂ 𝔼|δX|²`; (2.7) with `α = 1`, `β₁`, `β₂` for every
`ε ≥ 0`; Theorem 3.5 applies; (e) the crowding correction is no function of `𝔼[U]`: for a unit
`w`, `λ₁ = ½(δ_{−w} + δ_w)` and `λ₂ = ½(δ_{−2w} + δ_{2w})` share their mean, with
`A_{λ₁}(w) = w/√5`, `A_{λ₂}(w) = ½(3/√10 − 1/√2) w`; it is nonlinear in the valuation curves and
affine in their law, and an expectation kernel in the sense of Example 5.3 with `K = L²(ν)`;
(f) on `E = {−1, +1} × (0, 1]` with `ν(dς, dq) = c_ς q^{−1−ϱ} dq`, `c_ς > 0`, `0 < ϱ < 2`:
`ν(E) = ∞`, `∫ q² dν < ∞`, `h_c(ς, q) = ς q ∈ L²(ν)`; (g) the interaction is active: the inert
tuple at `h_x = 0`, the explicit tuple at `ε = 0`, and `𝔼 ∫_0^T ‖ε A_{Law(U^ε_t)}(U^ε_t)‖² dt > 0`.

Propositions:

* `ex_dealer_potential` — (a), on `L²(ν; ℝ¹)` for every measure `ν`.
* `ex_dealer_crowd` — the joint Lipschitz bound of (c), for all `u, u'` and `λ, λ' ∈ P₂(L²(ν))`.
* `ex_dealer_coeffs` — (b): `ex55Coeffs ν β₁ β₂ σ_c h_c 0 0 = affineCoeffs β₁ β₂ σ_c h_c`, and
  `x ↦ ⟨h_x x, u⟩` has gradient `∫ h_x(e) u(e) ν(de)`.
* `ex_dealer` — (c): for `T > 0`, `β₁, β₂ > 0`, `ε ≥ 0`, every `h_x` and `ξ₀`, the origin value
  `h(t, 0, δ₀) = h_c`, (2.3), Assumption 2.2, Assumption 2.3 with the printed `L`, and
  Assumption 2.4 for `G = 1` (`rank 1 = 1`, `c_G = 1`).
* `ex_dealer_mono` — (d): the crowding pairing, the cancellation (for all `x`, `u`), the printed
  interior inequality, and Assumption 2.5 with `G = 1`, `α = 1`, `β₁, β₂`.
* `ex_dealer_wp` — (d), last sentence: the conclusion of Theorem 3.5 (`thm_cwp`).
* `ex_dealer_twopoint` — (e), the two-point computation, for every unit `w`.
* `ex_dealer_not_mean` — (e), as printed, at every σ-finite `ν`: no `Φ` with
  `A_λ(u) = Φ(∫ v dλ, u)` for all `λ, u`, and `u ↦ A_λ(u)` not linear for some `λ`. **Refuted** by
  `ex_dealer_not_mean_false`: at `ν = 0` the fibre `L²(ν)` is `{0}`, so `A ≡ 0 = Φ(·, ·)`.
* `ex_dealer_not_mean_corr` — the corrected statement: the same with `L²(ν) ≠ {0}`.
* `ex_dealer_affine` — (e): `A_{s λ₁ + (1 − s) λ₂} = s A_{λ₁} + (1 − s) A_{λ₂}` for all
  `λ₁, λ₂ ∈ P₂(L²(ν))`, `s ∈ [0, 1]`; `A_{μ^U}(u) = ∫_H ∇V(u − u') μ(dθ')`; and the kernel
  `(θ, θ') ↦ ∇V(u − u')` is Lipschitz with constant `1` in the form of `ex_expfunc_jump`.
* `ex_dealer_marks` — (f).

Correspondence:

* `n = m = d = 1` as in Example 5.1(i), whose hypotheses `β₁, β₂ > 0` are kept; `L²(ν)` is
  `L²(ν; ℝ¹)`; `h_x` is a real profile in `L²(ν)`, `h_x x` the library `exposureOp` (reviewed in
  `definitions.md`), and `⟨h_x, u⟩` the Bochner integral `∫ h_x(e) u(e) ν(de)`.
* The step `W₂(μ^U, μ'^U) ≤ W₂(μ, μ')` is (2.11), `eq_margproj`, not restated. The
  `π ⊗ π`-integrability of `Φ` and the two double-integral identities of (d) are proof steps.
  "No smallness condition and no margin" is exposition: the propositions hold at every `ε ≥ 0`.
* (e) "not a function of `𝔼[U]`" is read as: `(λ, u) ↦ A_λ(u)` does not factor through
  `(∫ v dλ, u)`; "nonlinear in the valuation curves" as: `u ↦ A_λ(u)` is not linear for some `λ`.
  The sentence argues "for a unit `w ∈ L²(ν)`", which exists exactly when `L²(ν) ≠ {0}`; the
  standing setting admits `ν = 0`. The manuscript edit is the one of Example 5.4: add `ν ≠ 0`.
* The affine clause is stated for arbitrary `λ₁, λ₂`, broader than the printed two-point laws. The
  pointer "dependence nonlinear in the law itself is that of Example 5.4" is exposition.
* (f): the sides are `Bool` with `ς = if b then 1 else −1`, and `ν` is counting measure on the
  sides times Lebesgue measure on `(0, 1]` with density `c_ς q^{−1−ϱ}`. "Infinitely many small
  tickets", "the small-ticket limit" and the modelling narrative (quotes, routing, the dealer
  reading) are exposition; the Cont–Xiong comparison is literature.
* (g) is reviewed in the next section.

Witnesses: `Dissertation.Acceptance.A.ex_dealer_hypotheses` (the mark measure of (f) with
`c_{±1} = 1/2`, `ϱ = 1`, so `ν(E) = ∞`; a Lévy driver with `d = 1` on it, `𝒢₀ = ⊥`, `ξ₀ = 0`,
`T = β₁ = ε = 1`, `β₂ = 1/2`); `ex_dealer_unit_hypotheses` (`h_c(ς, q) = ς q` has unit norm
there); `ex_dealer_marks_hypotheses`.

Verdict: faithful, with the sentence "no function of `𝔼[U]` … nonlinear in the valuation curves"
refuted at `ν = 0` and corrected by `ν ≠ 0`; (g) in the next section.

<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_potential ed839d34f480cba1c2e5952133294af3 by=claude-author -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_crowd ed839d34f480cba1542ac74da98a0887 by=claude-author -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_coeffs ed839d34f480cba1a750d21d05188e99 by=claude-author -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer ed839d34f480cba13abeb1f4dcd6b497 by=claude-author -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_mono ed839d34f480cba1406bda9cea7a3cfe by=claude-author -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_wp ed839d34f480cba18b17ce1d81ae8449 by=claude-author -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_twopoint ed839d34f480cba10e7a45835d5244c0 by=claude-author -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_not_mean ed839d34f480cba11a653f42041ca376 by=claude-author -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_not_mean_corr ed839d34f480cba1db9bb88356786063 by=claude-author -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_affine ed839d34f480cba14f86326a4c8f6eab by=claude-author -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_marks ed839d34f480cba140a65f520ffefa33 by=claude-author -->

## Example 5.5, the interaction is inert or active: `Dissertation.PaperSpec.A.ex_dealer_inert`, `ex_dealer_active_data`, `ex_dealer_active_sde`, `ex_dealer_active_sol`, `ex_dealer_active_moments`, `ex_dealer_sym`, `ex_dealer_active_pos`, `ex_dealer_active_dep`

Manuscript (Example `ex:dealer`, "The interaction is active"): (g1) for `h_x = 0`, with `p` the
positive solution of `p' = β₁ p² − β₂`, `p(T) = 1`, the tuple `Y = p X`,
`Z = p σ_c / (1 + β₁ p)`, `U = p h_c / (1 + β₁ p)` solves the system, `Law(U_t)` is a Dirac mass,
`A_{Law(U_t)}(U_t) = ∇V(0) = 0`, and the same tuple solves it for every `ε`; (g2) with `β₁ = 1`,
`β₂ = ½`, `σ_c = 1`, `ξ₀ = 0`, `c_{±1} = (2 − ϱ)/2`, `h_c(ς, q) = ς q`, `h_x(ς, q) = q`:
`‖h_c‖ = ‖h_x‖ = 1`, `⟨h_c, h_x⟩ = 0`; (g3) the linear equation for `X⁰` has Lipschitz
coefficients, hence a unique solution `X⁰ ∈ S²(ℝ)`; (g4) `(X⁰, X⁰, ½, ½(h_c + h_x X⁰_{t−}))` solves
the system at `ε = 0`; (g5) `𝔼 X⁰_t = 0`, `v' = −(7/4) v + ½` for `v(t) = 𝔼|X⁰_t|²`,
`𝔼‖U⁰_t − 𝔼 U⁰_t‖² = ¼ v(t) = (1/14)(1 − e^{−7t/4})`, so `Law(U⁰_t)` is no Dirac mass for
`t ∈ (0, T]`; (g6) for `λ ∈ P₂(L²(ν))`,
`∫ ⟨A_λ(u), u⟩ λ(du) = ½ ∬ ‖u − v‖² / √(1 + ‖u − v‖²) λ(du) λ(dv)`, positive unless `λ` is a Dirac
mass, hence `A_{Law(U⁰_t)}(U⁰_t) ≠ 0` with positive probability for `t ∈ (0, T]`; (g7) for `ε > 0`,
along the solution `Θ^ε` of Theorem 3.5, `𝔼 ∫_0^T ‖ε A_{Law(U^ε_t)}(U^ε_t)‖² dt > 0`; (g8) the
solution depends on `ε`: no tuple solves the system at two strengths.

Propositions:

* `ex_dealer_inert` — (g1), in the standing setting with `n = m = d = 1`, `T > 0`, `β₁, β₂ > 0`:
  some `p` is positive on `[0, T]` with `p' = β₁ p² − β₂` there (derivatives within `[0, T]`),
  `p(T) = 1`, and equal on `[0, T]` to every such function; with `Z_t = p σ_c / (1 + β₁ p)` on
  `[0, T]` and `U_t = p h_c / (1 + β₁ p)` on `(0, T]`, there are `X, Y` with `Y = p X` on `[0, T]`
  almost surely such that `(X, Y, Z, U)` is a `Solution` at `h_x = 0` for every `ε ≥ 0`; and for
  almost every `t ∈ [0, T]` the `U`-marginal of the law of `Θ⁻_t` is `δ_{p h_c / (1 + β₁ p)}` and
  `A_{(Law Θ⁻_t)^U}(U_t) = 0` at every sample point.
* `ex_dealer_active_data` — (g2), for `h_c`, `h_x` given by their printed formulas `ν`-a.e.
* `ex_dealer_active_sde` — (g3): the exposure equation over `enlJoint 𝒢₀ D h𝒢₀`, in the form
  `LinearFSDEJ` (reviewed in `definitions.md`), has a solution with `𝔼 sup_{[0, T]} |X|² < ∞`, and
  two solutions are indistinguishable on `[0, T]`.
* `ex_dealer_active_sol` — (g4): a `Solution` at `ε = 0` with `ξ₀ = 0` with `Y = X` on `[0, T]`
  almost surely, `Z = ½` and `U = ½(ς q + q X_{t−})` in energy on `[0, T]`, and `X`
  indistinguishable on `[0, T]` from every solution of the exposure equation.
* `ex_dealer_active_moments` — (g5) and the second half of (g6), for every solution `X` of the
  exposure equation, with `U_t = ½(h_c + h_x X_t)`.
* `ex_dealer_sym` — (g6), first half, for every σ-finite `ν`.
* `ex_dealer_active_pos` — (g7), for every `Solution` at `ε > 0` with `ξ₀ = 0`.
* `ex_dealer_active_dep` — (g8), for `ε ≠ ε'`, both `≥ 0`.

Correspondence:

* Solutions are elements of `ℍ`: the propositions give the printed tuples up to
  indistinguishability of `X, Y` and up to energy-null sets for `Z, U`. In (g1) `U` is cut to
  `(0, T]` (`U_0 = 0`, a null set of times), and `Y = p X` holds almost surely on `[0, T]` because
  the `Solution` predicate asks every path of `Y` to have left limits and the library's `X` has them
  almost surely; the version is `PaperSolution.exists_cadlag_version`.
* (g1) The vanishing of the crowding correction is stated for almost every `t`, and for the law of
  the predictable tuple `Θ⁻_t`, whose `U`-marginal is `Law(U_t)`; the printed claim is for every
  `t`, where `U_t` is deterministic and the claim is the trivial `A_{δ_u}(u) = ∇V(0) = 0`. "The same
  tuple solves it for every `ε`" is stated for `ε ≥ 0`, the range the example fixes.
* (g3) The Poisson integrand of `LinearFSDEJ` is `½(ς q + q X_s)`, read at `X_s` rather than at the
  printed `X⁰_{s−}`: the two agree for almost every `(ω, s)`, so the compensated integrals are the
  same. `S²(ℝ)` is read as adapted, right-continuous and `𝔼 sup |X|² < ∞`.
* (g5) The moments are stated with `U_t = ½(h_c + h_x X_t)`; the printed `U⁰_t` uses `X⁰_{t−}`,
  which equals `X⁰_t` almost surely at every fixed `t` (the driver has no fixed-time jumps; not
  formalised) and at almost every `t` along every path. The printed intermediate
  `v' = −2v + ¼ + ¼(‖h_c‖² + ‖h_x‖² v)` is a proof step; the derivative of `v` is taken within
  `[0, T]`.
* (g7) `A_{Law(U^ε_t)}` is read at the `U`-marginal of the law of `Θ⁻_t`, the argument of the jump
  coefficient in (1.1); it is `Law(U_t)`. The proposition holds for every solution, not only the
  one of Theorem 3.5 (they coincide by Theorem 3.3).
* (g8) The printed reason ("subtracting the forward equations and the compensated-Poisson isometry
  would force the crowding correction to vanish") and the contradiction argument of (g7) are proof
  steps.
* Not formalised: "at an event of mark `e` the uncontrolled exposure change is
  `h_c(e) + h_x(e) X_{t−}`" (modelling).

Witnesses: `Dissertation.Acceptance.A.ex_dealer_hypotheses` for `ex_dealer_inert`;
`ex_dealer_active_hypotheses` (`ϱ = 1`, so `c_{±1} = 1/2`; a Lévy driver with `d = 1` on the mark
measure, `𝒢₀ = ⊥`, `T = 1`; `h_c`, `h_x` the library classes `dealerJump`, `dealerSize`, which have
the printed formulas `ν`-a.e.; `ε = 1 > 0`, `ε' = 0 ≠ ε`) for the active clauses.

Verdict: faithful, with the readings listed (versions, `X_s` for `X_{s−}` in the exposure equation
and the moments, almost every `t` in (g1)).

<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_inert ed839d34f480cba143f1c01894aef009 by=claude-author -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_active_data ed839d34f480cba10a4d05ba7e77f141 by=claude-author -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_active_sde ed839d34f480cba1fc9895add2c05eec by=claude-author -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_active_sol ed839d34f480cba1cbff2238ddd8268c by=claude-author -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_active_moments ed839d34f480cba13301041fc2c96a04 by=claude-author -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_sym ed839d34f480cba1b9de62ecc81aebd4 by=claude-author -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_active_pos ed839d34f480cba1a5e96fed66ecac37 by=claude-author -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_active_dep ed839d34f480cba16856f996f6b4b53e by=claude-author -->

## Remarks 2.7–2.11: `Dissertation.PaperSpec.A.rem_diag_mono`, `rem_diag_mono_converse`, `rem_intrinsic_uniform`, `rem_intrinsic_coupling`, `rem_intrinsic_basis`, `rem_beta1_fibre`, `rem_beta1_dich`, `rem_beta1_zero`, `rem_margin_reduce`, `rem_margin_unweighted`, `rem_margin_sharp`

Manuscript: Remark 2.7 (`rem:G-pairing`) explains the role of the full-rank `G`; its mathematical
content, `G`-coercivity controlling the forward variables when `m ≥ n` and the backward ones when
`n ≥ m`, is the bounds of Assumption 2.4 (claim `A:ass:G`, proposition `ass_G`), so the claim is
recorded as a duplicate of `A:ass:G`. Remark 2.8 (`rem:diag-mono`): the pointwise form of (2.7)
gives Assumption 2.5 by taking expectations, and the converse fails (Proposition 3.8); Examples
5.1(i) and 5.4 verify Assumption 2.5 exactly and perturbatively. Remark 2.9 (`rem:intrinsic`): for
`t > 0`, `ℱ_t` supports a uniform variable, a function of `W¹_t`; every coupling of two laws in
`P₂(H)` is the joint law of two `ℱ_t`-measurable inputs (Kallenberg, Lemma 4.22); so Assumptions
2.3 and 2.5 are properties of the coefficients, not of the basis; no richness of `ℱ_0` is needed;
the proofs use only the expected diagonal form. Remark 2.10 (`rem:beta1-dich`): for `ν ≠ 0`,
`L²(ν) ≠ {0}`; (2.7) with `δX = δY = δZ = 0` reduces to the jump channel; an additive
`h = h(t, x, e)` forces `β₁ = 0`, hence `m ≥ n` and `α, β₂ > 0`; when `m < n` the jump coefficient
must be `U`-dissipative; at `ν = 0` the restriction disappears (Example 5.2, both rank branches);
the theorem does not cover the additive form when `m < n`, `ν ≠ 0`; a comparison with
domination-monotonicity results (literature, claim `A:rem2.10:domination`). Remark 2.11
(`rem:margin`): the definition (2.12) of a margin; (2.7) with `β̄₁, β̄₂` is (2.12) with
`β̄ᵢ − c` and margin `c` for `0 < c < min β̄ᵢ`; for `m = n` a margin `c` in (2.12) gives `c / c_G`,
"not `c`", in the unweighted form (2.13).

Propositions:

* `rem_diag_mono` — Remark 2.8, first half, under (2.3) and Assumption 2.3 with some `L`: the
  pointwise inequality at almost every `t`, all points and laws, gives (2.7) (`Mono27At`) at almost
  every `t`.
* `rem_diag_mono_converse` — Remark 2.8, second half: at `n = m = d = 1` and every `T > 0`, the
  system of Proposition 3.8 (Example 5.1(i) with the drift (3.6), `β₁ = 2`, `β₂ = 1`, `ε = 1`)
  satisfies (2.3), Assumption 2.3 and Assumption 2.5 at `G = 1`, and for no `β ≥ 0`, `β'` the
  pointwise inequality.
* `rem_intrinsic_uniform`, `rem_intrinsic_coupling` — Remark 2.9, the uniform variable
  `Φ(W¹_t / √t)` and the realisation of couplings, over `enlJoint 𝒢₀ D h𝒢₀`, `d ≥ 1`, `t > 0`.
* `rem_intrinsic_basis` — Remark 2.9, "intrinsic": for two standing bases with the same `ν`, `d ≥ 1`
  and any `𝒢₀, 𝒢₀'` (no condition on `ℱ_0`), coefficients with (2.3) and `T > 0`, Assumption 2.3
  holds over one exactly when over the other, and, Assumption 2.3 holding, so does Assumption 2.5.
* `rem_beta1_fibre`, `rem_beta1_dich`, `rem_beta1_zero` — Remark 2.10 as listed above, with `n,
  m ≥ 1`, `T > 0`, `G` of full rank; "additive" read as `h(t, θ, μ) = h(t, θ', μ')` whenever
  `θ, θ'` have the same forward state; at `ν = 0` the instance is Example 5.1(i) at `n = m`, the
  `m < n` branch being `ex_brownian` (Example 5.2, whose generator has an additive jump
  coefficient).
* `rem_margin_reduce`, `rem_margin_unweighted`, `rem_margin_sharp` — Remark 2.11: the reduction
  for `0 < c < min β̄ᵢ`; for `m = n`, `G` of full rank, `c_G = s_min(G)⁻²` and `c > 0`, (2.12) with
  margin `c` gives (2.13) with margin `c / c_G`; and "not `c`": at `n = m = d = 1`, `G = 1/2`, the
  scaled Example 5.1(i) has (2.12) with margin `1` and fails (2.13) with margin `1`.

Correspondence:

* (2.7), (2.12), (2.13) are read with the expectation of the pairing existing (`Mono27At`,
  `Margin212`, `Margin213`). The printed step of Remark 2.8 ("taking expectations") holds without
  further hypotheses in the extended reading: the positive part of the pairing is bounded by the
  integrable right-hand side, so its expectation exists in `[−∞, ∞)`. For the integrable reading
  the proposition assumes (2.3) and Assumption 2.3, which hold wherever Assumption 2.5 is used; for
  a coefficient without them the pairing need not be integrable (`b = −y − y³` along
  `Y ∈ L² \ L⁴`). The minimum manuscript change is to say "under Assumption 2.3 and (2.3)" or to
  state the extended reading (REMEDIATION A13s).
* Remark 2.9's basis independence of Assumption 2.5 is stated given Assumption 2.3 (which supplies
  the integrability of the pairing on both bases); for Assumption 2.3 it is unconditional given
  (2.3). Without (2.3) an integrand on `H × H` need not be measurable for a coupling, which is why
  (2.3) is assumed, as it is standing in the paper. "The proofs use only the expected diagonal
  form" is a statement about the proofs, not formalised.
* Remark 2.10's "so `β₁ > 0` forces `h` to be strictly `U`-dissipative" is the reading of the first
  conjunct; "the restriction is structural" is exposition.
* Remark 2.11's "is" (the bound is (2.12)) is stated as the implication used; "recording weaker
  constants turns the difference into slack, which a perturbation … leaves intact" is the
  mechanism of Corollary 3.6, reviewed there.

Witnesses: `Dissertation.Acceptance.A.rem_affine_hypotheses` (Example 5.1(i) with `β₁ = β₂ = 1`
over a Lévy driver with `d = 1`, `ν = δ₀ ≠ 0`, `𝒢₀ = ⊥`, `T = 1`: (2.3), Assumption 2.3, the
pointwise condition, Assumption 2.5 with `G = 1`, and `0 < 1/2 < 1`); `rem_margin_hypotheses`
(the same system has (2.12) with constants and margin `1/2`); `rem_coupling_hypotheses`
(`δ_{(0,0)}` couples `δ₀` with itself); `ex_concrete_hypotheses`, `ex_brownian_hypotheses`.

Verdict: faithful, with the readings listed (the integrable reading of (2.7) in Remark 2.8, and
Assumption 2.3 assumed for the basis independence of Assumption 2.5).

<!-- spec-review: Dissertation.PaperSpec.A.rem_diag_mono ed839d34f480cba1e7ac23388d31fdc9 by=claude-author -->
<!-- spec-review: Dissertation.PaperSpec.A.rem_diag_mono_converse ed839d34f480cba14b5e4594e14d9dc7 by=claude-author -->
<!-- spec-review: Dissertation.PaperSpec.A.rem_intrinsic_uniform ed839d34f480cba13b7a9a5f65a5b218 by=claude-author -->
<!-- spec-review: Dissertation.PaperSpec.A.rem_intrinsic_coupling ed839d34f480cba1ff8eb9ca359fa48b by=claude-author -->
<!-- spec-review: Dissertation.PaperSpec.A.rem_intrinsic_basis ed839d34f480cba173243f3338d3fedc by=claude-author -->
<!-- spec-review: Dissertation.PaperSpec.A.rem_beta1_fibre ed839d34f480cba1c9fa0ba4a3588e95 by=claude-author -->
<!-- spec-review: Dissertation.PaperSpec.A.rem_beta1_dich ed839d34f480cba1312ac03d25ff8ea1 by=claude-author -->
<!-- spec-review: Dissertation.PaperSpec.A.rem_beta1_zero ed839d34f480cba10a600b0e388b329d by=claude-author -->
<!-- spec-review: Dissertation.PaperSpec.A.rem_margin_reduce ed839d34f480cba15843e0ffe4756126 by=claude-author -->
<!-- spec-review: Dissertation.PaperSpec.A.rem_margin_unweighted ed839d34f480cba1ba4163c9b3d796bd by=claude-author -->
<!-- spec-review: Dissertation.PaperSpec.A.rem_margin_sharp ed839d34f480cba1f5295e520594119c by=claude-author -->

## The abstract, the overview of Section 5, the conclusion, and the displays (1.1), (2.3), (4.1)

Manuscript: the abstract (`A:abstract`) states existence, uniqueness and stability for the
system (1.1) with `W₂` dependence on the law of the whole tuple, σ-finite `ν`, Lipschitz and
monotonicity hypotheses along the diagonal only, that expected diagonal monotonicity is strictly
weaker than the pointwise form, and that the dealer-market example is monotone at every
interaction strength, active along the solution in a specialisation, with a mark measure of
infinite activity. The second paragraph of Section 5 (`A:sec5:overview`) summarises Examples
5.1–5.5. The conclusion (`A:conclusion`) summarises Theorems 3.1, 3.3, 3.5, Corollary 3.6,
Proposition 3.8 with Remark 2.8, and Remark 2.10, and names open questions.

Clauses: each sentence of the three passages is the proposition of the result it summarises,
reviewed in that result's section above; the clauses reuse those propositions, proofs and
witnesses:

* abstract: `thm_stab`, `thm_uniq`, `thm_cwp`; `rem_diag_mono` and `prop_strict` for "strictly
  weaker"; `ex_dealer_mono`, `ex_dealer_wp` ("non-perturbatively": well-posed at every strength),
  `ex_dealer_active_pos`, `ex_dealer_marks`.
* overview: `ex_concrete_i`, `ex_concrete_ii` ("meeting every assumption exactly, both at
  arbitrary jump activity"); `ex_brownian`, `ex_expfunc`; `ex_fulllaw_beyond_radial` ("genuinely
  nonlinear functionals of the full tuple") and `ex_fulllaw_beyond_U` ("and of the jump
  integrand"), the latter refuted as printed at `ν = 0` and corrected by
  `ex_fulllaw_beyond_U_corr`, as in Example 5.4; `ex_dealer_mono`, `ex_dealer_wp`,
  `ex_dealer_active_pos`.
* conclusion: `thm_stab`, `thm_uniq`, `thm_cwp`, `cor_robust_wp` ("robust, at `m = n`, under
  full-tuple-law perturbations below the dissipativity margin"), `rem_diag_mono`, `prop_strict`,
  `rem_beta1_dich` ("in the `m < n` regime with `ν ≠ 0` it forces strictly `U`-dissipative jump
  feedback").

Readings: the descriptions of the setting in the abstract (the coefficients' arguments, the
σ-finite intensity, the diagonal form of the hypotheses) are the hypotheses of the propositions
reused, not separate claims. The conclusion's last sentence (relaxing coercivity, domination
monotonicity, common noise) names open questions and is not a claim.

The displays (1.1), (2.3) and (4.1) define objects and are recorded with scope `definition`: (1.1)
is the system whose solutions in the space `ℍ` of Section 3 are `Dissertation.PaperSpec.A.Solution`;
(2.3) is the joint Borel measurability `Dissertation.WellPosedness.Spec.JointBorel`; (4.1) is the
forced system whose solutions are `Dissertation.PaperSpec.A.ForcedSolution`. These definitions are
reviewed in `definitions.md`.

Verdict: faithful, by reuse of the propositions reviewed above.

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
`h = 0`), which exercised only zero conclusions (GitHub #247) and remain theorems; each is over a
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
<!-- spec-review: Dissertation.PaperSpec.A.sec2_infinite_activity ed839d34f480cba13a9f48f6bc72d40f by=claude-author -->
<!-- spec-review: Dissertation.PaperSpec.A.eq_compid ed839d34f480cba1551f4f42ffdf2fa8 by=claude-author -->
<!-- spec-review: Dissertation.PaperSpec.A.eq_zeromean ed839d34f480cba1ca027a9d4d1614c9 by=claude-author -->
<!-- spec-review: Dissertation.PaperSpec.A.sec2_prp ed839d34f480cba1577f0ed2476fcdb5 by=claude-author -->
<!-- spec-review: Dissertation.PaperSpec.A.sec2_hborel ed839d34f480cba1c7bf6ee7f1e38851 by=claude-author -->

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

Verdict: faithful, at a generality containing the paper's.

<!-- spec-review: Dissertation.PaperSpec.A.eq_fubiniiso ed839d34f480cba1f8905adfcaf41890 by=claude-author -->

## (2.5), the progressive coefficient processes: `Dissertation.PaperSpec.A.eq_coefmeas`

Manuscript (02-model-assumptions.tex:100–101, 123–131): "All coefficients are jointly Borel
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

Verdict: faithful.

<!-- spec-review: Dissertation.PaperSpec.A.eq_coefmeas ed839d34f480cba11ac3211646c24c86 by=claude-author -->

## (2.5), the predictable jump coefficient: `Dissertation.PaperSpec.A.eq_coefmeas_jump`

Manuscript (02-model-assumptions.tex:112–131): the Fubini isometry (2.4) and "every Poisson
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

Verdict: faithful.

<!-- spec-review: Dissertation.PaperSpec.A.eq_coefmeas_jump ed839d34f480cba1e13c6b7ca8ccca73 by=claude-author -->

## Remark 3.2, the solution class: `Dissertation.PaperSpec.A.rem_cwp_class`

Manuscript (03-main-results.tex:83–101): "Let `Θ = (X, Y, Z, U) ∈ ℍ_weak` satisfy (1.1). Then
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

## The paragraph after Theorem 3.1: `Dissertation.PaperSpec.A.thm_stab_companion`, `thm_stab_data`, `thm_stab_minimal`

Manuscript (03-main-results.tex:76–81): "If system 2 also satisfies Assumptions 2.4–2.5, with its
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
earlier witness `thm_stab_hypotheses` had two zero solutions (GitHub #247) and is no longer
linked.

Verdict: faithful.

<!-- spec-review: Dissertation.PaperSpec.A.thm_stab_companion ed839d34f480cba10ff3a550a92ccddf by=claude-author -->
<!-- spec-review: Dissertation.PaperSpec.A.thm_stab_data ed839d34f480cba1f26d5949b31ba63f by=claude-author -->
<!-- spec-review: Dissertation.PaperSpec.A.thm_stab_minimal ed839d34f480cba127494e1cb3f498aa by=claude-author -->

## The preamble of Section 5: `Dissertation.PaperSpec.A.sec5_limin`

Manuscript (05-examples.tex:3–7): "the restrictive hypothesis is the dissipativity of
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

Verdict: faithful.

<!-- spec-review: Dissertation.PaperSpec.A.sec5_limin ed839d34f480cba132884b458e231942 by=claude-author -->

## The paragraph after Corollary 3.6: `Dissertation.PaperSpec.A.cor_margin_channels`, `cor_margin_additive`, `cor_margin_finite`, `cor_margin_findim`

Manuscript (03-main-results.tex:278–288): "The margin hypothesis is demanding in the jump channel:
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
  covers neither, so it is narrower than the printed sentence. The broader case is a separate,
  open clause of `A:sec3:margin-paragraph` (route in GitHub #243: Borsuk–Ulam on a
  `(k + 1)`-dimensional sphere for an antipodal collision `F(u) = F(−u)`, and a symmetric
  `ℱ_t`-measurable sign `B` with inputs `U = B u`, `U' = −B u` of equal law). The conclusion
  "supplies no margin" is the failure of (2.13) for every margin `c > 0`, with admissible
  `β₁ ≥ 0`.
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
* `cor_margin_findim`: `Dissertation.Acceptance.A.cor_margin_findim_hypotheses`: a Lévy driver
  with `ν = δ₀` and `d = 1`, `𝒢₀ = ⊥`, and `L²(δ₀; ℝ¹)` finite dimensional; `n = 1`, `T = 1`,
  `β₁ = β₂ = 0`, `c = 1`, `σ_c = 0`, `h_c = 0` meet the remaining hypotheses.

Verdict: faithful for `cor_margin_channels`, `cor_margin_additive` and `cor_margin_findim`;
`cor_margin_finite` is the linear, Dirac-input case only and is narrower than the printed
sentence, whose general case is an open clause, so the paragraph is not fully covered.

<!-- spec-review: Dissertation.PaperSpec.A.cor_margin_channels ed839d34f480cba14127298d8cc156d9 by=claude-author -->
<!-- spec-review: Dissertation.PaperSpec.A.cor_margin_additive ed839d34f480cba19075028a95edf84d by=claude-author -->
<!-- spec-review: Dissertation.PaperSpec.A.cor_margin_finite ed839d34f480cba15e05ed8a37017606 by=claude-author -->
<!-- spec-review: Dissertation.PaperSpec.A.cor_margin_findim ed839d34f480cba153b1b629e759bb45 by=claude-author -->

## Remark 5.7, perturbative and non-perturbative law dependence

Manuscript (05-examples.tex, Remark `rem:regimes`): "Example 5.4 shows that arbitrary nonlinear
full-tuple law dependence can be added when it is smaller than the dissipativity margin.
Example 5.5 shows that a `U`-law interaction nonlinear in the valuation curves can have arbitrary
strength when its geometry is itself monotone, and remain active along the solution."

Clauses: each sentence summarises an example, reviewed in that example's section above; the
clauses reuse those propositions, proofs and witnesses:

* "can be added when it is smaller than the dissipativity margin": `ex_fulllaw_pert` (the law
  perturbation of Example 5.4 satisfies (3.4) with `c_pert = ‖G‖ L_p`) and `ex_fulllaw_wp` (under
  (5.1), `c_pert < c_diss`, the perturbed system satisfies Assumptions 2.2–2.5 with a margin and
  is well-posed). "Arbitrary nonlinear full-tuple law dependence" is the class of Example 5.4
  (Lipschitz profiles of `W₂` distances and Lipschitz functions of feature integrals of the
  `U`-marginal), as reviewed there; the remark claims no more than that example.
* "can have arbitrary strength when its geometry is itself monotone": `ex_dealer_mono`
  (Assumption 2.5 at every `ε ≥ 0`) and `ex_dealer_wp` (well-posedness at every `ε ≥ 0`).
* "and remain active along the solution": `ex_dealer_active_pos` (positive crowding energy along
  every solution at every `ε > 0`, in the specialisation of Example 5.5).

Verdict: faithful, by reuse of the propositions reviewed above.

## Remark 3.7, general rank: `Dissertation.PaperSpec.A.rem_generalrank`, `rem_generalrank_wp`

Manuscript (03-main-results.tex:290–295): "The restriction to `m = n` reflects only the
unweighted bookkeeping: the same splitting of the pairing into baseline and perturbation
brackets, run in the weighted quantities of (2.12), gives the identical conclusion for arbitrary
`m, n` when the margin and (3.4) are both recorded in those quantities."

Propositions: `rem_generalrank` and `rem_generalrank_wp` are `cor_robust` and `cor_robust_wp`
(reviewed under Corollary 3.6) with `n, m ≥ 1` arbitrary, `G ∈ ℝ^{m×n}` of full rank, the
baseline's margin taken in (2.12) (`Margin212`, the weighted form, reviewed under Remark 2.11)
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
<!-- spec-review: Dissertation.PaperSpec.A.rem_generalrank_wp ed839d34f480cba13f0dc6e9507d0e4e by=claude-author -->

## Lemma A.1, the law flows: `Dissertation.PaperSpec.A.lem_lawflow`, `lem_lawflow_invariant`

Manuscript (09-appendix.tex, Lemma `lem:lawflow`): "Let `X, Y` be càdlàg adapted and let `Z, U`
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

Verdict: faithful.

<!-- spec-review: Dissertation.PaperSpec.A.lem_lawflow ed839d34f480cba1090c1a53f2a6cf7f by=claude-author -->
<!-- spec-review: Dissertation.PaperSpec.A.lem_lawflow_invariant ed839d34f480cba184c9d1f8d6f2b814 by=claude-author -->

## (4.2) and (4.3), the coefficient bounds: `Dissertation.PaperSpec.A.eq_coeffint`, `eq_termg`

Manuscript (04-proof-wellposedness.tex:70–82): "By Assumptions 2.2–2.3, the coefficient processes
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

Verdict: faithful.

<!-- spec-review: Dissertation.PaperSpec.A.eq_coeffint ed839d34f480cba13c4b68e5e50bad34 by=claude-author -->
<!-- spec-review: Dissertation.PaperSpec.A.eq_termg ed839d34f480cba171988e2e6de37794 by=claude-author -->

## Example 5.1(i), sharpness: `Dissertation.PaperSpec.A.ex_concrete_i_sharp`

Manuscript (05-examples.tex:100–112): Example 5.1(i) states that the displayed identity
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
  `ν = 0` is covered (GitHub #246).

Witness: `Dissertation.Acceptance.A.ex_concrete_hypotheses`: at its instance Assumption 2.5 holds
with the system's own `β₁, β₂`, so (2.7) holds with `β₁' = β₁`, `β₂' = β₂`.

Verdict: faithful.

<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_i_sharp ed839d34f480cba19df1faec1593a821 by=claude-author -->

## Remark 3.4, uniqueness without origin integrability: `Dissertation.PaperSpec.A.rem_uniq_initial`, `rem_uniq_singular`

Manuscript (03-main-results.tex, Remark `rem:uniq-no-integ`): "the uniqueness only requires
Assumptions 2.3–2.5, as we only need to show that the difference `Θ¹ − Θ²` belongs to `ℍ` ... The
proof of Theorem 3.5 uses Assumption 2.2. Its initial-data condition `ξ₀ ∈ L²` is necessary for a
solution in `ℍ`, since `X₀ = ξ₀` and `𝔼 sup_{t≤T} |X_t|² < ∞`; the origin-value conditions are
sufficient but not necessary. For instance, adding the deterministic drift `t^{-1/2} ∉ L²(0, T)`
to the `b` of a system satisfying Assumptions 2.2–2.5 violates Assumption 2.2 and leaves
Assumptions 2.3–2.5 unchanged, yet the shift `X ↦ X − 2√t`, applied to the state and translating
the law argument accordingly, returns a system satisfying Assumptions 2.2–2.5, so a solution still
exists."

Clauses:

* "The uniqueness only requires Assumptions 2.3–2.5": `thm_uniq` (Theorem 3.3), whose hypotheses
  are (2.3) and Assumptions 2.3–2.5, without Assumption 2.2, for tuples of `ℍ_weak` (reused,
  reviewed under Theorem 3.3).
* "`ξ₀ ∈ L²` is necessary for a solution in `ℍ`": `rem_uniq_initial`: in the standing setting,
  `T ≥ 0`, a tuple with `WeakSolution` (a tuple of `ℍ_weak` satisfying (1.1)) whose forward
  component has `𝔼 sup_{t ≤ T} |X_t|² < ∞` has every coordinate of `ξ₀` in `L²`. A solution in
  `ℍ` is such a tuple; the proposition needs no assumption on the coefficients, as the printed
  argument (`X₀ = ξ₀` and the `S²` bound) uses none.
* "The origin-value conditions are sufficient but not necessary": `rem_uniq_singular`: with
  `𝒢₀ = ⊥`, `n = m = 1`, any `d`, every Lévy driver and every `T > 0`, the system of
  Example 5.1(i) (`β₁ = 1`, `β₂ = 0`, `σ_c = 0`, `h_c = 0`, which satisfies Assumptions 2.2–2.5)
  with `t^{-1/2}` added to `b` satisfies (2.3) and Assumptions 2.3–2.5 (`L = 1`, `G = 1`,
  `α = β₁ = 1`, `β₂ = 0`), violates Assumption 2.2 for every initial datum, and from `ξ₀ = 0` has a
  solution in `ℍ`: `WeakSolution` with finite `𝔼 sup |X|²` and `𝔼 sup |Y|²`, the drift integral
  read pathwise. The solution in the stronger sense `Solution` (finite drift energy) does not
  exist (`not_paperSolution_singularCoeffs`), so `ℍ` is read as the paper defines it, through
  `WeakSolution` and the `S²` bounds.
* The "For instance" sentence for **an arbitrary** system satisfying Assumptions 2.2–2.5 (the
  translated system satisfies Assumptions 2.2–2.5, so a solution exists by Theorem 3.5 and
  translating back) is not proved: `rem_uniq_singular` covers one base system, through an explicit
  solution rather than the translation. It is a separate, open clause (route in GitHub #243,
  item 2). "The proof of Theorem 3.5 uses Assumption 2.2" describes a proof and is not a clause.

Witness: `Dissertation.Acceptance.A.rem_uniq_hypotheses` for both new propositions: over a
probability space carrying a Lévy driver with `d = 1`, `ν = δ₀`, `𝒢₀ = ⊥`, `T = 1`, the singular
system has a `WeakSolution` from `0` with both `S²` bounds finite. `rem_uniq_singular` has no
hypotheses beyond the setting and `T > 0`.

Verdict: faithful for the three clauses stated; the general translation clause is open.

<!-- spec-review: Dissertation.PaperSpec.A.rem_uniq_initial ed839d34f480cba1fa628ed6b5f5989d by=claude-author -->
<!-- spec-review: Dissertation.PaperSpec.A.rem_uniq_singular ed839d34f480cba1c331e57f1b4633b6 by=claude-author -->

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
<!-- spec-review: Dissertation.PaperSpec.A.ex_brownian_rank_gt ed839d34f480cba154d947c79143fab0 by=claude-author -->

## §3, the solution definition and the solution space: `Dissertation.PaperSpec.A.sec3_one_null_set`, `sec3_HH_inclusion`, `sec3_HH_definite`

Manuscript (`03-main-results.tex`, the paragraphs on `ℍ` and on solutions): the elements of `ℍ`
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
* `sec3_HH_inclusion`: for `T ≥ 0` and `V` with values in `ℝⁿ`,
  `𝔼 ∫_0^T |V_t|² dt ≤ T 𝔼 sup_{t ≤ T} |V_t|²` in `[0, ∞]`, and a finite right side gives a
  finite energy of each coordinate (the `ℍ_weak` condition).
* `sec3_HH_definite`: for a tuple of `ℍ_weak`, `‖Θ‖²_ℍ` (`supSize`) is `0` if and only if `X`
  and `Y` are indistinguishable from `0` on `[0, T]`, `Z = 0` `dt ⊗ dP`-a.e. on `[0, T]`
  (`energyMeasure`) and `U = 0` `dt ⊗ dP ⊗ ν`-a.e. (`markedEnergyMeasure`).

Correspondence:

* "Both sides are càdlàg": the proof shows the right-continuity of each side and nothing else is
  needed: `X, Y` by `PaperWeakTuple` (every path); the drift and driver integrals by the
  integrability of almost every path on `[0, T]`; the compensated Poisson integrals by their
  almost sure càdlàg paths (`stochasticIntegral_cadlag`); `M` by hypothesis. The Brownian
  integral of the paper is an `L²` object; the identity is read with a càdlàg version, as the
  repository's solution notion `PaperWeakSolutionInt` does. The proposition does not assume `M` is
  that version, so it is broader.
* "`‖·‖_ℍ` is a norm rather than a seminorm" is read as definiteness on the identified classes.
  The seminorm properties (homogeneity, triangle inequality) are not stated: the sentence's point is
  that the identification removes the null vectors.
* "`(ℍ, ‖·‖_ℍ)` is a Banach space" (completeness) is not proved and is an open clause. The
  completeness of the integrand spaces exists in LevyStochCalc for progressive integrands
  (`exists_progressive_energy_limit`); the supremum part needs a càdlàg adapted limit.
* The inclusion `ℍ ⊂ ℍ_weak` is read as the energy condition of `ℍ_weak` for `X` and `Y`; the
  other conditions of `ℍ_weak` are those of `ℍ`.

Witness: `Dissertation.Acceptance.A.sec3_space_hypotheses` for `sec3_one_null_set` and
`sec3_HH_definite`: over a Lévy driver with `d = 1`, `ν = δ₀`, `𝒢₀ = ⊥`, `n = m = 1`, `T = 1`,
the solution of Example 5.1(i) (`β₁ = β₂ = 1`, `σ_c = h_c = 0`) from `ξ₀ ≡ e₁` gives a tuple of
`ℍ_weak` with the integrals of (1.1), with `X_0 = 1` almost surely (not the zero tuple).
`sec3_HH_inclusion` has no hypotheses beyond `T ≥ 0`.

Verdict: faithful for the clauses stated; completeness of `ℍ` is open.

<!-- spec-review: Dissertation.PaperSpec.A.sec3_one_null_set ed839d34f480cba1209a5aa6ac298690 by=claude-author -->
<!-- spec-review: Dissertation.PaperSpec.A.sec3_HH_inclusion ed839d34f480cba130514b735af5f227 by=claude-author -->
<!-- spec-review: Dissertation.PaperSpec.A.sec3_HH_definite ed839d34f480cba12b4c9985cfe528af by=claude-author -->

## Remark 5.6, the scope of the measure argument: `Dissertation.PaperSpec.A.rem_freelaw`

Manuscript (Remark `rem:freelaw`): "The proofs consume the tuple law through a single mechanism:
the `W₂` term of Assumption 2.3, dominated at every use by the synchronous coupling bound (2.8).
The right-hand side of (2.8) carries `𝔼‖δU‖²` whether or not the measure argument reads the
`U`-marginal, because the coefficients depend on `u` pointwise — a dependence Remark 2.10 makes
unavoidable whenever `β₁ > 0` and `ν ≠ 0`. Nothing is therefore gained by restricting the
coefficients to the `(X, Y, Z)`-marginal law: with the coupling bound taken in `ℋ`, the estimates
close at the full tuple law, and Example 5.5 exhibits that scope arising from a routing mechanism
rather than by construction."

Proposition (`rem_freelaw`): in the standing setting with `n, m, d ≥ 1`, `T > 0`, `ν ≠ 0` and `G`
of full rank, if the coefficients satisfy Assumption 2.5 with `G` and `β₁ > 0`, then for almost
every `t ∈ [0, T]` there are `(Θ, μ), (Θ', μ') ∈ 𝒟_t` with `μ = μ'` and the same `(X, Y, Z)` such
that `h(t, Θ, μ) = h(t, Θ', μ')` fails with positive probability.

Correspondence:

* "The `W₂` term … dominated by (2.8)": clause `eq_coupling` (reused, reviewed under Remark 2.6).
  "Through a single mechanism" describes the proofs and is not a clause.
* "Carries `𝔼‖δU‖²` whether or not the measure argument reads the `U`-marginal, because the
  coefficients depend on `u` pointwise": `rem_freelaw`. At a pair with one law every law term,
  whichever marginal it reads, vanishes; the coefficient still differs, so the `δU` term of the
  Lipschitz bound comes from the pointwise argument and cannot be removed by restricting the law.
  The proof takes `Θ = (0, 0, 0, B u₀)`, `Θ' = (0, 0, 0, −B u₀)` with `B` the Brownian increment
  `W¹_t − W¹_0` (a centred Gaussian, so `±B` have one law) and `u₀ ∈ L²(ν)` with `Gᵀ u₀ ≠ 0`; if
  `h` agreed at them, Remark 2.10's inequality would give `0 ≤ −4 β₁ t ‖Gᵀ u₀‖² < 0`. The
  hypothesis `d ≥ 1` supplies `B`; the standing setting has `d ≥ 1`.
* "Unavoidable whenever `β₁ > 0` and `ν ≠ 0`": clause `rem_beta1_dich` (reused, reviewed under
  Remark 2.10).
* "Nothing is therefore gained … the estimates close at the full tuple law" is the conclusion the
  remark draws from these clauses; the closing at the full tuple law is Theorems 3.1–3.5
  (reviewed there). The reference to Example 5.5 points to clauses reviewed under Example 5.5.

Witness: `Dissertation.Acceptance.A.rem_affine_hypotheses` (reused): a Lévy driver with `d = 1`,
`ν = δ₀ ≠ 0`, `𝒢₀ = ⊥`, `T = 1`, and Example 5.1(i) with Assumption 2.5 for `G = 1`,
`α = β₁ = β₂ = 1`.

Verdict: faithful for the clauses stated.

<!-- spec-review: Dissertation.PaperSpec.A.rem_freelaw ed839d34f480cba105f02a9629cb6b98 by=claude-author -->

## §3, completeness of the solution space: `Dissertation.PaperSpec.A.sec3_HH_complete`

Manuscript (`03-main-results.tex` at `e939294`, the paragraph on `ℍ`): "Under this identification
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
* "`‖·‖_ℍ` is a norm" is reviewed under `sec3_HH_definite`; the vector-space operations of the
  quotient are not separately stated.

Verdict: faithful. The clause is open (no proof).

<!-- spec-review: Dissertation.PaperSpec.A.sec3_HH_complete ed839d34f480cba140502fce3ed6073c by=claude-author -->

## The paragraph after Corollary 3.6, continuous functionals: `Dissertation.PaperSpec.A.cor_margin_separate`, `cor_margin_continuous`

Manuscript (`03-main-results.tex` at `e939294`, the paragraph after Corollary 3.6): "When,
moreover, `L²(ν)` is infinite-dimensional, jump feedback entering through finitely many functionals
of `u` supplies no margin either, since finitely many continuous functionals cannot separate the
points of an infinite-dimensional space".

Propositions:

* `cor_margin_separate`: for every real normed space `H` that is not finite dimensional, every
  `k` and every continuous `F : H → ℝᵏ`, `F` is not injective: "finitely many continuous
  functionals cannot separate the points of an infinite-dimensional space", with `F` the vector of
  the `k` functionals, possibly nonlinear.
* `cor_margin_continuous`: in the standing setting with `d ≥ 1`, for `T > 0`, with
  `L²(ν; ℝᵐ)` not finite dimensional, all `β₁ ≥ 0`, `β₂`, `G`, `c > 0`, coefficients `C`, `k` and
  maps `F_t : L²(ν; ℝᵐ) → ℝᵏ` continuous for every `t`: if
  `h(t, θ, μ) = h(t, θ', μ)` whenever `θ, θ'` share `x, y, z` and `F_t u = F_t u'`, for every law
  `μ`, then (2.13) (`Margin213`) fails.

Correspondence:

* "Jump feedback entering through finitely many functionals of `u`" is read as `h` depending on
  `u` only through `F_t u`, at each fixed `(t, x, y, z, μ)`; the dependence on `x, y, z`, on the
  law and on `t` is otherwise arbitrary. The linear, Dirac-law case is `cor_margin_finite`; this is
  the general reading of the sentence, with "continuous functionals" taken from its justification.
* `d ≥ 1` is part of the standing setting of Theorem 3.5 (`thm_cwp`); the argument needs one
  nontrivial event at a positive time, to give two random inputs with one law, which a Brownian
  coordinate supplies.
* The constants are those of `cor_margin_finite`: `β₁ ≥ 0`, any `β₂`, any `G`, `c > 0`.

Verdict: faithful. Both clauses are open (no proof; a proof of the first needs the Borsuk–Ulam
theorem or invariance of domain, which the library does not have).

<!-- spec-review: Dissertation.PaperSpec.A.cor_margin_separate ed839d34f480cba1b90f9a7b02bff832 by=claude-author -->
<!-- spec-review: Dissertation.PaperSpec.A.cor_margin_continuous ed839d34f480cba1bd840ffee2f6a13b by=claude-author -->

## Remark 3.4, the translation for a general system: `Dissertation.PaperSpec.A.rem_uniq_translation`

Manuscript (`03-main-results.tex` at `e939294`, Remark `rem:uniq-no-integ`): "adding the
deterministic drift `t^{-1/2} ∉ L²(0, T)` to the `b` of a system satisfying Assumptions 2.2–2.5
violates Assumption 2.2 and leaves Assumptions 2.3–2.5 unchanged, yet the shift `X ↦ X − 2√t`,
applied to the state and translating the law argument accordingly, returns a system satisfying
Assumptions 2.2–2.5, so a solution still exists."

Proposition `rem_uniq_translation`: in the standing setting with `n, m, d ≥ 1` (those of
Theorem 3.5), for `T > 0`, a system `C` with initial datum `ξ₀` satisfying (2.3) and
Assumptions 2.2–2.5 (`L, α, β₁, β₂`, `G` of full rank) and a nonzero `e ∈ ℝⁿ`:

* `C⁺ = C.addDrift (t ↦ t^{-1/2} e)` satisfies (2.3), Assumption 2.3 with `L` and Assumption 2.5
  with `G, α, β₁, β₂`, and violates Assumption 2.2 for every initial datum;
* `C̃ = translatedCoeffs C (t ↦ 2√t e) T` satisfies (2.3) and Assumptions 2.2, 2.3, 2.5 with the
  same constants and `ξ₀`;
* there is `(X, Y, Z, U)` with `Solution` for `C̃` from `ξ₀` such that `(X + 2√t e, Y, Z, U)` has
  `WeakSolution` for `C⁺` from `ξ₀` and finite `𝔼 sup |X + 2√t e|²` and `𝔼 sup |Y|²`.

Correspondence:

* "The deterministic drift `t^{-1/2}`" is a vector drift in `ℝⁿ`; it is read along an arbitrary
  nonzero direction `e`. `addDrift` is reviewed under `rem_uniq_singular`; `translatedCoeffs` in
  `definitions.md`.
* Assumption 2.4 concerns `G` alone and is unchanged by both operations; it is a hypothesis.
* "So a solution still exists" is read as `rem_uniq_singular` reads it: a solution in `ℍ` of the
  system with the singular drift, `WeakSolution` with both `S²` bounds, the drift integral read
  pathwise; the solution in the stronger sense `Solution` would need finite drift energy, which
  the drift `t^{-1/2}` excludes. The proposition also names the translated solution and states the
  translation back, which is the printed route.

Verdict: faithful. The clause is open (no proof); the specific system of `rem_uniq_singular` is
proved separately.

<!-- spec-review: Dissertation.PaperSpec.A.rem_uniq_translation ed839d34f480cba1800e3b89c10396d1 by=claude-author -->

## §4, the horizon: `Dissertation.PaperSpec.A.sec4_horizon_not_contractive`

Manuscript (`04-proof-wellposedness.tex` at `e939294`, the introduction to §4): "The continuation
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
