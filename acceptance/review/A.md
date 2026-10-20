# Reviews of the statements of paper A (well-posedness, at `1f67672`)

Each entry reads the manuscript passage and the proposition side by side. A marker records the
hash of the proposition reviewed and, for each claim the reading counts for, the digest of that
claim's source passage as read (`source=<claim>@<digest>`); a change of the proposition or of the
passage reopens the entry. The entries quote the manuscript at `1f67672` (`manuscript/`); a
marker whose digest is not the passage's current one records a reading of an earlier text.

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

Re-reading at `1f67672` (Remark 2.6, `sections/02-model-assumptions.tex` lines 200–232; Remark
5.6, `sections/05-examples.tex` lines 532–546). Of Remark 2.6 only (2.9) changed: it is printed at
`X_T`, "the `X`-marginal case of (2.8) at time `T`"; (2.8) reads as quoted above. Remark 5.6 now
gives the argument for the pointwise `u`-dependence (quoted in its section); it still uses (2.8) as
the bound "dominated at every use". The proposition still says what both passages say. It is
broader than the printed (2.8): the printed claim is its instance at `Θ := Θ_t`, `Θ' := Θ'_t` for
two diagonal inputs `(Θ_t, μ), (Θ'_t, μ')` at a common time on the probability space of §2, which
are square integrable (Definition 2.1), with `μ = lawP2 P Θ_t`, `μ' = lawP2 P Θ'_t`.

<!-- spec-review: Dissertation.PaperSpec.A.eq_coupling ed839d34f480cba17af7c36ae6c33114 by=claude-author source=A:rem:wasserstein-bounds@c04119bf34c0cb8093c0843e1c7b01bf93697e1e04d779493a112bce12987835 source=A:rem:freelaw@f13ee0338a04a13ffc7c298c326bbddd96efa2f48c9dc8e2a7281612c39beecb -->
<!-- spec-review: Dissertation.PaperSpec.A.eq_coupling ed839d34f480cba17af7c36ae6c33114 by=claude-author source=A:rem:wasserstein-bounds@a8c8906e45bdcd6591c7751bd3186ea3b83dd382cd95543acb4edcabc2093661 source=A:rem:freelaw@e2204cd5268c52bf28ead0e1dd0321d0914e8ca0c49f13ab56fa690ca4815fea -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.eq_coupling--claude-reviewer--2026-10-17T12_12_10Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_coupling ed839d34f480cba17af7c36ae6c33114 by=claude-reviewer source=A:rem:wasserstein-bounds@a8c8906e45bdcd6591c7751bd3186ea3b83dd382cd95543acb4edcabc2093661 source=A:rem:freelaw@e2204cd5268c52bf28ead0e1dd0321d0914e8ca0c49f13ab56fa690ca4815fea -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.eq_coupling--claude-auditor--2026-10-19T03_31_22Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_coupling ed839d34f480cba17af7c36ae6c33114 by=claude-auditor source=A:rem:wasserstein-bounds@baddffc87439566a55a973b4d3634494482f991387c121349eff7592be8093ab source=A:rem:freelaw@c2b143b44403046035d85f7e9d730c306f0b5cb52b01f72f3a72ded8e56980b7 -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.eq_coupling--claude-auditor--2026-10-20T11_24_07Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_coupling ed839d34f480cba17af7c36ae6c33114 by=claude-auditor source=A:rem:wasserstein-bounds@c04119bf34c0cb8093c0843e1c7b01bf93697e1e04d779493a112bce12987835 source=A:rem:freelaw@f13ee0338a04a13ffc7c298c326bbddd96efa2f48c9dc8e2a7281612c39beecb source=A:lemA1:polish@cdf7e5fd3a5753faf4d5aaea2d4e017db124558fd0461ec3b81dd52a3f8527cc -->

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

Re-reading at `1f67672` (lines 207–209 of `sections/02-model-assumptions.tex`): (2.9) is printed
as `W₂(ρ, ρ')² ≤ 𝔼|X_T − X'_T|²`, "the `X`-marginal case of (2.8) at time `T`", where it formerly
read `𝔼|δX|²`. The proposition says what the passage says; the printed claim is its instance at
`X := X_T`, `X' := X'_T`, square integrable and `ℱ_T`-measurable, with `ρ = lawP2 P X_T`,
`ρ' = lawP2 P X'_T`.

<!-- spec-review: Dissertation.PaperSpec.A.eq_couplingT ed839d34f480cba1b0b3c75b14edd5d3 by=claude-author source=A:rem:wasserstein-bounds@c04119bf34c0cb8093c0843e1c7b01bf93697e1e04d779493a112bce12987835 -->
<!-- spec-review: Dissertation.PaperSpec.A.eq_couplingT ed839d34f480cba1b0b3c75b14edd5d3 by=claude-author source=A:rem:wasserstein-bounds@a8c8906e45bdcd6591c7751bd3186ea3b83dd382cd95543acb4edcabc2093661 -->
Review by claude-reviewer: faithful (report `reports/Dissertation.PaperSpec.A.eq_couplingT--claude-reviewer--2026-10-17T12_12_34Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_couplingT ed839d34f480cba1b0b3c75b14edd5d3 by=claude-reviewer source=A:rem:wasserstein-bounds@a8c8906e45bdcd6591c7751bd3186ea3b83dd382cd95543acb4edcabc2093661 -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.eq_couplingT--claude-auditor--2026-10-19T03_34_37Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_couplingT ed839d34f480cba1b0b3c75b14edd5d3 by=claude-auditor source=A:rem:wasserstein-bounds@baddffc87439566a55a973b4d3634494482f991387c121349eff7592be8093ab -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.eq_couplingT--claude-auditor--2026-10-20T11_24_07Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_couplingT ed839d34f480cba1b0b3c75b14edd5d3 by=claude-auditor source=A:rem:wasserstein-bounds@c04119bf34c0cb8093c0843e1c7b01bf93697e1e04d779493a112bce12987835 -->

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

<!-- spec-review: Dissertation.PaperSpec.A.thm_stab ed839d34f480cba16bc55062de98e587 by=claude-author source=A:thm:stab@381ba74c22961e597927279a40c3d1204009169a635d33ce49e1a5962c04d6b8 source=A:thm:cwp@0dd6b95ee4474a8c7091ae6a816a6a0de0ea67b50d49a5c437094a757adcf5f3 source=A:abstract@3e98e9839e7e2470c7619601cd0e8f5468477dfdc4dc1f5681314fc4ca1483a9 source=A:conclusion@c886edc62e0561a1e17a961ffd1d0527a5bae43a5607635ce8e247276c91a829 -->
Review by claude-reviewer: faithful (report `reports/Dissertation.PaperSpec.A.thm_stab--claude-reviewer--2026-10-17T16_05_53Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.thm_stab ed839d34f480cba16bc55062de98e587 by=claude-reviewer source=A:thm:stab@381ba74c22961e597927279a40c3d1204009169a635d33ce49e1a5962c04d6b8 source=A:thm:cwp@0dd6b95ee4474a8c7091ae6a816a6a0de0ea67b50d49a5c437094a757adcf5f3 source=A:abstract@3e98e9839e7e2470c7619601cd0e8f5468477dfdc4dc1f5681314fc4ca1483a9 source=A:conclusion@c886edc62e0561a1e17a961ffd1d0527a5bae43a5607635ce8e247276c91a829 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.thm_stab--claude-auditor--2026-10-19T03_36_54Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.thm_stab ed839d34f480cba16bc55062de98e587 by=claude-auditor source=A:thm:stab@381ba74c22961e597927279a40c3d1204009169a635d33ce49e1a5962c04d6b8 source=A:thm:cwp@0dd6b95ee4474a8c7091ae6a816a6a0de0ea67b50d49a5c437094a757adcf5f3 source=A:abstract@3e98e9839e7e2470c7619601cd0e8f5468477dfdc4dc1f5681314fc4ca1483a9 source=A:conclusion@c886edc62e0561a1e17a961ffd1d0527a5bae43a5607635ce8e247276c91a829 -->

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

<!-- spec-review: Dissertation.PaperSpec.A.thm_uniq ed839d34f480cba1b8815741b34ba4e5 by=claude-author source=A:thm:uniq@03292da4be100aa38ea90d55eff64159cf4e923c05926fa169ebba6ed2985189 source=A:rem:uniq-no-integ@16ace776485cb414a0ad39fba869a577ec053811b32b39e09709fb01a4e0f75e source=A:abstract@3e98e9839e7e2470c7619601cd0e8f5468477dfdc4dc1f5681314fc4ca1483a9 source=A:conclusion@c886edc62e0561a1e17a961ffd1d0527a5bae43a5607635ce8e247276c91a829 -->
Review by claude-reviewer: faithful (report `reports/Dissertation.PaperSpec.A.thm_uniq--claude-reviewer--2026-10-17T16_05_53Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.thm_uniq ed839d34f480cba1b8815741b34ba4e5 by=claude-reviewer source=A:thm:uniq@03292da4be100aa38ea90d55eff64159cf4e923c05926fa169ebba6ed2985189 source=A:rem:uniq-no-integ@16ace776485cb414a0ad39fba869a577ec053811b32b39e09709fb01a4e0f75e source=A:abstract@3e98e9839e7e2470c7619601cd0e8f5468477dfdc4dc1f5681314fc4ca1483a9 source=A:conclusion@c886edc62e0561a1e17a961ffd1d0527a5bae43a5607635ce8e247276c91a829 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.thm_uniq--claude-auditor--2026-10-19T03_35_38Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.thm_uniq ed839d34f480cba1b8815741b34ba4e5 by=claude-auditor source=A:thm:uniq@03292da4be100aa38ea90d55eff64159cf4e923c05926fa169ebba6ed2985189 source=A:rem:uniq-no-integ@867ca613bdc7ff8b7ff2ba56fd6a8fa9594e1e7b57e69975069db081dd311798 source=A:abstract@3e98e9839e7e2470c7619601cd0e8f5468477dfdc4dc1f5681314fc4ca1483a9 source=A:conclusion@c886edc62e0561a1e17a961ffd1d0527a5bae43a5607635ce8e247276c91a829 -->

## (3.2) and (3.3), two steps of the proof of Theorem 3.3: `Dissertation.PaperSpec.A.eq_uniq_coeff`, `eq_uniq_bwd`

Manuscript (proof of Theorem `thm:uniq`, `03-main-results.tex` lines 110–172): with
`δΘ_t := Θ¹_t − Θ²_t`, `μ^k_t := Law(Θ^k_t)`, `δψ_t := ψ(t, Θ¹_t, μ¹_t) − ψ(t, Θ²_t, μ²_t)` for
`ψ ∈ {b, σ, f}` "and, at the predictable tuples as in (1.1),
`δh_t := h(t, Θ^{1,−}_t, ·, μ^{1,−}_t) − h(t, Θ^{2,−}_t, ·, μ^{2,−}_t)`". By Fubini
`Θ^k_t ∈ L²(Ω, ℱ_t; H)` for a.e. `t`, so Assumption 2.3 applies to the pair and, with (2.8),
"`𝔼[|δb_t|² + |δσ_t|²_F + ‖δh_t‖²_{L²(ν)} + |δf_t|²] ≤ C 𝔼|δΘ_t|²_H` for a.e. `t`, where `C` is
independent of `t`. Then (3.2) `𝔼 ∫_0^T [|δb_t|² + |δσ_t|²_F + ‖δh_t‖²_{L²(ν)} + |δf_t|²] dt
< ∞`." Lines 158–172: "For the backward equation, `δY_t = δg_T + ∫_t^T δf_s ds − ∫_t^T δZ_s dW_s
− ∫_t^T ∫_E δU_s(e) Ñ(ds, de)`, where `δg_T := g(X¹_T, Law(X¹_T)) − g(X²_T, Law(X²_T))`. As the
terminal conditions presuppose `Law(X^k_T) ∈ P₂(ℝⁿ)`, we have `X^k_T ∈ L²`, and Assumption 2.3
with (2.9) gives `𝔼|δg_T|² ≤ C 𝔼|δX_T|² < ∞`. Furthermore, (3.2) gives
`𝔼 ∫_0^T |δf_s|² ds < ∞`. By Lemma 4.1, (3.3) `𝔼 sup_{t ≤ T} |δY_t|²
≤ C_BP (𝔼|δg_T|² + 𝔼 ∫_0^T |δf_s|² ds) < ∞`, therefore `δY ∈ S²(ℝᵐ)`."

Propositions:

* `eq_uniq_coeff`: under the hypotheses of Theorem 3.3 (those of `thm_uniq`, verbatim):
  `∑_i energy(δb_i) + ∑_{i, j} energy(δσ_{ij}) + ∑_i markedEnergy(δh_i) + ∑_k energy(δf_k) < ∞`,
  with `δb, δσ, δf` the differences of `driftProc`, `diffusionProc`, `driverProc` along `Θ¹, Θ²`,
  and `δh_i` the difference of `jumpProc T (coeffJump P T C (leftLimProc X^k) (leftLimProc Y^k)
  Z^k U^k)`, `k = 1, 2`.
* `eq_uniq_bwd`: `∃ C_BP : ℝ → ℝ`, then under the same hypotheses:
  `∫⁻ sup_{t ∈ [0, T]} |δY_t|² ≤ ofReal(C_BP(T)) (∫⁻ |δg_T|² + ∑_k energy(δf_k))`, and
  `∫⁻ |δg_T|² + ∑_k energy(δf_k) < ∞`, with `δg_T` the difference of the `terminalVal`s.

Readings:

* The hypotheses are those of Theorem 3.3, written as in `thm_uniq` (reviewed with Theorem 3.3).
  Assumption 2.2 is not assumed, as printed. Along one solution, the solution notion
  (`WeakSolution`, through `PaperAdmissibleInt`) asks the diffusion process and the jump
  representative `γ` to have finite energy (`σ_sq`, `γ_sq`), as the `L²` stochastic integrals of
  (1.1) need, but asks the drift and the driver processes only for integrable paths on `[0, T]`
  (`b_int`, `f_int`): these two need not be square integrable along one solution, and for them
  only the differences are claimed to be, as printed.
* The expectations are lower integrals in `[0, ∞]` (`energy`, `markedEnergy`, `esq`) over
  `[0, T]`; `|δσ|²_F` is `∑_{i, j}`, `‖δh‖²_{L²(ν)}` is `∑_i ∫ δh_i(e)² ν(de)`, and "`< ∞`" is
  `< ⊤`.
* `δψ` along `Θ^k` through `driftProc`, `diffusionProc`, `driverProc` and `terminalVal` (reviewed
  in `definitions.md`): `ψ(t, Θ^k_t(ω), Law Θ^k_t)` for `t ∈ [0, T]`. `δh` at the predictable
  tuples through `leftLimProc` and the canonical representative `coeffJump` (reviewed), as in
  `thm_stab`. The paper makes every claim about these expressions `dt`-a.e. or time-integrated,
  and the marked energy is a lower integral, so its value is that of the `dP ⊗ dt ⊗ ν`-class; the
  expression is not asked to be measurable (at `t = 0` the left limits read the paths before `0`).
* The bound at a.e. `t` printed before (3.2), with `C` independent of `t`, is the step that gives
  (3.2), not the display; it is not stated.
* (3.3): `C_BP` is the constant of Lemma 4.1, which `lem_bpbsde` reads as a function of `T`
  chosen before everything; the proposition likewise chooses a function of `T` first, which is
  all (3.3) asserts of it. "`< ∞`" is the finiteness of `𝔼|δg_T|² + 𝔼 ∫_0^T |δf_s|² ds`; with a
  real constant the bound is then finite. `δY ∈ S²` is the consequence drawn from it and is not
  stated separately.
* The equation for `δY` printed before (3.3) is the instance of (4.16) at `λ = 1` and zero forcing
  (`eq_dY`), and is not part of these claims.

Proofs: two solutions in `ℍ_weak` solve the `λ`-forced system at `λ = 1` with zero forcing
(`paperWeakSolutionForcedInt_one_zero_iff`); extended off `[0, T]`, their difference is a
`PairDiff` (`PaperWeakSolutionForcedInt.exists_pairDiff`, from Assumptions 2.3 and 2.5 along the
diagonal), whose integrands have finite energy by its definition: this is (3.2) for `δb, δσ, δf`,
and for `δh` once the jump coefficient at the predictable tuples is identified with the solutions'
representatives `γ¹ − γ²` almost everywhere, so with equal marked energy
(`PaperWeakSolutionInt.markedEnergy_coeffJump_sub_leftLim_eq`, through
`ae_forcedJump_sub_leftLim_eq` and `markedEnergy_congr_ae`). (3.3): the estimate of Lemma 4.1 for
each backward coordinate of the difference system (`LinearBSDEJ.brownianPoisson_estimate`,
`C_BP(T) = 13 e^T + 3T`), summed over the coordinates with
`sup_t ∑_k |δY_{k,t}|² ≤ ∑_k sup_t |δY_{k,t}|²`; the extensions agree with the solutions on
`[0, T]`, and the data are finite because the backward coordinates have square-integrable terminal
values and finite-energy drivers.

Witness: `Dissertation.Acceptance.A.thm_uniq_hypotheses`, the hypotheses of Theorem 3.3 (reviewed
with Theorem 3.3), which are those of both propositions.

Verdict: faithful.

<!-- spec-review: Dissertation.PaperSpec.A.eq_uniq_coeff ed839d34f480cba11fcb76fb4b640955 by=claude-author source=A:eq:uniq-coeff@2dd8f5d9caccdcd87ce71c94e62f3be5dc6ab3ef350822523ab9098d57f3d769 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.eq_uniq_coeff--claude-auditor--2026-10-20T00_40_52Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_uniq_coeff ed839d34f480cba11fcb76fb4b640955 by=claude-auditor source=A:eq:uniq-coeff@2dd8f5d9caccdcd87ce71c94e62f3be5dc6ab3ef350822523ab9098d57f3d769 -->
<!-- spec-review: Dissertation.PaperSpec.A.eq_uniq_bwd ed839d34f480cba12aa97c204e9816a6 by=claude-author source=A:eq:uniq-bwd@9e27142522202b563f42928c519e570d6b67fdfb9d25b3a33bdd984b39c35ef8 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.eq_uniq_bwd--claude-auditor--2026-10-20T00_40_52Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_uniq_bwd ed839d34f480cba12aa97c204e9816a6 by=claude-auditor source=A:eq:uniq-bwd@9e27142522202b563f42928c519e570d6b67fdfb9d25b3a33bdd984b39c35ef8 -->

## The bound before (3.2) and the backward difference before (3.3), in the proof of Theorem 3.3: `Dissertation.PaperSpec.A.eq_uniq_coeff_ae`, `eq_uniq_bwd_eq`

Manuscript (proof of Theorem `thm:uniq`, `03-main-results.tex` lines 110–138 and 158–163): with
`δΘ_t := Θ¹_t − Θ²_t`, `μ^k_t := Law(Θ^k_t)`, `δψ_t := ψ(t, Θ¹_t, μ¹_t) − ψ(t, Θ²_t, μ²_t)` for
`ψ ∈ {b, σ, f}` "and, at the predictable tuples as in (1.1),
`δh_t := h(t, Θ^{1,−}_t, ·, μ^{1,−}_t) − h(t, Θ^{2,−}_t, ·, μ^{2,−}_t)`" (lines 110–117). By
Fubini `Θ^k_t ∈ L²(Ω, ℱ_t; H)` for a.e. `t`, "Thus `(Θ^k_t, μ^k_t) ∈ D_t` for a.e. `t`, and
Assumption 2.3 is applicable to the pair `(Θ¹_t, μ¹_t)`, `(Θ²_t, μ²_t)`; moreover
`W₂(μ¹_t, μ²_t)² ≤ 𝔼|δΘ_t|²_H` by (2.8). Hence Assumption 2.3 yields
`𝔼[|δb_t|² + |δσ_t|²_F + ‖δh_t‖²_{L²(ν)} + |δf_t|²] ≤ C 𝔼|δΘ_t|²_H` for a.e. `t`, where `C` is
independent of `t`." (lines 129–138, inside the pinned region of `A:eq:uniq-coeff`, lines
110–142). Lines 158–163, before the pinned region of `A:eq:uniq-bwd` (lines 168–172): "For the
backward equation, `δY_t = δg_T + ∫_t^T δf_s ds − ∫_t^T δZ_s dW_s
− ∫_t^T ∫_E δU_s(e) Ñ(ds, de)`, where `δg_T := g(X¹_T, Law(X¹_T)) − g(X²_T, Law(X²_T))`."

Propositions: each for every horizon `T > 0`, coefficients with (2.3) (`JointBorel`) and
Assumption 2.3 with constant `L`, and `Θ¹, Θ²` solving (1.1) in `ℍ_weak` (`WeakSolution`) from the
same initial datum `ξ₀`:

* `eq_uniq_coeff_ae`: `∃ K : ℝ → ℝ`, chosen first, such that for almost every `t ∈ [0, T]`
  `∫⁻ (|δb_t|² + ∑_i |δσ_{i,t}|² + ∑_i ∫⁻ |δh_{i,t}(e)|² ν(de) + |δf_t|²) dP
  ≤ ofReal(K(L)) ∫⁻ (|δX_t|² + |δY_t|² + ∑_k |δZ_{k,t}|² + ∑_k ∫⁻ |δU_{k,t}(e)|² ν(de)) dP`,
  with `δb, δσ, δf` the differences of `driftProc`, `diffusionProc`, `driverProc` along `Θ¹, Θ²`
  and `δh_i` that of `jumpProc T (coeffJump P T C (leftLimProc X^k) (leftLimProc Y^k) Z^k U^k)`.
* `eq_uniq_bwd_eq`: for every coordinate `k`, (a) almost every path of `δf_k` is integrable on
  `[0, T]`; (b) `δZ_k` and `δU_k` meet the conditions of the Itô and the compensated integral
  (the proof arguments of `stochasticIntegral`, given as data); (c) for every `t ∈ [0, T]`,
  almost surely, `δY_{k,t} = δg_{k,T} + ∫_{[t, T]} δf_k(s) ds − ((∫ δZ_k dW)_T − (∫ δZ_k dW)_t)
  − ((∫∫ δU_k dÑ)_T − (∫∫ δU_k dÑ)_t)`, with the library's integrals and `δg_{k,T}` the
  difference of the `terminalVal`s.

Readings:

* The hypotheses are the ones the two steps use: (2.3), Assumption 2.3 (whose coupling bounds
  (2.8) and (2.9) the step invokes) and two solutions in `ℍ_weak` with the same initial
  condition. The passages are printed in the proof of Theorem 3.3, under Assumptions 2.3–2.5 and a
  `G` of full rank, where Theorem 3.3 itself gives `Θ¹ = Θ²`; the scope review found that, read
  with those hypotheses, both assertions hold with both sides zero. Remark 3.4 says the argument
  uses "only the Lipschitz control of coefficient differences", and the propositions are stated
  under exactly that. They imply the printed assertions: the hypotheses of Theorem 3.3 contain
  these, with the same solution notion (`WeakSolution`, as in `thm_uniq`). The witness below has
  two distinct solutions.
* `C` independent of `t`: `K` is chosen before everything, as a function of the Lipschitz constant
  `L` alone, so it depends neither on `t` nor on `T`, the data or the solutions.
* `|δΘ_t|²_H = |δX_t|² + |δY_t|² + |δZ_t|²_F + ‖δU_t‖²_{L²(ν)}`, the norm of
  `H = ℝⁿ × ℝᵐ × ℝ^{m × d} × L²(ν; ℝᵐ)`; the expectations are lower integrals in `[0, ∞]` (`esq`,
  `∑_k esq` for `|·|²_F`, `∫⁻ |·|² ν(de)` for `‖·‖²_{L²(ν)}`), so the bound says nothing at a
  time where its right side is infinite. "For a.e. `t`" is Lebesgue-almost every `t ∈ [0, T]`.
* `δψ` through `driftProc`, `diffusionProc`, `driverProc` and `terminalVal` (reviewed in
  `definitions.md`), and `δh` at the predictable tuples through `leftLimProc` and `coeffJump`,
  exactly as in `eq_uniq_coeff` (reviewed with (3.2)).
* The backward difference is the difference of the backward equations of (1.1) at the two
  solutions, an identity of processes on `[0, T]`, read at each time almost surely: the form in
  which (1.1) is stated (`PaperWeakSolutionInt`). `∫_t^T … dW` and `∫_t^T ∫_E … Ñ` are differences
  of the library's integrals at `T` and `t`; (a) and (b) say the three integrals are not read at
  junk values. The section of (3.2) and (3.3) records these two assertions as not stated; these
  propositions state them.

Proofs: two solutions in `ℍ_weak` solve the `λ`-forced system at `λ = 1` with zero forcing
(`paperWeakSolutionForcedInt_one_zero_iff`); extended off `[0, T]`, their difference is a
difference system (`PairDiff`) with the coupling matrix `0` and `α = β₁ = β₂ = 0`, for which
Assumption 2.5 holds trivially (`diagonalMonotone_zero`, `terminalMonotone_zero`), so Assumption
2.3 along the diagonal suffices (`PaperWeakSolutionForcedInt.exists_pairDiff_lip`). Its Lipschitz
field (`PairDiff.lip`, (3.2) at almost every time, with `K = 10 (2L)²`) is the bound once the jump
coefficient at the predictable tuples is identified with the solutions' representatives almost
everywhere (`ae_forcedJump_sub_leftLim_eq`, read time first by
`ae_time_ae_of_ae_markedEnergyMeasure`). Its backward coordinates are linear backward equations
(`LinearBSDEJ`) with terminal value `δg_k` and drift `δf_k`, whose fields give (a)–(c) on `[0, T]`,
where the extensions agree with the solutions.

Witness: `Dissertation.Acceptance.A.rem_uniq_lip_hypotheses`: over a Lévy driver with `d = 1`,
`ν = δ₀` on `ℝ`, `𝒢₀ = ⊥`, `n = m = 1`, `T = π/4`, the system of Example 5.1(i) with
`σ_c = h_c = 0`, `β₂ = 1` and the reversed sign `β₁ = −1` (`b = y`, `σ = z`, `h = u`, `f = x`,
`g = x`) satisfies (2.3) and Assumption 2.3 with `L = 1`; from the initial datum `0` it has the
two solutions `(sin t, cos t, 0, 0)` and the zero tuple in `ℍ_weak`, with `δX_t = sin t` and
`δY_t = cos t` (stated); and it satisfies Assumption 2.5 for no `G` of full rank (stated), which is
why two distinct solutions can exist. By hand, `δb_t = cos t` and `δf_t = sin t`, so the left side
of the bound is `cos² t + sin² t = 1` at every `t` and its right side `40 · 1`; `δσ = δh = 0`. In
the backward difference `δg_T = sin(π/4) ≠ 0` and `∫_t^T δf_s ds = cos t − cos(π/4)`, so the
terminal and drift terms are present; the stochastic terms vanish.

Verdict: faithful; the hypotheses are those the steps use, and the printed passages, under the
hypotheses of Theorem 3.3, are their instances.

<!-- spec-review: Dissertation.PaperSpec.A.eq_uniq_coeff_ae ed839d34f480cba1a9e05e97904e4b0f by=claude-author source=A:eq:uniq-coeff@2dd8f5d9caccdcd87ce71c94e62f3be5dc6ab3ef350822523ab9098d57f3d769 -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.eq_uniq_coeff_ae--claude-auditor--2026-10-20T15_30_04Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_uniq_coeff_ae ed839d34f480cba1a9e05e97904e4b0f by=claude-auditor source=A:eq:uniq-coeff@2dd8f5d9caccdcd87ce71c94e62f3be5dc6ab3ef350822523ab9098d57f3d769 -->
<!-- spec-review: Dissertation.PaperSpec.A.eq_uniq_bwd_eq ed839d34f480cba1dacb4b647f5f4499 by=claude-author source=A:eq:uniq-bwd@9e27142522202b563f42928c519e570d6b67fdfb9d25b3a33bdd984b39c35ef8 -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.eq_uniq_bwd_eq--claude-auditor--2026-10-20T15_30_04Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_uniq_bwd_eq ed839d34f480cba1dacb4b647f5f4499 by=claude-auditor source=A:eq:uniq-bwd@9e27142522202b563f42928c519e570d6b67fdfb9d25b3a33bdd984b39c35ef8 -->

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

<!-- spec-review: Dissertation.PaperSpec.A.thm_cwp ed839d34f480cba10deeabcd10e6e74d by=claude-author source=A:thm:cwp@0dd6b95ee4474a8c7091ae6a816a6a0de0ea67b50d49a5c437094a757adcf5f3 source=A:abstract@3e98e9839e7e2470c7619601cd0e8f5468477dfdc4dc1f5681314fc4ca1483a9 source=A:intro:limin-comparison@90030b2d20a48b0ae1854a8fb2d4053ad1be2da6ece678b13095bd33e99bda43 source=A:conclusion@c886edc62e0561a1e17a961ffd1d0527a5bae43a5607635ce8e247276c91a829 -->
Review by claude-reviewer: faithful (report `reports/Dissertation.PaperSpec.A.thm_cwp--claude-reviewer--2026-10-17T16_05_53Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.thm_cwp ed839d34f480cba10deeabcd10e6e74d by=claude-reviewer source=A:thm:cwp@0dd6b95ee4474a8c7091ae6a816a6a0de0ea67b50d49a5c437094a757adcf5f3 source=A:abstract@3e98e9839e7e2470c7619601cd0e8f5468477dfdc4dc1f5681314fc4ca1483a9 source=A:intro:limin-comparison@90030b2d20a48b0ae1854a8fb2d4053ad1be2da6ece678b13095bd33e99bda43 source=A:conclusion@c886edc62e0561a1e17a961ffd1d0527a5bae43a5607635ce8e247276c91a829 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.thm_cwp--claude-auditor--2026-10-19T03_34_53Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.thm_cwp ed839d34f480cba10deeabcd10e6e74d by=claude-auditor source=A:thm:cwp@0dd6b95ee4474a8c7091ae6a816a6a0de0ea67b50d49a5c437094a757adcf5f3 source=A:abstract@3e98e9839e7e2470c7619601cd0e8f5468477dfdc4dc1f5681314fc4ca1483a9 source=A:intro:limin-comparison@90030b2d20a48b0ae1854a8fb2d4053ad1be2da6ece678b13095bd33e99bda43 source=A:conclusion@c886edc62e0561a1e17a961ffd1d0527a5bae43a5607635ce8e247276c91a829 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.thm_cwp--claude-auditor--2026-10-20T12_42_56Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.thm_cwp ed839d34f480cba10deeabcd10e6e74d by=claude-auditor source=A:thm:cwp@0dd6b95ee4474a8c7091ae6a816a6a0de0ea67b50d49a5c437094a757adcf5f3 source=A:abstract@3e98e9839e7e2470c7619601cd0e8f5468477dfdc4dc1f5681314fc4ca1483a9 source=A:intro:limin-comparison@90030b2d20a48b0ae1854a8fb2d4053ad1be2da6ece678b13095bd33e99bda43 source=A:sec4:proof-thm35@ed713718821e088c6ca09a59f75d22202a9e9960885df259a33fd8f6dd54fcbe source=A:conclusion@c886edc62e0561a1e17a961ffd1d0527a5bae43a5607635ce8e247276c91a829 -->

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

<!-- spec-review: Dissertation.PaperSpec.A.prop_strict ed839d34f480cba1f1c48950c52ae4f4 by=claude-author source=A:prop:strict@b18b8a1407fec705caed58f7f0bb7604c994a084d50703fdd8cc68b071003604 source=A:abstract@3e98e9839e7e2470c7619601cd0e8f5468477dfdc4dc1f5681314fc4ca1483a9 source=A:conclusion@c886edc62e0561a1e17a961ffd1d0527a5bae43a5607635ce8e247276c91a829 -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.prop_strict--claude-reviewer--2026-10-17T12_11_02Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.prop_strict ed839d34f480cba1f1c48950c52ae4f4 by=claude-reviewer source=A:prop:strict@b18b8a1407fec705caed58f7f0bb7604c994a084d50703fdd8cc68b071003604 source=A:abstract@3e98e9839e7e2470c7619601cd0e8f5468477dfdc4dc1f5681314fc4ca1483a9 source=A:conclusion@c886edc62e0561a1e17a961ffd1d0527a5bae43a5607635ce8e247276c91a829 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.prop_strict--claude-auditor--2026-10-19T03_31_23Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.prop_strict ed839d34f480cba1f1c48950c52ae4f4 by=claude-auditor source=A:prop:strict@b18b8a1407fec705caed58f7f0bb7604c994a084d50703fdd8cc68b071003604 source=A:abstract@3e98e9839e7e2470c7619601cd0e8f5468477dfdc4dc1f5681314fc4ca1483a9 source=A:conclusion@c886edc62e0561a1e17a961ffd1d0527a5bae43a5607635ce8e247276c91a829 -->

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

<!-- spec-review: Dissertation.PaperSpec.A.cor_robust ed839d34f480cba154326c82c977c8bd by=claude-author source=A:cor:robust@3d1625968e85be99f1f27b950433c30d582746e8a2445900a724b8d565e7c757 -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.cor_robust--claude-reviewer--2026-10-17T12_24_23Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.cor_robust ed839d34f480cba154326c82c977c8bd by=claude-reviewer source=A:cor:robust@3d1625968e85be99f1f27b950433c30d582746e8a2445900a724b8d565e7c757 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.cor_robust--claude-auditor--2026-10-19T03_36_02Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.cor_robust ed839d34f480cba154326c82c977c8bd by=claude-auditor source=A:cor:robust@3d1625968e85be99f1f27b950433c30d582746e8a2445900a724b8d565e7c757 -->
<!-- spec-review: Dissertation.PaperSpec.A.cor_robust_wp ed839d34f480cba16dd662e97e677716 by=claude-author source=A:cor:robust@3d1625968e85be99f1f27b950433c30d582746e8a2445900a724b8d565e7c757 source=A:conclusion@c886edc62e0561a1e17a961ffd1d0527a5bae43a5607635ce8e247276c91a829 -->
Review by claude-reviewer: faithful (report `reports/Dissertation.PaperSpec.A.cor_robust_wp--claude-reviewer--2026-10-17T16_05_53Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.cor_robust_wp ed839d34f480cba16dd662e97e677716 by=claude-reviewer source=A:cor:robust@3d1625968e85be99f1f27b950433c30d582746e8a2445900a724b8d565e7c757 source=A:conclusion@c886edc62e0561a1e17a961ffd1d0527a5bae43a5607635ce8e247276c91a829 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.cor_robust_wp--claude-auditor--2026-10-19T03_37_29Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.cor_robust_wp ed839d34f480cba16dd662e97e677716 by=claude-auditor source=A:cor:robust@3d1625968e85be99f1f27b950433c30d582746e8a2445900a724b8d565e7c757 source=A:conclusion@c886edc62e0561a1e17a961ffd1d0527a5bae43a5607635ce8e247276c91a829 -->
<!-- spec-review: Dissertation.PaperSpec.A.cor_robust_lip ed839d34f480cba14b18016daa0b4aac by=claude-author source=A:cor:robust@3d1625968e85be99f1f27b950433c30d582746e8a2445900a724b8d565e7c757 -->
Review by claude-reviewer: broader (report `reports/Dissertation.PaperSpec.A.cor_robust_lip--claude-reviewer--2026-10-17T16_03_52Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.cor_robust_lip ed839d34f480cba14b18016daa0b4aac by=claude-reviewer source=A:cor:robust@3d1625968e85be99f1f27b950433c30d582746e8a2445900a724b8d565e7c757 -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.cor_robust_lip--claude-auditor--2026-10-19T03_34_13Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.cor_robust_lip ed839d34f480cba14b18016daa0b4aac by=claude-auditor source=A:cor:robust@3d1625968e85be99f1f27b950433c30d582746e8a2445900a724b8d565e7c757 -->

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

<!-- spec-review: Dissertation.PaperSpec.A.ass_G ed839d34f480cba1654da9b84ef073af by=claude-author source=A:ass:G@0ca63278064f162ffc77480e11f78f5fba3573556a22730b0bd4ca763ba1886f -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.ass_G--claude-reviewer--2026-10-17T12_05_30Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ass_G ed839d34f480cba1654da9b84ef073af by=claude-reviewer source=A:ass:G@0ca63278064f162ffc77480e11f78f5fba3573556a22730b0bd4ca763ba1886f -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.ass_G--claude-auditor--2026-10-19T03_31_21Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ass_G ed839d34f480cba1654da9b84ef073af by=claude-auditor source=A:ass:G@0ca63278064f162ffc77480e11f78f5fba3573556a22730b0bd4ca763ba1886f -->

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

Re-reading at `1f67672` (lines 211–221 of `sections/02-model-assumptions.tex`): the paragraph of
(2.10) is unchanged (of the remark only (2.9) changed), and the proposition says what it says.

<!-- spec-review: Dissertation.PaperSpec.A.eq_lipfun ed839d34f480cba187b5540277706218 by=claude-author source=A:rem:wasserstein-bounds@c04119bf34c0cb8093c0843e1c7b01bf93697e1e04d779493a112bce12987835 -->
<!-- spec-review: Dissertation.PaperSpec.A.eq_lipfun ed839d34f480cba187b5540277706218 by=claude-author source=A:rem:wasserstein-bounds@a8c8906e45bdcd6591c7751bd3186ea3b83dd382cd95543acb4edcabc2093661 -->
Review by claude-reviewer: faithful (report `reports/Dissertation.PaperSpec.A.eq_lipfun--claude-reviewer--2026-10-17T16_03_52Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_lipfun ed839d34f480cba187b5540277706218 by=claude-reviewer source=A:rem:wasserstein-bounds@a8c8906e45bdcd6591c7751bd3186ea3b83dd382cd95543acb4edcabc2093661 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.eq_lipfun--claude-auditor--2026-10-19T03_34_14Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_lipfun ed839d34f480cba187b5540277706218 by=claude-auditor source=A:rem:wasserstein-bounds@baddffc87439566a55a973b4d3634494482f991387c121349eff7592be8093ab -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.eq_lipfun--claude-auditor--2026-10-20T11_24_07Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_lipfun ed839d34f480cba187b5540277706218 by=claude-auditor source=A:rem:wasserstein-bounds@c04119bf34c0cb8093c0843e1c7b01bf93697e1e04d779493a112bce12987835 -->

## Remark 2.6, (2.11): `Dissertation.PaperSpec.A.eq_margproj`

Manuscript: marginal projection `P₂(H) → P₂(L²(ν))`, `μ ↦ μ^U`, is 1-Lipschitz for `W₂`:
`W₂(μ^U, μ'^U) ≤ W₂(μ, μ')`.

Proposition: for every σ-finite `ν` on a countably generated `(E, ℰ)`, all `n, m, d` and all
`μ, μ' ∈ P₂(H)`: `w2P μ.margU μ'.margU ≤ w2H μ μ'`.

Correspondence: `μ^U` is `margU` (reviewed in `definitions.md`); `W₂` on `P₂(L²(ν; ℝᵐ))` is
`w2P` of the `L²(ν)` norm, and on `P₂(H)` it is `w2H` of the Hilbert norm. The statement has no
hypotheses beyond the standing setting.

Verdict: faithful.

Re-reading at `1f67672` (lines 222–231 of `sections/02-model-assumptions.tex`): the paragraph of
(2.11) is unchanged (of the remark only (2.9) changed), and the proposition says what it says.

<!-- spec-review: Dissertation.PaperSpec.A.eq_margproj ed839d34f480cba1c19abbad6d02050c by=claude-author source=A:rem:wasserstein-bounds@c04119bf34c0cb8093c0843e1c7b01bf93697e1e04d779493a112bce12987835 -->
<!-- spec-review: Dissertation.PaperSpec.A.eq_margproj ed839d34f480cba1c19abbad6d02050c by=claude-author source=A:rem:wasserstein-bounds@a8c8906e45bdcd6591c7751bd3186ea3b83dd382cd95543acb4edcabc2093661 -->
Review by claude-reviewer: faithful (report `reports/Dissertation.PaperSpec.A.eq_margproj--claude-reviewer--2026-10-17T16_03_52Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_margproj ed839d34f480cba1c19abbad6d02050c by=claude-reviewer source=A:rem:wasserstein-bounds@a8c8906e45bdcd6591c7751bd3186ea3b83dd382cd95543acb4edcabc2093661 -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.eq_margproj--claude-auditor--2026-10-19T03_34_37Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_margproj ed839d34f480cba1c19abbad6d02050c by=claude-auditor source=A:rem:wasserstein-bounds@baddffc87439566a55a973b4d3634494482f991387c121349eff7592be8093ab -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.eq_margproj--claude-auditor--2026-10-20T11_24_08Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_margproj ed839d34f480cba1c19abbad6d02050c by=claude-auditor source=A:rem:wasserstein-bounds@c04119bf34c0cb8093c0843e1c7b01bf93697e1e04d779493a112bce12987835 -->

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

<!-- spec-review: Dissertation.PaperSpec.A.lem_bpbsde ed839d34f480cba1202e3ec284da1f15 by=claude-author source=A:lem:bpbsde@d62094248f27ce8bc15117e3e39b9ea5169bf86a1af04e994e8c82a5ec2ff534 -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.lem_bpbsde--claude-reviewer--2026-10-17T12_23_54Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.lem_bpbsde ed839d34f480cba1202e3ec284da1f15 by=claude-reviewer source=A:lem:bpbsde@d62094248f27ce8bc15117e3e39b9ea5169bf86a1af04e994e8c82a5ec2ff534 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.lem_bpbsde--claude-auditor--2026-10-19T03_35_50Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.lem_bpbsde ed839d34f480cba1202e3ec284da1f15 by=claude-auditor source=A:lem:bpbsde@d62094248f27ce8bc15117e3e39b9ea5169bf86a1af04e994e8c82a5ec2ff534 -->

## The `M²` paragraph of the proof of Lemma 4.1: `Dissertation.PaperSpec.A.lem41_M2_no_square_moment`, `lem41_jump_times`, `lem41_M2_integrand`, `lem41_M2_zero_mean`

Manuscript (proof of Lemma `lem:bpbsde`, lines 139–152 and 173–187; the inventory pins line 151,
inside the sentence of lines 148–152): the stochastic-integral terms of (4.5) decompose into the
local martingales `M^W`, `M^1` and `M²_t := ∫_0^t ∫_E e^s |δU_s(e)|² Ñ(ds, de)`, "each of which we
now show satisfies `𝔼[M_T − M_t] = 0`. The three do not share one argument: `δU ∈ H_N` gives the
quadratic integrand of `M²` no square moments, so the `L²` theory behind the bounds below does not
reach it — nor, with `ν(E) = ∞` admitted, does localisation along jump times, which then fail to
exhaust `[0, T]`. `M²` is instead handled through the compensation formula, which asks only for
integrability." And (lines 173–187): "For `M²` the integrand `e^s |δU_s(e)|²` is predictable and
nonnegative and, because `δU ∈ H_N`, lies in `L¹(dP ⊗ ds ⊗ ν)`:
`𝔼 ∫_0^T ∫_E e^s |δU_s(e)|² ν(de) ds ≤ e^T 𝔼 ∫_0^T ‖δU_s‖²_{L²(ν)} ds < ∞`. Both the Poisson
integral and its compensator are therefore integrable, so the increment splits under the
expectation: `𝔼[M²_T − M²_t] = 𝔼 ∫_t^T ∫_E e^s |δU_s(e)|² Ñ(ds, de)
= 𝔼 ∫_t^T ∫_E e^s |δU_s(e)|² N(ds, de) − 𝔼 ∫_t^T ∫_E e^s |δU_s(e)|² ν(de) ds = 0`."

Propositions:

* `lem41_M2_no_square_moment`, the first clause: in every standing setting (`enlJoint`, `ν`
  σ-finite on a countably generated space) with `ν ≠ 0`, for `m, d ≥ 1` and `T > 0`, there is
  `δU : Fin m → ℝ → Ω → E → ℝ` of the class `H²_N` of Lemma 4.1 (marked predictable, zero off
  `[0, T]`, finite energy, coordinatewise) with `markedEnergy (e^s ∑_k δU_k²) = ⊤`, that is
  `𝔼 ∫_0^T ∫_E (e^s |δU_s(e)|²)² ν(de) ds = ∞`. A finite `ν` is admitted.
* `lem41_jump_times`: for every Lévy driver with `ν(E) = ∞`, almost surely
  `N((0, t] × E) = ∞` for every `t > 0`; every jump time, read in `[0, ∞]` as
  `τ_k = ⨅ t, ⨅ (_ : 0 ≤ t ∧ k ≤ N((0, t] × E)), ofReal t`, `k ∈ ℕ`, is `0`; and
  `sup_k τ_k < ofReal T` for every `T > 0`.
* `lem41_M2_integrand`: under the hypotheses of Lemma 4.1 (those of `lem_bpbsde`, verbatim),
  `(ω, s, e) ↦ e^s ∑_k δU_k(s, e)²` is `MarkedPredictable (enlJoint 𝒢₀ D h𝒢₀) ν`, and
  `0 ≤ e^s ∑_k δU_k(s, e)²` for every `(ω, s, e)`.
* `lem41_M2_zero_mean`: under the hypotheses of Lemma 4.1 (those of `lem_bpbsde`, verbatim),
  `𝔼 ∫_0^T ∫_E e^s |δU_s(e)|² ν(de) ds ≤ e^T ∑_k 𝔼 ∫_0^T ‖δU^k_s‖² ds`, the right side is finite,
  and for every `t ∈ [0, T]` the Poisson integral and the compensator of `e^s |δU_s(e)|²` over
  `(t, T] × E` have finite expectation and
  `∫ (∫_{(t, T] × E} e^s |δU|² dN − ∫_t^T ∫_E e^s |δU|² ν(de) ds) dP = 0`.

Readings:

* The first clause is a statement about the hypothesis `δU ∈ H_N`: membership does not give the
  quadratic integrand square moments, that is, some `δU ∈ H_N` has none. It is a general
  non-implication about the class, read where the class is not trivial: for `ν ≠ 0`, the case in
  which `M²` is not identically `0`. At `ν = 0` the fibre `L²(ν)` is trivial, every marked
  integrand has zero energy and `M² = 0`; that is the degenerate case Remark 2.10 sets aside
  ("When `ν = 0` the fibre `L²(ν)` is trivial, `δU = 0` identically, and the restriction
  disappears"), about which the sentence says nothing. Beyond the standing setting,
  `m, d ≥ 1` and `T > 0`, the only hypothesis is `ν ≠ 0`; a finite `ν` is admitted, `ν(E) = ∞`
  being the hypothesis of the localisation assertion of the same sentence, not of this one.
* Disagreement on the first clause, and its resolution. The author first read the sentence in
  every setting Lemma 4.1 covers, `ν = 0` included (§2 asks only that `ν` be σ-finite, the lemma
  is used at `ν = 0` through Theorem 3.5, and the sentence makes the localisation assertion
  conditional, "with `ν(E) = ∞` admitted", while stating no restriction on the first), and
  refuted that reading at `ν = 0`, where membership in `H_N` does give the quadratic integrand
  square moments, with the clause for `ν ≠ 0` beside it as a correction. Two blind reviews held
  that reading not to be the paper's: the sentence states the general non-implication, and the
  paper treats `ν = 0` as the degenerate case (Remark 2.10), so the faithful reading is the
  clause for `ν ≠ 0`. Resolution: the sentence is read for `ν ≠ 0`, and that clause is the
  claim's own, not a correction of it; the manuscript's sentence will say "when `ν ≠ 0`" at its
  next revision.
* "Square moments of the quadratic integrand": the square integral of `e^s |δU_s(e)|²` with
  respect to `dP ⊗ ds ⊗ ν` on `[0, T] × E`, which is `markedEnergy P ν T` of
  `e^s ∑_k δU_k(s, e)²`; `|δU|² = ∑_k δU_k²` in `ℝᵐ`. `δU` is existential, with the conditions of
  the class `H_N` of Lemma 4.1 as conjuncts (as `hU`, `hUv`, `hUs` of `lem_bpbsde`); `m, d ≥ 1`
  and `T > 0` are in force. The clause is about the class, so the other data of the lemma (the
  equation, `δY`, `δZ`, `δξ`, `φ`) are not constrained.
* The second clause: the jump times are those of `N`, `τ_k = inf {t ≥ 0 : N((0, t] × E) ≥ k}`,
  read in `[0, ∞]` (`⨅` of `ofReal t` over the times `t ≥ 0` with `N((0, t] × E) ≥ k`), where the
  infimum of the empty set is `∞`: `τ_k = 0` says that the set is nonempty and reaches down to
  `0`, so a driver without a `k`-th jump does not meet it (an infimum in `ℝ`, with `sInf ∅ = 0`,
  would not say this). "With `ν(E) = ∞` admitted, … localisation along jump times, which then
  fail to exhaust `[0, T]`" is read as three almost-sure conjuncts: every interval `(0, t]`,
  `t > 0`, carries infinitely many jumps (why the jump times fail); every `τ_k` is `0`; and
  `sup_k τ_k < T` for every `T > 0` (they do not exhaust `[0, T]`: stopping at them reaches no
  positive time). The proposition is broader than printed: it holds for every Lévy driver with
  `ν(E) = ∞`, without the initial enlargement or a horizon (the jump times are functions of `N`
  alone); the printed claim is its instance at the driver `D` of the setting of Lemma 4.1 when
  its intensity has `ν(E) = ∞`.
* The integrand clause (line 173, "the integrand `e^s |δU_s(e)|²` is predictable and
  nonnegative"): predictability is read as `MarkedPredictable` for the filtration of the
  setting, the notion the repository uses for marked integrands and the class of `hU`:
  measurability of `(ω, s, e) ↦ e^s ∑_k δU_k(s, e)²` for the σ-algebra on `Ω × ℝ × E`
  generated by the rectangles `F × (r, q] × B` with `r ≥ 0`, `F ∈ ℱ_r` and `ν(B) < ∞`
  (`markedPredictableSigma`). On the positive times it is the predictable σ-algebra of the
  filtration times the σ-algebra of `E` (`ν` σ-finite); it does not separate the nonpositive
  times, on which a marked predictable process takes a single value, which is no restriction
  here, `δU` vanishing at the negative times. Nonnegativity is pointwise, at every
  `(ω, s, e)`. The `L¹` membership of the same sentence is in the third clause. The hypotheses
  are those of Lemma 4.1, verbatim; the proof uses only `hU` and `hUv`.
* The third clause: `M²_T − M²_t` read pathwise as
  `∫_{(t, T] × E} e^s |δU_s(e)|² N(ds, de) − ∫_t^T ∫_E e^s |δU_s(e)|² ν(de) ds`, as `eq_zeromean`
  reads the compensated integral, with `∫_t^T` over `(t, T]`. The `L¹` bound is the display of
  lines 176–177, the energies on `[0, T]` as in `lem_bpbsde`; "both … are integrable" is the
  finiteness of the expectations of the two nonnegative integrals (lower integrals in `[0, ∞]`);
  `𝔼[M²_T − M²_t] = 0` is the Bochner expectation of the pathwise difference. The hypotheses are
  those of Lemma 4.1, verbatim; the proof uses only those on `δU`.

Proofs: the first clause with `δU^k_s(e) = 1_{(T/2, T]}(s) 1_A(e) c` for every `k`, `A`
measurable with `0 < ν(A) < ∞` (from σ-finiteness and `ν ≠ 0`) and
`c = 1_{(0, 1]}(W¹_{T/2}) (W¹_{T/2})^{−1/4}`: `W¹_{T/2}` has the law `N(0, T/2)`, whose density
is bounded above, and bounded below on `(0, 1]`, by positive constants, so
`𝔼 c² ≍ ∫_0^1 x^{−1/2} dx < ∞` and `𝔼 c⁴ ≍ ∫_0^1 x^{−1} dx = ∞`; then
`markedEnergy δU^k = 𝔼 c² · ν(A) · T/2` and the square moment is at least
`𝔼 c⁴ · ν(A) · T/2 = ∞` (`exists_markedPredictable_sq_markedEnergy_eq_top`). The second clause
from `sec2_infinite_activity`: almost surely `N((s, t] × E) = ∞` for `0 ≤ s < t`; at `s = 0`
this is the first conjunct, and then every `ε > 0` is in the set defining `τ_k`, so `τ_k ≤ ε`
for every `ε > 0`, `τ_k = 0`, and `sup_k τ_k = 0 < T`. The integrand clause
(`markedPredictable_exp_mul_sum_sq`): on the positive times a measurable function of the time
and of the marked predictable vector `(δU_k)_k` is marked predictable
(`MarkedPredictable.comp_measurable`), and the integrand vanishes at the nonpositive times — at
`s < 0` by `hUv`, at `s = 0` since a marked predictable process takes one value at all
nonpositive times (`MarkedPredictable.eq_of_nonpos`) — so it equals its cut to the positive
times; nonnegativity from `e^s > 0` and the squares. The third from (2.1) and (2.2)
(`aemeasurable_and_lintegral_compensation`, `integral_compensated_eq_zero`) at the marked
predictable `ψ = 1_{(t, T]}(s) e^s |δU_s(e)|²`, with `e^s ≤ e^T` on `[0, T]`
(`quadratic_compensation`, `lintegral_exp_mul_sum_sq_le`).

Witnesses: `Dissertation.Acceptance.A.lem41_M2_no_square_moment_hypotheses` for the first
clause (a Lévy driver with `d = 1`, `ν = δ₀ ≠ 0` on `ℝ`, `𝒢₀ = ⊥`, `m = 1`, `T = 1`);
`Dissertation.Acceptance.A.sec2_infinite_activity_hypotheses` for the second (Lebesgue measure
on `ℝ`, of infinite mass, carried by a Lévy driver with `d = 1`);
`Dissertation.Acceptance.A.lem_bpbsde_hypotheses` for the integrand clause and the third (the
hypotheses of Lemma 4.1 at the backward component of the solution of Example 5.1(i), reviewed
with Lemma 4.1).

Verdict: the first clause, read for `ν ≠ 0` with the disagreement above resolved, the second
clause, the integrand clause and the third clause are faithful, the second broader than printed.

<!-- spec-review: Dissertation.PaperSpec.A.lem41_M2_no_square_moment ed839d34f480cba18ac876cdb600252c by=claude-author source=A:lem4.1:M2-infinite-activity@89a434caa7c84ed5e2143713d1483dde1e7fa2001de1f51afe467a70f3c9fe8f -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.lem41_M2_no_square_moment_corr--claude-auditor--2026-10-19T22_59_53Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.lem41_M2_no_square_moment ed839d34f480cba18ac876cdb600252c by=claude-auditor source=A:lem4.1:M2-infinite-activity@89a434caa7c84ed5e2143713d1483dde1e7fa2001de1f51afe467a70f3c9fe8f -->
<!-- spec-review: Dissertation.PaperSpec.A.lem41_jump_times ed839d34f480cba17f1df52f488747a1 by=claude-author source=A:lem4.1:M2-infinite-activity@89a434caa7c84ed5e2143713d1483dde1e7fa2001de1f51afe467a70f3c9fe8f -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.lem41_jump_times--claude-auditor--2026-10-20T02_03_19Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.lem41_jump_times ed839d34f480cba17f1df52f488747a1 by=claude-auditor source=A:lem4.1:M2-infinite-activity@89a434caa7c84ed5e2143713d1483dde1e7fa2001de1f51afe467a70f3c9fe8f -->
<!-- spec-review: Dissertation.PaperSpec.A.lem41_M2_integrand ed839d34f480cba118f567d673033f15 by=claude-author source=A:lem4.1:M2-infinite-activity@89a434caa7c84ed5e2143713d1483dde1e7fa2001de1f51afe467a70f3c9fe8f -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.lem41_M2_integrand--claude-auditor--2026-10-20T02_03_19Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.lem41_M2_integrand ed839d34f480cba118f567d673033f15 by=claude-auditor source=A:lem4.1:M2-infinite-activity@89a434caa7c84ed5e2143713d1483dde1e7fa2001de1f51afe467a70f3c9fe8f -->
<!-- spec-review: Dissertation.PaperSpec.A.lem41_M2_zero_mean ed839d34f480cba15a569c2d7c1d42fd by=claude-author source=A:lem4.1:M2-infinite-activity@89a434caa7c84ed5e2143713d1483dde1e7fa2001de1f51afe467a70f3c9fe8f -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.lem41_M2_zero_mean--claude-auditor--2026-10-19T22_59_53Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.lem41_M2_zero_mean ed839d34f480cba15a569c2d7c1d42fd by=claude-auditor source=A:lem4.1:M2-infinite-activity@89a434caa7c84ed5e2143713d1483dde1e7fa2001de1f51afe467a70f3c9fe8f -->

## `M^W` and `M¹` in the proof of Lemma 4.1: `Dissertation.PaperSpec.A.lem41_MW`, `lem41_M1`, `lem41_M1_chain`

Manuscript (proof of Lemma `lem:bpbsde`, lines 139–148 and 153–172; clauses of the claim pinned at
line 151): "The stochastic-integral terms in (4.5) decompose into three local martingales
`M^W_t := ∫_0^t e^s ⟨δY_{s−}, δZ_s dW_s⟩`, `M^1_t := ∫_0^t ∫_E e^s ⟨δY_{s−}, δU_s(e)⟩ Ñ(ds, de)`,
`M^2_t := ∫_0^t ∫_E e^s |δU_s(e)|² Ñ(ds, de)`, each of which we now show satisfies
`𝔼[M_T − M_t] = 0`. […] For `M^W`, BDG and Cauchy–Schwarz give
`𝔼 sup_{t ≤ T} |M^W_t| ≤ c_BDG e^T (𝔼 sup_{t ≤ T} |δY_t|²)^{1/2} (𝔼 ∫_0^T |δZ_s|²_F ds)^{1/2} < ∞`,
and for `M^1` BDG, Cauchy–Schwarz and (2.1) give
`𝔼 sup_{t ≤ T} |M^1_t| ≤ c_BDG 𝔼[(∫_0^T ∫_E e^{2s} |δY_{s−}|² |δU_s(e)|² N(ds, de))^{1/2}]
≤ c_BDG e^T (𝔼 sup_{t ≤ T} |δY_t|²)^{1/2} (𝔼 ∫_0^T ∫_E |δU_s(e)|² N(ds, de))^{1/2}
= c_BDG e^T (𝔼 sup_{t ≤ T} |δY_t|²)^{1/2} (𝔼 ∫_0^T ∫_E |δU_s(e)|² ν(de) ds)^{1/2}
= c_BDG e^T (𝔼 sup_{t ≤ T} |δY_t|²)^{1/2} (𝔼 ∫_0^T ‖δU_s‖²_{L²(ν)} ds)^{1/2} < ∞`.
These bounds put the running suprema of `M^W` and `M^1` in `L¹`, so the supremum criterion gives
`𝔼[M_T − M_t] = 0` for `M ∈ {M^W, M^1}`." The §4 preamble (lines 30–35) fixes BDG in
quadratic-variation form, at `p = 1` for the zero-mean arguments, with one universal constant
`c_BDG`.

Propositions (hypotheses: those of Lemma 4.1, `lem_bpbsde`, verbatim):

* `lem41_MW`: there is `c₀ > 0` such that for every `c ≥ c₀`: the integrand
  `H_s(j) = e^s ∑_k δY^k_{s−} δZ^{kj}_s` (with `δY^k_{s−}` = `leftLimProc δY k s ω` for `s > 0`
  and `0` for `s ≤ 0`) has a local Itô integral `M^W` on `[0, T]`
  (`IsLocalBrownianIntegral D.W (enlJoint …) _ T H M^W`), and every such `M^W` satisfies
  `∫⁻ sup_{t ∈ [0, T]} ‖M^W_t‖ ≤ ofReal (c e^T) (∫⁻ sup_{t ∈ [0, T]} esq δY_t)^{1/2}
  (∑_{k, j} energy δZ^{kj})^{1/2}`, the right side is finite, and for every `t ∈ [0, T]`,
  `M^W_T − M^W_t` is integrable with mean zero.
* `lem41_M1`: the same for `φ_s(e) = e^s ∑_k δY^k_{s−} δU^k_s(e)`, the local compensated
  integral (`IsLocalCompensatedIntegral D.N (enlJoint …) _ T φ M^1`) and
  `(∑_k markedEnergy δU^k)^{1/2}` in place of the `δZ` energy.
* `lem41_M1_chain`: with the Poisson integrals over `(0, T] × E` (lower integrals against
  `D.N.N ω`), `∫⁻ (∫∫ e^{2s} |δY_{s−}|² |δU_s(e)|² dN)^{1/2} ≤ ofReal e^T
  (∫⁻ sup esq δY)^{1/2} (∫⁻ ∫∫ |δU|² dN)^{1/2}`; `∫⁻ ∫∫ |δU|² dN = ∫⁻ ∫_{(0, T]} ∫_E |δU|² dν ds`;
  and the latter is `∑_k markedEnergy δU^k`.

Readings:

* The local martingales are local stochastic integrals. Their integrands carry `δY_{s−}`, of which
  Lemma 4.1 gives only `𝔼 sup |δY|² < ∞` (the membership step of the same proof, the first
  conjunct of `lem_bpbsde`), so `𝔼 ∫ e^{2s} |δY_{s−}|² |δZ_s|² ds` can be infinite (for a
  martingale `δY_t = 𝔼[δξ | ℱ_t]` with `δξ ∈ L² \ L⁴` it is), and the `L²` integrals of the
  library do not apply; the paper's "local martingales" are the local integrals. They are
  defined (`IsLocalBrownianIntegral`, `IsLocalCompensatedIntegral`, reviewed in `definitions.md`)
  as càdlàg adapted processes agreeing, up to stopping times exhausting `[0, T]`, with the `L²`
  integrals of the integrand cut off at those times; the definition determines `M` up to
  indistinguishability on `[0, T]`, so "every such `M`" is the paper's `M^W` (resp. `M^1`), and
  the existence conjunct is the paper's definition `M^W_t := ∫_0^t …`. The local-martingale
  property is carried by the definition and not stated as a separate conjunct.
* `δY_{s−}` is the left limit of `δY` at `s ∈ (0, T]`, which exists by hypothesis; at `s ≤ 0`
  the integrand is set to `0`: Lemma 4.1 constrains `δY` on `[0, T]` only, `δZ` and `δU` vanish
  at negative times, and the integrals do not see the time `0` (a Lebesgue-null time; `N` charges
  no fixed time). At `s > T` the integrands vanish with `δZ`, `δU`.
* `⟨δY_{s−}, δZ_s dW_s⟩ = ∑_j (∑_k δY^k_{s−} δZ^{kj}_s) dW^j_s`, the library's multidimensional
  integral of the vector integrand; `|δZ_s|²_F = ∑_{k, j} (δZ^{kj}_s)²`, so `𝔼 ∫_0^T |δZ_s|²_F ds`
  is `∑_{k, j} energy`; `𝔼 ∫_0^T ‖δU_s‖² ds = ∑_k markedEnergy`; `𝔼 sup_{t ≤ T} |δY_t|²` is the
  lower integral of the supremum of `esq`, as in `lem_bpbsde`. Expectations of nonnegative
  quantities are lower integrals in `[0, ∞]`; "`< ∞`" is the finiteness of the right side, which
  with the bound puts the running suprema in `L¹` (line 171).
* `c_BDG`: one universal constant in the paper, unspecified; each proposition asserts its bound
  for every value of it at least some `c₀ > 0` (here `c₀ = 9`), as the other propositions with
  `c_BDG` do, so all of them hold together for every `c_BDG` at least the largest `c₀`. The
  reading is that `c_BDG` is a sufficiently large universal constant, every value at least `c₀`;
  it is not every constant for which Davis's inequality holds: the best constant of that
  inequality may be smaller than `9`, and at such a value the propositions say nothing. The paper
  fixes `c_BDG` only as one universal constant valid at `p = 1` and `p = 2` (lines 29–33) and
  states no value of it; its later uses (the finiteness of the bounds, the supremum criterion,
  constants such as `C_Φ = C_Φ(T, L, c_BDG)`) need only some universal value, which any value at
  least the largest `c₀` is.
* The filtration. The local integrals are local martingales for `enlJoint 𝒢₀ D h𝒢₀`, the usual
  augmentation of `ℱ^{W,N}_t ∨ ℱ₀` (right-continuous, with the `P`-null sets), the filtration of
  the paper (reviewed in `definitions.md`). The `L²` integrals cut off at the localising times
  are the library's for that filtration (`isBrownianFiltration_enlJoint`,
  `isPoissonFiltration_enlJoint`), martingales for it, and the localising times are its stopping
  times; those of the proofs, the exit times of the path of `δY` from balls (`exitSeq`) and the
  times the energy of the integrand reaches a level (`energyHit`), are stopping times because the
  filtration is right-continuous (`isStoppingTime_exitSeq`, `isStoppingTime_energyHit`, with
  `isRightContinuous_enlJoint`). `M` stopped at the `k`-th time is the `k`-th `L²` integral
  stopped there (`definitions.md`), so `M` is a local martingale for that filtration.
* Marked progressive integrands and representatives are harmless. The conditions of the library's
  integrals, and so of the cut-off integrands in `IsLocalBrownianIntegral` and
  `IsLocalCompensatedIntegral`, ask for progressive (on `Ω × ℝ × E`, marked progressive)
  measurability, which predictability implies (`MarkedPredictable.markedProgressivelyMeasurable`,
  `progressivelyMeasurable_of_predictable_of_vanish`), so the paper's predictable integrands are
  among those admitted; and the integrals depend only on the class of the integrand up to a
  `P ⊗ ds` (resp. `P ⊗ ds ⊗ ν`) null set on `[0, T]` (`multidimStochasticIntegral_congr_of_energy`,
  `compensatedIntegral_congr_of_markedEnergy`), so admitting more integrands adds no other
  integral: the integral of an admitted integrand that agrees almost everywhere with the paper's
  predictable one is, at every time of `[0, T]` and almost surely, the paper's. Here the
  integrands are themselves predictable: they are the products of `δZ`, `δU` (predictable by
  hypothesis, zero after `T`) with the weight `e^s δY_{s−}` cut to `(0, T]`, which is predictable
  (the left limits of an adapted path with left limits).
* "`𝔼[M_T − M_t] = 0`" is read for every `t ∈ [0, T]` with the increment integrable (Bochner
  expectation of an integrable function), the conclusion of the supremum criterion
  (`sec4_supremum_criterion`), which the proof replaces by a direct argument.
* The chain for `M^1`. Its first link, `𝔼 sup |M^1| ≤ c_BDG 𝔼 [M^1]_T^{1/2}` with the
  quadratic variation `[M^1]_T = ∫∫ e^{2s} |δY_{s−}|² |δU|² N(ds, de)`, is BDG at `p = 1` in
  quadratic-variation form for a discontinuous local martingale (Davis's inequality), cited from
  He, Wang and Yan; it is not stated (recorded in the claim's `scope_note`, as the BDG inequality
  is in `A:sec4:supremum-criterion`). The bound it leads to, `lem41_M1`, is stated and proved
  through the predictable quadratic variation `⟨M^1⟩_T = ∫_0^T ∫_E e^{2s} |δY_{s−}|² |δU|² ν ds`
  (Lenglart's inequality), with the same right-hand side. The later links are
  `lem41_M1_chain`: the Cauchy–Schwarz link, stated without the common factor `c_BDG ≥ 0` of both
  sides (equivalent); the compensation link (2.1) with `∫_0^T` read over `(0, T]`; and the norm
  link, the definition of `‖δU_s‖_{L²(ν)}` (energies on `[0, T]`, which differ from `(0, T]` by
  a null set).
* Not formalised here: that the stochastic-integral terms of (4.5) are `M^W`, `M^1` and `M^2`
  (the decomposition belongs to (4.5), `A:eq:itoY2`, a proof step not stated); `M^2` is the
  `M²` paragraph (`lem41_M2_zero_mean`, read pathwise), and that it is a local martingale is
  `lem41_M2_martingale`.

Proofs: BDG at `p = 1` for the `L²` integrals (`lintegral_biSup_le_brownian`,
`lintegral_biSup_le_compensated`, constant `9`) by Lenglart's argument
(`lintegral_le_of_good_lambda`): the integral of the integrand cut off when its energy reaches `δ` (`energyHit`, a stopping time)
agrees with the integral up to that time (the library's locality), Doob's `L²` inequality bounds
its squared supremum by `4 𝔼 (A_T ∧ δ)`, and the tail bounds integrate over `δ`. The local
integrals exist along the exit times of `δY` from balls (`exitSeq`), up to which
`|δY_{s−}|` is bounded and the cut-off integrands have finite energy
(`exists_isLocalBrownianIntegral`); BDG passes to them by monotone convergence
(`IsLocalBrownianIntegral.lintegral_biSup_le`), and with `|e^s δY_{s−}|² ≤ e^{2T} sup |δY|²` and
Cauchy–Schwarz (`localBrownian_weight`, `localCompensated_weight`) gives the bounds, with
`𝔼 sup |δY|² < ∞` from `lem_bpbsde`. The zero means: the increments of the cut-off integrals have
mean zero, converge almost surely to `M_T − M_t`, and are Cauchy in `L¹` by BDG applied to the
differences (`integrable_and_integral_eq_zero_of_cauchy`). The chain: pathwise
`e^{2s} |δY_{s−}|² ≤ e^{2T} sup |δY|²` and Hölder (`sqrt_setLIntegral_leftLim_le`,
`lintegral_mul_sqrt_le`), (2.1) at the marked predictable `|δU|²` cut to the positive times
(`poisson_sumSq_compensation`), and `Ioc` and `Icc` differing by a null set
(`lintegral_Ioc_sumSq_eq_markedEnergy`).

Witness: `Dissertation.Acceptance.A.lem_bpbsde_nonzero_hypotheses` — a Lévy driver with `d = 1`,
`ν = δ₀`, `𝒢₀ = ⊥`, `m = 1`, `T = 1`, `δZ = δU = 1_{(0, 1]}` (energy `1` each, stated), `φ = 0`,
`δY` the sum of everywhere-càdlàg versions of `∫_0^t δZ dW` and `∫_0^t ∫ δU dÑ`, `δξ = δY_1`: every
hypothesis of Lemma 4.1 holds, and the integrands of `M^W`, `M^1` are not zero (the existing
witness of Lemma 4.1, `lem_bpbsde_hypotheses`, is the zero solution of Example 5.1(i)).

Verdict: `lem41_MW` and `lem41_M1` faithful with representation choices (local stochastic
integrals for the local martingales; the integrand at `s ≤ 0`; `c_BDG` as every value at least
`c₀`); `lem41_M1_chain` faithful with representation choices (the common factor `c_BDG` dropped,
`(0, T]` for `∫_0^T`); the first link of the `M^1` chain is a cited result, recorded in
`scope_note`.

<!-- spec-review: Dissertation.PaperSpec.A.lem41_MW ed839d34f480cba1d59592d221a6cd18 by=claude-author source=A:lem4.1:M2-infinite-activity@89a434caa7c84ed5e2143713d1483dde1e7fa2001de1f51afe467a70f3c9fe8f -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.lem41_MW--claude-auditor--2026-10-20T08_55_13Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.lem41_MW ed839d34f480cba1d59592d221a6cd18 by=claude-auditor source=A:lem4.1:M2-infinite-activity@89a434caa7c84ed5e2143713d1483dde1e7fa2001de1f51afe467a70f3c9fe8f -->
<!-- spec-review: Dissertation.PaperSpec.A.lem41_M1 ed839d34f480cba10bd49a12773fa34d by=claude-author source=A:lem4.1:M2-infinite-activity@89a434caa7c84ed5e2143713d1483dde1e7fa2001de1f51afe467a70f3c9fe8f -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.lem41_M1--claude-auditor--2026-10-20T08_55_13Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.lem41_M1 ed839d34f480cba10bd49a12773fa34d by=claude-auditor source=A:lem4.1:M2-infinite-activity@89a434caa7c84ed5e2143713d1483dde1e7fa2001de1f51afe467a70f3c9fe8f -->
<!-- spec-review: Dissertation.PaperSpec.A.lem41_M1_chain ed839d34f480cba11e7d5cd5bc08d7ae by=claude-author source=A:lem4.1:M2-infinite-activity@89a434caa7c84ed5e2143713d1483dde1e7fa2001de1f51afe467a70f3c9fe8f -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.lem41_M1_chain--claude-auditor--2026-10-20T08_55_13Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.lem41_M1_chain ed839d34f480cba11e7d5cd5bc08d7ae by=claude-auditor source=A:lem4.1:M2-infinite-activity@89a434caa7c84ed5e2143713d1483dde1e7fa2001de1f51afe467a70f3c9fe8f -->

## `M²` is a local martingale, in the proof of Lemma 4.1: `Dissertation.PaperSpec.A.lem41_M2_martingale`

Manuscript (proof of Lemma `lem:bpbsde`, lines 139–145, with the paragraph on `M²` at lines
173–187): "The stochastic-integral terms in (4.5) decompose into three local martingales […]
`M²_t := ∫_0^t ∫_E e^s |δU_s(e)|² Ñ(ds, de)`, each of which we now show satisfies
`𝔼[M_T − M_t] = 0`." The paragraph on `M²` reads it through the compensation formula: "the
integrand `e^s |δU_s(e)|²` is predictable and nonnegative and, because `δU ∈ H_N`, lies in
`L¹(dP ⊗ ds ⊗ ν)` […] Both the Poisson integral and its compensator are therefore integrable"
(quoted in full with `lem41_M2_zero_mean`).

Proposition (hypotheses: those of Lemma 4.1, `lem_bpbsde`, verbatim): with
`M²_t = ∫_{(0, t] × E} e^s ∑_k δU_k(s, e)² N(ds, de) − ∫_{(0, t]} ∫_E e^s ∑_k δU_k(s, e)² ν(de) ds`
(Bochner integrals against `D.N.N ω` and against `ν` and `ds`, pathwise), for every
`t ∈ [0, T]` the lower integral `∫⁻ ∫⁻_{(0, t] × E} e^s ∑_k δU_k² dN dP` is finite, `M²_t` is
integrable, and `M²_t` is `AEStronglyMeasurable` for `enlJoint 𝒢₀ D h𝒢₀ t`; and for
`0 ≤ s ≤ t ≤ T`, `P[M²_t | enlJoint 𝒢₀ D h𝒢₀ s] =ᵐ[P] M²_s`.

Readings:

* `M²` read pathwise. The paper does not take `M²` as an `L²` compensated integral: its
  integrand has no square moment in general (`lem41_M2_no_square_moment`), and with
  `ν(E) = ∞` localisation along jump times fails (`lem41_jump_times`); it reads `M²` through the
  compensation formula, as the Poisson integral minus its compensator, both integrable. That is
  `M²` here, as in `lem41_M2_zero_mean`, with `∫_0^t` over `(0, t]` (Lebesgue-null `{0}`, and `N`
  charges no fixed time). For an integrand whose Poisson integral is integrable, the integral
  against `Ñ` of the general theory of integrals against random measures is that difference.
* "Is a local martingale" (lines 139–141) is stated as "is a martingale on `[0, T]`", which is
  stronger: a martingale on `[0, T]` is a local martingale on `[0, T]` (the localising times all
  `T`). It holds because both terms are integrable, which the paper establishes for `M²`
  (lines 173–179). The martingale property is read in its standard form: integrability at every
  `t ∈ [0, T]`, adaptedness, and `𝔼[M²_t | ℱ_s] = M²_s` almost surely for `s ≤ t` in `[0, T]`,
  where the conditional expectation sees `M²_t` only up to a null set. Adaptedness is stated up
  to a null set (`AEStronglyMeasurable` for `ℱ_t`): the Poisson integral at time `t` is the lower
  integral of an `ℱ_t ⊗ 𝓑 ⊗ 𝓔`-measurable function against the random measure, which is
  `ℱ_t`-measurable off a null set; the filtration contains the `P`-null sets, so this is
  adaptedness of a version. The finiteness of the expectation of the Poisson integral, the first
  conjunct, is the paper's "the Poisson integral … integrable" at every `t`.
* The filtration is `enlJoint 𝒢₀ D h𝒢₀`, the usual augmentation of `ℱ^{W,N}_t ∨ ℱ₀`, the filtration
  of the paper and of `M^W` and `M¹` (`lem41_MW`).
* Not stated: the regularity of the paths of `M²`, which the paper does not use; its only use of
  `M²` is `𝔼[M²_T − M²_t] = 0`, `lem41_M2_zero_mean`.
* The instantiation that gives the printed claim. The proposition is broader than the printed
  sentence: it asserts the martingale property of `M²` on `[0, T]` where the paper asserts that
  `M²` is a local martingale with `𝔼[M²_T − M²_t] = 0`. Both printed assertions follow from it.
  Taking expectations in `𝔼[M²_T | ℱ_t] = M²_t` (the proposition at `s = t`, `t = T`) gives
  `𝔼[M²_T − M²_t] = 0`. A martingale on `[0, T]` is a local martingale there, with the constant
  localising times `T`. The martingale property itself is the paper's tool, (2.1), applied to the
  marked predictable integrand `1_A 1_{(s, t]}(r) e^r |δU_r(e)|²`, `A ∈ ℱ_s`, which is
  nonnegative and in `L¹(dP ⊗ ds ⊗ ν)` since `δU ∈ H²_N`: it gives `𝔼[1_A (M²_t − M²_s)] = 0`.

Proof: `pathwiseCompensated` (`BrownianPoisson/PathwiseMartingale.lean`). Cut to the times up to
`t`, the marked predictable integrand is `ℱ_t ⊗ 𝓑 ⊗ 𝓔`-measurable; the random measure restricted
to `(0, t] × A`, `ν(A) < ∞`, is `ℱ_t`-measurable and almost surely finite, and on the events
`{N((0, t] × A) ≤ n}` a finite kernel, so the lower integral against it is `ℱ_t`-measurable off a
null set, and exhausting `E` by sets of finite measure gives the integral on `(0, t] × E`
(`exists_measurable_ae_eq_lintegral_N`, `aestronglyMeasurable_pathwiseCompensated`).
Integrability from (2.1) and `𝔼 ∫_0^T ∫_E e^s |δU|² ν(de) ds ≤ e^T ∑_k markedEnergy δU^k < ∞`
(`integrable_pathwiseCompensated`). The martingale property: for `A ∈ ℱ_s` the integrand
`1_A 1_{(s, t]}(r) e^r |δU_r(e)|²` is marked predictable, so (2.2) gives
`𝔼[1_A (M²_t − M²_s)] = 0` (`setIntegral_pathwiseCompensated_eq`), and the conditional
expectation follows (`condExp_pathwiseCompensated`, by `ae_eq_condExp_of_forall_setIntegral_eq`).

Witness: `Dissertation.Acceptance.A.lem_bpbsde_infinite_hypotheses`, the hypotheses of Lemma 4.1
at an instance of infinite activity, the regime of the claim: a Lévy driver with `d = 1` and the
intensity `ν` Lebesgue measure on `E = ℝ`, σ-finite with `ν(ℝ) = ∞` (stated), `𝒢₀ = ⊥`,
`m = 1`, `T = 1`, the integrands `δZ = 1_{(0, 1]}` and `δU_s(e) = 1_{(0, 1]}(s) 1_{(0, 1]}(e)`,
`φ = 0`, `δY` the sum of everywhere-càdlàg versions of `∫_0^t δZ dW` and
`∫_0^t ∫_E δU Ñ(ds, de)`, and `δξ = δY_1`. It makes `δU` nonzero in `L²(ν)`: its marked energy
on `[0, 1]` is `1` (stated). The integrand of `M²` is then `e^s 1_{(0, 1]}(s) 1_{(0, 1]}(e)`, not
zero. The former witness, `lem_bpbsde_nonzero_hypotheses` (`ν = δ₀`, of finite mass), is that of
`lem41_MW` and `lem41_M1`.

Verdict: broader (a martingale on `[0, T]` for the printed local martingale; the printed claim
follows by the instantiation above), with representation choices (`M²` read pathwise, as in
`lem41_M2_zero_mean`; adaptedness up to a null set).

<!-- spec-review: Dissertation.PaperSpec.A.lem41_M2_martingale ed839d34f480cba1983f1a786ecea56b by=claude-author source=A:lem4.1:M2-infinite-activity@89a434caa7c84ed5e2143713d1483dde1e7fa2001de1f51afe467a70f3c9fe8f -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.lem41_M2_martingale--claude-auditor--2026-10-20T10_33_55Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.lem41_M2_martingale ed839d34f480cba1983f1a786ecea56b by=claude-auditor source=A:lem4.1:M2-infinite-activity@89a434caa7c84ed5e2143713d1483dde1e7fa2001de1f51afe467a70f3c9fe8f -->

## (4.6), the bound at every time in the proof of Lemma 4.1: `Dissertation.PaperSpec.A.eq_supE`

Manuscript (proof of Lemma `lem:bpbsde`, lines 188–217): taking expectations in (4.5) and Young's
inequality give `𝔼 e^t |δY_t|² + 𝔼 ∫_t^T e^s (|δZ_s|²_F + ‖δU_s‖²) ds
≤ 𝔼 e^T |δξ|² + 𝔼 ∫_t^T e^s |φ_s|² ds`. "Bounding `1 ≤ e^s ≤ e^T` on both sides leaves, for every
`t ≤ T`, `𝔼|δY_t|² + 𝔼 ∫_t^T (|δZ_s|²_F + ‖δU_s‖²_{L²(ν)}) ds ≤ R`,
`R := e^T (𝔼|δξ|² + 𝔼 ∫_0^T |φ_s|² ds)`. Both terms on the left are nonnegative and `R` does not
depend on `t`, so each is bounded by `R` on its own, the first uniformly in `t` and the second at
`t = 0`; adding them, (4.6) `sup_{t ≤ T} 𝔼|δY_t|² + 𝔼 ∫_0^T (|δZ_s|²_F + ‖δU_s‖²_{L²(ν)}) ds
≤ 2R = C₀ (𝔼|δξ|² + 𝔼 ∫_0^T |φ_s|² ds)`, `C₀ := 2e^T`."

Proposition: under the hypotheses of Lemma 4.1 (those of `lem_bpbsde`, verbatim): for every
`t ∈ [0, T]`, `∫⁻ |δY_t|² + ∫⁻ ∫_{[t, T]} (∑_k |δZ_k|² + ∑_k ∫ |δU_k(e)|² ν(de)) ds
≤ ofReal(e^T) (∫⁻ |δξ|² + ∑_k 𝔼 ∫_0^T |φ_k|² ds)`; and
`sup_{t ∈ [0, T]} ∫⁻ |δY_t|² + (∑_{k, j} energy(δZ_{kj}) + ∑_k markedEnergy(δU_k))
≤ ofReal(2 e^T) (∫⁻ |δξ|² + ∑_k 𝔼 ∫_0^T |φ_k|² ds)`.

Readings:

* The hypotheses are those in force in the proof, the hypotheses of Lemma 4.1, written as in
  `lem_bpbsde` (reviewed with Lemma 4.1); the bound at every time and (4.6) use them all.
* "For every `t ≤ T`": every `t ∈ [0, T]`; `∫_t^T` over `[t, T]` (the same as `(t, T]` for
  Lebesgue measure). The expectations are lower integrals in `[0, ∞]`; `|δY_t|² = ∑_k δY_k(t)²`
  (`esq`), `|δZ_s|²_F = ∑_{k, j}`, `‖δU_s‖² = ∑_k ∫ δU_k(s, e)² ν(de)`, as in `lem_bpbsde`. `R` is
  written out, `ofReal(e^T)` times the data.
* (4.6): the supremum over `t ∈ [0, T]` of the expectations, plus the energies on `[0, T]` (the
  second term of the bound at `t = 0`), at most `C₀ (…)` with `C₀ = 2e^T` explicit, which is
  `2R`. The intermediate display with the weights `e^s` is a step of the proof, not stated.

Proof: for each coordinate, the equation is a linear backward equation with a progressive version
of `φ` (`exists_linearBSDEJ_of_measurable`); the weighted second-moment identities at the
horizons `t` and `T` differ by the integral of their rate over `(t, T]`, which Young's inequality
and `1 ≤ e^s ≤ e^T` bound below (`LinearBSDEJ.lintegral_sq_at_add_energy_le`); summed over the
coordinates (`brownianPoisson_energy_at_vec_of_measurable`), and (4.6) by the bound at every time
and at `t = 0` (`brownianPoisson_supE_vec_of_measurable`).

Witness: `Dissertation.Acceptance.A.lem_bpbsde_hypotheses`, the hypotheses of Lemma 4.1 at the
backward component of the solution of Theorem 3.5 for Example 5.1(i) (reviewed with Lemma 4.1).

Verdict: faithful.

<!-- spec-review: Dissertation.PaperSpec.A.eq_supE ed839d34f480cba17f3cae8e2942fb86 by=claude-author source=A:eq:supE@f8d195505541585ca475bfa8dacd155e918c8cab4d02984f325636e45bc61066 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.eq_supE--claude-auditor--2026-10-19T22_59_53Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_supE ed839d34f480cba17f3cae8e2942fb86 by=claude-auditor source=A:eq:supE@f8d195505541585ca475bfa8dacd155e918c8cab4d02984f325636e45bc61066 -->

## The weighted inequality in the proof of Lemma 4.1: `Dissertation.PaperSpec.A.eq_supE_weighted`

Manuscript (proof of Lemma `lem:bpbsde`, lines 188–199), after the pathwise identity (4.5) at
`t ∈ [0, T]` and the zero means of its three stochastic terms: "Taking expectations in (4.5)
therefore removes the three martingale terms, and bounding the drift term by Young's inequality,
`2⟨δY_s, φ_s⟩ ≤ |δY_s|² + |φ_s|²`, cancels the `|δY_s|²` integrals on the two sides:
`𝔼 e^t |δY_t|² + 𝔼 ∫_t^T e^s (|δZ_s|²_F + ‖δU_s‖²_{L²(ν)}) ds ≤ 𝔼 e^T |δξ|²
+ 𝔼 ∫_t^T e^s |φ_s|² ds`." The display lies before the pinned region of `A:eq:supE` (lines
208–217), whose bound by `R` it gives once `1 ≤ e^s ≤ e^T`.

Proposition: under the hypotheses of Lemma 4.1 (those of `lem_bpbsde`, verbatim), for every
`t ∈ [0, T]`, `ofReal(e^t) ∫⁻ |δY_t|² + ∫⁻ ∫_{[t, T]} ofReal(e^s) (∑_k |δZ_{k,s}|²
+ ∑_k ∫⁻ |δU_{k,s}(e)|² ν(de)) ds ≤ ofReal(e^T) ∫⁻ |δξ|² + ∫⁻ ∫_{[t, T]} ofReal(e^s) |φ_s|² ds`.

Readings:

* The hypotheses are those in force in the proof, the hypotheses of Lemma 4.1, as for (4.6).
* "For every `t`": (4.5) is written at every `t ∈ [0, T]`, and so is the display. `∫_t^T` is over
  `[t, T]`; `𝔼 e^t |δY_t|²` is `e^t 𝔼|δY_t|²`, the weight being deterministic. The expectations
  are lower integrals in `[0, ∞]`, sample-outer: `|δY_t|²` and `|φ_s|²` are `esq`,
  `|δZ_s|²_F = ∑_k |δZ_{k,s}|²` (the rows of `δZ` are its coordinates) and
  `‖δU_s‖² = ∑_k ∫ δU_k(s, e)² ν(de)`, as in `lem_bpbsde`. The bound says nothing when its right
  side is infinite; under the hypotheses it is finite.
* Taking expectations in (4.5) and Young's inequality are the proof; (4.5) is not stated
  (`A:eq:itoY2`, whose note records that the proof uses it through this display).
* The section of (4.6) records this display as a step of the proof, not stated; it is stated
  here.

Proof: for each coordinate the equation is a linear backward equation (`LinearBSDEJ`) with a
progressive version `ψ` of `φ`, equal to `φ` almost everywhere on `Ω × [0, T]` and of the same
energy (`exists_linearBSDEJ_of_measurable`). The weighted second-moment identities at the weight
`e^s` at the horizons `t` and `T` (`LinearBSDEJ.exp_mul_integral_mul_self_eq_at`, from the
library's identity for Itô–Lévy processes) differ by the integral of their rate over `(t, T]`, in
which Young's inequality `2 y ψ ≤ y² + ψ²` cancels the `y²` terms
(`LinearBSDEJ.exp_lintegral_sq_at_add_energy_le`); the sum over the coordinates, with `ψ`
replaced by `φ` in the last integral, is `brownianPoisson_weighted_at_vec_of_measurable`.

Witness: `Dissertation.Acceptance.A.lem_bpbsde_nonzero_hypotheses`: over a Lévy driver with
`d = 1`, `ν = δ₀` on `ℝ`, `𝒢₀ = ⊥`, `m = 1`, `T = 1`, the integrands `δZ = δU = 1_{(0, 1]}`,
`φ = 0`, `δY_t = ∫_0^t δZ dW + ∫_0^t ∫_E δU Ñ(ds, de)` and `δξ = δY_1` meet the hypotheses of
Lemma 4.1, `δZ` with energy `1` (stated). By hand `𝔼|δY_t|² = 2t`, and at `t` the inequality reads
`2t e^t + 2(e − e^t) ≤ 2e`: the weighted `δZ`- and `δU`-integral is positive for `t < 1`, and the
terminal term is `2e`.

Verdict: faithful.

<!-- spec-review: Dissertation.PaperSpec.A.eq_supE_weighted ed839d34f480cba197b43e0802d21b08 by=claude-author source=A:eq:supE@f8d195505541585ca475bfa8dacd155e918c8cab4d02984f325636e45bc61066 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.eq_supE_weighted--claude-auditor--2026-10-20T15_31_29Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_supE_weighted ed839d34f480cba197b43e0802d21b08 by=claude-auditor source=A:eq:supE@f8d195505541585ca475bfa8dacd155e918c8cab4d02984f325636e45bc61066 -->

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

<!-- spec-review: Dissertation.PaperSpec.A.lem_small ed839d34f480cba12f6a12214671fd14 by=claude-author source=A:lem:small@bffd23b982e584c71b1ab55af148dce8ccd1f30bcb7d7cda8b1ed69982efc706 -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.lem_small--claude-reviewer--2026-10-17T12_26_58Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.lem_small ed839d34f480cba12f6a12214671fd14 by=claude-reviewer source=A:lem:small@bffd23b982e584c71b1ab55af148dce8ccd1f30bcb7d7cda8b1ed69982efc706 -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.lem_small--claude-auditor--2026-10-19T03_37_18Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.lem_small ed839d34f480cba12f6a12214671fd14 by=claude-auditor source=A:lem:small@bffd23b982e584c71b1ab55af148dce8ccd1f30bcb7d7cda8b1ed69982efc706 -->

## (4.7) and (4.8), the frozen step in the proof of Lemma 4.2: `Dissertation.PaperSpec.A.eq_frozenfwd`, `eq_frozenbwd`

Manuscript (proof of Lemma `lem:small`, lines 258–310): "Fix `λ ∈ [0, 1]` and a forcing `q`. For
a trial tuple `Θ = (X, Y, Z, U) ∈ ℍ` write `μ^Θ_t := Law(Θ_t)`, `μ^{Θ,−}_t := Law(Θ⁻_t)`, and
define `Φ_λ(Θ) := Θ̄ = (X̄, Ȳ, Z̄, Ū)` by the forward and backward constructions below.
*Forward.* Let `X̄` be given by the frozen forward dynamics (4.7)
`X̄_t = ξ₀ + λ ∫_0^t b(s, Θ_s, μ^Θ_s) ds + λ ∫_0^t σ(s, Θ_s, μ^Θ_s) dW_s
+ λ ∫_0^t ∫_E h(s, Θ⁻_s, e, μ^{Θ,−}_s) Ñ(ds, de) + ∫_0^t q^b_s ds + ∫_0^t q^σ_s dW_s
+ ∫_0^t ∫_E q^h_s(e) Ñ(ds, de)`. In (4.7) the coefficient `h` is evaluated at the left limits
`(Θ⁻_s, μ^{Θ,−}_s)`; by Lemma `lem:lawflow` these agree with `(Θ_s, μ^Θ_s)` outside a
`dt ⊗ dP`-null set, so either form may be used inside the `dt ⊗ dP`-integrals below. Since
`Θ ∈ ℍ`, (4.2) gives `𝔼 ∫_0^T |ψ(s, Θ_s, μ^Θ_s)|² ds < ∞` for `ψ ∈ {b, σ, h}`, and
`q^b, q^σ, q^h` are square-integrable by hypothesis. The coefficients are jointly Borel, so these
integrands are progressively measurable and the jump integrand is predictable. Cauchy–Schwarz on
the drift and Doob/BDG on the two martingale integrals then give `𝔼 sup_{t ≤ T} |X̄_t|² < ∞`, so
(4.7) defines a unique `X̄ ∈ S²(ℝⁿ)`. *Backward.* The random variable
`Ξ := λ g(X̄_T, Law(X̄_T)) + q^g_T + ∫_0^T (λ f(s, Θ_s, μ^Θ_s) + q^f_s) ds` lies in
`L²(Ω, ℱ_T; ℝᵐ)` by (4.3), (4.2) applied to `f`, and the square-integrability of `q^g_T` and
`q^f`. Set `M_t := 𝔼[Ξ | ℱ_t]`. By the Brownian–Poisson predictable representation property there
are unique `Z̄ ∈ H²_W`, `Ū ∈ H²_N` with `M_t = M_0 + ∫_0^t Z̄_s dW_s + ∫_0^t ∫_E Ū_s(e) Ñ(ds, de)`.
Put `Ȳ_t := M_t − ∫_0^t (λ f(s, Θ_s, μ^Θ_s) + q^f_s) ds`. Doob's inequality and `Ξ ∈ L²` give
`M ∈ S²(ℝᵐ)`. The drift is square-integrable by (4.2) and `q^f ∈ L²`, so Cauchy–Schwarz gives
`Ȳ ∈ S²(ℝᵐ)`. By construction `(Ȳ, Z̄, Ū)` solves the frozen linear BSDE (4.8)
`Ȳ_t = λ g(X̄_T, Law(X̄_T)) + q^g_T + ∫_t^T (λ f(s, Θ_s, μ^Θ_s) + q^f_s) ds − ∫_t^T Z̄_s dW_s
− ∫_t^T ∫_E Ū_s(e) Ñ(ds, de)`, so `Θ̄ ∈ ℍ` and `Φ_λ : ℍ → ℍ` is well defined."

Propositions: under the hypotheses of Lemma 4.2 (those of `lem_small`, verbatim: the standing
setting, `T > 0`, (2.3), Assumption 2.2 with the datum `ξ₀` and Assumption 2.3 with the constant
`L`), for `λ ∈ [0, 1]`, a forcing `q` of the class of (4.1) (`PredForcing` over `enlJoint`) and a
trial `Θ` with `HTuple` over `enlJoint`:

* `eq_frozenfwd`: (a) `∫_{[0, T]} ∫⁻ ‖ψ(s, Θ_s, lawP2 P Θ_s)‖ₑ² < ⊤` for `ψ ∈ {b, σ, h}`;
  (b) there is `X̄` with `FrozenForward … Θ X̄`, every path of every coordinate of `X̄` having a
  left limit at every `t ∈ (0, T]`, and `∫⁻ sup_{t ∈ [0, T]} |X̄_t|² < ⊤`; (c) any two `X̄` with
  `FrozenForward … Θ X̄` agree, coordinatewise, at every `t ∈ [0, T]` on one set of full measure.
* `eq_frozenbwd`: (a) for every `X̄` with `FrozenForward … Θ X̄`, each coordinate of
  `Ξ = λ terminalVal(X̄) + q^g + ∫_{[0, T]} (λ driverProc(Θ) + q^f)` is strongly
  `ℱ_T`-measurable and in `L²(P)`; (b) there is `Θ̄` with `FrozenStep … Θ Θ̄`; (c) for any two
  `Θ̄¹, Θ̄²` with `FrozenStep … Θ Θ̄ᵏ`, `X̄¹, X̄²` and `Ȳ¹, Ȳ²` are indistinguishable on `[0, T]`
  and `Z̄¹ − Z̄²`, `Ū¹ − Ū²` have zero energy on `[0, T]`, coordinatewise.

Readings:

* The trial and the step. `Θ ∈ ℍ` is `HTuple`, `Φ_λ` the relation `FrozenStep`: (4.7)
  (`FrozenForward`), (4.8) in each coordinate (`LinearBSDEJ`) and `Θ̄ ∈ ℍ`; all three are reviewed
  in `definitions.md`. "`Φ_λ : ℍ → ℍ` is well defined" is (b) and (c) of `eq_frozenbwd`: an image
  exists and two images are equal in `ℍ`, which identifies processes indistinguishable on
  `[0, T]` and integrands differing by zero energy.
* The jump integrand of (4.7). `h(s, Θ⁻_s(ω), ·, μ^{Θ,−}_s)` is an element of `L²(ν)` for each
  `(s, ω)`; the compensated integral integrates a function of `(ω, s, e)` that represents it, a
  class up to `dP ⊗ ds ⊗ ν`-null sets. `FrozenForward` takes such a representative `γ`
  (`∃ γ`, with `γ_s(ω, ·) = h(s, Θ⁻_s(ω), ·, μ^{Θ,−}_s)` in `L²(ν)` for almost every
  `s ∈ [0, T]`, almost surely) meeting the conditions of the integral. Existence is for some
  representative and uniqueness for any two, so the solution does not depend on the choice. The
  left limits are `tupleAt` of `leftLimProc X`, `leftLimProc Y` with `Z`, `U` unchanged, as in
  `PaperWeakSolution`. The remark that `h` may be taken at `(Θ_s, μ^Θ_s)` inside
  `dt ⊗ dP`-integrals is used by the proof (`exists_paperAdmissible` builds the representative at
  `Θ_s` and moves it to `Θ⁻_s`); it is not stated.
* The linear forms. Each coordinate of (4.7) is `LinearFSDEJ` from `ξ₀ᵢ` with drift `λ b_i + q^b_i`,
  diffusion row `λ σ_{i·} + q^σ_{i·}` and jump integrand `λ γ_i + q^h_i`, the processes along the
  trial cut to `[0, T]` (`driftProc`, `diffusionProc`, `jumpProc`): the printed six integrals
  combined by linearity of the drift, Itô and compensated integrals. The identity holds almost
  surely at each `t ∈ [0, T]`, `X̄` adapted with every path right-continuous. (4.8) is
  `LinearBSDEJ` with terminal value `λ g(X̄_T, Law(X̄_T)) + q^g_T` (`terminalVal` at `X̄`) and drift
  `λ f + q^f` along the trial (`driverProc`).
* Norms and expectations. `|σ|` is the Frobenius norm (the Euclidean norm on `ℝ^{n × d}`), `|h|`
  the norm of `L²(ν; ℝⁿ)`, `μ^Θ_s = lawP2 P Θ_s`, in the norms of Assumption 2.3.
  `𝔼 ∫_0^T |ψ|² ds` is read time-outer, `∫_{[0, T]} 𝔼 |ψ|² ds` in `[0, ∞]`, as (4.2) is
  (`eq_coeffint`); the two orders agree by Tonelli where the integrand is jointly measurable.
  `𝔼 sup_{t ≤ T} |X̄_t|²` is the lower integral of the supremum over `[0, T]` of `esq`.
* `Ξ ∈ L²(Ω, ℱ_T; ℝᵐ)` is read coordinatewise, strongly `enlJoint_T`-measurable and in `L²(P)`,
  the drift integral the Bochner integral over `[0, T]` of each path. It is asserted for every
  solution of (4.7), which by (c) of `eq_frozenfwd` are indistinguishable.
* `X̄ ∈ S²(0, T; ℝⁿ)`. `S²` is the space of càdlàg adapted processes `V` with
  `𝔼 sup_{t ≤ T} |V_t|² < ∞` (`03-main-results.tex` line 9). `FrozenForward` makes `X̄` adapted
  with every path right-continuous at every time (`LinearFSDEJ`); (b) adds that every path of
  every coordinate has a left limit at every `t ∈ (0, T]`, in the form in which `HTuple` and
  `WeakSolution` state the càdlàg paths of the `X`- and `Y`-slots of `ℍ`, and
  `𝔼 sup_{t ≤ T} |X̄_t|² < ∞`. So the `X̄` of (b) is in `S²(0, T; ℝⁿ)`, every path càdlàg on
  `[0, T]`: the existence part of "(4.7) defines a unique `X̄ ∈ S²(ℝⁿ)`" in full.
* Uniqueness in `eq_frozenfwd` is among all solutions of `FrozenForward` (adapted, right-continuous
  paths, left limits not asked), not only those in `S²`: broader than printed. The `X̄` of (b) is
  one of them, so the unique solution is the càdlàg one up to indistinguishability.
* Not stated: that the integrands are progressively measurable and the jump integrand predictable
  (lines 281–282); `FrozenForward` asks the integrands' joint and progressive measurability, the
  jump integrand marked progressively measurable (what the compensated integral needs), not
  predictable. The objects of the backward construction, `M_t = 𝔼[Ξ | ℱ_t]`, its representation
  and `M ∈ S²` (lines 292–302), are steps of the proof; the uniqueness of `Z̄, Ū` in the
  representation is subsumed in (c) of `eq_frozenbwd`.

Proofs: (4.7)(a) is (4.2) (`Dissertation.Acceptance.A.eq_coeffint`) at the trial, whose right side
is finite by the `𝔼 sup` bounds of `X`, `Y`, the energies of `Z`, `U`
(`PaperWeakTuple.setLIntegral_lintegral_channels_lt_top`) and Assumption 2.2. (b): along the trial
the integrals of (1.1) exist with a representative `γ` at the predictable tuple
(`PaperWeakTuple.exists_paperAdmissible`, (2.5) from (2.3) by `JointBorel.coeffRegular`),
`λ Ψ(Θ) + q` is a forcing (`PaperAdmissible.forcing`, `Forcing.smul`, `Forcing.add`), and the
linear forward equation has a solution (`Forcing.exists_linearFSDEJ`); set to `0` off a null set
outside which its paths have left limits, it still solves (4.7) and every path is càdlàg
(`LinearFSDEJ.ae_leftLim`, `LinearFSDEJ.indicator`; `FrozenForward.exists_leftLim`), and it is
in `S²` (`lintegral_biSup_esq_lt_top_of_linearFSDEJ`, Lemma 4.1). (c): two representatives give
forward integrands that agree for the marked energy measure (`ae_forcedJump_eq_of_rep`), so the
compensated integrals agree almost surely at each time and the right-continuous solutions are
indistinguishable (`LinearFSDEJ.ae_forall_Icc_eq`). (4.8)(a): (4.3)
(`lintegral_esq_terminalVal_le`) with (2.3) for the measurability of `g`, and the drift integral
of the forcing (`ProgressivelyMeasurable.stronglyMeasurable_setIntegral`,
`memLp_two_setIntegral`). (b): the càdlàg solution of (4.7)(b) (`FrozenForward.exists_leftLim`);
the terminal representation of `enlJoint` (`hasTerminalRep_enlJoint`,
`HasTerminalRep.exists_linearBSDEJ`); predictable versions of `Z̄`,
`Ū` (`LinearBSDEJ.exists_predictable`); `Ȳ` set to `0` off a null set (`LinearBSDEJ.indicator`);
the `S²` bounds of Lemma 4.1. (c): the forward coordinates by (4.7)(c), so the terminal values
agree almost surely, and Lemma 4.1 for the difference of the backward coordinates, whose data
vanish (`LinearBSDEJ.eq_of_ae_eq_terminal`).

Witness: `Dissertation.Acceptance.A.frozen_hypotheses`: at the instance of `thm_cwp_hypotheses`
(Example 5.1(i), `n = m = d = 1`, `T = 1`, `ν = δ₀`, `L = 1`, datum `0`), (2.3) and
Assumptions 2.2–2.3, `λ = 1`, the zero forcing in the class of (4.1), and two distinct trials of
`ℍ`: the zero tuple and the constant tuple `(X, Y, Z, U) = (1, 1, 0, 0)` (`hTuple_const`).

Verdict: faithful (both true as printed; the uniqueness of (4.7) broader than printed).

<!-- spec-review: Dissertation.PaperSpec.A.eq_frozenfwd ed839d34f480cba18303299f6df7eded by=claude-author source=A:eq:frozenfwd@4e585ce7f397c971a8de4acdb6d81d0be45f342db82a0166e9d3d3578fcb0504 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.eq_frozenfwd--claude-auditor--2026-10-20T02_03_32Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_frozenfwd ed839d34f480cba18303299f6df7eded by=claude-auditor source=A:eq:frozenfwd@4e585ce7f397c971a8de4acdb6d81d0be45f342db82a0166e9d3d3578fcb0504 -->
<!-- spec-review: Dissertation.PaperSpec.A.eq_frozenbwd ed839d34f480cba178b77fba8e33d01f by=claude-author source=A:eq:frozenbwd@17276cb1f64eca4139ee188be1e81dc912dab34d5bd02a5596d5d4321fdb9764 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.eq_frozenbwd--claude-auditor--2026-10-20T00_44_30Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_frozenbwd ed839d34f480cba178b77fba8e33d01f by=claude-auditor source=A:eq:frozenbwd@17276cb1f64eca4139ee188be1e81dc912dab34d5bd02a5596d5d4321fdb9764 -->

## (4.9), Step 1 of the proof of Lemma 4.2: `Dissertation.PaperSpec.A.eq_coeffdiff`

Manuscript (proof of Lemma `lem:small`, lines 312–348): "Take `Θ¹, Θ² ∈ ℍ`, write
`Θ̄ᵏ = Φ_λ(Θᵏ)`, and set `δψ_s := ψ(s, Θ¹_s, μ^{Θ¹}_s) − ψ(s, Θ²_s, μ^{Θ²}_s)`
(`ψ ∈ {b, σ, h, f}`), `δX := X¹ − X²`, `δX̄ := X̄¹ − X̄²`, and likewise for the remaining
components of `Θ¹ − Θ²` and of `Θ̄¹ − Θ̄²` […]. *Step 1: the coefficient differences.* Write
`S_s := |δb_s| + |δσ_s|_F + ‖δh_s‖_{L²(ν)} + |δf_s|`. Assumption 2.3, applied to the diagonal
inputs `(Θ¹_s, μ^{Θ¹}_s)` and `(Θ²_s, μ^{Θ²}_s)`, gives
`S_s ≤ L(|δX_s| + |δY_s| + |δZ_s|_F + ‖δU_s‖_{L²(ν)} + W₂(μ^{Θ¹}_s, μ^{Θ²}_s))`. Squaring,
using Cauchy–Schwarz in `ℝ⁵`, taking expectations, and bounding the deterministic Wasserstein
term by (2.8) give `𝔼 S_s² ≤ 10L² 𝔼[|δX_s|² + |δY_s|² + |δZ_s|²_F + ‖δU_s‖²]`. Integrating in
`s` and dominating the `X`- and `Y`-slots by their suprema, (4.9)
`𝔼 ∫_0^T S_s² ds ≤ 10L² 𝔼 ∫_0^T (|δX_s|² + |δY_s|² + |δZ_s|²_F + ‖δU_s‖²) ds
≤ 10L² (T 𝔼 sup_{t ≤ T} |δX_t|² + T 𝔼 sup_{t ≤ T} |δY_t|²
+ 𝔼 ∫_0^T (|δZ_s|²_F + ‖δU_s‖²) ds) ≤ L⋆² ‖Θ¹ − Θ²‖²_ℍ`, `L⋆² := 10L² max{T, 1}`."

Proposition: under the hypotheses of Lemma 4.2 (as for (4.7)), for two trials `Θ¹, Θ²` with
`HTuple` over `enlJoint`, the three links, in `[0, ∞]`:
`∫_{[0, T]} ∫⁻ coeffDiffNorm(Θ¹, Θ²)_s² ≤ ofReal(10L²) ∫_{[0, T]} ∫⁻ (|δX_s|² + |δY_s|²
+ ∑_k |δZ_{k,s}|² + ∑_k ‖δU_{k,s}‖²_{L²(ν)})
≤ ofReal(10L²) (ofReal T ∫⁻ sup_{[0, T]} |δX|² + ofReal T ∫⁻ sup_{[0, T]} |δY|²
+ (∑_{k, j} energy(δZ_{kj}) + ∑_k markedEnergy(δU_k)))
≤ ofReal(10L² max{T, 1}) supSize(δX, δY, δZ, δU)`.

Readings:

* `S_s` is `coeffDiffNorm` (reviewed in `definitions.md`) at the tuples `Θᵏ_s = tupleAt` of the
  trials and their laws `lawP2 P Θᵏ_s`; `|δσ|_F` is the Euclidean norm on `ℝ^{n × d}` and
  `‖δh‖` the norm of `L²(ν; ℝⁿ)`. `|δZ_s|²_F = ∑_k |δZ_{k,s}|²`, the rows of `Z` being its
  coordinates; `‖δU_s‖² = ∑_k ‖δU_{k,s}‖²_{L²(ν)}`.
* `𝔼 ∫_0^T` is read time-outer, `∫_{[0, T]} 𝔼`, in `[0, ∞]`, as in (4.2); the `Z`- and `U`-slots
  of the second link are the energies, `𝔼 ∫_0^T` sample-outer, which agree with the time-outer
  form by Tonelli since `Z`, `U` are predictable.
* `‖Θ¹ − Θ²‖²_ℍ` is `supSize` of the difference, `𝔼 sup |δX|² + 𝔼 sup |δY|²` plus the energies of
  `δZ` and `δU`, the squared norm of `ℍ` of §3 (`supSize`, reviewed with Lemma 4.3).
* The constants are the printed ones, `10L²` and `L⋆² = 10L² max{T, 1}`, explicit.
* The display before (4.9), `𝔼 S_s² ≤ 10L² 𝔼[…]` at almost every `s`, is the step the first link
  integrates (`LipInteriorAt.lintegral_sq_coeffDiff_le`); it is not stated on its own. The
  frozen images `Θ̄ᵏ` do not enter (4.9) and are not assumed.
* The proof uses Assumption 2.3 only; (2.3) and Assumption 2.2 are kept as the enclosing statement
  has them.

Proof: at almost every `s ∈ [0, T]` the two trials are diagonal inputs (`Θᵏ_s` strongly
`ℱ_s`-measurable and square integrable, `PaperWeakTuple.stronglyMeasurable_tupleAt`,
`ae_memLp_tupleAt`), and the interior bound of Assumption 2.3 at `s`, squared with
`(a + b + c + e + W)² ≤ 5(a² + b² + c² + e² + W²)` and the coupling bound (2.8) for the
Hilbert-norm `W₂`, gives `𝔼 S_s² ≤ 10L² 𝔼 |Θ¹_s − Θ²_s|²_H`
(`LipInteriorAt.lintegral_sq_coeffDiff_le`, `sq_le_five_mul_sq_add`), bounded by the coordinates
(`ofReal_channelSq_tupleAt_le`). The second link replaces the trials by their progressive
extensions, equal on `[0, T]` (`PaperWeakTuple.exists_progTuple`), and reads the time integral by
Tonelli (`setLIntegral_lintegral_coords_le`). The third is `T ≤ max{T, 1}` and `1 ≤ max{T, 1}`.

Witness: `Dissertation.Acceptance.A.frozen_hypotheses`, with two distinct trials of `ℍ`: the zero
tuple and the constant tuple `(X, Y, Z, U) = (1, 1, 0, 0)` (`hTuple_const`). Their difference has
`δX = δY = −1` and `δZ = δU = 0`, so `‖Θ¹ − Θ²‖²_ℍ = 2`; by hand, for the system of
Example 5.1(i) with `β₁ = β₂ = 1` (`b = −y`, `σ = −z`, `h = −u`, `f = x`), `δb = e₁`, `δf = −e₁`
and `δσ = δh = 0`, so `S_s = 2`, and the three links read `4 ≤ 20 ≤ 20 ≤ 20`.

Verdict: faithful.

<!-- spec-review: Dissertation.PaperSpec.A.eq_coeffdiff ed839d34f480cba1b363f744d12fe99d by=claude-author source=A:eq:coeffdiff@a02482f342dcea543d3e2b9f5367fcfcc00191aef184c33ffa0477616f3b3bb3 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.eq_coeffdiff--claude-auditor--2026-10-20T00_44_30Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_coeffdiff ed839d34f480cba1b363f744d12fe99d by=claude-auditor source=A:eq:coeffdiff@a02482f342dcea543d3e2b9f5367fcfcc00191aef184c33ffa0477616f3b3bb3 -->

## The bound before (4.9) at almost every time, Step 1 of the proof of Lemma 4.2: `Dissertation.PaperSpec.A.eq_coeffdiff_ae`

Manuscript (proof of Lemma `lem:small`, Step 1, lines 325–337), with the objects of lines 312–323
quoted in the section of (4.9): "Write `S_s := |δb_s| + |δσ_s|_F + ‖δh_s‖_{L²(ν)} + |δf_s|`.
Assumption 2.3, applied to the diagonal inputs `(Θ¹_s, μ^{Θ¹}_s)` and `(Θ²_s, μ^{Θ²}_s)`, gives
`S_s ≤ L(|δX_s| + |δY_s| + |δZ_s|_F + ‖δU_s‖_{L²(ν)} + W₂(μ^{Θ¹}_s, μ^{Θ²}_s))`. Squaring,
using Cauchy–Schwarz in `ℝ⁵`, taking expectations, and bounding the deterministic Wasserstein
term by (2.8) give `𝔼 S_s² ≤ 10L² 𝔼[|δX_s|² + |δY_s|² + |δZ_s|²_F + ‖δU_s‖²]`." Lines 333–337 lie
before the pinned region of `A:eq:coeffdiff` (lines 339–348); the next sentence integrates the
bound in `s`.

Proposition: under the hypotheses of Lemma 4.2 (`T > 0`, (2.3), Assumptions 2.2–2.3 with `L` and
the datum `ξ₀`), for two trials `Θ¹, Θ²` with `HTuple` over `enlJoint`, for almost every
`s ∈ [0, T]`, `∫⁻ coeffDiffNorm(Θ¹, Θ²)_s² dP ≤ ofReal(10L²) ∫⁻ (|δX_s|² + |δY_s|²
+ ∑_k |δZ_{k,s}|² + ∑_k ∫⁻ |δU_{k,s}(e)|² ν(de)) dP`.

Readings:

* `S_s` is `coeffDiffNorm` at the tuples `Θᵏ_s` and their laws, as in (4.9) (reviewed in
  `definitions.md` and with (4.9)); the right side is `|Θ¹_s − Θ²_s|²_H` written by coordinates,
  as there. The expectations are lower integrals in `[0, ∞]`.
* The time: the step applies Assumption 2.3 to "the diagonal inputs `(Θᵏ_s, μ^{Θᵏ}_s)`", which
  `Θᵏ_s` is at almost every `s` (square integrable and `ℱ_s`-measurable); the bound is read at
  almost every `s ∈ [0, T]` (Lebesgue), the times at which the step makes sense, and is what the
  first link of (4.9) integrates. The constant `10L²` is the printed one.
* The hypotheses are those of the enclosing statement, as for (4.9); the step uses Assumption 2.3
  alone. The frozen images do not enter.
* The section of (4.9) records this bound as not stated on its own; it is stated here.

Proof: at almost every `s ∈ [0, T]` the trials are diagonal inputs
(`PaperWeakTuple.stronglyMeasurable_tupleAt`, `ae_memLp_tupleAt`), and the interior bound of
Assumption 2.3 at `s` with the coupling bound gives `𝔼 S_s² ≤ 10L² 𝔼|Θ¹_s − Θ²_s|²_H`
(`LipInteriorAt.lintegral_sq_coeffDiff_le`), bounded by the coordinates (`tupleAt_sub`,
`ofReal_channelSq_tupleAt_le`).

Witness: `Dissertation.Acceptance.A.frozen_pair_window_hypotheses`, as for the forward difference
before (4.10): at the system of Example 5.1(i) with `β₁ = β₂ = 1`, `σ_c = h_c = 0` (`b = −y`,
`σ = −z`, `h = −u`, `f = x`) and `L = 1`, the trials the zero tuple and
`(1, 1, 1_{(0, 1]}, 1_{(0, 1]})`, whose coefficient differences `δb = 1_{[0, 1]}`,
`δσ = 1_{(0, 1]}` and `δh = 1_{(0, 1]}` have energy `1` each (stated). By hand `δf = −1`, so
`S_s = 4` on `(0, 1]`, and the bound reads `16 ≤ 10 · (1 + 1 + 1 + 1) = 40` there.

Verdict: faithful.

<!-- spec-review: Dissertation.PaperSpec.A.eq_coeffdiff_ae ed839d34f480cba122e3ae64778e3109 by=claude-author source=A:eq:coeffdiff@a02482f342dcea543d3e2b9f5367fcfcc00191aef184c33ffa0477616f3b3bb3 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.eq_coeffdiff_ae--claude-auditor--2026-10-20T15_31_29Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_coeffdiff_ae ed839d34f480cba122e3ae64778e3109 by=claude-auditor source=A:eq:coeffdiff@a02482f342dcea543d3e2b9f5367fcfcc00191aef184c33ffa0477616f3b3bb3 -->

## The forward difference before (4.10), Step 2 of the proof of Lemma 4.2: `Dissertation.PaperSpec.A.eq_fwddiff_identity`

Manuscript (proof of Lemma `lem:small`, Step 2, lines 350–355), with the objects of lines 312–323
quoted in the section of (4.10): "*Step 2: the forward difference.* Taking the difference of (4.7)
at `Θ¹` and `Θ²`, `δX̄_t = λ ∫_0^t δb_s ds + λ ∫_0^t δσ_s dW_s + λ ∫_0^t ∫_E δh_s(e) Ñ(ds, de)`."
The display lies before the pinned region of `A:eq:fwddiff` (lines 357–372); it is that claim's
first clause, as its scope note records.

Proposition: under the hypotheses and with the objects of `eq_fwddiff`, verbatim (Lemma 4.2's
`T > 0`, (2.3), Assumption 2.2 with the datum `ξ₀`, Assumption 2.3 with `L`; `λ ∈ [0, 1]`, a
forcing `q` with `PredForcing` over `enlJoint`, trials `Θ¹, Θ²` with `HTuple`, and
`FrozenStep … Θᵏ Θ̄ᵏ` with the same `λ`, `ξ₀`, `q`), but with no constant: (a) `δσ` and `δh`
meet the conditions of the Itô and the compensated integral (the proof arguments of
`stochasticIntegral`, as in `eq_fwddiff`); (b) for every `i`, almost every path `s ↦ δb_i(s)` is
integrable on `[0, T]`; (c) for every `i` and every `t ∈ [0, T]`, almost surely,
`δX̄_{i,t} = λ ∫_{[0, t]} δb_i(s) ds + λ (∫ δσ_i dW)_t + λ (∫∫ δh_i dÑ)_t`, with the library's
integrals; (d) for every `Mσ` whose coordinates are versions on `[0, T]` of `∫ δσ_i dW` with
almost every path right-continuous on `[0, T)`, almost surely, at every `t ∈ [0, T]` at once, the
same identity with `Mσ_{i,t}` in place of the Brownian integral.

Readings:

* The objects and the coefficient differences are those of the section of (4.10): `δψ_s` at
  `(Θᵏ_s, μ^{Θᵏ}_s)` (line 316), `δb, δσ` the differences of `driftProc` and `diffusionProc`, and
  `δh` that of the canonical representative `coeffJump` at the tuple. (4.7) evaluates `h` at the
  left limits `(Θ⁻_s, μ^{Θ,−}_s)` through a representative (`FrozenForward`); the remark after
  (4.7) (lines 272–275) makes the two forms interchangeable inside the `dt ⊗ dP`-integrals, which
  is what turns "the difference of (4.7)" into an identity with the passage's `δh_s`. The
  proposition takes `δh_s` at the tuple; the proof makes the replacement.
* "Taking the difference of (4.7) at `Θ¹` and `Θ²`": the common datum `ξ₀` and the fixed forcing
  `q` cancel (lines 322–323), so the identity has neither; `λ` stands outside the three
  integrals, as printed.
* An identity of processes. The library's Brownian integral is defined time by time, up to
  modification, so (c) states the identity at each time almost surely, the form in which (4.7)
  itself is stated (`FrozenForward`, `LinearFSDEJ`). (d) is its pathwise form, with any version of
  the Brownian integral right-continuous on `[0, T)` (one with càdlàg paths exists by
  `eq_fwddiff` (b)): the form in which the identity enters the supremum of the first link of
  (4.10). The compensated integral has càdlàg paths by construction and appears as it is.
* The drift integral is the Bochner integral over `[0, t]`; (b) states that it is not read at a
  junk value: almost every path of `δb` is integrable on `[0, T]`.
* The hypotheses are those of Lemma 4.2, verbatim, as for (4.10); the step uses (2.3) and
  Assumptions 2.2–2.3 (the integrals along the trials) and the frozen steps.

Proof: `frozenStep_fwd_sub` (the first part of the proof of (4.10), extracted): along each trial
the integrals of (1.1) exist with `coeffJump` (`PaperWeakTuple.paperAdmissible_coeffJump`), (4.7)
holds with the jump integrand `λ coeffJump + q^h` (`ae_forcedJump_eq_of_rep`,
`LinearFSDEJ.congr_jump`), and the difference is the linear forward equation from `0` with
integrands `λ δb, λ δσ, λ δh` (`LinearFSDEJ.sub`). Its equation at each time, with the scaling of
the two integrals (`multidimStochasticIntegral_const_mul_ae`, `compensatedIntegral_const_mul_ae`)
and of the Bochner integral, is (c); (b) is `ae_mem_integrablePaths`. For (d), both sides are
right-continuous on `[0, T)` almost surely (the paths of `δX̄`, the continuous drift primitive
`driftLeg`, `Mσ` and the càdlàg compensated integral) and agree at each time almost surely, so
they agree at every time of `[0, T]` on one set of full measure
(`ae_forall_Icc_eq_of_ae_rightCont`).

Representation choices, as the blind audit listed them (each harmless): (1) `δh` is the
difference of `coeffJump`, a jointly measurable representative of `h(s, Θᵏ_s, ·, μᵏ_s)`, at the
tuple `Θ_s` rather than at `Θ⁻_s`, which is the paper's own definition of `δψ` at line 316; the
two agree `dt ⊗ dP ⊗ ν`-almost everywhere (Lemma A.1), so their compensated integrals agree
almost surely. (2) "Meets the conditions of the integrals" is the library's class (jointly
measurable, progressively or marked progressively measurable, finite energy), whose integrals
coincide with those of the paper's predictable representatives for integrands equal almost
everywhere. (3) The law flow is `lawP2 P Θ_s` at every `s`, the Dirac mass at `0` on the null set
of times where `Θ_s` is not square integrable: one Borel representative of `Law(Θ_s)`. (4) The
simultaneous-in-`t` form quantifies over the right-continuous versions of the Brownian integral,
which the library defines time by time, and uses the library's càdlàg compensated integral: the
paper's convention for identities of càdlàg processes. (5) `Θ̄ᵏ` is the full frozen step
`FrozenStep` (`Φ_λ(Θᵏ)`), as in the paper; the processes are coordinatewise, and `Z`, `U` vanish
off `[0, T]`.

Witness: `Dissertation.Acceptance.A.frozen_pair_window_hypotheses`, as for (4.10): the instance
of `frozen_hypotheses` (a Lévy driver with `d = 1`, `ν = δ₀` on `ℝ`, `𝒢₀ = ⊥`, `n = m = 1`,
`T = 1`, the system of Example 5.1(i) with `β₁ = β₂ = 1`, `σ_c = h_c = 0`, so `b = −y`,
`σ = −z`, `h = −u`, datum `0`, `λ = 1`, the zero forcing) with the trials the zero tuple and
`(X, Y, Z, U) = (1, 1, 1_{(0, 1]}, 1_{(0, 1]})` (`hTuple_const_window`) and their frozen steps. It
makes all three coefficient differences nonzero: `δb = 1_{[0, 1]}`, `δσ = 1_{(0, 1]}` and
`δh = 1_{(0, 1]}` (through `coeffJump`, at the mark `0`) each have energy `1` on `[0, 1]`
(stated). By hand `δX̄_t = t + ∫_0^t 1_{(0, 1]} dW + ∫_0^t ∫ 1_{(0, 1]} Ñ(ds, de)`, so the drift,
Itô and compensated terms of the identity are all present. The former witness,
`frozen_pair_hypotheses` (trials `0` and `(1, 1, 0, 0)`), made only `δb` nonzero.

Verdict: faithful with representation choices (those listed above). (d) adds the pathwise form,
which follows from (c) and the regularity of the paths.

<!-- spec-review: Dissertation.PaperSpec.A.eq_fwddiff_identity ed839d34f480cba1cdc19be62d7635bf by=claude-author source=A:eq:fwddiff@77e48f26f92871ddcb580b9647738e2ba0b66be8eedc87a40ecaffa53cf9e98c -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.eq_fwddiff_identity--claude-auditor--2026-10-20T10_33_47Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_fwddiff_identity ed839d34f480cba1cdc19be62d7635bf by=claude-auditor source=A:eq:fwddiff@77e48f26f92871ddcb580b9647738e2ba0b66be8eedc87a40ecaffa53cf9e98c -->

## (4.10), Step 2 of the proof of Lemma 4.2: `Dissertation.PaperSpec.A.eq_fwddiff`

Manuscript (proof of Lemma `lem:small`, Step 2, lines 350–374), with the objects of lines 312–323
("Take `Θ¹, Θ² ∈ ℍ`, write `Θ̄ᵏ = Φ_λ(Θᵏ)`, and set
`δψ_s := ψ(s, Θ¹_s, μ^{Θ¹}_s) − ψ(s, Θ²_s, μ^{Θ²}_s)` (`ψ ∈ {b, σ, h, f}`), `δX := X¹ − X²`,
`δX̄ := X̄¹ − X̄²` […]; the common initial datum `ξ₀` and the fixed forcing `q` cancel in every
difference"): "*Step 2: the forward difference.* Taking the difference of (4.7) at `Θ¹` and `Θ²`,
`δX̄_t = λ ∫_0^t δb_s ds + λ ∫_0^t δσ_s dW_s + λ ∫_0^t ∫_E δh_s(e) Ñ(ds, de)`. Squaring, taking
the supremum in `t`, and taking expectations, (4.10)
`𝔼 sup_{t ≤ T} |δX̄_t|² ≤ 3λ² [𝔼 (∫_0^T |δb_s| ds)² + 𝔼 sup_{t ≤ T} |∫_0^t δσ_s dW_s|²
+ 𝔼 sup_{t ≤ T} |∫_0^t ∫_E δh_s(e) Ñ(ds, de)|²]
≤ 3λ² [T 𝔼 ∫_0^T |δb_s|² ds + c_BDG 𝔼 ∫_0^T |δσ_s|²_F ds + c_BDG 𝔼 ∫_0^T ‖δh_s‖²_{L²(ν)} ds]
≤ 3λ² max{T, c_BDG} 𝔼 ∫_0^T (|δb_s|² + |δσ_s|²_F + ‖δh_s‖²_{L²(ν)}) ds
≤ 3λ² max{T, c_BDG} 𝔼 ∫_0^T S_s² ds ≤ C_X λ² ‖Θ¹ − Θ²‖²_ℍ`, `C_X := 3 max{T, c_BDG} L⋆²`, the
jump term by (2.1), the next step since the summands of `S_s` are non-negative, and the last by
(4.9)." The pinned region is the display, lines 357–372; `S_s` and `L⋆² = 10L² max{T, 1}` are
those of (4.9).

Proposition: `∃ c₀ > 0` such that for every `c ≥ c₀`, in the standing setting, under the
hypotheses of Lemma 4.2 (those of `lem_small`, verbatim: `T > 0`, (2.3), Assumption 2.2 with the
datum `ξ₀` and Assumption 2.3 with the constant `L`), for `λ ∈ [0, 1]`, a forcing `q` of the
class of (4.1) (`PredForcing` over `enlJoint`), two trials `Θ¹, Θ²` with `HTuple` over `enlJoint`
and `Θ̄¹, Θ̄²` with `FrozenStep … Θᵏ Θ̄ᵏ` (the same `λ`, `ξ₀` and `q`), and with
`δb_i = driftProc(Θ¹)_i − driftProc(Θ²)_i`, `δσ_{ij} = diffusionProc(Θ¹)_{ij} −
diffusionProc(Θ²)_{ij}`, `δh_i = coeffJump(Θ¹)_i − coeffJump(Θ²)_i`: (a) `δσ` and `δh` meet the
conditions of the Itô and the compensated integral (the proof arguments of `stochasticIntegral`
exist); (b) there is `Mσ` whose coordinates are versions on `[0, T]` of `∫ δσ_i dW`, almost every
path right-continuous on `[0, T)` with left limits on `(0, T]`; (c) for every such `Mσ`,
`∫⁻ sup_{[0, T]} |δX̄|² ≤ ofReal(3λ²) (∫⁻ (∫_{[0, T]} ‖(δb_i(s))_i‖ₑ ds)²
+ ∫⁻ sup_{[0, T]} |Mσ|² + ∫⁻ sup_{[0, T]} |(∫∫ δh_i dÑ)_i|²)
≤ ofReal(3λ²) (ofReal T ∑_i energy(δb_i) + ofReal c ∑_{i, j} energy(δσ_{ij})
+ ofReal c ∑_i markedEnergy(δh_i))`; and (d) the remaining links
`… ≤ ofReal(3λ² max{T, c}) (∑_i energy(δb_i) + ∑_{i, j} energy(δσ_{ij}) + ∑_i markedEnergy(δh_i))
≤ ofReal(3λ² max{T, c}) ∫_{[0, T]} ∫⁻ coeffDiffNorm(Θ¹, Θ²)_s²
≤ ofReal(3 max{T, c} (10L² max{T, 1}) λ²) supSize(Θ¹ − Θ²)`.

Readings:

* The objects. `Θ ∈ ℍ` is `HTuple` and `Θ̄ᵏ = Φ_λ(Θᵏ)` is `FrozenStep` (both reviewed in
  `definitions.md`); by (4.8) two images of one trial are equal in `ℍ`, so the statement for any
  images is the statement for `Φ_λ`. `δX̄` is `X̄¹ − X̄²`, coordinatewise.
* The coefficient differences. The passage defines `δψ_s` at `(Θᵏ_s, μ^{Θᵏ}_s)` (line 316). On
  `[0, T]` the drift and diffusion processes are the coordinates of `b` and `σ` along the tuple and
  its law (`driftProc_of_mem`), and `coeffJump` at the tuple is the canonical representative of
  `h(s, Θ_s, ·, μ_s)` in `L²(ν; ℝⁿ)` at every `s ∈ [0, T]` (`coeffJump_ae_eq`; `coeffJump` is
  reviewed in `definitions.md`); all three vanish off `[0, T]`. So `|δb_s|` is the Euclidean
  norm of `(δb_i(s))_i`, `𝔼 ∫_0^T |δb_s|² ds = ∑_i energy(δb_i)`,
  `𝔼 ∫_0^T |δσ_s|²_F ds = ∑_{i, j} energy(δσ_{ij})` and
  `𝔼 ∫_0^T ‖δh_s‖²_{L²(ν)} ds = ∑_i markedEnergy(δh_i)`.
* The jump integrand of the difference. (4.7) evaluates `h` at `(Θ⁻_s, μ^{Θ,−}_s)` through a
  representative (`FrozenForward`), while the difference displayed at line 353 has `δh_s`, defined
  at `(Θ_s, μ^Θ_s)`. The paper's remark after (4.7) (lines 272–275: the two agree outside a
  `dt ⊗ dP`-null set by Lemma A.1) is what makes the difference of the two forward equations an
  equation with `δh_s`: integrands agreeing for the marked energy measure have almost surely
  equal compensated integrals at each time. The proposition takes the passage's `δh_s` at the
  tuple; the proof makes the replacement.
* The two stochastic suprema. The library's Brownian integral is defined time by time, so
  `𝔼 sup_{t ≤ T} |∫_0^t δσ_s dW_s|²` is read through a version with regular paths, as in
  `WeakForcedSolution`: (b) asserts that a càdlàg version exists, and (c) holds for every version
  almost every path of which is right-continuous on `[0, T)` with left limits on `(0, T]` (any
  two are indistinguishable on `[0, T]`, so the value does not depend on the choice). The
  compensated integral has almost surely càdlàg paths by construction and is used as it is. The
  integrals take measurability, progressive measurability and finite energy on every horizon as
  arguments, so (a) asserts them, as `eq_dX` does.
* The constant `c_BDG`. The paper fixes one universal constant `c_BDG`, valid at `p = 1` and at
  `p = 2`, Doob's inequality giving `4` at `p = 2` (lines 30–33). The proposition chooses `c₀ > 0`
  first and asserts the chain for every value `c ≥ c₀` of the constant, so it holds for the
  paper's `c_BDG` whenever that is at least `c₀`; it holds with `c₀ = 4`. Each of (4.10), (4.12)
  and (4.13) chooses its own `c₀`; those of (4.12) and (4.13) are chosen at least that of (4.10)
  (and of (4.12)), so one value of `c_BDG` at least the largest serves the three, and all the
  bounds increase with `c`.
* The constants are the printed ones, explicit: `3λ²`, `max{T, c}`, and
  `C_X = 3 max{T, c} L⋆²` with `L⋆² = 10L² max{T, 1}`; `C_X` depends on `T, L, c_BDG` only, as
  line 442 states.
* Expectations are lower integrals in `[0, ∞]`. `𝔼 (∫_0^T |δb_s| ds)²` is `∫⁻` of the square of
  the lower integral over `[0, T]` of `‖(δb_i(s))_i‖ₑ`; each `𝔼 sup_{t ≤ T}` is `∫⁻` of the
  supremum over `[0, T]` of `esq`. The `𝔼 ∫` of the second and third links are the energies,
  sample-outer; `𝔼 ∫_0^T S_s² ds` is read time-outer, `∫_{[0, T]} 𝔼`, which is the left side of
  `eq_coeffdiff`, so that the last link is (4.9) (the two orders agree by Tonelli where the
  integrand is jointly measurable; the proof of the fourth link swaps them for the coordinate
  processes).
* The justifications ("the jump term by (2.1)", the compensation formula, which identifies the
  expected quadratic variation of the compensated integral with `𝔼 ∫_0^T ‖δh_s‖² ds`; "the next
  step since the summands of `S_s` are non-negative"; "the last by (4.9)") are steps of the
  proof, not stated. The difference equation displayed before (4.10) is the claim's clause
  `eq_fwddiff_identity`, reviewed in the section before this one; here it is a step of the proof
  of the first link.
* The hypotheses are those of Lemma 4.2, verbatim; the step uses (2.3), Assumption 2.2 (finite
  energies of the coefficient processes) and Assumption 2.3.

Proof: along each trial the integrals of (1.1) exist with `coeffJump`, which also represents the
jump coefficient at the predictable tuple (`PaperWeakTuple.paperAdmissible_coeffJump`), so (4.7)
holds with the jump integrand `λ coeffJump + q^h` (`ae_forcedJump_eq_of_rep`,
`LinearFSDEJ.congr_jump`); the difference is the linear forward equation from `0` with integrands
`λ δb, λ δσ, λ δh` (`LinearFSDEJ.sub`). On one set of full measure
`δX̄_t = λ (∫_0^t δb_s ds + M_t + N_t)` at every `t ∈ [0, T]`, for càdlàg versions `M, N` of the
two legs (scaling of the integrals, `ae_forall_Icc_eq_of_rightContinuous`), which with
`|a + b + c|² ≤ 3(|a|² + |b|² + |c|²)` and `|∫_0^t δb| ≤ ∫_0^T |δb|` (`eval_integral_piLp`) gives
the first link (`LinearFSDEJ.lintegral_biSup_esq_le_legs`). The second is Cauchy–Schwarz
(`lintegral_sq_lintegral_toLp_le`) and Doob's inequality with the isometries, the multidimensional
one through a cross witness (`lintegral_biSup_esq_brownian_le`,
`lintegral_biSup_esq_compensated_le`), with `4 ≤ c`; the third is `T, c ≤ max{T, c}`; the fourth
reads the energies through the sample energies (`lintegral_sampleEnergy_add`) and bounds them at
each `s` by `S_s²` (`sum_energy_le_coeffDiffNorm`, with `b_sub_eq_toLp`, `σ_sub_eq_toLp`,
`coeFn_h_sub`); the fifth is (4.9) (`eq_coeffdiff`).

Witness: `Dissertation.Acceptance.A.frozen_pair_window_hypotheses`: at the instance of
`frozen_hypotheses` (Example 5.1(i) with `β₁ = β₂ = 1`, `n = m = d = 1`, `T = 1`, `ν = δ₀`,
`L = 1`, datum `0`, `λ = 1`, the zero forcing), the two distinct trials of `ℍ`, the zero tuple and
`(X, Y, Z, U) = (1, 1, 1_{(0, 1]}, 1_{(0, 1]})` (`hTuple_const_window`), with frozen steps from
(4.8). It makes the three forward coefficient differences nonzero: `δb = 1_{[0, 1]}`,
`δσ = 1_{(0, 1]}` and `δh = 1_{(0, 1]}` (through `coeffJump`) each have energy `1` on `[0, 1]`
(stated), so each of the three terms on the right of the first link of (4.10) is nonzero (by hand
`δX̄_t = t + ∫_0^t 1_{(0, 1]} dW + ∫_0^t ∫ 1_{(0, 1]} Ñ(ds, de)`). The former witness,
`frozen_pair_hypotheses` (the trials `0` and `(1, 1, 0, 0)`; by hand `δX̄_t = t`, `δb = 1`,
`δσ = δh = 0`, `δf = −1`, `S = 2`, `‖Θ¹ − Θ²‖²_ℍ = 2`, and the chain reads
`1 ≤ 3 ≤ 3 ≤ 3c ≤ 12c ≤ 60c`), made only the drift term nonzero.

Verdict: faithful.

<!-- spec-review: Dissertation.PaperSpec.A.eq_fwddiff ed839d34f480cba1898e8661a670d8b9 by=claude-author source=A:eq:fwddiff@77e48f26f92871ddcb580b9647738e2ba0b66be8eedc87a40ecaffa53cf9e98c -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.eq_fwddiff--claude-auditor--2026-10-20T04_27_24Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_fwddiff ed839d34f480cba1898e8661a670d8b9 by=claude-auditor source=A:eq:fwddiff@77e48f26f92871ddcb580b9647738e2ba0b66be8eedc87a40ecaffa53cf9e98c -->

## (4.11), Step 3 of the proof of Lemma 4.2: `Dissertation.PaperSpec.A.eq_terdiff`

Manuscript (proof of Lemma `lem:small`, Step 3, lines 376–389): "Put
`δξ̄ := λ[g(X̄¹_T, Law(X̄¹_T)) − g(X̄²_T, Law(X̄²_T))]`. Then
`𝔼|δξ̄|² ≤ λ² L² 𝔼(|δX̄_T| + W₂(Law(X̄¹_T), Law(X̄²_T)))²
≤ 2λ² L² (𝔼|δX̄_T|² + W₂(Law(X̄¹_T), Law(X̄²_T))²) ≤ C_g λ² 𝔼|δX̄_T|²`, `C_g := 4L²`, the first
step by (2.6) and the last by (2.9)." Here `X̄^k = Φ_λ(Θ^k)` is the forward component of the
frozen step of a trial `Θ^k ∈ ℍ`, `λ ∈ [0, 1]`, and `δX̄ = X̄¹ − X̄²`.

Proposition: on every filtered probability space, for every `g : ℝⁿ × P₂(ℝⁿ) → ℝᵐ` with the
terminal bound (2.6) of Assumption 2.3 with the constant `L` (`LipTerminal`), every `λ ∈ ℝ` and
all `ℱ_T`-measurable square-integrable `X₁, X₂`, the three links hold, in `[0, ∞]`:
`∫⁻ ‖λ (g(X₁, Law X₁) − g(X₂, Law X₂))‖² ≤ ofReal(λ² L²) ∫⁻ (‖X₁ − X₂‖ + W₂)²
≤ ofReal(2λ² L²) (∫⁻ ‖X₁ − X₂‖² + W₂²) ≤ ofReal(4L² λ²) ∫⁻ ‖X₁ − X₂‖²`, with
`W₂ = w2P(Law X₁, Law X₂)`.

Readings:

* The proposition is broader than printed: it holds on every filtered probability space
  `(Ω, ℱ, P)`, for every real `λ` and `L`, for every `g : ℝⁿ × P₂(ℝⁿ) → ℝᵐ` with the terminal
  bound (2.6) alone (`LipTerminal`, one field of Assumption 2.3), and for any two
  `ℱ_T`-measurable square-integrable terminal values `X₁, X₂`, which is all the step uses of
  `X̄^k_T` and `λ`. The printed claim is its instance at: `ℱ = enlJoint 𝒢₀ D h𝒢₀` and `P` of the
  standing setting of Lemma 4.2, with its horizon `T`; `g = C.g`, the terminal function of the
  coefficients `C`; `L` the constant of Assumption 2.3 (so `L ≥ 0`), for which
  `LipTerminal (enlJoint 𝒢₀ D h𝒢₀) P T L C.g` is `Assumption23.terminal` of the lemma's
  hypothesis; `λ ∈ [0, 1]`, the parameter of the frozen step; and `X_k = X̄^k_T`, that is
  `ω ↦ (X̄^k_i(T, ω))_i` as in `terminalVal`, where `X̄^k` is the forward component of the frozen
  step `Φ_λ(Θ^k)` (`FrozenStep` with the same `λ`, `C`, `ξ₀` and forcing `q`) of the trial
  `Θ^k ∈ ℍ`, `k = 1, 2`: `ℱ_T`-measurable since `X̄^k` is adapted, and square integrable since
  `X̄^k ∈ S²`. At this instance `λ • (g(X₁, Law X₁) − g(X₂, Law X₂))` has the coordinates
  `λ terminalVal(X̄¹) − λ terminalVal(X̄²)`, the difference of the terminal values
  `λ terminalVal(X̄^k) + q^g_T` of the two frozen steps, which is `δξ̄`; `X₁ − X₂ = δX̄_T` and
  `W₂ = W₂(Law X̄¹_T, Law X̄²_T)`. The same bound is used at 03:166 and 04:753.
* `C_g λ²` with `C_g = 4L²` explicit; `W₂` is the 2-Wasserstein distance of the Euclidean norm on
  `P₂(ℝⁿ)` of the laws of the terminal values (`w2P`, `lawP2`, as in (2.6) and (2.9)). The
  expectations are lower integrals in `[0, ∞]` of `‖·‖ₑ²`; `W₂` enters through `ofReal`.
* (2.6) holds with no sign condition on `L` in `LipTerminal`; the links do not need one either
  (a negative `L` forces `δξ̄ = 0`).

Proof: pointwise from (2.6), `‖λ v‖² = λ² ‖v‖² ≤ λ² L² (‖δX_T‖ + W₂)²`; then
`(a + b)² ≤ 2a² + 2b²` and `W₂² ≤ 𝔼‖δX_T‖²` (the coupling bound (2.9), `ofReal_w2P_lawP2_sq_le`).

Witness: `Dissertation.Acceptance.A.eq_terdiff_hypotheses`: at the instance of
`thm_cwp_hypotheses` (a Lévy driver with `d = 1`, `ν = δ₀`, `𝒢₀ = ⊥`, `n = m = 1`, `T = 1`), the
terminal function `g(x, ρ) = x` of Example 5.1(i) satisfies (2.6) with `L = 1`, and the terminal
values `0` and `e₁` are `ℱ_1`-measurable and square integrable.

Verdict: faithful (broader, printed claim an instance).

<!-- spec-review: Dissertation.PaperSpec.A.eq_terdiff ed839d34f480cba104ed4a8f00254090 by=claude-author source=A:eq:terdiff@0caddd587e020626144250f6aae2937e7b9eb2d9473e34140e10631526acde4c -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.eq_terdiff--claude-auditor--2026-10-19T22_59_53Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_terdiff ed839d34f480cba104ed4a8f00254090 by=claude-auditor source=A:eq:terdiff@0caddd587e020626144250f6aae2937e7b9eb2d9473e34140e10631526acde4c -->

## The backward difference before (4.12), Step 4 of the proof of Lemma 4.2: `Dissertation.PaperSpec.A.eq_bwddiff_identity`

Manuscript (proof of Lemma `lem:small`, Step 4, lines 391–397), with the objects of lines 312–323
quoted in the section of (4.10): "*Step 4: the backward difference.* Taking the difference of
(4.8) at `Θ¹` and `Θ²`, the terms `q^g_T` and `q^f` cancelling, `δȲ_t = δξ̄ + ∫_t^T λ δf_s ds
− ∫_t^T δZ̄_s dW_s − ∫_t^T ∫_E δŪ_s(e) Ñ(ds, de)`, which is (4.4) with `δξ = δξ̄` and
`φ_s = λ δf_s`." Here `δξ̄ := λ [g(X̄¹_T, Law(X̄¹_T)) − g(X̄²_T, Law(X̄²_T))]` (line 378). The
display lies before the pinned region of `A:eq:bwddiff` (lines 409–422); it is the twin of the
forward difference before (4.10), `eq_fwddiff_identity`.

Proposition: under the hypotheses of (4.10), verbatim (Lemma 4.2's `T > 0`, (2.3), Assumption 2.2
with the datum `ξ₀`, Assumption 2.3 with `L`; `λ ∈ [0, 1]`, a forcing `q` with `PredForcing` over
`enlJoint`, trials `Θ¹, Θ²` with `HTuple`, and `FrozenStep … Θᵏ Θ̄ᵏ` with the same `λ`, `ξ₀`,
`q`), for every coordinate `k`, `(δȲ_k, δZ̄_k, δŪ_k)` satisfies `LinearBSDEJ` with terminal value
`λ (terminalVal(X̄¹)_k − terminalVal(X̄²)_k)` and drift `λ δf_k`, `δf_k` the difference of the
`driverProc`s at the trials.

Readings:

* `LinearBSDEJ` (reviewed in `definitions.md`) is the linear backward equation (4.4) in the
  library's form: almost surely at each `t ∈ [0, T]`,
  `Y_t = ξ + ∫_t^T φ_s ds − (∫_0^T Z dW − ∫_0^t Z dW) − (∫_0^T ∫_E U Ñ − ∫_0^t ∫_E U Ñ)`, with
  `Z`, `U`, `φ` progressive, of finite energy on `[0, T]` and vanishing off it, `ξ ∈ L²` and `Y`
  adapted with right-continuous paths. The proposition states the printed identity in that form
  ("which is (4.4) with `δξ = δξ̄` and `φ_s = λ δf_s`"), at each time almost surely, as (4.8)
  itself is stated in `FrozenStep`, coordinatewise. The regularity it carries is what the next
  sentence (lines 398–407, also before the pinned region) lists as the hypotheses of Lemma 4.1
  for the difference: `δȲ` adapted (with right-continuous paths, its left limits following from
  the equation), `δZ̄`, `δŪ` and `λ δf` of finite energy, `δξ̄` square integrable.
* The objects: `δȲ, δZ̄, δŪ` are the differences of the backward components of the two frozen
  steps; `terminalVal(X̄)_k` is coordinate `k` of `g(X̄_T, Law(X̄_T))`, so the terminal value is
  `δξ̄` (the frozen terminal values are `λ g + q^g_T`, and `q^g_T` cancels, as printed); `δf_k` is
  the driver difference at the trials and their laws (line 316), through `driverProc`, and `λ`
  stands outside it (`q^f` cancels).
* The section of (4.12) records the text before its display as steps of the proof, not stated;
  the difference equation is stated here.

Proof: the difference of the two linear backward equations of the frozen steps
(`LinearBSDEJ.sub`), whose terminal values and drifts are rewritten by `ring`.

Witness: `Dissertation.Acceptance.A.frozen_pair_window_hypotheses`, as for the forward difference
before (4.10) (`λ = 1`, the zero forcing, the trials the zero tuple and
`(1, 1, 1_{(0, 1]}, 1_{(0, 1]})` at Example 5.1(i) with `β₁ = β₂ = 1`, `σ_c = h_c = 0`, so
`f = x`, `g = x`). By hand `δf = −1`, and `δξ̄ = δX̄_1 = 1 + ∫_0^1 1_{(0, 1]} dW
+ ∫_0^1 ∫ 1_{(0, 1]} Ñ(ds, de)` with `𝔼|δξ̄|² = 3`: the terminal value and the drift of the
equation are both nonzero.

Verdict: faithful.

<!-- spec-review: Dissertation.PaperSpec.A.eq_bwddiff_identity ed839d34f480cba1d4d84f3b5a301248 by=claude-author source=A:eq:bwddiff@de9905541b6f5056f355fb8ba0c38a5ec78c92b2259b3b8960caf0be162e2643 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.eq_bwddiff_identity--claude-auditor--2026-10-20T15_31_29Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_bwddiff_identity ed839d34f480cba1d4d84f3b5a301248 by=claude-auditor source=A:eq:bwddiff@de9905541b6f5056f355fb8ba0c38a5ec78c92b2259b3b8960caf0be162e2643 -->

## (4.12), Step 4 of the proof of Lemma 4.2: `Dissertation.PaperSpec.A.eq_bwddiff`

Manuscript (proof of Lemma `lem:small`, Step 4, lines 391–424), with the objects of Steps 1–3
(lines 312–389): "*Step 4: the backward difference.* Taking the difference of (4.8) at `Θ¹` and
`Θ²`, the terms `q^g_T` and `q^f` cancelling,
`δȲ_t = δξ̄ + ∫_t^T λ δf_s ds − ∫_t^T δZ̄_s dW_s − ∫_t^T ∫_E δŪ_s(e) Ñ(ds, de)`, which is (4.4)
with `δξ = δξ̄` and `φ_s = λ δf_s`. `δȲ` is càdlàg adapted, and the remaining hypotheses hold:
`(δZ̄, δŪ) ∈ H²_W × H²_N` since `Θ̄¹, Θ̄² ∈ ℍ`, `δξ̄ ∈ L²(ℱ_T)` by (4.3),
`λ δf ∈ L²(Ω × [0, T])` by (4.9), as `|δf| ≤ S`. By Lemma 4.1, (4.12)
`𝔼 sup_{t ≤ T} |δȲ_t|² + 𝔼 ∫_0^T (|δZ̄_s|²_F + ‖δŪ_s‖²_{L²(ν)}) ds
≤ C_BP (𝔼|δξ̄|² + λ² 𝔼 ∫_0^T |δf_s|² ds)
≤ C_BP (C_g λ² 𝔼|δX̄_T|² + L⋆² λ² ‖Θ¹ − Θ²‖²_ℍ)
≤ C_BP (C_g λ² 𝔼 sup_{t ≤ T} |δX̄_t|² + L⋆² λ² ‖Θ¹ − Θ²‖²_ℍ)
≤ C_BP (C_g C_X λ⁴ + L⋆² λ²) ‖Θ¹ − Θ²‖²_ℍ ≤ C_Y λ² ‖Θ¹ − Θ²‖²_ℍ`,
`C_Y := C_BP (C_g C_X + L⋆²)`, the second inequality by (4.11) and (4.9), the fourth by (4.10),
and the last by `λ⁴ ≤ λ²` for `λ ∈ [0, 1]`." The pinned region is the display, lines 409–422.
Here `δξ̄ := λ [g(X̄¹_T, Law(X̄¹_T)) − g(X̄²_T, Law(X̄²_T))]` and `C_g := 4L²` (lines 378, 386),
`L⋆² = 10L² max{T, 1}` (4.9), `C_X = 3 max{T, c_BDG} L⋆²` (4.10), and
`C_BP := C₀(5 + 4c_BDG) + 4T`, `C₀ := 2e^T`, is the constant fixed in the proof of Lemma 4.1
(`04-proof-wellposedness.tex` lines 215, 244).

Proposition: `∃ c₀ > 0` such that for every `c ≥ c₀`, under the hypotheses of (4.10) (those of
Lemma 4.2, `λ ∈ [0, 1]`, the forcing `q`, two trials of `ℍ` and their frozen steps), with
`C_BP = 2e^T (5 + 4c) + 4T`, `L⋆² = 10L² max{T, 1}` and `C_X = 3 max{T, c} L⋆²`:
`∫⁻ sup_{[0, T]} |δȲ|² + (∑_{k, j} energy(δZ̄_{kj}) + ∑_k markedEnergy(δŪ_k))
≤ ofReal(C_BP) (∫⁻ |(λ (terminalVal(X̄¹)_k − terminalVal(X̄²)_k))_k|²
+ ofReal(λ²) ∑_k energy(δf_k))
≤ ofReal(C_BP) (ofReal(4L²λ²) ∫⁻ |δX̄_T|² + ofReal(L⋆²λ²) supSize(Θ¹ − Θ²))
≤ ofReal(C_BP) (ofReal(4L²λ²) ∫⁻ sup_{[0, T]} |δX̄|² + ofReal(L⋆²λ²) supSize(Θ¹ − Θ²))
≤ ofReal(C_BP) (ofReal(4L² C_X λ⁴ + L⋆²λ²) supSize(Θ¹ − Θ²))
≤ ofReal(C_BP (4L² C_X + L⋆²) λ²) supSize(Θ¹ − Θ²)`, with
`δf_k = driverProc(Θ¹)_k − driverProc(Θ²)_k`.

Readings:

* The objects. `δȲ, δZ̄, δŪ` are the differences of the backward components of the two frozen
  steps, coordinatewise; `terminalVal(X̄)_k` is coordinate `k` of `g(X̄_T, Law(X̄_T))`, so the
  coordinates of `δξ̄` are `λ (terminalVal(X̄¹)_k − terminalVal(X̄²)_k)` (the frozen terminal
  values are `λ g + q^g_T`, and `q^g_T` cancels); `δf_k` is the driver difference at the tuples
  and their laws, as `δψ` is defined (line 316), through `driverProc`, the coordinate of `f` on
  `[0, T]`. `‖Θ¹ − Θ²‖²_ℍ` is `supSize` of the trial differences.
* `C_BP` is the constant of Lemma 4.1. The passage takes it "by Lemma 4.1", and the proof of
  Lemma 4.1 fixes it as `C_BP = C₀(5 + 4c_BDG) + 4T` with `C₀ = 2e^T`; the proposition states
  this value explicitly, so the first link is Lemma 4.1 for the backward difference with the
  constant of Lemma 4.1. (`lem_bpbsde` states Lemma 4.1 with an existential function `C_BP(T)`;
  the explicit value is the stronger reading here.) It depends on `T` and `c_BDG` only, as line
  443 states. `C_g = 4L²`, `L⋆²`, `C_X` and `C_Y = C_BP(C_g C_X + L⋆²)` are the printed ones,
  explicit; `C_g C_X λ⁴` is written `4L² C_X λ⁴`.
* The constant `c_BDG`: as for (4.10). Here `c₀` is the largest of `4` and the `c₀` of (4.10), so
  the fourth link uses (4.10) at the same `c`.
* Expectations are lower integrals in `[0, ∞]`: `𝔼 sup` is `∫⁻` of the supremum over `[0, T]`
  of `esq`; `𝔼 ∫_0^T (|δZ̄|²_F + ‖δŪ‖²)` is the sum of the energies; `𝔼|δξ̄|²` and `𝔼|δX̄_T|²` are
  `∫⁻ esq`; `λ² 𝔼 ∫_0^T |δf_s|² ds` is `ofReal(λ²)` times the sum of the energies of `δf_k`.
* The text before the display (lines 391–407: the difference equation and the hypotheses of
  Lemma 4.1 for it) consists of steps of the proof; they are not stated, and the proof of the
  first link establishes them (`LinearBSDEJ.sub`).

Proof: the difference of the two backward equations (4.8) is the linear backward equation with
terminal value `δξ̄` and drift `λ δf` (`LinearBSDEJ.sub`); Lemma 4.1 in each coordinate
(`LinearBSDEJ.brownianPoisson_estimate`, constant `13e^T + 3T ≤ C_BP` for `c ≥ 4`), the running
supremum of the vector by those of the coordinates (`lintegral_biSup_esq_le`) and
`energy(λ φ) = λ² energy(φ)` give the first link; (4.11) at `X_k = X̄^k_T` (`eq_terdiff`) and
`∑_k energy(δf_k) ≤ 𝔼 ∫_0^T S_s² ds ≤ L⋆² ‖Θ¹ − Θ²‖²_ℍ` (`sum_energy_le_coeffDiffNorm`, (4.9))
the second; `|δX̄_T|² ≤ sup_{t ≤ T} |δX̄_t|²` the third; (4.10) at the same `c` the fourth; and
`λ⁴ ≤ λ²` the fifth.

Witness: `Dissertation.Acceptance.A.frozen_pair_hypotheses`, as for (4.10). By hand,
`δȲ_t = t`, `δZ̄ = δŪ = 0`, `δξ̄ = 1`, `δf = −1`, and with `C_X = 30c` the chain reads
`1 ≤ 2C_BP ≤ 24C_BP ≤ 24C_BP ≤ (240c + 20) C_BP ≤ (240c + 20) C_BP`.

Verdict: faithful.

<!-- spec-review: Dissertation.PaperSpec.A.eq_bwddiff ed839d34f480cba1d8920d62bd288ec6 by=claude-author source=A:eq:bwddiff@de9905541b6f5056f355fb8ba0c38a5ec78c92b2259b3b8960caf0be162e2643 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.eq_bwddiff--claude-auditor--2026-10-20T04_27_38Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_bwddiff ed839d34f480cba1d8920d62bd288ec6 by=claude-auditor source=A:eq:bwddiff@de9905541b6f5056f355fb8ba0c38a5ec78c92b2259b3b8960caf0be162e2643 -->

## (4.13), Step 5 of the proof of Lemma 4.2: `Dissertation.PaperSpec.A.eq_contract`

Manuscript (proof of Lemma `lem:small`, Step 5, lines 426–445): "*Step 5: the contraction.* Since
`Φ_λ(Θ¹) − Φ_λ(Θ²) = (δX̄, δȲ, δZ̄, δŪ)`, (4.13)
`‖Φ_λ(Θ¹) − Φ_λ(Θ²)‖²_ℍ = 𝔼 sup_{t ≤ T} |δX̄_t|² + 𝔼 sup_{t ≤ T} |δȲ_t|²
+ 𝔼 ∫_0^T (|δZ̄_s|²_F + ‖δŪ_s‖²_{L²(ν)}) ds ≤ (C_X + C_Y) λ² ‖Θ¹ − Θ²‖²_ℍ
≤ C_Φ λ² ‖Θ¹ − Θ²‖²_ℍ`, `C_Φ := max{1, C_X + C_Y}`, the first inequality by (4.10) and (4.12).
Here `L⋆ = L⋆(T, L)`, `C_X = C_X(T, L, c_BDG)`, `C_g = C_g(L)`, `C_BP = C_BP(T, c_BDG)`, so
`C_Φ = C_Φ(T, L, c_BDG)`." The pinned region is the display, lines 429–439.

Proposition: `∃ c₀ > 0` such that for every `c ≥ c₀`, under the hypotheses of (4.10), with
`C_X = 3 max{T, c} · 10L² max{T, 1}` and `C_Y = (2e^T (5 + 4c) + 4T)(4L² C_X + 10L² max{T, 1})`:
`supSize(Θ̄¹ − Θ̄²) = ∫⁻ sup_{[0, T]} |δX̄|² + ∫⁻ sup_{[0, T]} |δȲ|²
+ (∑_{k, j} energy(δZ̄_{kj}) + ∑_k markedEnergy(δŪ_k))
≤ ofReal((C_X + C_Y) λ²) supSize(Θ¹ − Θ²) ≤ ofReal(max{1, C_X + C_Y} λ²) supSize(Θ¹ − Θ²)`.

Readings:

* `‖Φ_λ(Θ¹) − Φ_λ(Θ²)‖²_ℍ` is `supSize` of the differences of the images (the squared norm of
  `ℍ` of §3, reviewed with Lemma 4.3), and `Φ_λ(Θ¹) − Φ_λ(Θ²) = (δX̄, δȲ, δZ̄, δŪ)` is the
  coordinatewise difference. The equality is the definition of `supSize`, stated with the
  passage's grouping of the `δZ̄`- and `δŪ`-energies.
* The constants are those of (4.10) and (4.12), explicit, and `C_Φ = max{1, C_X + C_Y}`; they
  depend on `T, L, c_BDG` only, as lines 441–445 state: each is a fixed expression in `T`, `L`
  and the value `c` of `c_BDG`, which is quantified before the data (`∃ c₀ > 0, ∀ c ≥ c₀`
  first), so `C_Φ` is a function of `(T, L, c_BDG)` chosen before everything else. The sentence
  lies after the pinned region; the claim's scope note records it.
* The constant `c_BDG`: as for (4.10); `c₀` is the largest of those of (4.10) and (4.12).
* "the first inequality by (4.10) and (4.12)" is the proof. The rest of the paragraph after the
  region (lines 445–455: `λ*`, the Banach fixed-point theorem) belongs to the conclusion of the
  proof of Lemma 4.2, whose statement is `lem_small`.

Proof: the equality unfolds `supSize`; the first inequality adds the chains of (4.10) and (4.12)
at the same `c`; the second is `C_X + C_Y ≤ max{1, C_X + C_Y}`.

Witness: `Dissertation.Acceptance.A.frozen_pair_hypotheses`, as for (4.10); by hand
`‖Φ_λ(Θ¹) − Φ_λ(Θ²)‖²_ℍ = 1 + 1 + 0 = 2` and `‖Θ¹ − Θ²‖²_ℍ = 2`.

Verdict: faithful.

<!-- spec-review: Dissertation.PaperSpec.A.eq_contract ed839d34f480cba1410aaf91d78575ad by=claude-author source=A:eq:contract@747835f57a1b4c1429243cdebab1cc3873022b5774d61884f0b447b1a5d04f41 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.eq_contract--claude-auditor--2026-10-20T04_27_45Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_contract ed839d34f480cba1410aaf91d78575ad by=claude-auditor source=A:eq:contract@747835f57a1b4c1429243cdebab1cc3873022b5774d61884f0b447b1a5d04f41 -->

## `λ_*` and the contraction by `1/2`, after (4.13), in the proof of Lemma 4.2: `Dissertation.PaperSpec.A.eq_contract_half`

Manuscript (proof of Lemma `lem:small`, Step 5, lines 445–454), after (4.13) and the dependences
of its constants (quoted in the section of (4.13)): "so `C_Φ = C_Φ(T, L, c_BDG)`. Setting
`λ_* := (2 √C_Φ)⁻¹ ∈ (0, 1/2]` gives `C_Φ λ² ≤ 1/4` for `λ ∈ [0, λ_*]`, so that (4.13) reads
`‖Φ_λ(Θ¹) − Φ_λ(Θ²)‖_ℍ ≤ (1/2) ‖Θ¹ − Θ²‖_ℍ`, `λ ∈ [0, λ_*]`." The sentence lies after the
pinned region of `A:eq:contract` (lines 429–439); `lem_small` leaves its threshold an
unspecified function of `(T, L)`, so neither the printed `λ_*` nor the contraction by `1/2` was
stated before.

Proposition: `∃ c₀ > 0` such that for every `c ≥ c₀`, under the hypotheses of Lemma 4.2 (`T > 0`,
(2.3), Assumptions 2.2–2.3 with `L` and `ξ₀`), for all reals `C_Φ`, `λ_*` with
`C_Φ = max{1, C_X + C_Y}` (`C_X = 3 max{T, c} · 10L² max{T, 1}`,
`C_Y = (2e^T (5 + 4c) + 4T)(4L² C_X + 10L² max{T, 1})`, the constants of (4.13)) and
`λ_* = (2 √C_Φ)⁻¹`: `0 < λ_* ≤ 1/2`; and for every `λ ∈ [0, λ_*]`, `C_Φ λ² ≤ 1/4` and, for a
forcing `q` (`PredForcing`), two trials `Θ¹, Θ²` (`HTuple`) and their frozen steps at `λ`
(`FrozenStep`, same `λ`, `ξ₀`, `q`),
`supSize(Θ̄¹ − Θ̄²)^{1/2} ≤ ofReal(1/2) supSize(Θ¹ − Θ²)^{1/2}`.

Readings:

* The constants are those of (4.13), stated by the same explicit formulas in `T`, `L` and the
  value `c` of `c_BDG`, quantified before the data as for (4.13); `λ_*` is the printed
  `(2 √C_Φ)⁻¹`, introduced as a real equal to it, as `C_Φ` is.
* `‖·‖_ℍ` is the square root of `supSize` (the squared norm of `ℍ` of §3) in `[0, ∞]`, `x^{1/2}`
  as `ENNReal.rpow`; `Φ_λ(Θᵏ)` is the frozen step `Θ̄ᵏ` (`FrozenStep`), as in (4.13). "So that
  (4.13) reads" is the contraction itself, stated for every `λ ∈ [0, λ_*]`, `λ ≤ 1/2 ≤ 1`.
* The hypotheses are those of (4.13), with `λ` restricted to `[0, λ_*]`.
* The section of (4.13) assigns this sentence to the conclusion of the proof of Lemma 4.2; it is
  stated here.

Proof: `C_Φ ≥ 1` gives `√C_Φ ≥ 1`, so `0 < λ_* ≤ 1/2`, and `C_Φ λ_*² = 1/4`, so
`C_Φ λ² ≤ 1/4` for `0 ≤ λ ≤ λ_*`. The contraction is (4.13) (`eq_contract` at the same `c`) with
`C_Φ λ² ≤ 1/4`, raised to the power `1/2` (`(1/4)^{1/2} = 1/2`).

Witness: `Dissertation.Acceptance.A.frozen_pair_window_lam_hypotheses`: the instance of
`frozen_pair_window_hypotheses` with the frozen steps at an arbitrary `λ ∈ [0, 1]`, in particular
at every `λ ∈ [0, λ_*]` (`frozen_hypotheses`: Example 5.1(i) with `β₁ = β₂ = 1`, `σ_c = h_c = 0`,
datum `0`, `L = 1`, the zero forcing; the trials the zero tuple and
`(1, 1, 1_{(0, 1]}, 1_{(0, 1]})`, each with a frozen step at `λ`; `δb`, `δσ`, `δh` of energy `1`,
stated). By hand `‖Θ¹ − Θ²‖²_ℍ = 1 + 1 + 1 + 1 = 4`, and at `λ > 0` the frozen difference has
`δX̄_t = λ (t + ∫_0^t 1_{(0, 1]} dW + ∫_0^t ∫ 1_{(0, 1]} Ñ(ds, de))`, so both sides are positive.

Verdict: faithful.

<!-- spec-review: Dissertation.PaperSpec.A.eq_contract_half ed839d34f480cba1a63dc37c47701d1d by=claude-author source=A:eq:contract@747835f57a1b4c1429243cdebab1cc3873022b5774d61884f0b447b1a5d04f41 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.eq_contract_half--claude-auditor--2026-10-20T15_31_29Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_contract_half ed839d34f480cba1a63dc37c47701d1d by=claude-auditor source=A:eq:contract@747835f57a1b4c1429243cdebab1cc3873022b5774d61884f0b447b1a5d04f41 -->

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

<!-- spec-review: Dissertation.PaperSpec.A.lem_pert ed839d34f480cba1eefcd4522364d865 by=claude-author source=A:lem:pert@ea2eb3fcdf75fe4c7dccc111e320388b6d82e0967dd051aa673e75f7a5f1c1e9 -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.lem_pert--claude-reviewer--2026-10-17T12_26_32Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.lem_pert ed839d34f480cba1eefcd4522364d865 by=claude-reviewer source=A:lem:pert@ea2eb3fcdf75fe4c7dccc111e320388b6d82e0967dd051aa673e75f7a5f1c1e9 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.lem_pert--claude-auditor--2026-10-19T03_38_06Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.lem_pert ed839d34f480cba1eefcd4522364d865 by=claude-auditor source=A:lem:pert@ea2eb3fcdf75fe4c7dccc111e320388b6d82e0967dd051aa673e75f7a5f1c1e9 -->

## (4.15) and (4.16), the difference equations in the proof of Lemma 4.3: `Dissertation.PaperSpec.A.eq_dX`, `eq_dY`

Manuscript (proof of Lemma `lem:pert`, lines 511–533): "The difference equations below involve
the forcings only through `δq`, which we therefore write simply as `q`." With
`δψ_t := ψ(t, Θ¹_t, μ¹_t) − ψ(t, Θ²_t, μ²_t)`, `ψ ∈ {b, σ, h, f}`, `μ^k_t := Law(Θ^k_t)`,
"likewise `δg_T`, with `δh` evaluated at the predictable tuples `(Θ^{k,−}_t, μ^{k,−}_t)`. … The
difference equations are
`d δX_t = (λ δb_t + q^b_t) dt + (λ δσ_t + q^σ_t) dW_t + ∫_E (λ δh_t(e) + q^h_t(e)) Ñ(dt, de)`,
(4.15) `d δY_t = −(λ δf_t + q^f_t) dt + δZ_t dW_t + ∫_E δU_t(e) Ñ(dt, de)`,
`δY_T = λ δg_T + q^g_T`. (4.16)" Section 2 (`02-model-assumptions.tex`, lines 35–45) defines
`Θ^−_t = (X_{t−}, Y_{t−}, Z_t, U_t)` and fixes Borel representatives `μ_t`, `μ^−_t` of the law
flows: "Expressions such as `b(t, Θ_t, μ_t)` are thereby defined at every `t`, while every claim
made about them is `dt`-a.e. or time-integrated."

Propositions:

* `eq_dX`: under the hypotheses of Lemma 4.3 (those of `lem_pert`, verbatim), for every
  coordinate `i`: the drift `λ (δb)_i + q^b_i` (the difference of the `driftProc`s and of the
  forcings) has almost surely integrable paths on `[0, T]`; the diffusion `λ (δσ)_i + q^σ_i`
  meets the conditions of the Brownian integral (existential proofs `hσm`, `hσp`, `hσq`); some
  `H : Ω → ℝ → E → ℝ` meeting the conditions of the compensated integral (jointly measurable,
  marked progressively measurable for `enlJoint`, finite energy on every horizon) agrees,
  `markedEnergyMeasure`-almost everywhere on `Ω × [0, T] × E`, with
  `λ (coeffJump(h, Θ¹⁻) − coeffJump(h, Θ²⁻))_i + q^h_i` (each cut to `[0, T]` by `jumpProc`); and
  for every such `H` and every `t ∈ [0, T]`, almost surely
  `δX_{i,t} = δξ₀_i + ∫_{[0, t]} (λ δb_i + q^b_i) ds + ∫_0^t (λ δσ_i + q^σ_i) dW
  + ∫_0^t ∫_E H Ñ(ds, de)`.
* `eq_dY`: under the same hypotheses, for every coordinate `k`: the driver `λ (δf)_k + q^f_k` has
  almost surely integrable paths on `[0, T]`; almost surely
  `δY_{k,T} = λ (g(X¹_T, Law X¹_T) − g(X²_T, Law X²_T))_k + q^g_k`; `δZ_k` and `δU_k` meet the
  conditions of the stochastic integrals (existential proofs); and for every `t ∈ [0, T]`, almost
  surely `δY_{k,t} = λ δg_k + q^g_k + ∫_{[t, T]} (λ δf_k + q^f_k) ds − (∫_0^T − ∫_0^t) δZ_k dW
  − (∫_0^T − ∫_0^t) ∫_E δU_k Ñ(ds, de)`.

Readings:

* The hypotheses are those of Lemma 4.3, written as in `lem_pert` (reviewed with Lemma 4.3).
* `q = δq`: the differences `q^{·,1} − q^{·,2}` of the forcings; `δξ₀ = ξ₀¹ − ξ₀²`
  coordinatewise; `δψ` along `Θ^k` through `driftProc`, `diffusionProc`, `driverProc` and
  `terminalVal` (reviewed in `definitions.md`), `ψ(s, Θ^k_s(ω), Law Θ^k_s)` for `s ∈ [0, T]`.
* The differential notation is read in integral form, forward from `0` for `δX` (`δX_0 = δξ₀` is
  the identity at `t = 0`) and backward from `T` for `δY`, almost surely at each `t ∈ [0, T]`,
  with the canonical stochastic integrals of the library over `enlJoint`, as in `LinearFSDEJ`,
  `LinearBSDEJ` and the class `WeakForcedSolution`. `∫_0^t` is over `[0, t]` and `∫_t^T` over
  `[t, T]` (the same for Lebesgue measure); the drift and driver integrals are pathwise, with
  their integrability stated. `δY_T = λ δg_T + q^g_T` is stated on its own as well as inside the
  identity at `t = T`.
* `δh` at the predictable tuples: `Θ^{k,−}_s = (X^k_{s−}, Y^k_{s−}, Z^k_s, U^k_s)` through
  `leftLimProc`, and `h(s, Θ^{k,−}_s, ·, μ^{k,−}_s)` through its canonical representative
  `coeffJump` (reviewed in `definitions.md`), `μ^{k,−}_s` the law of `Θ^{k,−}_s`. The paper makes
  every claim about these expressions `dt`-a.e. or time-integrated, so the jump integrand is a
  `dP ⊗ dt ⊗ ν`-class on `Ω × [0, T] × E`, and its compensated integral is that of a
  representative meeting the conditions of the integral. The proposition states that such a
  representative exists and that the identity holds with every one. It does not ask the
  expression at the predictable tuple itself to meet those conditions: at `s = 0` the left limits
  `X_{0−}`, `Y_{0−}` read the paths before `0`, on which `WeakForcedSolution` places no condition,
  so on that null set of times the expression need not be measurable.

Proofs: extended off `[0, T]`, the solutions solve `SolvesForcedInt`, and the difference of the
extensions is a `PairDiff` with Lipschitz constants `10 (2L)²` and `4 (2L)²`, from Assumptions
2.3 and 2.5 along the diagonal (`PaperWeakSolutionForcedInt.exists_pairDiff`); its coordinates
solve `LinearFSDEJ` and `LinearBSDEJ`, whose equations are (4.15) and (4.16) for the extensions,
which agree with the solutions on `[0, T]`, with the jump integrand `λ (γ¹ − γ²) + q^h` of the
solutions' representatives. That integrand agrees almost everywhere with the one at the
predictable tuples (`PaperWeakSolutionForcedInt.ae_forcedJump_sub_leftLim_eq`: the paths frozen
outside `[0, T]` are càdlàg with the same left limits on `(0, T]`, their predictable tuple is
their tuple at almost every time, and `jump_rep`), so it is a representative; every
representative has almost surely the same compensated integral
(`compensatedIntegral_congr_of_markedEnergy`). The path integrability comes from the solutions
(`b_int`, `f_int`), and `δY_T` from the backward equation at `T`.

Witness: `Dissertation.Acceptance.A.lem_pert_two_data_hypotheses`, the hypotheses of Lemma 4.3
(reviewed with Lemma 4.3), which are those of both propositions.

Verdict: faithful.

<!-- spec-review: Dissertation.PaperSpec.A.eq_dX ed839d34f480cba17f8ea34acd5ecf0b by=claude-author source=A:eq:dX@a877929483513c2add78424568742c35536e0d941243980e25f83f1d3832b241 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.eq_dX--claude-auditor--2026-10-19T22_56_03Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_dX ed839d34f480cba17f8ea34acd5ecf0b by=claude-auditor source=A:eq:dX@a877929483513c2add78424568742c35536e0d941243980e25f83f1d3832b241 -->
<!-- spec-review: Dissertation.PaperSpec.A.eq_dY ed839d34f480cba1cc37dd9a0d2b35ad by=claude-author source=A:eq:dY@a877929483513c2add78424568742c35536e0d941243980e25f83f1d3832b241 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.eq_dY--claude-auditor--2026-10-19T22_56_08Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_dY ed839d34f480cba1cc37dd9a0d2b35ad by=claude-auditor source=A:eq:dY@a877929483513c2add78424568742c35536e0d941243980e25f83f1d3832b241 -->

## (4.18), the four bounds and the fifth integrand in Step 1 of the proof of Lemma 4.3: `Dissertation.PaperSpec.A.eq_bdg4_XZ`, `eq_bdg4_sigmaY`, `eq_bdg4_XU`, `eq_bdg4_hY`, `eq_bdg4_fifth`

Manuscript (proof of Lemma `lem:pert`, lines 579–622): "Of the last five terms of (4.17), the
first four are bounded by BDG and Cauchy–Schwarz, with (2.1) in the jump terms:
`𝔼 sup_{t ≤ T} |∫_0^t ⟨G δX_{s−}, δZ_s dW_s⟩| ≤ c_BDG ‖G‖ (𝔼 sup_{t ≤ T} |δX_t|²)^{1/2}
(𝔼 ∫_0^T |δZ_t|²_F dt)^{1/2}`,
`𝔼 sup_{t ≤ T} |∫_0^t ⟨G (λ δσ_s + q^σ_s) dW_s, δY_{s−}⟩| ≤ c_BDG ‖G‖ (𝔼 sup_{t ≤ T} |δY_t|²)^{1/2}
(𝔼 ∫_0^T |λ δσ_t + q^σ_t|²_F dt)^{1/2}`,
`𝔼 sup_{t ≤ T} |∫_0^t ∫_E ⟨G δX_{s−}, δU_s(e)⟩ Ñ(ds, de)| ≤ c_BDG ‖G‖ (𝔼 sup_{t ≤ T} |δX_t|²)^{1/2}
(𝔼 ∫_0^T ‖δU_t‖²_{L²(ν)} dt)^{1/2}`,
`𝔼 sup_{t ≤ T} |∫_0^t ∫_E ⟨G (λ δh_s + q^h_s)(e), δY_{s−}⟩ Ñ(ds, de)| ≤ c_BDG ‖G‖
(𝔼 sup_{t ≤ T} |δY_t|²)^{1/2} (𝔼 ∫_0^T ‖λ δh_t + q^h_t‖²_{L²(ν)} dt)^{1/2}`. (4.18)
Since `Θ¹ − Θ² ∈ ℍ`, `𝔼 sup_{t ≤ T} |δX_t|² + 𝔼 sup_{t ≤ T} |δY_t|² + 𝔼 ∫_0^T (|δZ_t|²_F
+ ‖δU_t‖²_{L²(ν)}) dt = ‖Θ¹ − Θ²‖²_ℍ < ∞`, and by the computation of (4.9), with the forcings
square-integrable, `𝔼 ∫_0^T (|λ δσ_t + q^σ_t|²_F + ‖λ δh_t + q^h_t‖²_{L²(ν)}) dt < ∞`. The four
suprema in (4.18) are therefore integrable, so the supremum criterion applies to those four local
martingales. The fifth has predictable integrand, and by Cauchy–Schwarz
`𝔼 ∫_0^T ∫_E |⟨λ δh_t(e) + q^h_t(e), Gᵀ δU_t(e)⟩| ν(de) dt ≤ ‖G‖ (𝔼 ∫_0^T ‖λ δh_t + q^h_t‖²_{L²(ν)}
dt)^{1/2} (𝔼 ∫_0^T ‖δU_t‖²_{L²(ν)} dt)^{1/2} < ∞`. Hence (2.2) applies, and all five terms have
zero expectation." The §4 preamble (lines 30–35) fixes BDG in quadratic-variation form, at `p = 1`
for the zero-mean arguments, with one universal constant `c_BDG`.

Propositions (hypotheses: those of Lemma 4.3, `lem_pert`, verbatim, as in `eq_dX`; the bounds
first fix `c₀ > 0` and take every `c ≥ c₀`):

* `eq_bdg4_XZ`: with `L^X_s = (δX_{s−} for s ∈ (0, T], 0 otherwise)` (`leftLimProc` of
  `X¹ − X²`), the integrand `H_s(j) = ∑_k (G L^X_s)_k δZ^{kj}_s` has a local Itô integral `M` on
  `[0, T]` (`IsLocalBrownianIntegral D.W (enlJoint …) _ T H M`), and every such `M` satisfies
  `∫⁻ sup_{t ∈ [0, T]} ‖M_t‖ ≤ ofReal (c ‖GX G‖) (∫⁻ sup_{t ∈ [0, T]} esq δX_t)^{1/2}
  (∑_{k, j} energy δZ^{kj})^{1/2}`, the right side is finite, and for every `t ∈ [0, T]`,
  `M_T − M_t` is integrable with mean zero.
* `eq_bdg4_sigmaY`: the same for `H_s(j) = ∑_k (G Σ_{·j, s})_k L^Y_{k, s}` with
  `Σ_{ij} = λ (diffusionProc¹ − diffusionProc²)_{ij} + (q^σ_1 − q^σ_2)_{ij}` (the expression of
  `eq_dX`), with `esq δY` and `(∑_{i, j} energy Σ_{ij})^{1/2}` on the right.
* `eq_bdg4_XU`: the same for the marked integrand `φ_s(e) = ∑_k (G L^X_s)_k δU^k_s(e)` and the
  local compensated integral (`IsLocalCompensatedIntegral D.N …`), with
  `(∑_k markedEnergy δU^k)^{1/2}` on the right.
* `eq_bdg4_hY`: some `H : Fin n → Ω → ℝ → E → ℝ` meeting the conditions of the compensated
  integral agrees `markedEnergyMeasure`-almost everywhere with
  `λ (coeffJump(h, Θ¹⁻) − coeffJump(h, Θ²⁻)) + (q^h_1 − q^h_2)` (cut to `[0, T]` by `jumpProc`),
  coordinatewise, as in `eq_dX`; and for every such `H`, the bound of `eq_bdg4_XU` holds for
  `φ_s(e) = ∑_k (G H_s(e))_k L^Y_{k, s}`, with `esq δY` and `(∑_i markedEnergy H_i)^{1/2}` on the
  right.
* `eq_bdg4_fifth` (no constant): `∑_{i, j} energy Σ_{ij} < ⊤`; such an `H` exists; and for every
  such `H`, `∑_i markedEnergy H_i < ⊤` and
  `∫⁻ ∫⁻_{[0, T]} ∫⁻ ofReal |⟨H_s(e), Gᵀ δU_s(e)⟩| dν ds dP ≤ ofReal ‖GX G‖
  (∑_i markedEnergy H_i)^{1/2} (∑_k markedEnergy δU^k)^{1/2}`, the right side finite.

Readings:

* The hypotheses are those of Lemma 4.3, written as in `lem_pert` (reviewed with Lemma 4.3); the
  differences `δX = X¹ − X²`, …, `q = δq` and `δσ` along `Θ^k` are those of `eq_dX`, `eq_dY`.
* The four integrals are local stochastic integrals, as `M^W` and `M¹` in the proof of Lemma 4.1
  (`lem41_MW`): their integrands carry `δX_{s−}` or `δY_{s−}`, of which `Θ¹ − Θ² ∈ ℍ` gives only
  the second moments of the suprema, so the integrands need not have finite energy and the `L²`
  integrals do not apply. `IsLocalBrownianIntegral` and `IsLocalCompensatedIntegral` (reviewed in
  `definitions.md`) determine the integral up to indistinguishability on `[0, T]`, so "every such
  `M`" is the paper's integral; the existence conjunct is its definition. `𝔼 sup_{t ≤ T} |∫_0^t …|`
  is the lower integral of the supremum over `[0, T]` of `‖M_t‖`.
* `δX_{s−}`, `δY_{s−}` are the left limits at the times of `(0, T]`, where they exist on every
  path (`WeakForcedSolution`), and the weight is set to `0` at other times: the integrals over
  `[0, t]`, `t ≤ T`, do not see times after `T`, nor the time `0` (Lebesgue-null, and `N` charges
  no fixed time), and off `[0, T]` the paths and the representatives `H` are unconstrained.
* `⟨G δX_{s−}, δZ_s dW_s⟩ = ∑_j (∑_k (G δX_{s−})_k δZ^{kj}_s) dW^j_s` and
  `⟨G Σ_s dW_s, δY_{s−}⟩ = ∑_j (∑_k (G Σ_{·j, s})_k δY^k_{s−}) dW^j_s`, the library's
  multidimensional integral of the vector integrand; likewise with `δU_s(e)` and `H_s(e)` against
  `Ñ`. `|·|_F² = ∑_{i, j} (·)²`, so `𝔼 ∫_0^T |·|²_F dt` is `∑ energy`, and
  `𝔼 ∫_0^T ‖·‖²_{L²(ν)} dt` is `∑ markedEnergy`; `‖G‖` is the operator norm `‖GX G‖`; the
  suprema of `|δX|²`, `|δY|²` are those of `esq`, as in `supSize`.
* `λ δh + q^h`, with `δh` at the predictable tuples, enters through a representative `H`, as in
  `eq_dX` and for the same reason: the paper makes every claim about the expression `dt`-a.e., so
  its compensated integral is that of a representative meeting the conditions of the integral;
  the proposition states that one exists and bounds the integral of every one, and
  `𝔼 ∫_0^T ‖λ δh_t + q^h_t‖² dt` is the marked energy of the representative (the same for all,
  as they agree almost everywhere).
* Marked progressive integrands and representatives are harmless. The representatives `H` are
  asked to meet the conditions of the library's compensated integral: joint measurability,
  marked progressive measurability, finite energy on every horizon. That class contains the
  paper's: `λ δh + q^h` has a marked predictable representative, measurable for the predictable
  σ-algebra times that of `E` (the first conjunct of `eq_bdg4_fifth_mean`), and one cut to
  `(0, T]` is still marked predictable, so jointly measurable and marked progressively measurable
  (`MarkedPredictable.markedProgressivelyMeasurable`), and has finite energy on every horizon
  (that on `[0, T]`, the energy of every representative, finite by `eq_bdg4_fifth`); so the
  bound of `eq_bdg4_hY`, stated for every admitted `H`, covers the paper's. Admitting more
  representatives adds no other integral: the library's integrals depend only on the class of
  the integrand up to a `P ⊗ ds` (resp. `P ⊗ ds ⊗ ν`) null set on `[0, T]`
  (`multidimStochasticIntegral_congr_of_energy`, `compensatedIntegral_congr_of_markedEnergy`),
  and all representatives agree almost everywhere, so their integrals agree, at every time of
  `[0, T]`, almost surely. The same holds
  for the progressive measurability asked of the cut-off integrands in `IsLocalBrownianIntegral`
  and `IsLocalCompensatedIntegral`: predictability implies it, so the paper's integrands are
  among those admitted. The first and third integrands are predictable (`δZ`, `δU` and the
  weights cut to `(0, T]`); the second carries `Σ`, which is progressively measurable (as `q^σ`
  is, by `Forcing`), the usual condition for an Itô integrand.
* `c_BDG`: as for `lem41_MW`, each bound holds for every value at least some `c₀ > 0` (here
  `c₀ = 9`), so the bounds hold together with the paper's other uses of `c_BDG` for every value at
  least the largest `c₀`. The reading is that `c_BDG` is a sufficiently large universal constant,
  every value at least `c₀`, not every constant for which Davis's inequality holds: the best
  constant of that inequality may be smaller than `9`, and at such a value the propositions say
  nothing. The paper fixes `c_BDG` only as one universal constant (lines 29–33) and states no
  value of it; its uses need only some universal value.
* The filtration. The four local integrals are local martingales for `enlJoint 𝒢₀ D h𝒢₀`, the
  usual augmentation of `ℱ^{W,N}_t ∨ ℱ₀` (right-continuous, with the `P`-null sets), the filtration
  of the paper and of the hypotheses: the cut-off `L²` integrals are the library's for it, and
  the localising times, the exit times of the frozen path from balls (`exitSeq`), are its
  stopping times because it is right-continuous (`isStoppingTime_exitSeq`,
  `isRightContinuous_enlJoint`); see `lem41_MW`.
* "`< ∞`" and "the four suprema … are integrable": the finiteness of each right side, which with
  the bound puts the running supremum in `L¹`. "The supremum criterion applies": its conclusion,
  `𝔼[M_T − M_t] = 0` with `M_T − M_t` integrable, is stated for every `t ∈ [0, T]` (the identity
  (4.19) uses `t = 0`).
* The display at lines 600–605 is the definition of the norm of `ℍ` (`supSize`) at the hypothesis
  `Θ¹ − Θ² ∈ ℍ`; it enters through that hypothesis. The display at lines 606–610 is
  `eq_bdg4_fifth`'s first conjunct and its `∑_i markedEnergy H_i < ⊤`.
* The first link of each bound, BDG at `p = 1` in quadratic-variation form for the local martingale
  (Davis's inequality), is cited (He, Wang and Yan) and not stated; each bound is proved through
  the predictable quadratic variation (Lenglart's inequality) with the paper's right-hand side.
  (2.1) "in the jump terms" turns `𝔼 ∫∫ |·|² N(ds, de)` into `𝔼 ∫∫ |·|² ν(de) ds`; the predictable
  quadratic variation is the latter already, so the proofs do not need it.
* Not formalised here (recorded in `scope_note`): that the four integrals and the fifth term are
  the stochastic terms of (4.17) (the decomposition belongs to (4.17), `A:eq:Gid-path`). "The
  fifth has predictable integrand" and the zero mean of the fifth term by (2.2) (lines 612–613
  and 622) are the clause `eq_bdg4_fifth_mean`, reviewed in its own section below.

Proofs: the weights `G δX_{s−}` and `Gᵀ δY_{s−}` cut to `(0, T]` (`matLeftLimWeight`) are
predictable, at most `(∑ |G_{ki}|) R` before the path leaves the ball of radius `R`, and
`|w_s|² ≤ ‖G‖² sup_{t ≤ T} |·|²` (`matLeftLimWeight_props`, with `‖Gᵀ‖ = ‖G‖`); `⟨G v, y⟩ =
⟨Gᵀ y, v⟩` (`sum_mulVec_mul_eq`) writes the second and fourth integrands with the weight
`Gᵀ δY_{s−}`. `localBrownian_weight` and `localCompensated_weight` (BDG at `p = 1` with constant
`9` by Lenglart's argument, the local integral along the exit times of the frozen path, and the
zero means by `L¹`-Cauchy convergence; see `lem41_MW`) give the existence, the bounds with
`c₀ = 9` and the zero means, with the integrability of `δZ`, `δU` from `eq_dY`, of
`Σ` and `H` from `eq_dX`, and `𝔼 sup |δX|², 𝔼 sup |δY|² < ∞` from `supSize < ⊤`. The fifth
integrand: `|⟨h, Gᵀ u⟩| ≤ ‖G‖ |h| |u|` pointwise and the Cauchy–Schwarz inequality on
`Ω × [0, T] × E` (`lintegral_abs_dotProduct_le`).

Witnesses: three instances of the hypotheses of Lemma 4.3, which are those of all five
propositions, each pointed at the clauses whose integrands it makes nonzero. All three are built
by `affineWindow_pair` over a Lévy driver with `d = 1`, `ν = δ₀` on `ℝ`, `𝒢₀ = ⊥`,
`n = m = 1`, `T = 1`, for the system of Example 5.1(i) with `β₁ = β₂ = 1` and
`σ_c = h_c = 0` (`b = −y`, `σ = −z`, `h = −u`, `f = x`, `g = x`), with `G = 1`, `L = 1`,
`α = β₁ = β₂ = 1` and `λ̲ = λ = 1`. With `M^W`, `M^N` everywhere-càdlàg versions of
`∫_0^t 1_{(0, 1]} dW` and `∫_0^t ∫ 1_{(0, 1]} Ñ(ds, de)`, the tuple
`X = x₀ + a M^W + c M^N`, `Y = y₀ + a' M^W + c' M^N`, `Z = a' 1_{(0, 1]}`, `U = c' 1_{(0, 1]}`
solves the system at `λ = 0` with the forcing `(0, a 1_{(0, 1]}, c 1_{(0, 1]}, 0, Y_1)`, hence
(4.1) at `λ = 1` with the forcing `q = (0, a 1_{(0, 1]}, c 1_{(0, 1]}, 0, Y_1) − Ψ(Θ)`, `Ψ(Θ)` the
coefficient processes along the tuple (`SolvesForced.of_zero_sub_coeff`); `q` is a forcing of the
class of the paper (its jump component `(c + c') 1_{(0, 1]}` is marked predictable), and the
forced diffusion and jump integrands of the solution are `a 1_{(0, 1]}` and `c 1_{(0, 1]}`. Each
witness pairs this solution with the one at the parameters `0`, the zero tuple from the datum
`0`; the difference lies in `ℍ`.

* `Dissertation.Acceptance.A.lem_pert_backward_window_hypotheses` for `eq_bdg4_XZ` and
  `eq_bdg4_XU`: `x₀ = 1`, `a' = c' = 1`, the rest `0`, from the data `1` and `0`. The difference
  is `δX ≡ 1`, `δY = M^W + M^N`, `δZ = δU = 1_{(0, 1]}`; the integrands
  `⟨G δX_{s−}, δZ_s ·⟩` and `⟨G δX_{s−}, δU_s(e)⟩` are `1_{(0, 1]}`, of energy `1` (stated).
* `Dissertation.Acceptance.A.lem_pert_forward_window_hypotheses` for `eq_bdg4_sigmaY` and
  `eq_bdg4_hY`: `a = c = y₀ = 1`, the rest `0`, from the datum `0`. The difference is
  `δX = M^W + M^N`, `δY ≡ 1`, `δZ = δU = 0`, with `λ δσ + δq^σ = 1_{(0, 1]}` and
  `λ δh + δq^h = 1_{(0, 1]}` (`δh` through `coeffJump` at the predictable tuples, almost
  everywhere on `Ω × [0, 1] × ℝ`). The integrand `⟨G (λ δσ_s + q^σ_s) ·, δY_{s−}⟩` is
  `1_{(0, 1]}`, of energy `1`; for every `H` equal almost everywhere to `λ δh + q^h`,
  `⟨G H_s(e), δY_{s−}⟩` has marked energy `1` (stated).
* `Dissertation.Acceptance.A.lem_pert_jump_window_hypotheses` for `eq_bdg4_fifth` and
  `eq_bdg4_fifth_mean`: `c = c' = 1`, the rest `0`, from the datum `0`; the forcings differ by a
  jump-channel term, `q^h = 2 · 1_{(0, 1]}` against `0`. The difference is `δX = δY = M^N`,
  `δZ = 0`, `δU = 1_{(0, 1]}`, with `λ δh + δq^h = 1_{(0, 1]}` almost everywhere. For every `H`
  equal almost everywhere to `λ δh + q^h` (the condition of both clauses, with or without the
  conditions on `H` they add), the fifth integrand `⟨H_s(e), Gᵀ δU_s(e)⟩` has marked energy `1`
  (stated).

The former witness, `lem_pert_forced_hypotheses` (forcings `0` and `q^σ = 1_{(0, 1]}`), showed
only that `δZ` or `λ δσ + δq^σ` has nonzero energy, with the jump terms identically zero.

Verdict: faithful with representation choices (local stochastic integrals for the four
integrals, for the filtration `enlJoint`; the left limits cut to `(0, T]`; `λ δh + q^h` through
representatives, as in (4.15), which include the paper's predictable one; `c_BDG` as every value
at least `c₀`); the first link of each bound is recorded in `scope_note`; the predictability of
the fifth integrand and the zero mean of the fifth term are `eq_bdg4_fifth_mean`.

<!-- spec-review: Dissertation.PaperSpec.A.eq_bdg4_XZ ed839d34f480cba1ea9600d62db2bc6a by=claude-author source=A:eq:bdg4@5d58d75e0ff64d35f9d623ce18ac9506f4664d0ce027e18e70d50e5e24c79b67 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.eq_bdg4_XZ--claude-auditor--2026-10-20T08_55_37Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_bdg4_XZ ed839d34f480cba1ea9600d62db2bc6a by=claude-auditor source=A:eq:bdg4@5d58d75e0ff64d35f9d623ce18ac9506f4664d0ce027e18e70d50e5e24c79b67 -->
<!-- spec-review: Dissertation.PaperSpec.A.eq_bdg4_sigmaY ed839d34f480cba1cb9feae8e68982b0 by=claude-author source=A:eq:bdg4@5d58d75e0ff64d35f9d623ce18ac9506f4664d0ce027e18e70d50e5e24c79b67 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.eq_bdg4_sigmaY--claude-auditor--2026-10-20T08_55_37Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_bdg4_sigmaY ed839d34f480cba1cb9feae8e68982b0 by=claude-auditor source=A:eq:bdg4@5d58d75e0ff64d35f9d623ce18ac9506f4664d0ce027e18e70d50e5e24c79b67 -->
<!-- spec-review: Dissertation.PaperSpec.A.eq_bdg4_XU ed839d34f480cba18a39ea87912f080a by=claude-author source=A:eq:bdg4@5d58d75e0ff64d35f9d623ce18ac9506f4664d0ce027e18e70d50e5e24c79b67 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.eq_bdg4_XU--claude-auditor--2026-10-20T08_55_37Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_bdg4_XU ed839d34f480cba18a39ea87912f080a by=claude-auditor source=A:eq:bdg4@5d58d75e0ff64d35f9d623ce18ac9506f4664d0ce027e18e70d50e5e24c79b67 -->
<!-- spec-review: Dissertation.PaperSpec.A.eq_bdg4_hY ed839d34f480cba11d2a86bd66838ee7 by=claude-author source=A:eq:bdg4@5d58d75e0ff64d35f9d623ce18ac9506f4664d0ce027e18e70d50e5e24c79b67 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.eq_bdg4_hY--claude-auditor--2026-10-20T08_55_37Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_bdg4_hY ed839d34f480cba11d2a86bd66838ee7 by=claude-auditor source=A:eq:bdg4@5d58d75e0ff64d35f9d623ce18ac9506f4664d0ce027e18e70d50e5e24c79b67 -->
<!-- spec-review: Dissertation.PaperSpec.A.eq_bdg4_fifth ed839d34f480cba1bb7df8f3a4d24d8b by=claude-author source=A:eq:bdg4@5d58d75e0ff64d35f9d623ce18ac9506f4664d0ce027e18e70d50e5e24c79b67 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.eq_bdg4_fifth--claude-auditor--2026-10-20T08_55_37Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_bdg4_fifth ed839d34f480cba1bb7df8f3a4d24d8b by=claude-auditor source=A:eq:bdg4@5d58d75e0ff64d35f9d623ce18ac9506f4664d0ce027e18e70d50e5e24c79b67 -->

## The fifth term of (4.17), its predictable integrand and its zero mean: `Dissertation.PaperSpec.A.eq_bdg4_fifth_mean`

Manuscript (proof of Lemma `lem:pert`, Step 1, lines 552–555 and 610–622): the jump covariation
splits through `N = Ñ + dt ν` as
`∫_0^T ∫_E ⟨G (λ δh_t + q^h_t)(e), δU_t(e)⟩ N(dt, de) = ∫_0^T ∫_E ⟨G (λ δh_t + q^h_t)(e), δU_t(e)⟩
Ñ(dt, de) + ∫_0^T ∫_E ⟨λ δh_t(e) + q^h_t(e), Gᵀ δU_t(e)⟩ ν(de) dt`, the first term on the right
being the fifth stochastic term of (4.17); and (lines 610–622) "The four suprema in (4.18) are
therefore integrable, so the supremum criterion applies to those four local martingales. The
fifth has predictable integrand, and by Cauchy–Schwarz `𝔼 ∫_0^T ∫_E |⟨λ δh_t(e) + q^h_t(e),
Gᵀ δU_t(e)⟩| ν(de) dt ≤ ‖G‖ (…)^{1/2} (…)^{1/2} < ∞`. Hence (2.2) applies, and all five terms have
zero expectation." (2.2) (§2, lines 20–24): "the zero-mean property of the compensated integral
reads `𝔼 ∫_0^T ∫_E ψ_s(e) Ñ(ds, de) = 0` whenever `𝔼 ∫_0^T ∫_E |ψ_s(e)| ν(de) ds < ∞`", for
predictable `ψ` (line 14).

Proposition (hypotheses: those of Lemma 4.3, `lem_pert`, verbatim, as in `eq_bdg4_fifth`): there
is `H : Fin n → Ω → ℝ → E → ℝ`, each coordinate `MarkedPredictable (enlJoint 𝒢₀ D h𝒢₀) ν`, equal
`markedEnergyMeasure`-almost everywhere to
`λ (coeffJump(h, Θ¹⁻) − coeffJump(h, Θ²⁻)) + (q^h_1 − q^h_2)` (cut to `[0, T]` by `jumpProc`),
coordinatewise; and for every such `H`, with `ψ_s(e) = ⟨H_s(e), Gᵀ δU_s(e)⟩`: `ψ` is
`MarkedPredictable (enlJoint 𝒢₀ D h𝒢₀) ν`; `∫⁻ ∫⁻_{(0, T] × E} ‖ψ‖ₑ dN dP < ⊤`;
`∫⁻ ∫⁻_{(0, T]} ∫⁻ ‖ψ‖ₑ dν ds dP < ⊤`; and
`∫ (∫_{(0, T] × E} ψ dN − ∫_{(0, T]} ∫_E ψ dν ds) dP = 0`.

Readings:

* The fifth term, read pathwise, is the Poisson integral minus its compensator, as `M²` is in the
  proof of Lemma 4.1 (`lem41_M2_zero_mean`, `lem41_M2_martingale`) and as the paper's own
  splitting through `N = Ñ + dt ν` at lines 552–555 writes it. Both parts are integrable (the
  second and third conjuncts), so the difference is the compensated integral of the general
  theory, and its expectation is the paper's `𝔼 ∫_0^T ∫_E ψ Ñ(ds, de)`; `∫_0^T` is over
  `(0, T]` (Lebesgue-null `{0}`, and `N` charges no fixed time).
* "The fifth has predictable integrand": `ψ` is marked predictable for the filtration of the
  setting (`MarkedPredictable`, the notion used for `δU` and `q^h` in the hypotheses; as for the
  integrand of `M²`, `lem41_M2_integrand`). The integrand `λ δh + q^h` is the paper's expression
  at the predictable tuples, which the paper makes claims about `dt`-a.e.: the proposition states
  that a marked predictable representative of it exists (the first conjunct) and makes its other
  claims for every such representative, as `eq_bdg4_hY` does for the representatives of the
  compensated integral. The representatives agree almost everywhere, and the quantities stated
  depend only on that class (the expectation of the Poisson integral equals that of the
  compensator by (2.1), so changing `H` on a `markedEnergyMeasure`-null set does not change
  them); stating them for every one is the paper's "the" integrand.
* The integrability `𝔼 ∫_0^T ∫_E |ψ| ν(de) dt < ∞` is that of `eq_bdg4_fifth`, at `(0, T]` here
  and for the marked predictable representatives; the finiteness of `𝔼 ∫∫ |ψ| dN`, equal to it
  by (2.1), makes the Poisson integral and so the pathwise difference integrable.
  "All five terms have zero expectation" is, for the fifth, the last conjunct; for the other four
  it is the zero means of `eq_bdg4_XZ`, `eq_bdg4_sigmaY`, `eq_bdg4_XU`, `eq_bdg4_hY` at `t = 0`.
* The filtration is `enlJoint 𝒢₀ D h𝒢₀` (the usual augmentation of `ℱ^{W,N}_t ∨ ℱ₀`), that of the
  hypotheses.
* Not stated: that the fifth term is the stochastic term of (4.17) (it belongs to (4.17),
  `A:eq:Gid-path`).

Proofs: the representative. The tuple `Θ⁻_s = (X_{s−}, Y_{s−}, Z_s, U_s)` cut to `(0, T]` is a
predictable field in the tuple space (`measurable_predictableSigma_tupleAt_leftLim_Ioc`, from the
left limits of adapted paths and the predictable law flow of `LawFlowPredictable.lean`); composed
with the jointly measurable `h` and the canonical representative `lpRep` of `L²(ν; ℝⁿ)`, and cut
to the positive times, it gives a marked predictable integrand equal to `coeffJump(h, Θ⁻)` at
every time of `(0, T]` (`markedPredictable_ite_comp`,
`exists_markedPredictable_coeffJump_leftLim`); with `q^h` marked predictable (`PredForcing`) this
gives `H`, and almost every point of `Ω × [0, T] × E` has its time in `(0, T]`
(`ae_markedEnergyMeasure_mem_Ioc`). For every such `H`: `ψ` is a continuous function of the
marked predictable `(H, δU)`; its energy is finite by comparison with the representative of
`eq_bdg4_fifth` (`markedEnergy_sub_eq_zero_of_ae_eq`, `markedEnergy_add_le`); the integrability
by Cauchy–Schwarz (`lintegral_abs_dotProduct_le`, the bound of `eq_bdg4_fifth`); the Poisson
integral by (2.1) (`aemeasurable_and_lintegral_compensation`); and the zero mean by (2.2)
(`integral_compensated_eq_zero`).

Representation choices, as the blind audit listed them (each harmless): (1) `δh` is the
difference of `coeffJump` at the left-limit tuples `(Θ^{k,−}_s, Law(Θ^{k,−}_s))`, a jointly
measurable representative of `h(s, Θ^{k,−}_s, ·, μ^{k,−}_s)` cut to `[0, T]`, with the law taken
as `lawP2` at every time (the Dirac mass at `0` on a null set of times); (2) the paper's reading of
the Poisson integrand through a `𝒫 ⊗ 𝓔`-measurable representative is made explicit: a marked
predictable `H` equal almost everywhere to `λ δh + q^h` exists, and the conclusions hold for
every such `H`; (3) the fifth term, a compensated integral of an `L¹` (not `L²`) integrand, is
read pathwise as the Poisson integral minus its compensator, with the integrability of both
stated, the meaning under which (2.2) is used; (4) the processes are coordinatewise, the pairing
is the dot product with `Gᵀ δU`, and the marked predictable σ-algebra has no cells at times
`≤ 0` (a null time).

Witness: `Dissertation.Acceptance.A.lem_pert_jump_window_hypotheses`, the third instance of the
(4.18) section (`c = c' = 1`: the forcings differ by the jump-channel term `q^h = 2 · 1_{(0, 1]}`,
and `δU = 1_{(0, 1]}`, `λ δh + δq^h = 1_{(0, 1]}` almost everywhere). For every `H` equal almost
everywhere to `λ δh + q^h`, the fifth integrand `ψ = ⟨H, Gᵀ δU⟩` has marked energy `1` (stated),
so the fifth term is not trivial. The former witness, `lem_pert_forced_hypotheses`, had `q^h = 0`
and `δU = 0`, so the fifth integrand vanished there.

Verdict: faithful with representation choices (those listed above: the fifth term read
pathwise; the integrand through its marked predictable representatives, every one of them).

<!-- spec-review: Dissertation.PaperSpec.A.eq_bdg4_fifth_mean ed839d34f480cba153e1a9d9480bd7ff by=claude-author source=A:eq:bdg4@5d58d75e0ff64d35f9d623ce18ac9506f4664d0ce027e18e70d50e5e24c79b67 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.eq_bdg4_fifth_mean--claude-auditor--2026-10-20T10_34_04Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_bdg4_fifth_mean ed839d34f480cba153e1a9d9480bd7ff by=claude-auditor source=A:eq:bdg4@5d58d75e0ff64d35f9d623ce18ac9506f4664d0ce027e18e70d50e5e24c79b67 -->

## (4.19), the `G`-energy identity in Step 1 of the proof of Lemma 4.3: `Dissertation.PaperSpec.A.eq_Gid`

Manuscript (proof of Lemma `lem:pert`, Step 1, lines 546–632): Itô's product formula gives the
pathwise identity (4.17), whose five stochastic integrals have zero expectation (lines 579–622).
"Taking expectations and dropping the left limits in the drift multipliers (the `dt`-integral
convention above) reduces (4.17) to
`𝔼⟨G δX_T, δY_T⟩ − 𝔼⟨G δξ₀, δY_0⟩ = 𝔼 ∫_0^T [⟨λ δb_t + q^b_t, Gᵀ δY_t⟩
+ ⟨λ δσ_t + q^σ_t, Gᵀ δZ_t⟩_F + ∫_E ⟨λ δh_t(e) + q^h_t(e), Gᵀ δU_t(e)⟩ ν(de)
+ ⟨−λ δf_t − q^f_t, G δX_t⟩] dt`." (4.19)

Proposition: under the hypotheses of Lemma 4.3 (those of `lem_pert`, verbatim):
`⟨G δX_T, δY_T⟩` and `⟨G δξ₀, δY_0⟩` are `P`-integrable; the integrand
`R = (λ δb + q^b) ⬝ Gᵀ δY + ∑_j (λ δσ_{·j} + q^σ_{·j}) ⬝ Gᵀ δZ_{·j}
+ ∫_E (λ δh(e) + q^h(e)) ⬝ Gᵀ δU(e) ν(de) + (−λ δf − q^f) ⬝ G δX` is integrable for `P ⊗ ds`
on `Ω × [0, T]`; and `∫ ⟨G δX_T, δY_T⟩ dP − ∫ ⟨G δξ₀, δY_0⟩ dP = ∫ ∫_{[0, T]} R ds dP`.

Readings:

* The hypotheses, `q = δq`, the coefficient differences and `δh` at the predictable tuples are
  read as in `eq_dX` and `eq_dY`.
* The pairings in coordinates: `⟨u, v⟩ = u ⬝ v`, `Gᵀ` the transposed matrix,
  `⟨A, B⟩_F = ∑_j A_{·j} ⬝ B_{·j}` over the `d` columns (`Gᵀ δZ` column by column), and
  `⟨−λ δf − q^f, G δX⟩` with the vector `−λ δf − q^f`, as printed.
* The expectations are Bochner integrals; the integrability of the two pairings and of `R` on
  `Ω × [0, T]` is stated, so the identity is between the expectations the paper means, and
  `𝔼 ∫_0^T` is `∫ dP` of `∫_{[0, T]} ds`. `δh` enters only through its `ν`-integral at almost
  every `(ω, s)`, so the values of the expression at `s = 0` (see `eq_dX`) do not matter.
* (4.19) is the expectation form; the pathwise identity (4.17) and the bounds (4.18) are separate
  claims (`A:eq:Gid-path`, `A:eq:bdg4`) and are not stated here.

Proof: (4.19) for the difference system (`PairDiff.integral_mulVec_dotProduct_eq`: the bilinear
second-moment identity of two Itô–Lévy processes over the same driver, summed with the weights
`G_{ki}`) at the extensions of `exists_pairDiff`, read on the window `Ω × [0, T]` by Fubini with
the integrability of its integrand (`integrable_gPairing`); the extensions agree with the solutions
on `[0, T]`, and the jump integrand of the representatives agrees with the one at the predictable
tuples (`ae_forcedJump_sub_leftLim_eq`, `ae_ae_of_ae_markedEnergyMeasure`). The implementation
takes the identity directly in expectation form, without (4.17) and (4.18).

Witness: `Dissertation.Acceptance.A.lem_pert_two_data_hypotheses`, the hypotheses of Lemma 4.3.

Verdict: faithful.

<!-- spec-review: Dissertation.PaperSpec.A.eq_Gid ed839d34f480cba187a9b1634afe69c9 by=claude-author source=A:eq:Gid@46e224212d4e8316516a327f1bb7618acbfc1904c3aa6992f40bd866ace4d2b4 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.eq_Gid--claude-auditor--2026-10-19T22_56_14Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_Gid ed839d34f480cba187a9b1634afe69c9 by=claude-auditor source=A:eq:Gid@46e224212d4e8316516a327f1bb7618acbfc1904c3aa6992f40bd866ace4d2b4 -->

## (4.20), the insertion of monotonicity in Step 2 of the proof of Lemma 4.3: `Dissertation.PaperSpec.A.eq_intmono`

Manuscript (proof of Lemma `lem:pert`, Step 2, lines 634–646): "In the `h`-channel `δh_t` is
evaluated at the predictable tuples `(Θ^{k,−}_t, μ^{k,−}_t)`, which agree with `(Θ^k_t, μ^k_t)`
for `dt`-a.e. `t` by Lemma A.1. Assumption 2.5, applied at the common input pair
`(Θ¹_t, μ¹_t), (Θ²_t, μ²_t)`, therefore bounds the unperturbed part of the integrand of (4.19):
`λ 𝔼[⟨δb_t, Gᵀ δY_t⟩ + ⟨δσ_t, Gᵀ δZ_t⟩_F + ∫_E ⟨δh_t(e), Gᵀ δU_t(e)⟩ ν(de) + ⟨−δf_t, G δX_t⟩]
≤ −λ β₁ 𝔼[|Gᵀ δY_t|² + |Gᵀ δZ_t|²_F + ‖Gᵀ δU_t‖²_{L²(ν)}] − λ β₂ 𝔼|G δX_t|²`." (4.20)

Proposition: under the hypotheses of Lemma 4.3 (those of `lem_pert`, verbatim), at almost every
`t ∈ [0, T]`: the pairing `⟨δb_t, GX Gᵀ δY_t⟩ + ⟨δσ_t, GZ Gᵀ δZ_t⟩
+ ∫_E ⟨δh_t(e), GX Gᵀ δU_t(e)⟩ ν(de) + ⟨−δf_t, GX G δX_t⟩` is `P`-integrable, and `λ` times its
expectation is at most `−λ β₁ ∫ (‖GX Gᵀ δY_t‖² + ‖GZ Gᵀ δZ_t‖² + ‖GU Gᵀ ν δU_t‖²) dP
− λ β₂ ∫ ‖GX G δX_t‖² dP`, with `δψ_t = ψ(t, Θ¹_t, Law Θ¹_t) − ψ(t, Θ²_t, Law Θ²_t)` for
`ψ = b, σ, f`, `Θ^k_t = tupleAt`, `δh_t` the same at the predictable tuples (`tupleAt` of the left
limits) and their laws, and `δX_t, δY_t, δZ_t, δU_t` the channels of `Θ¹_t − Θ²_t`.

Readings:

* The integrand is that of (2.7) (`pairing27`, reviewed with Assumption 2.5) at the pair, in the
  printed order of its terms and with `h` at the predictable tuples; the operators `GX`, `GZ`,
  `GU` and the right side are those of `Mono27At`, times `λ`.
* "At `dt`-a.e. `t`": almost every `t ∈ [0, T]`. The integrability of the pairing is stated, so
  its expectation is the one meant; the expectations on the right are Bochner integrals of
  nonnegative functions, as in `Mono27At`.
* `μ^{k,−}_t` is the law `lawP2` of the predictable tuple, not a fixed Borel version; the two
  agree for almost every `t` (Lemma A.1), and the claim is made at almost every `t`.

Proof: at almost every `t` the tuples are diagonal inputs at `t` (strongly `ℱ_t`-measurable,
through the extensions of `exists_solvesForcedInt`, and square integrable), Assumption 2.5 at `t`
bounds the expectation of `pairing27`, and the predictable tuples agree with the tuples almost
surely (`PaperWeakTuple.ae_ae_tupleAt_leftLimProc_eq`), hence also their laws; then multiply by
`λ ≥ 0`.

Witness: `Dissertation.Acceptance.A.lem_pert_two_data_hypotheses`, the hypotheses of Lemma 4.3.

Verdict: faithful.

<!-- spec-review: Dissertation.PaperSpec.A.eq_intmono ed839d34f480cba14dbfddebc754cdd1 by=claude-author source=A:eq:intmono@150f4be88223dcfe3fe2768079cc4c41f3b4f9d82be386a911848afcc85a0509 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.eq_intmono--claude-auditor--2026-10-19T22_56_20Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_intmono ed839d34f480cba14dbfddebc754cdd1 by=claude-auditor source=A:eq:intmono@150f4be88223dcfe3fe2768079cc4c41f3b4f9d82be386a911848afcc85a0509 -->

## (4.21), the terminal side in Step 2 of the proof of Lemma 4.3: `Dissertation.PaperSpec.A.eq_termmono`

Manuscript (proof of Lemma `lem:pert`, Step 2, lines 648–656): "The terminal side of (4.19) is
bounded by the terminal monotonicity of Assumption 2.5:
`𝔼⟨G δX_T, δY_T⟩ = λ 𝔼⟨G δX_T, δg_T⟩ + 𝔼⟨G δX_T, q^g_T⟩
≥ λ α 𝔼|G δX_T|² − |𝔼⟨G δX_T, q^g_T⟩|`." (4.21)

Proposition: under the hypotheses of Lemma 4.3 (those of `lem_pert`, verbatim): the pairings
`⟨G δX_T, δY_T⟩`, `⟨G δX_T, δg_T⟩` and `⟨G δX_T, q^g_T⟩` are `P`-integrable;
`∫ ⟨G δX_T, δY_T⟩ = λ ∫ ⟨G δX_T, δg_T⟩ + ∫ ⟨G δX_T, q^g_T⟩`; and
`λ α ∫ |G δX_T|² − |∫ ⟨G δX_T, q^g_T⟩| ≤ λ ∫ ⟨G δX_T, δg_T⟩ + ∫ ⟨G δX_T, q^g_T⟩`.

Readings:

* The chain `= … ≥ …` is the conjunction of the equation and the inequality between its middle
  and right members.
* `δg_T = g(X¹_T, Law X¹_T) − g(X²_T, Law X²_T)` through `terminalVal`, `q^g = δq^g`,
  `|G δX_T|² = (G δX_T) ⬝ (G δX_T)`; the expectations are Bochner integrals, with the
  integrability of the three pairings stated.

Proof: `δY_T = λ δg_T + q^g_T` almost surely (the backward equation at `T`) and linearity; the
terminal monotonicity of Assumption 2.5 at the pair (`PairDiff.monoT`); `λ ≥ 0` and
`−|x| ≤ x`.

Witness: `Dissertation.Acceptance.A.lem_pert_two_data_hypotheses`, the hypotheses of Lemma 4.3.

Verdict: faithful.

<!-- spec-review: Dissertation.PaperSpec.A.eq_termmono ed839d34f480cba1ea261f16df305b5f by=claude-author source=A:eq:termmono@6bab7182201b7abad4829837a498ea8162e4f6bfdba1422c65464bb9053a79d0 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.eq_termmono--claude-auditor--2026-10-19T22_56_25Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_termmono ed839d34f480cba1ea261f16df305b5f by=claude-auditor source=A:eq:termmono@6bab7182201b7abad4829837a498ea8162e4f6bfdba1422c65464bb9053a79d0 -->

## (4.20) and (4.21) inserted into (4.19), in Step 2 of the proof of Lemma 4.3: `Dissertation.PaperSpec.A.eq_coerc_insert`

Manuscript (proof of Lemma `lem:pert`, Step 2, lines 669–680, between the region of (4.21) and
that of (4.22), which the inventory pins at lines 683–693; the clause belongs to `A:eq:coerc`):
"Inserting (4.20) and (4.21) into (4.19) gives
`λ α 𝔼|G δX_T|² − |𝔼⟨G δX_T, q^g_T⟩| − 𝔼⟨G δξ₀, δY_0⟩
≤ −λ β₁ 𝔼 ∫_0^T [|Gᵀ δY_t|² + |Gᵀ δZ_t|²_F + ‖Gᵀ δU_t‖²] dt − λ β₂ 𝔼 ∫_0^T |G δX_t|² dt
+ 𝔼 ∫_0^T (⟨q^b_t, Gᵀ δY_t⟩ + ⟨q^σ_t, Gᵀ δZ_t⟩_F + ⟨−q^f_t, G δX_t⟩
+ ∫_E ⟨q^h_t(e), Gᵀ δU_t(e)⟩ ν(de)) dt`."

Proposition: under the hypotheses of Lemma 4.3 (those of `lem_pert` and of `eq_coerc`,
verbatim): the integrands `(G δX_T) ⬝ (G δX_T)`, `(G δX_T) ⬝ q^g_T` and `(G δξ₀) ⬝ δY_0` are
`P`-integrable; on `Ω × [0, T]`, for `P ⊗ ds`, the integrands `(G δX) ⬝ (G δX)`,
`B = (Gᵀ δY) ⬝ (Gᵀ δY) + ∑_j (Gᵀ δZ_{·j}) ⬝ (Gᵀ δZ_{·j}) + ∫_E (Gᵀ δU(e)) ⬝ (Gᵀ δU(e)) ν(de)` and
`F = q^b ⬝ Gᵀ δY + ∑_j q^σ_{·j} ⬝ Gᵀ δZ_{·j} + (−q^f) ⬝ G δX + ∫_E q^h(e) ⬝ Gᵀ δU(e) ν(de)` are
integrable; on `(Ω × [0, T]) × E`, for `(P ⊗ ds) ⊗ ν`, the integrands `(Gᵀ δU) ⬝ (Gᵀ δU)` and
`q^h ⬝ Gᵀ δU` are integrable; and
`λ α ∫ (G δX_T) ⬝ (G δX_T) dP − |∫ (G δX_T) ⬝ q^g_T dP| − ∫ (G δξ₀) ⬝ δY_0 dP
≤ −λ β₁ ∫ ∫_{[0, T]} B ds dP − λ β₂ ∫ ∫_{[0, T]} (G δX) ⬝ (G δX) ds dP + ∫ ∫_{[0, T]} F ds dP`.

Readings:

* The hypotheses are those in force at this point of Step 2, the hypotheses of Lemma 4.3, written
  as in `eq_coerc` (reviewed with Lemma 4.3); `q = δq`, the differences of the forcings, and
  `δξ₀ = ξ₀¹ − ξ₀²`.
* The display, term by term and in the printed order: `λ α 𝔼|G δX_T|²`, `−|𝔼⟨G δX_T, q^g_T⟩|`
  and `−𝔼⟨G δξ₀, δY_0⟩` on the left, the last signed, as printed; on the right the two coercive
  terms with their factors `−λ β₁` and `−λ β₂`, and the signed forcing pairing (no absolute
  values, as printed), whose third term is `⟨−q^f, G δX⟩` with the vector `−q^f`, as in (4.19).
  The pairings are in coordinates as in `eq_Gid`: `⟨u, v⟩ = u ⬝ v`, `Gᵀ` the transpose,
  `⟨A, B⟩_F = ∑_j A_{·j} ⬝ B_{·j}` over the `d` columns, so `|Gᵀ δZ|²_F` is
  `∑_j (Gᵀ δZ_{·j}) ⬝ (Gᵀ δZ_{·j})`; `|v|² = v ⬝ v`; and `‖Gᵀ δU_t‖²` is the `L²(ν)` norm,
  `∫_E |Gᵀ δU_t(e)|² ν(de)`. The blocks are written as in `eq_coerc`.
* `𝔼 ∫_0^T` is `∫ dP` of `∫_{[0, T]} ds`, Bochner integrals. The finiteness of every expectation
  the display uses is stated: the integrability of the three integrands on `Ω` and of the three on
  `Ω × [0, T]`. Two of these contain a `ν`-integral, `‖Gᵀ δU‖²` and `∫_E ⟨q^h, Gᵀ δU⟩ dν`; the
  integrability of their integrands on `Ω × [0, T] × E` is stated too, so that at almost every
  `(ω, t)` they are integrals of integrable functions. No side of the inequality is a junk value.
* "Inserting (4.20) and (4.21) into (4.19) gives": the display is the conclusion; how (4.20), a
  bound at almost every `t`, is integrated over `[0, T]`, and how the chain of (4.21) is used, is
  the proof's. The display involves neither `η` nor `𝒦`, defined just before it.

Proof: (4.19) for the difference system (`PairDiff.integral_mulVec_dotProduct_eq`, which proves
`eq_Gid`), its integrand split into `λ` times the coefficient part and the forcing part; the
interior monotonicity at the pair at almost every `t` (`PairDiff.mono`, the content of (4.20))
integrated over `[0, T]` and multiplied by `λ > 0`; the terminal identity
`δY_T = λ δg_T + q^g_T` and the terminal monotonicity (`PairDiff.monoT`, which proves
`eq_termmono`); and `−|x| ≤ x` (`PairDiff.blocks_le_pairings`). All at the extensions of
`exists_pairDiff`, which agree with the solutions on `[0, T]`, read on the window by Fubini.
The integrability from the square integrability of the coordinates on `Ω`, on the window and on
the marked window (`integrable_dotProduct_of_memLp`, `memLp_mulVec`, `integrable_gPairing`,
`integrable_blockX_window`, `integrable_blockY_window`).

Witness: `Dissertation.Acceptance.A.lem_pert_two_data_hypotheses`, the hypotheses of Lemma 4.3.

Verdict: faithful.

<!-- spec-review: Dissertation.PaperSpec.A.eq_coerc_insert ed839d34f480cba19e2302a704da248e by=claude-author source=A:eq:coerc@28fd9c283ce2f0feb20f2c6130e074c16ed3aaced00c1a84f6c2847774c3221c -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.eq_coerc_insert--claude-auditor--2026-10-20T04_27_54Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_coerc_insert ed839d34f480cba19e2302a704da248e by=claude-auditor source=A:eq:coerc@28fd9c283ce2f0feb20f2c6130e074c16ed3aaced00c1a84f6c2847774c3221c -->

## (4.22), the coercivity bound in Step 2 of the proof of Lemma 4.3: `Dissertation.PaperSpec.A.eq_coerc`, `eq_coerc_blocks`

Manuscript (proof of Lemma `lem:pert`, Step 2, lines 657–695): with `P` as in (4.14),
"`N' := 𝔼|δX_T|² + 𝔼|δY_0|² + 𝔼 ∫_0^T (|δX_t|² + |δY_t|² + |δZ_t|²_F + ‖δU_t‖²) dt`,
`𝒦 := η N' + (‖G‖²/(4η)) P`, `η > 0`. Inserting (4.20) and (4.21) into (4.19) gives […].
Rearranging, and applying Young's inequality with `|Gᵀ v| ≤ ‖G‖ |v|` and `|G v| ≤ ‖G‖ |v|`, gives
`λ α 𝔼|G δX_T|² + λ β₂ 𝔼 ∫_0^T |G δX_t|² dt
+ λ β₁ 𝔼 ∫_0^T [|Gᵀ δY_t|² + |Gᵀ δZ_t|²_F + ‖Gᵀ δU_t‖²] dt
≤ |𝔼⟨G δξ₀, δY_0⟩| + |𝔼⟨G δX_T, q^g_T⟩| + 𝔼 ∫_0^T (|⟨q^b, Gᵀ δY⟩| + |⟨q^σ, Gᵀ δZ⟩_F|) dt
+ 𝔼 ∫_0^T (|∫_E ⟨q^h(e), Gᵀ δU(e)⟩ ν(de)| + |⟨q^f, G δX⟩|) dt ≤ 𝒦`." (4.22) And, after the
display (lines 694–695, outside the region the inventory pins, lines 683–693): "Each coercive
block present on the left of (4.22) is therefore at most `𝒦`."

Propositions:

* `eq_coerc`: under the hypotheses of Lemma 4.3 (those of `lem_pert`, verbatim): `N' ≠ ∞`, with
  `N' = ∫⁻ |δX_T|² + ∫⁻ |δY_0|² + (∑ energy(δX_i) + ∑ energy(δY_k) + ∑ energy(δZ_{kj})
  + ∑ markedEnergy(δU_k))`; `P ≠ ∞`, with `P = dataSize` of the differences; the left side of
  (4.22) is at most the sum `M` of the six pairings in absolute value; and for every `η > 0`,
  `M ≤ η N'.toReal + (‖GX G‖²/(4η)) P.toReal`.
* `eq_coerc_blocks`: under the same hypotheses, verbatim, for every `η > 0` each of the three
  blocks of the left side of (4.22), `λ α ∫ (G δX_T) ⬝ᵥ (G δX_T) dP`,
  `λ β₂ ∫ ∫_{[0, T]} (G δX) ⬝ᵥ (G δX) ds dP` and
  `λ β₁ ∫ ∫_{[0, T]} [(Gᵀ δY) ⬝ᵥ (Gᵀ δY) + ∑_j (Gᵀ δZ_j) ⬝ᵥ (Gᵀ δZ_j)
  + ∫_E (Gᵀ δU(e)) ⬝ᵥ (Gᵀ δU(e)) ν(de)] ds dP`, written as in `eq_coerc`, is at most
  `η N'.toReal + (‖GX G‖²/(4η)) P.toReal`, with `N'` and `P` as in `eq_coerc`.

Readings:

* `N'` is in `[0, ∞]` (lower integrals, the energies on `[0, T]`) and `P = dataSize`, reviewed
  with Theorem 3.1; their finiteness is stated, so the real values in `𝒦` are the paper's.
* `‖G‖` is the operator norm of `x ↦ G x` between Euclidean spaces (`‖GX G‖`, as in the
  constants of Lemma 4.3); it is also that of `Gᵀ`.
* The blocks and pairings are in coordinates as in `eq_Gid`; `𝔼 ∫_0^T` is `∫ dP` of
  `∫_{[0, T]} ds` (Bochner integrals of functions integrable on the window, shown in the proof),
  and `|⟨q^σ, Gᵀ δZ⟩_F|` is the absolute value of the Frobenius pairing. `η` is quantified for the
  second inequality only, the first not involving it; `𝒦` is defined for each `η > 0`.
* The sentence after (4.22) is `eq_coerc_blocks`. A "coercive block" is one of the three
  summands of the left side of (4.22), with its factor `λ α`, `λ β₂` or `λ β₁`; "present" refers
  to the blocks whose constant is positive (Assumption 2.5 allows `α`, `β₁` or `β₂` to vanish).
  The proposition bounds all three: a block whose constant vanishes is `0 ≤ 𝒦`, so the printed
  claim, for the blocks present, is the case of the positive constants. `𝒦` is quantified as in
  `eq_coerc`, for every `η > 0`, and the hypotheses are those of `eq_coerc` (Lemma 4.3),
  verbatim. "Therefore": each block is nonnegative (`λ > 0`, the constants `≥ 0`, integrands
  of squares), hence at most the left side of (4.22), hence at most `𝒦`.

Proof: the first inequality from (4.19) for the difference system, with the interior and
terminal monotonicity at the pair inserted and `x ≤ |x|` (`PairDiff.blocks_le_abs_pairings`, at
`λ > 0`); the second by Young's inequality with `|G x|² ≤ ‖G‖² |x|²` and its transpose, pairing
by pairing (`abs_initial_pairing_le`, `abs_terminal_forcing_le`, `integral_abs_forcing_le`);
finiteness from the difference system (square-integrable terminal and initial values, finite
energies) and the forcings (`Forcing.dataSize_ne_top_of_memLp`); all at the extensions of
`exists_pairDiff`, which agree with the solutions on `[0, T]`. `eq_coerc_blocks` from
`eq_coerc`: `λ ≥ λ̲ > 0`, `α, β₁, β₂ ≥ 0` (`Assumption25.constants`), and the integrands of the
blocks are sums of `v ⬝ᵥ v ≥ 0`, so each block is nonnegative and at most the sum of the three,
which is at most `M ≤ 𝒦`.

Witness: `Dissertation.Acceptance.A.lem_pert_two_data_hypotheses`, the hypotheses of Lemma 4.3,
for both propositions.

Verdict: faithful, both.

<!-- spec-review: Dissertation.PaperSpec.A.eq_coerc ed839d34f480cba1763b5cdd464a968d by=claude-author source=A:eq:coerc@28fd9c283ce2f0feb20f2c6130e074c16ed3aaced00c1a84f6c2847774c3221c -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.eq_coerc--claude-auditor--2026-10-19T22_56_33Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_coerc ed839d34f480cba1763b5cdd464a968d by=claude-auditor source=A:eq:coerc@28fd9c283ce2f0feb20f2c6130e074c16ed3aaced00c1a84f6c2847774c3221c -->
<!-- spec-review: Dissertation.PaperSpec.A.eq_coerc_blocks ed839d34f480cba17bd256e67c544535 by=claude-author source=A:eq:coerc@28fd9c283ce2f0feb20f2c6130e074c16ed3aaced00c1a84f6c2847774c3221c -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.eq_coerc_blocks--claude-auditor--2026-10-20T02_03_19Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_coerc_blocks ed839d34f480cba17bd256e67c544535 by=claude-auditor source=A:eq:coerc@28fd9c283ce2f0feb20f2c6130e074c16ed3aaced00c1a84f6c2847774c3221c -->

## (4.23), the forward estimate in Step 3 of the proof of Lemma 4.3: `Dissertation.PaperSpec.A.eq_fwd`

Manuscript (proof of Lemma `lem:pert`, Step 3, lines 697–714): "Fix `t ≤ T` and integrate (4.15)
over `[0, s]`, `s ≤ t`, with `δX_0 = δξ₀`. Squaring, taking the supremum over `s` and
expectations, Cauchy–Schwarz on the drift, BDG on the two martingales and Assumption 2.3 give
`𝔼 sup_{s ≤ t} |δX_s|² ≤ C(𝔼|δξ₀|² + 𝔼 ∫_0^t (|δb_s|² + |δσ_s|²_F + ‖δh_s‖²) ds + P) ≤ …
≤ C(∫_0^t 𝔼 sup_{r ≤ s} |δX_r|² ds + 𝔼 ∫_0^T (|δY_s|² + |δZ_s|²_F + ‖δU_s‖²) ds + P)`. The map
`t ↦ 𝔼 sup_{s ≤ t} |δX_s|²` is nondecreasing and finite, since `Θ¹ − Θ² ∈ ℍ`, so Grönwall gives
(4.23) `𝔼 sup_{t ≤ T} |δX_t|² ≤ C(𝔼 ∫_0^T (|δY_t|² + |δZ_t|²_F + ‖δU_t‖²) dt + P)`." Here `P` is
the data size of (4.14) of the differences of the data, and `C` follows the convention of §4: a
positive constant depending only on `T, L, ‖G‖, c_G, α, β₁, β₂` and `c_BDG`.

Proposition: `∃ K` of `(T, L, ‖G‖, c_G, α, β₁, β₂)` such that, in the standing setting and under
the hypotheses of Lemma 4.3 (those of `lem_pert`, verbatim),
`∫⁻ sup_{t ∈ [0, T]} |δX_t|² ≤ ofReal(C) (∑_k energy(δY_k) + ∑_{k, j} energy(δZ_{kj})
+ ∑_k markedEnergy(δU_k) + dataSize(δξ₀, δq^b, δq^σ, δq^h, δq^f, δq^g))` with
`C = K(T, L, ‖GX G‖, s_min(G)⁻², α, β₁, β₂)`.

Readings:

* The hypotheses are those in force at Step 3, the hypotheses of Lemma 4.3, written as in
  `lem_pert` (reviewed with Lemma 4.3); `P` is `dataSize` (reviewed with Theorem 3.1) of the
  differences of the initial data and of the forcings.
* The constant: `K` is chosen before everything else, as a function of exactly the parameters of
  the §4 convention, `T, L, ‖G‖, c_G, α, β₁, β₂` (`c_BDG` is a universal number, so a function of
  these covers a dependence on it), with `c_G = s_min(G)⁻²`. No other dependence is stated at
  (4.23), and Step 3 uses `λ` only through `λ ∈ [0, 1]` (in
  `|λ δψ + q^ψ|² ≤ 2|δψ|² + 2|q^ψ|²`), so `C` depends neither on `λ` nor on the lower bound `λ̲`
  of Lemma 4.3, which stays among the hypotheses, where it only restricts `λ` to `(0, 1]`.
  `ofReal` reads a negative value as `0`; since `K` is existential and the right side grows with
  `C`, this is the reading with `C ≥ 0`.
* The expectations are lower integrals in `[0, ∞]`: `𝔼 sup_{t ≤ T} |δX_t|²` is `∫⁻` of the
  supremum over `t ∈ [0, T]` of `esq`, and `𝔼 ∫_0^T (|δY|² + |δZ|²_F + ‖δU‖²)` the energies on
  `[0, T]`, coordinatewise. The bound says nothing when the right side is infinite; it is finite
  under the hypotheses.
* The displays at `t ≤ T` and the Grönwall argument are steps of the proof; they are not stated.

Proof: `K = c_X(T, 10 (2L)²)` (`fwdSupConst`), a function of `T` and `L`: at the extensions of
`exists_pairDiff`, which agree with the solutions on `[0, T]`, the difference system satisfies
`𝔼 sup |δX|² ≤ 3 𝔼|δξ₀|² + 3T 𝔼 ∫ |λ δb + q^b|² + 12 𝔼 ∫ (|λ δσ + q^σ|²_F + ‖λ δh + q^h‖²)`
(`PairDiff.lintegral_biSup_fwd_le`, the `S²` bound of Lemma 4.1 for each forward coordinate), the
rate bound `|λ x + q|² ≤ 2|x|² + 2|q|²` with (3.2) (`PairDiff.rateEnergy_le`), and the forward
estimate `𝔼|δX_T|² + 𝔼 ∫_0^T |δX|² ≤ k_F (J + P)` of the closure step (`PairDiff.forward_le`, a
weighted energy bound in place of Grönwall); `PairDiff.lintegral_biSup_fwd_le_energy` assembles
them.

Witness: `Dissertation.Acceptance.A.lem_pert_two_data_hypotheses`, the hypotheses of Lemma 4.3
(reviewed with Lemma 4.3).

Verdict: faithful.

<!-- spec-review: Dissertation.PaperSpec.A.eq_fwd ed839d34f480cba1e1eabbb5a5cd78ba by=claude-author source=A:eq:fwd@ee1691dc39d0f4cefa77ed2bd65bf23b9082b6eaf7bce69caf875dc14c06ae8f -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.eq_fwd--claude-auditor--2026-10-20T02_03_32Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_fwd ed839d34f480cba1e1eabbb5a5cd78ba by=claude-auditor source=A:eq:fwd@ee1691dc39d0f4cefa77ed2bd65bf23b9082b6eaf7bce69caf875dc14c06ae8f -->

## The chain before (4.23), Step 3 of the proof of Lemma 4.3: `Dissertation.PaperSpec.A.eq_fwd_chain`

Manuscript (proof of Lemma `lem:pert`, Step 3, lines 697–711), with `P` the data size and `δψ`,
`δh` as defined at lines 511–526 ("`δψ_t := ψ(t, Θ¹_t, μ¹_t) − ψ(t, Θ²_t, μ²_t)`, … with `δh`
evaluated at the predictable tuples `(Θ^{k,−}_t, μ^{k,−}_t)`"): "Fix `t ≤ T` and integrate
(4.15) over `[0, s]`, `s ≤ t`, with `δX_0 = δξ₀`. Squaring, taking the supremum over `s` and
expectations, Cauchy–Schwarz on the drift, BDG on the two martingales and Assumption 2.3 give
`𝔼 sup_{s ≤ t} |δX_s|² ≤ C(𝔼|δξ₀|² + 𝔼 ∫_0^t (|δb_s|² + |δσ_s|²_F + ‖δh_s‖²) ds + P)
≤ C(𝔼|δξ₀|² + 𝔼 ∫_0^t (|δX_s|² + |δY_s|² + |δZ_s|²_F + ‖δU_s‖²) ds + P)
≤ C(∫_0^t 𝔼 sup_{r ≤ s} |δX_r|² ds + 𝔼 ∫_0^T (|δY_s|² + |δZ_s|²_F + ‖δU_s‖²) ds + P)`. The map
`t ↦ 𝔼 sup_{s ≤ t} |δX_s|²` is nondecreasing and finite, since `Θ¹ − Θ² ∈ ℍ`, so Grönwall gives
(4.23)". The chain and the sentence lie before the pinned region of `A:eq:fwd` (lines 712–714).

Proposition: `∃ K₁ K₂ K₃` of `(T, L, ‖G‖, c_G, α, β₁, β₂)` such that, under the hypotheses of
Lemma 4.3 (those of `lem_pert`, verbatim), with `C_i = K_i(T, L, ‖GX G‖, s_min(G)⁻², α, β₁, β₂)`:
for every `t ∈ [0, T]`,
`∫⁻ sup_{s ∈ [0, t]} |δX_s|² ≤ ofReal(C₁) (∫⁻ |δξ₀|² + (∑_i energy_t(δb_i)
+ ∑_{i, j} energy_t(δσ_{ij}) + ∑_i markedEnergy_t(δh_i)) + P)`,
`ofReal(C₁) (…) ≤ ofReal(C₂) (∫⁻ |δξ₀|² + (∑_i energy_t(δX_i) + ∑_k energy_t(δY_k)
+ ∑_{k, j} energy_t(δZ_{kj}) + ∑_k markedEnergy_t(δU_k)) + P)` and
`ofReal(C₂) (…) ≤ ofReal(C₃) (∫_{[0, t]} ∫⁻ sup_{r ∈ [0, s]} |δX_r|² ds + (∑_k energy_T(δY_k)
+ ∑_{k, j} energy_T(δZ_{kj}) + ∑_k markedEnergy_T(δU_k)) + P)`; `t ↦ ∫⁻ sup_{s ∈ [0, t]} |δX_s|²`
is monotone on `[0, T]`; and it is finite at every `t ∈ [0, T]`. Here `energy_t`,
`markedEnergy_t` are the energies on `[0, t]`, `P = dataSize` of the differences of the data,
`δb`, `δσ` the differences of `driftProc`, `diffusionProc`, and `δh_i` that of
`jumpProc T (coeffJump P T C (leftLimProc X^k) (leftLimProc Y^k) Z^k U^k)`.

Readings:

* The hypotheses are those in force at Step 3, as for (4.23). The constants: each link has its
  `C`, chosen before everything else as a function of the parameters of the §4 convention, as for
  (4.23); in particular `C` does not depend on `t`, which is fixed after it ("Fix `t ≤ T`"), nor
  on `λ` or `λ̲`. `ofReal` and the reading with `C ≥ 0` are as there.
* The links are stated as printed, as three inequalities between consecutive members. `𝔼|δξ₀|²`
  is `∫⁻ esq` of the difference of the initial data; `𝔼 ∫_0^t` is over `[0, t]`, in `[0, ∞]`
  (`energy`, `markedEnergy` at the horizon `t`); `∫_0^t 𝔼 sup_{r ≤ s} |δX_r|² ds` is the
  time-outer integral over `[0, t]` of the lower integral of the running supremum, as printed;
  the last link's `𝔼 ∫_0^T` is at the horizon `T`.
* `δb_s`, `δσ_s` are the coefficient differences at `(Θᵏ_s, μᵏ_s)`, `δh_s` the jump coefficient
  difference at the predictable tuples (lines 519–523), through `coeffJump` of the left limits,
  as in Theorem 3.3 (`eq_uniq_coeff`); `λ` and `q` do not appear in the first link, as printed
  (the forcings enter through `P`).
* "Nondecreasing and finite": `MonotoneOn` on `[0, T]` and `< ⊤` at every `t ∈ [0, T]`. "Since
  `Θ¹ − Θ² ∈ ℍ`" is the reason, the hypothesis `supSize(Θ¹ − Θ²) < ∞`. Grönwall and (4.23) are
  the next step, stated by `eq_fwd`.
* The section of (4.23) records the displays at `t ≤ T` as steps of the proof, not stated; they
  are stated here.

Proof: `K₁ = 2(3T + 12) + 3`, `K₂ = K₁ (10 (2L)² + 1)`, `K₃ = 2K₂`. At the extensions of
`exists_pairDiff`, which agree with the solutions on `[0, T]`: the forward coordinates of the
difference system solve on `[0, t]` the forward equation with integrands restricted to `[0, t]`
(`LinearFSDEJ.truncate`), so the `S²` bound of Lemma 4.1 holds on `[0, t]`
(`LinearFSDEJ.lintegral_biSup_sq_le_at`, `3 𝔼|δξ₀|² + 3t 𝔼 ∫_0^t |λ δb + q^b|²
+ 12 𝔼 ∫_0^t (|λ δσ + q^σ|²_F + ‖λ δh + q^h‖²)`); with `|λx + q|² ≤ 2|x|² + 2|q|²` on `[0, t]`
(`PairDiff.realisedEnergy_le_at`, the coefficient differences being jointly measurable because
`λ ≥ λ̲ > 0`), `t ≤ T` and the forcings' energies on `[0, t]` at most `P`, this is the first link.
The jump coefficient at the predictable tuples agrees with the representatives almost everywhere
on `Ω × [0, T] × E` (`ae_forcedJump_sub_leftLim_eq`, divided by `λ ≠ 0`), so its marked energy on
`[0, t]` is theirs (`markedEnergy_congr_ae_of_le`). The second link is (3.2) integrated over
`[0, t]` (`PairDiff.coeffEnergy_le_at`, `K = 10 (2L)²`), the third
`𝔼 ∫_0^t |δX_s|² ds ≤ ∫_0^t 𝔼 sup_{r ≤ s} |δX_r|² ds` (`PairDiff.energy_le_lintegral_biSup`),
`𝔼|δξ₀|² ≤ P` and the energies on `[0, t]` at most those on `[0, T]`. The map is monotone because
the suprema grow with `t`, and finite because it is at most `𝔼 sup_{t ≤ T} |δX_t|² ≤ supSize`.

Witness: `Dissertation.Acceptance.A.lem_pert_backward_window_hypotheses` (from `affineWindow_pair`
with `x₀ = 1`, `a = c = y₀ = 0`, `a' = c' = 1`): over a Lévy driver with `d = 1`, `ν = δ₀`,
`𝒢₀ = ⊥`, `n = m = 1`, `T = 1`, the system of Example 5.1(i) with `β₁ = β₂ = 1`,
`σ_c = h_c = 0` (`b = −y`, `σ = −z`, `h = −u`, `f = x`, `g = x`) with (2.3) and Assumptions
2.3–2.5 at `L = 1`, `G = 1`, `α = β₁ = β₂ = 1`; `λ̲ = λ = 1`; two solutions of (4.1) for
forcings of the class of the paper, from the initial data `1` and `0`, whose difference lies in
`ℍ` and is `δX ≡ 1`, `δY = M^W + M^N`, `δZ = δU = 1_{(0, 1]}` (the energies of
`⟨G δX_{s−}, δZ_s⟩` and `⟨G δX_{s−}, δU_s⟩` are `1`, stated). By hand, at every `t`,
`𝔼 sup_{s ≤ t} |δX_s|² = 𝔼|δξ₀|² = 1`, the map is constant, and `δb = −δY`, `δσ = −δZ`,
`δh = −δU` and `δZ, δU` are nonzero on `(0, t]`: every member of the chain is positive.

Verdict: faithful.

<!-- spec-review: Dissertation.PaperSpec.A.eq_fwd_chain ed839d34f480cba15b2aba22478deb02 by=claude-author source=A:eq:fwd@ee1691dc39d0f4cefa77ed2bd65bf23b9082b6eaf7bce69caf875dc14c06ae8f -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.eq_fwd_chain--claude-auditor--2026-10-20T15_31_29Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_fwd_chain ed839d34f480cba15b2aba22478deb02 by=claude-auditor source=A:eq:fwd@ee1691dc39d0f4cefa77ed2bd65bf23b9082b6eaf7bce69caf875dc14c06ae8f -->

## (4.24), Itô's formula in Step 4 of the proof of Lemma 4.3: `Dissertation.PaperSpec.A.eq_bwdito`

Manuscript (proof of Lemma `lem:pert`, Step 4, lines 716–725): "Itô's formula applied to
`e^{κt} |δY_t|²` gives, for `κ > 0`, (4.24) `𝔼 e^{κt} |δY_t|² + 𝔼 ∫_t^T e^{κs} (κ |δY_s|²
+ |δZ_s|²_F + ‖δU_s‖²_{L²(ν)}) ds ≤ 𝔼 e^{κT} |λ δg_T + q^g_T|² + 2 𝔼 ∫_t^T e^{κs}
⟨δY_s, λ δf_s + q^f_s⟩ ds`." The proof then inserts (4.25) under `∫_t^T e^{κs} … ds` and reads
the result "for every `t`" (lines 745–755), taking the supremum over `t`.

Proposition: under the hypotheses of Lemma 4.3 (those of `lem_pert`, verbatim), for every `κ > 0`
and every `t ∈ [0, T]`: `|δY_t|²` and `|λ δg_T + q^g_T|²` are `P`-integrable;
`e^{κs} (κ |δY_s|² + ∑_{k, j} δZ_{kj}(s)² + ∑_k ∫_E δU_k(s, e)² ν(de))` and
`e^{κs} ∑_k δY_{k,s} (λ δf_{k,s} + q^f_{k,s})` are integrable for `P ⊗ ds` on `Ω × [t, T]`; and
`e^{κt} ∫ |δY_t|² dP + ∫ ∫_{[t, T]} e^{κs} (κ |δY_s|² + |δZ_s|²_F + ‖δU_s‖²) ds dP
≤ e^{κT} ∫ |λ δg_T + q^g_T|² dP + 2 ∫ ∫_{[t, T]} e^{κs} ⟨δY_s, λ δf_s + q^f_s⟩ ds dP`.

Readings:

* The hypotheses are those of Lemma 4.3, written as in `lem_pert`; `q = δq`; `δg_T` and `δf` are
  the differences of `terminalVal` and `driverProc` along `Θ¹, Θ²` (reviewed in
  `definitions.md`).
* "For `κ > 0`" with `t` free: every `κ > 0` and every `t ∈ [0, T]`, as the proof uses it.
* The expectations are Bochner integrals, those on the left and the terminal one of nonnegative
  functions; the integrability of the four integrands is stated, so no junk value enters and the
  inequality is between the expectations the paper means. `𝔼 ∫_t^T` is `∫ dP` of `∫_{[t, T]} ds`
  (the same as over `(t, T]` for Lebesgue measure). In coordinates `|δY|² = ∑_k δY_k²`,
  `|δZ|²_F = ∑_{k, j} δZ_{kj}²`, `‖δU‖²_{L²(ν)} = ∑_k ∫_E δU_k(e)² ν(de)` (a Bochner integral in
  `e`, of an integrable function for almost every `(ω, s)`), `⟨x, y⟩ = ∑_k x_k y_k`.
* The terminal term is printed with `|λ δg_T + q^g_T|²`, which is `|δY_T|²` almost surely by
  (4.16); it is written with the terminal data, as printed.
* The step holds with equality; the proposition states `≤`, as printed.

Proof: each backward coordinate of the difference system (at the extensions of `exists_pairDiff`,
which agree with the solutions on `[0, T]`) solves the linear backward equation with terminal
value `λ δg_k + q^g_k` and drift `λ δf_k + q^f_k`. For such a solution the weighted second-moment
identity holds on `Ω × [t, T]` (`LinearBSDEJ.exp_mul_window_eq`): read forward, the solution
satisfies the bilinear identity `LinearFSDEJ.integral_mul_eq_at`; integrated against `e^{κs}`
(`mul_eq_add_setIntegral_of_hasDerivAt`) and read for `P ⊗ ds` on `[0, τ]`
(`LinearFSDEJ.setIntegral_weight_rate_eq`), it is differenced between `τ = T` and `τ = t`
(`integral_window_split`). Summed over the coordinates and read by Fubini, it is (4.24) with
equality. The proof of Lemma 4.3 in the implementation does not use (4.24).

Witness: `Dissertation.Acceptance.A.lem_pert_two_data_hypotheses`, the hypotheses of Lemma 4.3.

Verdict: faithful.

<!-- spec-review: Dissertation.PaperSpec.A.eq_bwdito ed839d34f480cba1ac3ad318e96e1e46 by=claude-author source=A:eq:bwdito@393867a8ee02929733b52a376171325b807e01b0d81452f311285bdc89d2c889 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.eq_bwdito--claude-auditor--2026-10-20T00_40_53Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_bwdito ed839d34f480cba1ac3ad318e96e1e46 by=claude-auditor source=A:eq:bwdito@393867a8ee02929733b52a376171325b807e01b0d81452f311285bdc89d2c889 -->

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

<!-- spec-review: Dissertation.PaperSpec.A.eq_bwdyoung ed839d34f480cba13db23656421cf5a0 by=claude-author source=A:eq:bwdyoung@6de6e9ca136a07fe246605603408e399b279d06e2d18e1d458a34b7b82ce829c -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.eq_bwdyoung--claude-auditor--2026-10-19T18_47_22Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_bwdyoung ed839d34f480cba13db23656421cf5a0 by=claude-auditor source=A:eq:bwdyoung@6de6e9ca136a07fe246605603408e399b279d06e2d18e1d458a34b7b82ce829c -->

## (4.25) inserted in (4.24), and the backward bound at every time, in Step 4 of the proof of Lemma 4.3: `Dissertation.PaperSpec.A.eq_wgt_insert`

Manuscript (proof of Lemma `lem:pert`, Step 4, lines 735–752), after (4.24) "for `κ > 0`" and
(4.25) "for every `0 < ε ≤ 1`", "with `C` independent of `ε`" (quoted in their sections): "Insert
(4.25) in (4.24): `𝔼 e^{κt} |δY_t|² + 𝔼 ∫_t^T e^{κs} [(κ − C/ε) |δY_s|²
+ (1 − ε)(|δZ_s|²_F + ‖δU_s‖²_{L²(ν)})] ds ≤ 𝔼 e^{κT} |λ δg_T + q^g_T|²
+ (C/ε) 𝔼 ∫_t^T e^{κs} (|δX_s|² + |q^f_s|²) ds`. Take `ε < 1` and `κ > C/ε`. The `δY`-integral
on the left is then nonnegative and may be dropped, and the weights satisfy
`1 ≤ e^{κs} ≤ e^{κT}` on `[0, T]`, so `𝔼|δY_t|² + 𝔼 ∫_t^T (|δZ_s|²_F + ‖δU_s‖²) ds
≤ C(𝔼|λ δg_T + q^g_T|² + 𝔼 ∫_t^T (|δX_s|² + |q^f_s|²) ds)`." Both displays lie before the
pinned region of `A:eq:wgt` (lines 756–760); the next sentence takes the supremum over `t`.

Proposition: `∃ K` of `(T, L, ‖G‖, c_G, α, β₁, β₂, λ̲)` and `∃ K'` of
`(ε, κ, T, L, ‖G‖, c_G, α, β₁, β₂, λ̲)` such that, under the hypotheses of Lemma 4.3 (those of
`lem_pert`, verbatim), with `C = K(T, L, ‖GX G‖, s_min(G)⁻², α, β₁, β₂, λ̲)`:

* for every `ε ∈ (0, 1]`, `κ > 0` and `t ∈ [0, T]`: the functions `∑_k δY_{k,t}²`,
  `∑_k (λ δg_k + δq^g_k)²` (on `Ω`), `e^{κs} ((κ − C/ε) ∑_k δY_{k,s}² + (1 − ε)(∑_{k, j}
  δZ_{kj,s}² + ∑_k ∫ δU_{k,s}(e)² ν(de)))` and `e^{κs} (∑_i δX_{i,s}² + ∑_k δq^f_{k,s}²)` (on
  `Ω × [t, T]`, for `P ⊗ ds`) are integrable, and
  `e^{κt} ∫ ∑_k δY_{k,t}² dP + ∫ ∫_{[t, T]} e^{κs} ((κ − C/ε) ∑_k δY_{k,s}² + (1 − ε)(…)) ds dP
  ≤ e^{κT} ∫ ∑_k (λ δg_k + δq^g_k)² dP + (C/ε) ∫ ∫_{[t, T]} e^{κs} (∑_i δX_{i,s}²
  + ∑_k δq^f_{k,s}²) ds dP`, Bochner integrals in `ℝ`;
* for every `ε ∈ (0, 1)`, `κ > C/ε` and `t ∈ [0, T]`: `∑_{k, j} δZ_{kj,s}² + ∑_k ∫ δU_{k,s}(e)²
  ν(de)` and `∑_i δX_{i,s}² + ∑_k δq^f_{k,s}²` are integrable on `Ω × [t, T]`, and
  `∫ ∑_k δY_{k,t}² dP + ∫ ∫_{[t, T]} (∑_{k, j} δZ_{kj,s}² + ∑_k ∫ δU_{k,s}(e)² ν(de)) ds dP
  ≤ C' (∫ ∑_k (λ δg_k + δq^g_k)² dP + ∫ ∫_{[t, T]} (∑_i δX_{i,s}² + ∑_k δq^f_{k,s}²) ds dP)`,
  `C' = K'(ε, κ, T, L, ‖GX G‖, s_min(G)⁻², α, β₁, β₂, λ̲)`.

Here `δg_k = terminalVal(X¹)_k − terminalVal(X²)_k`, `δq = q¹ − q²`.

Readings:

* The hypotheses are those in force at Step 4, as for (4.24) and (4.25); `κ > 0` and
  `0 < ε ≤ 1` are the ranges at which (4.24) and (4.25) are printed, and the display holds for
  all of them; the second display for every choice "`ε < 1` and `κ > C/ε`".
* The constants. `C` is that of (4.25): chosen before `ε`, `κ` and `t`, a function of the
  parameters of the §4 convention and of `λ̲`, read as for (4.25). The `C` of the second display
  is a new constant: after "Take `ε < 1` and `κ > C/ε`" it may depend on the choice of `ε` and
  `κ`, so `K'` takes them as arguments; with `ε` and `κ` fixed as functions of the structural
  constants it is one of these.
* The integrals are real, as in (4.24): the coefficient `κ − C/ε` of the display may be negative,
  and the reading in `ℝ` keeps the printed display verbatim; the integrability of every integrand
  is stated, so no integral is read at the junk value `0`. The second display is read in `ℝ` too,
  every term being the integral of a nonnegative integrable function. `𝔼 e^{κt} |δY_t|²` is
  `e^{κt} 𝔼|δY_t|²`, the weight being deterministic; `∫_t^T` is over `[t, T]`;
  `|δZ_s|²_F = ∑_{k, j}`, `‖δU_s‖² = ∑_k ∫ δU_k(s, e)² ν(de)`, as in (4.24).
* `q = δq` and `δg_T`, `δf` as in (4.24); "the `δY`-integral may be dropped" and the bounds on the
  weights are the proof of the second display.
* The section of (4.26) and (4.27) records the displays between (4.24) and (4.27) as steps of the
  proof, not stated; these two and the first two links before (4.27) (`eq_bwd_chain`) are stated
  now.

Proof: `K = 2 (10 (2L)²) + 3`, the constant of (4.25), and `K' = e^{κT} max{1, K/ε}/(1 − ε)`. At
the extensions of `exists_pairDiff`, for each backward coordinate, the weighted identity on the
window `Ω × [t, T]` (`LinearBSDEJ.exp_mul_window_eq`, the identity behind (4.24)) is summed over
the coordinates. The Young bound (4.25) at almost every `s` is a real inequality once its
expectations, finite at almost every `s`, are written as real integrals (with
`∫⁻ |δU|² dν = ofReal(∫ δU² dν)` almost everywhere); against the weight `e^{κs}` it integrates
over `[t, T]` by Fubini's theorem (`PairDiff.integral_weighted_young_le`), and subtracting gives
the display (`PairDiff.weighted_window_le`). For `ε < 1` and `κ > K/ε`, `(κ − K/ε) ≥ 0`,
`1 ≤ e^{κt}`, `1 ≤ e^{κs} ≤ e^{κT}` on `[t, T]` and `1 − ε > 0` give the second display
(`PairDiff.window_le`). The integrands are integrable by the finite energies of the difference
system and of `δq^f` (`PairDiff.integrable_window`, `integrable_exp_mul_window`); the extensions
agree with the solutions on `[0, T]`.

Witness: `Dissertation.Acceptance.A.lem_pert_backward_window_hypotheses`, described with the
chain before (4.23) (`λ̲ = λ = 1`, `δX ≡ 1`, `δY = M^W + M^N`, `δZ = δU = 1_{(0, 1]}`). By hand
`𝔼|δY_t|² = 2t`, `λ δg_T + δq^g_T = δY_1` with `𝔼|δY_1|² = 2`, the weighted `δZ`- and
`δU`-integral is `2 ∫_t^1 e^{κs} ds > 0` for `t < 1`, and `𝔼 ∫_t^1 e^{κs} |δX_s|² ds > 0`: both
sides of both displays are positive.

Verdict: faithful.

<!-- spec-review: Dissertation.PaperSpec.A.eq_wgt_insert ed839d34f480cba14b6f1b0835c7416b by=claude-author source=A:eq:wgt@1f83bb20576ba7e561a74ddc8aa535854a49efdb61f9fb1ffc80d72ea5b14701 -->

## (4.26) and (4.27), the backward estimates in Step 4 of the proof of Lemma 4.3: `Dissertation.PaperSpec.A.eq_wgt`, `eq_bwd`

Manuscript (proof of Lemma `lem:pert`, Step 4, lines 735–778): inserting (4.25) in (4.24), "Take
`ε < 1` and `κ > C/ε`. The `δY`-integral on the left is then nonnegative and may be dropped, and
the weights satisfy `1 ≤ e^{κs} ≤ e^{κT}` on `[0, T]`, so `𝔼|δY_t|² + 𝔼 ∫_t^T (|δZ_s|²_F
+ ‖δU_s‖²) ds ≤ C(𝔼|λ δg_T + q^g_T|² + 𝔼 ∫_t^T (|δX_s|² + |q^f_s|²) ds)`. With
`𝔼|δg_T|² ≤ C 𝔼|δX_T|²`, the forcings in `P`, and `∫_t^T ≤ ∫_0^T` on the right, the bound no
longer depends on `t`. Taking the supremum over `t` in the first term on the left and `t = 0` in
the second, there remains (4.26) `sup_{t ≤ T} 𝔼|δY_t|² + 𝔼 ∫_0^T (|δZ_t|²_F + ‖δU_t‖²) dt
≤ C(𝔼|δX_T|² + 𝔼 ∫_0^T |δX_t|² dt + P)`. Writing (4.16) forward from `δY_0`, BDG,
Cauchy–Schwarz, Assumption 2.3 with the coupling bound (2.8), and (4.26) give
`𝔼 sup_{t ≤ T} |δY_t|² ≤ … ≤ C(𝔼|δX_T|² + 𝔼 ∫_0^T |δX_t|² dt + P)`. The first term of (4.26) may
therefore be replaced by `𝔼 sup_{t ≤ T} |δY_t|²`: (4.27) `𝔼 sup_{t ≤ T} |δY_t|²
+ 𝔼 ∫_0^T (|δZ_t|²_F + ‖δU_t‖²) dt ≤ C(𝔼|δX_T|² + 𝔼 ∫_0^T |δX_t|² dt + P)`."

Propositions: each `∃ K` of `(T, L, ‖G‖, c_G, α, β₁, β₂)` such that, under the hypotheses of
Lemma 4.3 (those of `lem_pert`, verbatim), with `C = K(T, L, ‖GX G‖, s_min(G)⁻², α, β₁, β₂)`:

* `eq_wgt`: `sup_{t ∈ [0, T]} ∫⁻ |δY_t|² + (∑_{k, j} energy(δZ_{kj}) + ∑_k markedEnergy(δU_k))
  ≤ ofReal(C) (∫⁻ |δX_T|² + ∑_i energy(δX_i) + dataSize(δξ₀, δq))`;
* `eq_bwd`: the same with `∫⁻ sup_{t ∈ [0, T]} |δY_t|²` as the first term.

Readings:

* The hypotheses, the constant (chosen first, a function of exactly the parameters of the §4
  convention, `ofReal`) and `P` are read as for (4.23). No other dependence is stated at (4.26)
  or (4.27), and Step 4 uses `λ` only through `λ ∈ [0, 1]` (in the terminal value
  `λ δg_T + q^g_T`, the Young bound (4.25) and the driver `λ δf + q^f`), so `C` does not depend on
  `λ̲`.
* `sup_{t ≤ T} 𝔼|δY_t|²` is the supremum over `t ∈ [0, T]` of lower integrals of `esq`;
  `𝔼 sup_{t ≤ T} |δY_t|²` the lower integral of the supremum; `𝔼|δX_T|²` and
  `𝔼 ∫_0^T |δX_t|² dt` are `esq` at `T` and the energies of the coordinates on `[0, T]`, all in
  `[0, ∞]`.
* The choices `ε < 1`, `κ > C/ε` and the displays between (4.24) and (4.27) are steps of the
  proof; they are not stated. Each proposition chooses its own `K`.

Proofs: (4.27) with `K = c_Y(T, 10 (2L)², 4 (2L)²)` (`bwdSupConst`), a function of `T` and `L`:
at the extensions of `exists_pairDiff`, the difference system satisfies
`𝔼 sup |δY|² ≤ 3 𝔼|δY_0|² + 3T 𝔼 ∫ |λ δf + q^f|² + 12 𝔼 ∫ (|δZ|²_F + ‖δU‖²)`
(`PairDiff.lintegral_biSup_bwd_le`, the `S²` bound of Lemma 4.1 for each backward coordinate),
the rate bound (`PairDiff.rateEnergy_le`), and the backward estimate of the closure step
`𝔼|δY_0|² + 𝔼 ∫_0^T (|δY|² + |δZ|²_F + ‖δU‖²) ≤ k_B (𝔼|δX_T|² + 𝔼 ∫_0^T |δX|² + P)`
(`PairDiff.backward_le`, a weighted energy bound in place of the choice of `ε` and `κ`);
`PairDiff.lintegral_biSup_bwd_add_le` assembles them. (4.26) follows from (4.27) with the same
constant, since `sup_t 𝔼|δY_t|² ≤ 𝔼 sup_t |δY_t|²`. The implementation does not pass through
(4.24) and (4.25) here.

Witness: `Dissertation.Acceptance.A.lem_pert_two_data_hypotheses`, the hypotheses of Lemma 4.3,
which are those of both propositions.

Verdict: faithful.

<!-- spec-review: Dissertation.PaperSpec.A.eq_wgt ed839d34f480cba149f1ed71dc85d931 by=claude-author source=A:eq:wgt@1f83bb20576ba7e561a74ddc8aa535854a49efdb61f9fb1ffc80d72ea5b14701 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.eq_wgt--claude-auditor--2026-10-20T02_03_32Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_wgt ed839d34f480cba149f1ed71dc85d931 by=claude-auditor source=A:eq:wgt@1f83bb20576ba7e561a74ddc8aa535854a49efdb61f9fb1ffc80d72ea5b14701 -->
<!-- spec-review: Dissertation.PaperSpec.A.eq_bwd ed839d34f480cba173f30a686b4b22f5 by=claude-author source=A:eq:bwd@3114f6e187919402a154d20d84baf24f22a2a1052d28f7faf3558a9335716cf5 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.eq_bwd--claude-auditor--2026-10-20T02_03_32Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_bwd ed839d34f480cba173f30a686b4b22f5 by=claude-auditor source=A:eq:bwd@3114f6e187919402a154d20d84baf24f22a2a1052d28f7faf3558a9335716cf5 -->

## The first two links of the chain before (4.27), in Step 4 of the proof of Lemma 4.3: `Dissertation.PaperSpec.A.eq_bwd_chain`

Manuscript (proof of Lemma `lem:pert`, Step 4, lines 761–772): "Writing (4.16) forward from
`δY_0`, BDG, Cauchy–Schwarz, Assumption 2.3 with the coupling bound (2.8), and (4.26) give
`𝔼 sup_{t ≤ T} |δY_t|² ≤ C(𝔼|δY_0|² + 𝔼 ∫_0^T |λ δf_s + q^f_s|² ds
+ 𝔼 ∫_0^T (|δZ_s|²_F + ‖δU_s‖²) ds) ≤ C(𝔼|δY_0|² + 𝔼 ∫_0^T (|δX_s|² + |δY_s|² + |δZ_s|²_F
+ ‖δU_s‖²) ds + P) ≤ C(𝔼|δX_T|² + 𝔼 ∫_0^T |δX_t|² dt + P)`." The chain lies before the pinned
region of `A:eq:bwd` (lines 775–778); its last link, by (4.26), gives (4.27).

Proposition: `∃ K₁ K₂` of `(T, L, ‖G‖, c_G, α, β₁, β₂)` such that, under the hypotheses of
Lemma 4.3 (those of `lem_pert`, verbatim), with `C_i = K_i(T, L, ‖GX G‖, s_min(G)⁻², α, β₁, β₂)`:
`∫⁻ sup_{t ∈ [0, T]} |δY_t|² ≤ ofReal(C₁) (∫⁻ |δY_0|² + ∑_k energy(λ δf_k + δq^f_k)
+ (∑_{k, j} energy(δZ_{kj}) + ∑_k markedEnergy(δU_k)))` and
`ofReal(C₁) (…) ≤ ofReal(C₂) (∫⁻ |δY_0|² + (∑_i energy(δX_i) + ∑_k energy(δY_k)
+ ∑_{k, j} energy(δZ_{kj}) + ∑_k markedEnergy(δU_k)) + P)`, with `δf_k` the difference of the
`driverProc`s and `P = dataSize` of the differences of the data.

Readings:

* The hypotheses are those in force at Step 4, as for (4.27); the constants, one per link, are
  chosen first as functions of the parameters of the §4 convention, read as for (4.27) (Step 4
  uses `λ` only through `λ ∈ [0, 1]`).
* The first link is the forward-form BDG bound, the second the Lipschitz step: the two links
  that (4.27) does not imply. The third link is (4.26) inserted, and gives (4.27) (`eq_bwd`,
  with `eq_wgt`); it is not stated again.
* Expectations are lower integrals in `[0, ∞]`: `𝔼 sup_{t ≤ T} |δY_t|²` the lower integral of the
  running supremum of `esq`, `𝔼|δY_0|²` that of `esq` at `0`, `𝔼 ∫_0^T |λ δf_s + q^f_s|²` the
  energies of the coordinates, `|δZ|²_F = ∑_{k, j}` and `‖δU‖² = ∑_k ∫ δU_k(e)² ν(de)`.

Proof: `K₁ = 3T + 12`, `K₂ = (3T + 12)(2 · 10 (2L)² + 2)`. At the extensions of `exists_pairDiff`:
the `S²` bound of Lemma 4.1 for each backward coordinate of the difference system
(`LinearBSDEJ.lintegral_biSup_sq_le`, `3 𝔼|δY_0|² + 3T 𝔼 ∫ |λ δf + q^f|²
+ 12 𝔼 ∫ (|δZ|²_F + ‖δU‖²)`), summed over the coordinates with the running supremum of the vector
by those of the coordinates (`lintegral_biSup_esq_le`), is the first link; the rate bound
`𝔼 ∫ |λ δf + q^f|² ≤ 2 · 10 (2L)² 𝔼 ∫ (|δX|² + |δY|² + |δZ|²_F + ‖δU‖²) + 2P`
(`PairDiff.rateEnergy_le`) the second.

Witness: `Dissertation.Acceptance.A.lem_pert_backward_window_hypotheses`, described with the
chain before (4.23). By hand `δY_0 = 0`, `𝔼 sup_{t ≤ 1} |δY_t|² ≥ 𝔼|δY_1|² = 2`, the `δZ`- and
`δU`-energies are `1` each and `𝔼 ∫_0^1 |δX|² = 1`: every member of the chain is positive.

Verdict: faithful.

<!-- spec-review: Dissertation.PaperSpec.A.eq_bwd_chain ed839d34f480cba1bd5456c76b6d343a by=claude-author source=A:eq:bwd@3114f6e187919402a154d20d84baf24f22a2a1052d28f7faf3558a9335716cf5 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.eq_bwd_chain--claude-auditor--2026-10-20T15_31_29Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_bwd_chain ed839d34f480cba1bd5456c76b6d343a by=claude-auditor source=A:eq:bwd@3114f6e187919402a154d20d84baf24f22a2a1052d28f7faf3558a9335716cf5 -->

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

<!-- spec-review: Dissertation.PaperSpec.A.lem_cont ed839d34f480cba15f6eb38f12c8d372 by=claude-author source=A:lem:cont@c383f5951a193b52153def310e145b684712418abdb0ed5c8405a458be4b45de -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.lem_cont--claude-reviewer--2026-10-17T12_25_19Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.lem_cont ed839d34f480cba15f6eb38f12c8d372 by=claude-reviewer source=A:lem:cont@c383f5951a193b52153def310e145b684712418abdb0ed5c8405a458be4b45de -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.lem_cont--claude-auditor--2026-10-19T03_35_26Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.lem_cont ed839d34f480cba15f6eb38f12c8d372 by=claude-auditor source=A:lem:cont@c383f5951a193b52153def310e145b684712418abdb0ed5c8405a458be4b45de -->

## §4.4, uniqueness along the homotopy: `Dissertation.PaperSpec.A.sec4_uniq_homotopy`

Manuscript (§4.4, before Lemma `lem:cont`, lines 875–878): "Taking identical sources and the common
initial datum in Lemma 4.3 (at lower bound `λ̲ = λ*`) yields uniqueness at each `λ ∈ [λ*, 1]`;
Lemma 4.2 gives it on `[0, λ*]`. It remains to prove existence up to `λ = 1`." Here `λ*` is the
small-coupling threshold of Lemma 4.2 (as Lemma 4.4 says), and uniqueness is the uniqueness half
of `WP(λ)`: two solutions of (4.1) in `ℍ` with the same initial datum and forcing coincide.

Proposition: `∃ λ*` of `(T, L)` such that, in the standing setting, for `T > 0`, under (2.3) and
Assumptions 2.2–2.5 with `L, α, β₁, β₂` and a full-rank `G`: `0 < λ*(T, L) ≤ 1`, and for every
`λ` with `λ* ≤ λ ≤ 1` or `0 ≤ λ ≤ λ*`, every forcing `q` (`PredForcing`) and any two
`ForcedSolution`s at `λ` with the datum `ξ₀` and the forcing `q`, `X¹, X²` and `Y¹, Y²` are
indistinguishable on `[0, T]` and the differences of `Z` and of `U` have zero energy.

Readings:

* The hypotheses are those of the continuation step, the hypotheses of Theorem 3.5 (as
  `thm_cwp`/`lem_cont`); Lemma 4.3 uses Assumptions 2.3–2.5 and Lemma 4.2 Assumptions 2.2–2.3.
* `λ*` is chosen before everything, a function of `(T, L)`, as in `lem_small`; its range
  `(0, 1]` is asserted in the situation of the statement. The two ranges of the sentence are the
  two disjuncts on `λ`.
* Uniqueness in the sense of `WP(λ)` (reviewed in `definitions.md`): solutions in `ℍ`
  (`ForcedSolution`), the conclusion of `WP`. "Identical sources and the common initial datum":
  one forcing `q` and one datum `ξ₀` for both solutions.

Proof: with `λ*` the constant of `lem_small`; on `[λ*, 1]` by `lem_pert` at `λ̲ = λ*`,
`ξ¹ = ξ² = ξ₀` (`ℱ₀`-measurable by Assumption 2.2) and `q¹ = q² = q`, whose difference of two
solutions in `ℍ` lies in `ℍ` (`ForcedSolution.supSize_sub_lt_top`) and whose data size is `0`, so
the size of the difference is `0` (`ForcedSolution.eq_of_supSize_sub_eq_zero`); on `[0, λ*]` by
`WP(λ)` of `lem_small`.

Witness: `Dissertation.Acceptance.A.thm_cwp_hypotheses` (Example 5.1(i): (2.3) and
Assumptions 2.2–2.5 at `L = 1`, `G = 1`, `α = β₁ = β₂ = 1`).

Verdict: faithful.

<!-- spec-review: Dissertation.PaperSpec.A.sec4_uniq_homotopy ed839d34f480cba178b10f6f962eecce by=claude-author source=A:sec4:uniqueness-along-homotopy@518b95da43921c8290496ba8c58a2f74ebe2bce2191c71305e264312b4786bd7 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.sec4_uniq_homotopy--claude-auditor--2026-10-19T22_59_53Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.sec4_uniq_homotopy ed839d34f480cba178b10f6f962eecce by=claude-auditor source=A:sec4:uniqueness-along-homotopy@518b95da43921c8290496ba8c58a2f74ebe2bce2191c71305e264312b4786bd7 -->

## §4.5, the proof of Theorem 3.5: `Dissertation.PaperSpec.A.sec45_proof_thm35`, and `thm_cwp`

Manuscript (§4.5, lines 941–952): "By Lemma 4.2, `WP(λ)` holds for `λ ∈ [0, λ*]`. With `ζ₀` from
Lemma 4.4, set `λ_k := min{λ* + k ζ₀, 1}`, `k ≥ 0`, so that `λ_0 = λ*`, `λ_{k+1} − λ_k ≤ ζ₀` and
`λ_k = 1` once `k ≥ ⌈(1 − λ*)/ζ₀⌉`. Lemma 4.4 carries `WP(λ_k)` to `WP(λ_{k+1})` at every step, so
`WP(1)` holds; taking `q ≡ 0` there gives a unique solution of (1.1) in `ℍ`." Lemma 4.4
(lines 880–886), to which "`ζ₀` from Lemma 4.4" refers: "There is `ζ₀ > 0`, depending only on
`T`, `L`, `‖G‖`, `c_G`, `α`, `β₁`, `β₂`, `λ*` and `c_BDG`, such that: if `λ₀ ∈ [λ*, 1]` and
`WP(λ₀)` holds, then `WP(λ₀ + ζ)` holds for every `ζ ∈ [0, ζ₀]` with `λ₀ + ζ ≤ 1`."

Proposition (`sec45_proof_thm35`): `∃ λ*` of `(T, L)` and `ζ₀` of
`(T, L, ‖G‖, c_G, α, β₁, β₂, λ*)` such that, in the standing setting, for `T > 0`, under (2.3) and
Assumptions 2.2–2.5: `0 < λ* ≤ 1`; `ζ₀(…, λ*) > 0`; for every `λ₀` with `λ* ≤ λ₀ ≤ 1` and
`WP(λ₀)`, `WP(λ₀ + ζ)` for every `ζ` with `0 ≤ ζ ≤ ζ₀(…, λ*)` and `λ₀ + ζ ≤ 1`; `WP(λ)` for every
`λ ∈ [0, λ*]`; `min{λ* + 0 · ζ₀, 1} = λ*`, `λ_{k+1} − λ_k ≤ ζ₀` for every `k`, `λ_k = 1` for
`k ≥ ⌈(1 − λ*)/ζ₀⌉₊`, `WP(λ_k)` for every `k`, and `WP(1)`, with `λ_k = min{λ* + k ζ₀, 1}` written
out and `ζ₀` evaluated at `(T, L, ‖G‖, s_min(G)⁻², α, β₁, β₂, λ*(T, L))`. The last sentence,
"taking `q ≡ 0` there gives a unique solution of (1.1) in `ℍ`", is Theorem 3.5, the claim's
second clause `thm_cwp` (reviewed in its own section).

Readings:

* `λ*` is the threshold of Lemma 4.2: a function of `(T, L)` chosen before everything, with its
  range `(0, 1]` and its property `WP(λ)` on `[0, λ*]` stated as conjuncts, as in `lem_small`.
* `ζ₀` is the constant of Lemma 4.4 ("With `ζ₀` from Lemma 4.4"): a function chosen before
  everything with the dependence Lemma 4.4 states, `(T, L, ‖G‖, c_G, α, β₁, β₂, λ*)` with
  `c_G = s_min(G)⁻²` as in `lem_cont`, evaluated at `λ* = λ*(T, L)`, with its positivity and its
  property, the continuation step `WP(λ₀) ⇒ WP(λ₀ + ζ)` for `λ₀ ∈ [λ*, 1]`, `ζ ∈ [0, ζ₀]`,
  `λ₀ + ζ ≤ 1`, stated as conjuncts in exactly the form of `lem_cont` at `λ* = λ*(T, L)` (the same
  quantifiers in the same order). The property is what "Lemma 4.4 carries `WP(λ_k)` to
  `WP(λ_{k+1})` at every step" uses, at `λ₀ = λ_k` and `ζ = λ_{k+1} − λ_k`. The dependence on
  `c_BDG`, a universal constant, is not an argument: `ζ₀` has the eight arguments of `lem_cont`.
* `⌈(1 − λ*)/ζ₀⌉` is the natural-number ceiling `⌈·⌉₊` (its argument is `≥ 0`); `k ≥ 0` ranges
  over `ℕ`. "Lemma 4.4 carries `WP(λ_k)` to `WP(λ_{k+1})` at every step, so `WP(1)` holds": the
  conclusions `WP(λ_k)` for every `k` and `WP(1)`; the induction is the proof.
* The hypotheses are those of Theorem 3.5 (`thm_cwp`), which this proof proves.

Proof: with the functions of `lem_small` and `lem_cont`, whose conclusions at `λ* = λ*(T, L)`
give the range of `λ*`, `WP(λ)` on `[0, λ*]`, the positivity of `ζ₀` and its continuation
property; the arithmetic of `min` and `⌈·⌉₊` (`lambdaSeq_facts`), and induction on `k` with that
property at `λ₀ = λ_k ∈ [λ*, 1]` and `ζ = λ_{k+1} − λ_k ∈ [0, ζ₀]`; `WP(1)` is `WP(λ_K)` at
`K = ⌈(1 − λ*)/ζ₀⌉₊`.

Witness: `Dissertation.Acceptance.A.thm_cwp_hypotheses`, for both clauses.

Verdict: faithful; the last sentence shares the proposition of Theorem 3.5.

<!-- spec-review: Dissertation.PaperSpec.A.sec45_proof_thm35 ed839d34f480cba1227f3637481e69e0 by=claude-author source=A:sec4:proof-thm35@ed713718821e088c6ca09a59f75d22202a9e9960885df259a33fd8f6dd54fcbe -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.sec45_proof_thm35--claude-auditor--2026-10-20T02_03_19Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.sec45_proof_thm35 ed839d34f480cba1227f3637481e69e0 by=claude-auditor source=A:sec4:proof-thm35@ed713718821e088c6ca09a59f75d22202a9e9960885df259a33fd8f6dd54fcbe -->

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

<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_i_ham ed839d34f480cba1cf9f26355b828c6a by=claude-author source=A:ex:concrete@c1a37ef0e0904d01777b03bccdee013a671a60dda2b3a63f5bcfcdc22dd81785 -->
Review by claude-reviewer: broader (report `reports/Dissertation.PaperSpec.A.ex_concrete_i_ham--claude-reviewer--2026-10-17T12_16_01Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_i_ham ed839d34f480cba1cf9f26355b828c6a by=claude-reviewer source=A:ex:concrete@c1a37ef0e0904d01777b03bccdee013a671a60dda2b3a63f5bcfcdc22dd81785 -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.ex_concrete_i_ham--claude-auditor--2026-10-19T03_31_21Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_i_ham ed839d34f480cba1cf9f26355b828c6a by=claude-auditor source=A:ex:concrete@1e2bfcc4d0a6c0d3ac3168b0c7042d0db4a93670e277d64901f8076820cef633 -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_i ed839d34f480cba1d2f6e8919288ad6b by=claude-author source=A:ex:concrete@c1a37ef0e0904d01777b03bccdee013a671a60dda2b3a63f5bcfcdc22dd81785 source=A:sec5:overview@85ef567e93b2eddcbd19ae70a2daac18fc886c5303ea56d4b6dc281d39f4f3e9 -->
Review by claude-reviewer: faithful (report `reports/Dissertation.PaperSpec.A.ex_concrete_i--claude-reviewer--2026-10-17T12_13_03Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_i ed839d34f480cba1d2f6e8919288ad6b by=claude-reviewer source=A:ex:concrete@c1a37ef0e0904d01777b03bccdee013a671a60dda2b3a63f5bcfcdc22dd81785 source=A:sec5:overview@85ef567e93b2eddcbd19ae70a2daac18fc886c5303ea56d4b6dc281d39f4f3e9 -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.ex_concrete_i--claude-auditor--2026-10-19T03_36_52Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_i ed839d34f480cba1d2f6e8919288ad6b by=claude-auditor source=A:ex:concrete@1e2bfcc4d0a6c0d3ac3168b0c7042d0db4a93670e277d64901f8076820cef633 source=A:sec5:overview@85ef567e93b2eddcbd19ae70a2daac18fc886c5303ea56d4b6dc281d39f4f3e9 -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_i_pairing ed839d34f480cba1272d037d1e16e040 by=claude-author source=A:ex:concrete@c1a37ef0e0904d01777b03bccdee013a671a60dda2b3a63f5bcfcdc22dd81785 -->
Review by claude-reviewer: faithful (report `reports/Dissertation.PaperSpec.A.ex_concrete_i_pairing--claude-reviewer--2026-10-17T16_05_52Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_i_pairing ed839d34f480cba1272d037d1e16e040 by=claude-reviewer source=A:ex:concrete@c1a37ef0e0904d01777b03bccdee013a671a60dda2b3a63f5bcfcdc22dd81785 -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.ex_concrete_i_pairing--claude-auditor--2026-10-19T03_38_21Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_i_pairing ed839d34f480cba1272d037d1e16e040 by=claude-auditor source=A:ex:concrete@1e2bfcc4d0a6c0d3ac3168b0c7042d0db4a93670e277d64901f8076820cef633 -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_i_wp ed839d34f480cba13343e4213bb7f62d by=claude-author source=A:ex:concrete@c1a37ef0e0904d01777b03bccdee013a671a60dda2b3a63f5bcfcdc22dd81785 -->
Review by claude-reviewer: faithful (report `reports/Dissertation.PaperSpec.A.ex_concrete_i_wp--claude-reviewer--2026-10-17T16_05_52Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_i_wp ed839d34f480cba13343e4213bb7f62d by=claude-reviewer source=A:ex:concrete@c1a37ef0e0904d01777b03bccdee013a671a60dda2b3a63f5bcfcdc22dd81785 -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.ex_concrete_i_wp--claude-auditor--2026-10-19T03_37_01Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_i_wp ed839d34f480cba13343e4213bb7f62d by=claude-auditor source=A:ex:concrete@1e2bfcc4d0a6c0d3ac3168b0c7042d0db4a93670e277d64901f8076820cef633 -->

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

<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_i_clamp ed839d34f480cba1f386f903a2799dd0 by=claude-author source=A:ex:concrete@c1a37ef0e0904d01777b03bccdee013a671a60dda2b3a63f5bcfcdc22dd81785 -->
Review by claude-reviewer: faithful (report `reports/Dissertation.PaperSpec.A.ex_concrete_i_clamp--claude-reviewer--2026-10-17T12_14_00Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_i_clamp ed839d34f480cba1f386f903a2799dd0 by=claude-reviewer source=A:ex:concrete@c1a37ef0e0904d01777b03bccdee013a671a60dda2b3a63f5bcfcdc22dd81785 -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.ex_concrete_i_clamp--claude-auditor--2026-10-19T03_38_15Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_i_clamp ed839d34f480cba1f386f903a2799dd0 by=claude-auditor source=A:ex:concrete@1e2bfcc4d0a6c0d3ac3168b0c7042d0db4a93670e277d64901f8076820cef633 -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_i_clamp_wp ed839d34f480cba14bccae170a8d514d by=claude-author source=A:ex:concrete@c1a37ef0e0904d01777b03bccdee013a671a60dda2b3a63f5bcfcdc22dd81785 -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.ex_concrete_i_clamp_wp--claude-reviewer--2026-10-17T12_15_11Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_i_clamp_wp ed839d34f480cba14bccae170a8d514d by=claude-reviewer source=A:ex:concrete@c1a37ef0e0904d01777b03bccdee013a671a60dda2b3a63f5bcfcdc22dd81785 -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.ex_concrete_i_clamp_wp--claude-auditor--2026-10-19T03_38_30Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_i_clamp_wp ed839d34f480cba14bccae170a8d514d by=claude-auditor source=A:ex:concrete@1e2bfcc4d0a6c0d3ac3168b0c7042d0db4a93670e277d64901f8076820cef633 -->

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

<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_ii_mean ed839d34f480cba1adb40add6e4f8112 by=claude-author source=A:ex:concrete@c1a37ef0e0904d01777b03bccdee013a671a60dda2b3a63f5bcfcdc22dd81785 -->
Review by claude-reviewer: faithful (report `reports/Dissertation.PaperSpec.A.ex_concrete_ii_mean--claude-reviewer--2026-10-17T12_19_08Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_ii_mean ed839d34f480cba1adb40add6e4f8112 by=claude-reviewer source=A:ex:concrete@c1a37ef0e0904d01777b03bccdee013a671a60dda2b3a63f5bcfcdc22dd81785 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.ex_concrete_ii_mean--claude-auditor--2026-10-19T03_31_21Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_ii_mean ed839d34f480cba1adb40add6e4f8112 by=claude-auditor source=A:ex:concrete@1e2bfcc4d0a6c0d3ac3168b0c7042d0db4a93670e277d64901f8076820cef633 -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_ii ed839d34f480cba1cba84bcbe1866633 by=claude-author source=A:ex:concrete@c1a37ef0e0904d01777b03bccdee013a671a60dda2b3a63f5bcfcdc22dd81785 source=A:sec5:overview@85ef567e93b2eddcbd19ae70a2daac18fc886c5303ea56d4b6dc281d39f4f3e9 -->
Review by claude-reviewer: faithful (report `reports/Dissertation.PaperSpec.A.ex_concrete_ii--claude-reviewer--2026-10-17T12_18_31Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_ii ed839d34f480cba1cba84bcbe1866633 by=claude-reviewer source=A:ex:concrete@c1a37ef0e0904d01777b03bccdee013a671a60dda2b3a63f5bcfcdc22dd81785 source=A:sec5:overview@85ef567e93b2eddcbd19ae70a2daac18fc886c5303ea56d4b6dc281d39f4f3e9 -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.ex_concrete_ii--claude-auditor--2026-10-19T03_34_14Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_ii ed839d34f480cba1cba84bcbe1866633 by=claude-auditor source=A:ex:concrete@1e2bfcc4d0a6c0d3ac3168b0c7042d0db4a93670e277d64901f8076820cef633 source=A:sec5:overview@85ef567e93b2eddcbd19ae70a2daac18fc886c5303ea56d4b6dc281d39f4f3e9 -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_ii_pairing ed839d34f480cba16aa5f84a4f3328b5 by=claude-author source=A:ex:concrete@c1a37ef0e0904d01777b03bccdee013a671a60dda2b3a63f5bcfcdc22dd81785 -->
Review by claude-reviewer: faithful (report `reports/Dissertation.PaperSpec.A.ex_concrete_ii_pairing--claude-reviewer--2026-10-17T16_05_52Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_ii_pairing ed839d34f480cba16aa5f84a4f3328b5 by=claude-reviewer source=A:ex:concrete@c1a37ef0e0904d01777b03bccdee013a671a60dda2b3a63f5bcfcdc22dd81785 -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.ex_concrete_ii_pairing--claude-auditor--2026-10-19T03_33_35Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_ii_pairing ed839d34f480cba16aa5f84a4f3328b5 by=claude-auditor source=A:ex:concrete@1e2bfcc4d0a6c0d3ac3168b0c7042d0db4a93670e277d64901f8076820cef633 -->

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

<!-- spec-review: Dissertation.PaperSpec.A.ex_brownian ed839d34f480cba13b36df98cbfaee33 by=claude-author source=A:rem:beta1-dich@ce35242e5c61dc248a5bf9b36f678223d523cf9e6c42793d8e5d2fd12e1df0ea source=A:ex:brownian@73039b50faf59ac9d4c6bfe0d2609ec518c20d4f2edffd1960252336508e71b5 source=A:sec5:overview@85ef567e93b2eddcbd19ae70a2daac18fc886c5303ea56d4b6dc281d39f4f3e9 -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.ex_brownian--claude-reviewer--2026-10-17T12_10_35Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_brownian ed839d34f480cba13b36df98cbfaee33 by=claude-reviewer source=A:rem:beta1-dich@ce35242e5c61dc248a5bf9b36f678223d523cf9e6c42793d8e5d2fd12e1df0ea source=A:ex:brownian@73039b50faf59ac9d4c6bfe0d2609ec518c20d4f2edffd1960252336508e71b5 source=A:sec5:overview@85ef567e93b2eddcbd19ae70a2daac18fc886c5303ea56d4b6dc281d39f4f3e9 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.ex_brownian--claude-auditor--2026-10-19T03_34_12Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_brownian ed839d34f480cba13b36df98cbfaee33 by=claude-auditor source=A:rem:beta1-dich@20e41bdfd1e0996ebf1050ab15273a783631b8c503a6635284298cc387eea4f4 source=A:ex:brownian@73039b50faf59ac9d4c6bfe0d2609ec518c20d4f2edffd1960252336508e71b5 source=A:sec5:overview@85ef567e93b2eddcbd19ae70a2daac18fc886c5303ea56d4b6dc281d39f4f3e9 -->

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

<!-- spec-review: Dissertation.PaperSpec.A.ex_expfunc ed839d34f480cba1c0ebc41bbfe679cc by=claude-author source=A:ex:expfunc@bd45b535010dec4f0a3fd33a96a52f00a138499f3145d6b0e5c89d643405ac28 source=A:sec5:overview@85ef567e93b2eddcbd19ae70a2daac18fc886c5303ea56d4b6dc281d39f4f3e9 -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.ex_expfunc--claude-reviewer--2026-10-17T12_20_36Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_expfunc ed839d34f480cba1c0ebc41bbfe679cc by=claude-reviewer source=A:ex:expfunc@bd45b535010dec4f0a3fd33a96a52f00a138499f3145d6b0e5c89d643405ac28 source=A:sec5:overview@85ef567e93b2eddcbd19ae70a2daac18fc886c5303ea56d4b6dc281d39f4f3e9 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.ex_expfunc--claude-auditor--2026-10-19T03_34_12Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_expfunc ed839d34f480cba1c0ebc41bbfe679cc by=claude-auditor source=A:ex:expfunc@6ba8e9a8bd4a3a1d756a510bfc8571612af5e4c854e3bd45a28c1b5172afaaad source=A:sec5:overview@85ef567e93b2eddcbd19ae70a2daac18fc886c5303ea56d4b6dc281d39f4f3e9 -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_expfunc_limin ed839d34f480cba1dc8d682dbdc81fa7 by=claude-author source=A:ex:expfunc@bd45b535010dec4f0a3fd33a96a52f00a138499f3145d6b0e5c89d643405ac28 source=A:intro:limin-comparison@90030b2d20a48b0ae1854a8fb2d4053ad1be2da6ece678b13095bd33e99bda43 source=A:sec5:overview@85ef567e93b2eddcbd19ae70a2daac18fc886c5303ea56d4b6dc281d39f4f3e9 -->
Review by claude-reviewer: broader (report `reports/Dissertation.PaperSpec.A.ex_expfunc_limin--claude-reviewer--2026-10-17T16_03_52Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_expfunc_limin ed839d34f480cba1dc8d682dbdc81fa7 by=claude-reviewer source=A:ex:expfunc@bd45b535010dec4f0a3fd33a96a52f00a138499f3145d6b0e5c89d643405ac28 source=A:intro:limin-comparison@90030b2d20a48b0ae1854a8fb2d4053ad1be2da6ece678b13095bd33e99bda43 source=A:sec5:overview@85ef567e93b2eddcbd19ae70a2daac18fc886c5303ea56d4b6dc281d39f4f3e9 -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.ex_expfunc_limin--claude-auditor--2026-10-19T03_34_13Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_expfunc_limin ed839d34f480cba1dc8d682dbdc81fa7 by=claude-auditor source=A:ex:expfunc@6ba8e9a8bd4a3a1d756a510bfc8571612af5e4c854e3bd45a28c1b5172afaaad source=A:intro:limin-comparison@90030b2d20a48b0ae1854a8fb2d4053ad1be2da6ece678b13095bd33e99bda43 source=A:sec5:overview@85ef567e93b2eddcbd19ae70a2daac18fc886c5303ea56d4b6dc281d39f4f3e9 -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_expfunc_jump ed839d34f480cba1e622a1683bfc9f0d by=claude-author source=A:ex:expfunc@bd45b535010dec4f0a3fd33a96a52f00a138499f3145d6b0e5c89d643405ac28 -->
Review by claude-reviewer: broader (report `reports/Dissertation.PaperSpec.A.ex_expfunc_jump--claude-reviewer--2026-10-17T16_03_52Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_expfunc_jump ed839d34f480cba1e622a1683bfc9f0d by=claude-reviewer source=A:ex:expfunc@bd45b535010dec4f0a3fd33a96a52f00a138499f3145d6b0e5c89d643405ac28 -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.ex_expfunc_jump--claude-auditor--2026-10-19T03_31_22Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_expfunc_jump ed839d34f480cba1e622a1683bfc9f0d by=claude-auditor source=A:ex:expfunc@6ba8e9a8bd4a3a1d756a510bfc8571612af5e4c854e3bd45a28c1b5172afaaad -->

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

<!-- spec-review: Dissertation.PaperSpec.A.rem_diag_mono ed839d34f480cba146c1633f8e03b86c by=claude-author source=A:rem:diag-mono@7928dd1d49b99eb2d2a145a7e4d29d2497427effb69158a6c0887b5532f9856a source=A:abstract@3e98e9839e7e2470c7619601cd0e8f5468477dfdc4dc1f5681314fc4ca1483a9 source=A:conclusion@c886edc62e0561a1e17a961ffd1d0527a5bae43a5607635ce8e247276c91a829 -->
Review by claude-reviewer: broader (report `reports/Dissertation.PaperSpec.A.rem_diag_mono--claude-reviewer--2026-10-17T16_05_52Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.rem_diag_mono ed839d34f480cba146c1633f8e03b86c by=claude-reviewer source=A:rem:diag-mono@7928dd1d49b99eb2d2a145a7e4d29d2497427effb69158a6c0887b5532f9856a source=A:abstract@3e98e9839e7e2470c7619601cd0e8f5468477dfdc4dc1f5681314fc4ca1483a9 source=A:conclusion@c886edc62e0561a1e17a961ffd1d0527a5bae43a5607635ce8e247276c91a829 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.rem_diag_mono--claude-auditor--2026-10-19T03_34_01Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.rem_diag_mono ed839d34f480cba146c1633f8e03b86c by=claude-auditor source=A:rem:diag-mono@7928dd1d49b99eb2d2a145a7e4d29d2497427effb69158a6c0887b5532f9856a source=A:abstract@3e98e9839e7e2470c7619601cd0e8f5468477dfdc4dc1f5681314fc4ca1483a9 source=A:conclusion@c886edc62e0561a1e17a961ffd1d0527a5bae43a5607635ce8e247276c91a829 -->
<!-- spec-review: Dissertation.PaperSpec.A.rem_diag_mono_converse ed839d34f480cba14b5e4594e14d9dc7 by=claude-author source=A:rem:diag-mono@7928dd1d49b99eb2d2a145a7e4d29d2497427effb69158a6c0887b5532f9856a source=A:abstract@3e98e9839e7e2470c7619601cd0e8f5468477dfdc4dc1f5681314fc4ca1483a9 source=A:conclusion@c886edc62e0561a1e17a961ffd1d0527a5bae43a5607635ce8e247276c91a829 -->
Review by claude-reviewer: faithful (report `reports/Dissertation.PaperSpec.A.rem_diag_mono_converse--claude-reviewer--2026-10-17T16_05_52Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.rem_diag_mono_converse ed839d34f480cba14b5e4594e14d9dc7 by=claude-reviewer source=A:rem:diag-mono@7928dd1d49b99eb2d2a145a7e4d29d2497427effb69158a6c0887b5532f9856a source=A:abstract@3e98e9839e7e2470c7619601cd0e8f5468477dfdc4dc1f5681314fc4ca1483a9 source=A:conclusion@c886edc62e0561a1e17a961ffd1d0527a5bae43a5607635ce8e247276c91a829 -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.rem_diag_mono_converse--claude-auditor--2026-10-19T03_36_03Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.rem_diag_mono_converse ed839d34f480cba14b5e4594e14d9dc7 by=claude-auditor source=A:rem:diag-mono@7928dd1d49b99eb2d2a145a7e4d29d2497427effb69158a6c0887b5532f9856a source=A:abstract@3e98e9839e7e2470c7619601cd0e8f5468477dfdc4dc1f5681314fc4ca1483a9 source=A:conclusion@c886edc62e0561a1e17a961ffd1d0527a5bae43a5607635ce8e247276c91a829 -->
<!-- spec-review: Dissertation.PaperSpec.A.rem_intrinsic_uniform ed839d34f480cba13b7a9a5f65a5b218 by=claude-author source=A:rem:intrinsic@f295e589f911d066b117817c51144d266f818d7cbded73c7095853895483c166 -->
Review by claude-reviewer: faithful (report `reports/Dissertation.PaperSpec.A.rem_intrinsic_uniform--claude-reviewer--2026-10-17T16_03_52Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.rem_intrinsic_uniform ed839d34f480cba13b7a9a5f65a5b218 by=claude-reviewer source=A:rem:intrinsic@f295e589f911d066b117817c51144d266f818d7cbded73c7095853895483c166 -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.rem_intrinsic_uniform--claude-auditor--2026-10-19T03_31_22Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.rem_intrinsic_uniform ed839d34f480cba13b7a9a5f65a5b218 by=claude-auditor source=A:rem:intrinsic@f295e589f911d066b117817c51144d266f818d7cbded73c7095853895483c166 -->
<!-- spec-review: Dissertation.PaperSpec.A.rem_intrinsic_coupling ed839d34f480cba1ff8eb9ca359fa48b by=claude-author source=A:rem:intrinsic@f295e589f911d066b117817c51144d266f818d7cbded73c7095853895483c166 -->
Review by claude-reviewer: faithful (report `reports/Dissertation.PaperSpec.A.rem_intrinsic_coupling--claude-reviewer--2026-10-17T16_03_53Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.rem_intrinsic_coupling ed839d34f480cba1ff8eb9ca359fa48b by=claude-reviewer source=A:rem:intrinsic@f295e589f911d066b117817c51144d266f818d7cbded73c7095853895483c166 -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.rem_intrinsic_coupling--claude-auditor--2026-10-19T03_36_39Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.rem_intrinsic_coupling ed839d34f480cba1ff8eb9ca359fa48b by=claude-auditor source=A:rem:intrinsic@f295e589f911d066b117817c51144d266f818d7cbded73c7095853895483c166 -->
<!-- spec-review: Dissertation.PaperSpec.A.rem_intrinsic_basis ed839d34f480cba132c02ed3a09a0eba by=claude-author source=A:rem:intrinsic@f295e589f911d066b117817c51144d266f818d7cbded73c7095853895483c166 -->
Review by claude-reviewer: broader (report `reports/Dissertation.PaperSpec.A.rem_intrinsic_basis--claude-reviewer--2026-10-17T16_05_52Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.rem_intrinsic_basis ed839d34f480cba132c02ed3a09a0eba by=claude-reviewer source=A:rem:intrinsic@f295e589f911d066b117817c51144d266f818d7cbded73c7095853895483c166 -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.rem_intrinsic_basis--claude-auditor--2026-10-19T03_34_37Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.rem_intrinsic_basis ed839d34f480cba132c02ed3a09a0eba by=claude-auditor source=A:rem:intrinsic@f295e589f911d066b117817c51144d266f818d7cbded73c7095853895483c166 -->

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

<!-- spec-review: Dissertation.PaperSpec.A.sec2_separable ed839d34f480cba1673cfd9d331f5aa6 by=claude-author source=A:sec2:separable-L2nu@ae53c7fb64bdc4c1d458158131bce4ad8a6101350c43ccc2c48c3c458f6e166e -->
Review by claude-reviewer: faithful (report `reports/Dissertation.PaperSpec.A.sec2_separable--claude-reviewer--2026-10-17T12_22_48Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.sec2_separable ed839d34f480cba1673cfd9d331f5aa6 by=claude-reviewer source=A:sec2:separable-L2nu@ae53c7fb64bdc4c1d458158131bce4ad8a6101350c43ccc2c48c3c458f6e166e -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.sec2_separable--claude-auditor--2026-10-19T03_34_36Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.sec2_separable ed839d34f480cba1673cfd9d331f5aa6 by=claude-auditor source=A:sec2:separable-L2nu@ae53c7fb64bdc4c1d458158131bce4ad8a6101350c43ccc2c48c3c458f6e166e -->
<!-- spec-review: Dissertation.PaperSpec.A.sec2_infinite_activity ed839d34f480cba13a9f48f6bc72d40f by=claude-author source=A:sec2:infinite-activity-atoms@9f39b94445462cf5bd885113323065e33b702bc828630f1707c4ea24b315889e -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.sec2_infinite_activity--claude-reviewer--2026-10-17T12_21_04Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.sec2_infinite_activity ed839d34f480cba13a9f48f6bc72d40f by=claude-reviewer source=A:sec2:infinite-activity-atoms@9f39b94445462cf5bd885113323065e33b702bc828630f1707c4ea24b315889e -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.sec2_infinite_activity--claude-auditor--2026-10-19T03_34_37Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.sec2_infinite_activity ed839d34f480cba13a9f48f6bc72d40f by=claude-auditor source=A:sec2:infinite-activity-atoms@9f39b94445462cf5bd885113323065e33b702bc828630f1707c4ea24b315889e -->
<!-- spec-review: Dissertation.PaperSpec.A.eq_compid ed839d34f480cba1551f4f42ffdf2fa8 by=claude-author source=A:eq:compid@a62f2f651f15297ca0005558e8980950d28aaaa1062298dd4c00ea019fe06299 -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.eq_compid--claude-reviewer--2026-10-17T12_11_27Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_compid ed839d34f480cba1551f4f42ffdf2fa8 by=claude-reviewer source=A:eq:compid@a62f2f651f15297ca0005558e8980950d28aaaa1062298dd4c00ea019fe06299 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.eq_compid--claude-auditor--2026-10-19T03_31_22Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_compid ed839d34f480cba1551f4f42ffdf2fa8 by=claude-auditor source=A:eq:compid@a62f2f651f15297ca0005558e8980950d28aaaa1062298dd4c00ea019fe06299 -->
<!-- spec-review: Dissertation.PaperSpec.A.eq_zeromean ed839d34f480cba1ca027a9d4d1614c9 by=claude-author source=A:eq:zeromean@74dcd6eaa5929b1a9d4f4a1b6af308d62e1c2dd6a28ef7f0329a7ba65184f4ee -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.eq_zeromean--claude-reviewer--2026-10-17T12_15_00Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_zeromean ed839d34f480cba1ca027a9d4d1614c9 by=claude-reviewer source=A:eq:zeromean@74dcd6eaa5929b1a9d4f4a1b6af308d62e1c2dd6a28ef7f0329a7ba65184f4ee -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.eq_zeromean--claude-auditor--2026-10-19T03_31_22Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_zeromean ed839d34f480cba1ca027a9d4d1614c9 by=claude-auditor source=A:eq:zeromean@74dcd6eaa5929b1a9d4f4a1b6af308d62e1c2dd6a28ef7f0329a7ba65184f4ee -->
<!-- spec-review: Dissertation.PaperSpec.A.sec2_prp ed839d34f480cba1577f0ed2476fcdb5 by=claude-author source=A:sec2:prp@4abed1a193ffeafc8c98d073e7c33bcde2f293ba9bb58b16d1a0464060b8dcea -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.sec2_prp--claude-reviewer--2026-10-17T12_22_12Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.sec2_prp ed839d34f480cba1577f0ed2476fcdb5 by=claude-reviewer source=A:sec2:prp@4abed1a193ffeafc8c98d073e7c33bcde2f293ba9bb58b16d1a0464060b8dcea -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.sec2_prp--claude-auditor--2026-10-19T03_34_14Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.sec2_prp ed839d34f480cba1577f0ed2476fcdb5 by=claude-auditor source=A:sec2:prp@4abed1a193ffeafc8c98d073e7c33bcde2f293ba9bb58b16d1a0464060b8dcea -->
<!-- spec-review: Dissertation.PaperSpec.A.sec2_hborel ed839d34f480cba1c7bf6ee7f1e38851 by=claude-author source=A:sec2:hborel-derivation@212a07e14afa5d0609973352865fe2ce8ae09c6d715739e9e87b738950e721a8 -->
Review by claude-reviewer: faithful (report `reports/Dissertation.PaperSpec.A.sec2_hborel--claude-reviewer--2026-10-17T12_20_16Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.sec2_hborel ed839d34f480cba1c7bf6ee7f1e38851 by=claude-reviewer source=A:sec2:hborel-derivation@212a07e14afa5d0609973352865fe2ce8ae09c6d715739e9e87b738950e721a8 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.sec2_hborel--claude-auditor--2026-10-19T03_31_21Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.sec2_hborel ed839d34f480cba1c7bf6ee7f1e38851 by=claude-auditor source=A:sec2:hborel-derivation@212a07e14afa5d0609973352865fe2ce8ae09c6d715739e9e87b738950e721a8 -->

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

<!-- spec-review: Dissertation.PaperSpec.A.eq_fubiniiso ed839d34f480cba1f8905adfcaf41890 by=claude-author source=A:eq:fubiniiso@597a92f6004ad8db02800eef365f8f95188c907f3f53c17cccf909c2a49ed061 -->
Review by claude-reviewer: broader (report `reports/Dissertation.PaperSpec.A.eq_fubiniiso--claude-reviewer--2026-10-17T12_13_20Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_fubiniiso ed839d34f480cba1f8905adfcaf41890 by=claude-reviewer source=A:eq:fubiniiso@597a92f6004ad8db02800eef365f8f95188c907f3f53c17cccf909c2a49ed061 -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.eq_fubiniiso--claude-auditor--2026-10-19T03_31_21Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_fubiniiso ed839d34f480cba1f8905adfcaf41890 by=claude-auditor source=A:eq:fubiniiso@597a92f6004ad8db02800eef365f8f95188c907f3f53c17cccf909c2a49ed061 -->

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

<!-- spec-review: Dissertation.PaperSpec.A.eq_coefmeas ed839d34f480cba11ac3211646c24c86 by=claude-author source=A:eq:coefmeas@951bc71349ab7748916546e7dcfd8ef117078c5b8dcd1e5f4e035106ef459170 -->
Review by claude-reviewer: broader (report `reports/Dissertation.PaperSpec.A.eq_coefmeas--claude-reviewer--2026-10-17T12_08_44Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_coefmeas ed839d34f480cba11ac3211646c24c86 by=claude-reviewer source=A:eq:coefmeas@951bc71349ab7748916546e7dcfd8ef117078c5b8dcd1e5f4e035106ef459170 -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.eq_coefmeas--claude-auditor--2026-10-19T03_31_22Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_coefmeas ed839d34f480cba11ac3211646c24c86 by=claude-auditor source=A:eq:coefmeas@951bc71349ab7748916546e7dcfd8ef117078c5b8dcd1e5f4e035106ef459170 -->

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

<!-- spec-review: Dissertation.PaperSpec.A.eq_coefmeas_jump ed839d34f480cba1e13c6b7ca8ccca73 by=claude-author source=A:eq:coefmeas@951bc71349ab7748916546e7dcfd8ef117078c5b8dcd1e5f4e035106ef459170 -->
Review by claude-reviewer: broader (report `reports/Dissertation.PaperSpec.A.eq_coefmeas_jump--claude-reviewer--2026-10-17T16_03_52Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_coefmeas_jump ed839d34f480cba1e13c6b7ca8ccca73 by=claude-reviewer source=A:eq:coefmeas@951bc71349ab7748916546e7dcfd8ef117078c5b8dcd1e5f4e035106ef459170 -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.eq_coefmeas_jump--claude-auditor--2026-10-19T03_34_12Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_coefmeas_jump ed839d34f480cba1e13c6b7ca8ccca73 by=claude-auditor source=A:eq:coefmeas@951bc71349ab7748916546e7dcfd8ef117078c5b8dcd1e5f4e035106ef459170 -->

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

<!-- spec-review: Dissertation.PaperSpec.A.rem_cwp_class ed839d34f480cba1dac1a53237b9beb3 by=claude-author source=A:rem:cwp-class@391a3db056fefb35dea3e08d03c460ac0787411fb1d02916f36e10dbfe0f733a source=A:rem:uniq-no-integ@16ace776485cb414a0ad39fba869a577ec053811b32b39e09709fb01a4e0f75e -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.rem_cwp_class--claude-reviewer--2026-10-17T12_12_05Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.rem_cwp_class ed839d34f480cba1dac1a53237b9beb3 by=claude-reviewer source=A:rem:cwp-class@391a3db056fefb35dea3e08d03c460ac0787411fb1d02916f36e10dbfe0f733a source=A:rem:uniq-no-integ@16ace776485cb414a0ad39fba869a577ec053811b32b39e09709fb01a4e0f75e -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.rem_cwp_class--claude-auditor--2026-10-19T03_38_10Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.rem_cwp_class ed839d34f480cba1dac1a53237b9beb3 by=claude-auditor source=A:rem:cwp-class@391a3db056fefb35dea3e08d03c460ac0787411fb1d02916f36e10dbfe0f733a source=A:rem:uniq-no-integ@867ca613bdc7ff8b7ff2ba56fd6a8fa9594e1e7b57e69975069db081dd311798 -->

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

<!-- spec-review: Dissertation.PaperSpec.A.thm_stab_companion ed839d34f480cba10ff3a550a92ccddf by=claude-author source=A:thm3.1:companion@11a0e3868fdbf57060a945ccaf31e655f33cacd376b0122ef3bfcbde089339f1 -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.thm_stab_companion--claude-reviewer--2026-10-17T12_19_01Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.thm_stab_companion ed839d34f480cba10ff3a550a92ccddf by=claude-reviewer source=A:thm3.1:companion@11a0e3868fdbf57060a945ccaf31e655f33cacd376b0122ef3bfcbde089339f1 -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.thm_stab_companion--claude-auditor--2026-10-19T03_37_17Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.thm_stab_companion ed839d34f480cba10ff3a550a92ccddf by=claude-auditor source=A:thm3.1:companion@11a0e3868fdbf57060a945ccaf31e655f33cacd376b0122ef3bfcbde089339f1 -->
<!-- spec-review: Dissertation.PaperSpec.A.thm_stab_data ed839d34f480cba1f26d5949b31ba63f by=claude-author source=A:thm3.1:companion@11a0e3868fdbf57060a945ccaf31e655f33cacd376b0122ef3bfcbde089339f1 -->
Review by claude-reviewer: faithful (report `reports/Dissertation.PaperSpec.A.thm_stab_data--claude-reviewer--2026-10-17T16_05_53Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.thm_stab_data ed839d34f480cba1f26d5949b31ba63f by=claude-reviewer source=A:thm3.1:companion@11a0e3868fdbf57060a945ccaf31e655f33cacd376b0122ef3bfcbde089339f1 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.thm_stab_data--claude-auditor--2026-10-19T03_37_06Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.thm_stab_data ed839d34f480cba1f26d5949b31ba63f by=claude-auditor source=A:thm3.1:companion@11a0e3868fdbf57060a945ccaf31e655f33cacd376b0122ef3bfcbde089339f1 -->
<!-- spec-review: Dissertation.PaperSpec.A.thm_stab_minimal ed839d34f480cba127494e1cb3f498aa by=claude-author source=A:thm3.1:companion@11a0e3868fdbf57060a945ccaf31e655f33cacd376b0122ef3bfcbde089339f1 -->
Review by claude-reviewer: faithful (report `reports/Dissertation.PaperSpec.A.thm_stab_minimal--claude-reviewer--2026-10-17T16_05_53Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.thm_stab_minimal ed839d34f480cba127494e1cb3f498aa by=claude-reviewer source=A:thm3.1:companion@11a0e3868fdbf57060a945ccaf31e655f33cacd376b0122ef3bfcbde089339f1 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.thm_stab_minimal--claude-auditor--2026-10-19T03_36_39Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.thm_stab_minimal ed839d34f480cba127494e1cb3f498aa by=claude-auditor source=A:thm3.1:companion@11a0e3868fdbf57060a945ccaf31e655f33cacd376b0122ef3bfcbde089339f1 -->

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

<!-- spec-review: Dissertation.PaperSpec.A.sec5_limin ed839d34f480cba132884b458e231942 by=claude-author source=A:sec:examples@3f24646e833f5a7b1bfdeb3449b26795f12ebfae2cde62dff93327979908d073 -->
Review by claude-reviewer: broader (report `reports/Dissertation.PaperSpec.A.sec5_limin--claude-reviewer--2026-10-17T12_25_43Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.sec5_limin ed839d34f480cba132884b458e231942 by=claude-reviewer source=A:sec:examples@3f24646e833f5a7b1bfdeb3449b26795f12ebfae2cde62dff93327979908d073 -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.sec5_limin--claude-auditor--2026-10-19T03_31_22Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.sec5_limin ed839d34f480cba132884b458e231942 by=claude-auditor source=A:sec:examples@3f24646e833f5a7b1bfdeb3449b26795f12ebfae2cde62dff93327979908d073 -->

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

<!-- spec-review: Dissertation.PaperSpec.A.rem_generalrank ed839d34f480cba1bcd1d82734738c5b by=claude-author source=A:rem:generalrank@d7d2976d856eb17cca4f2ce81183317ed11c078bb8c7bf4a7d4da20f32b3da6d -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.rem_generalrank--claude-reviewer--2026-10-17T12_13_00Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.rem_generalrank ed839d34f480cba1bcd1d82734738c5b by=claude-reviewer source=A:rem:generalrank@d7d2976d856eb17cca4f2ce81183317ed11c078bb8c7bf4a7d4da20f32b3da6d -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.rem_generalrank--claude-auditor--2026-10-19T03_36_13Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.rem_generalrank ed839d34f480cba1bcd1d82734738c5b by=claude-auditor source=A:rem:generalrank@d7d2976d856eb17cca4f2ce81183317ed11c078bb8c7bf4a7d4da20f32b3da6d -->
<!-- spec-review: Dissertation.PaperSpec.A.rem_generalrank_wp ed839d34f480cba118d1835a02488a97 by=claude-author source=A:rem:generalrank@d7d2976d856eb17cca4f2ce81183317ed11c078bb8c7bf4a7d4da20f32b3da6d -->
Review by claude-reviewer: faithful (report `reports/Dissertation.PaperSpec.A.rem_generalrank_wp--claude-reviewer--2026-10-17T16_05_53Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.rem_generalrank_wp ed839d34f480cba118d1835a02488a97 by=claude-reviewer source=A:rem:generalrank@d7d2976d856eb17cca4f2ce81183317ed11c078bb8c7bf4a7d4da20f32b3da6d -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.rem_generalrank_wp--claude-auditor--2026-10-19T03_37_46Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.rem_generalrank_wp ed839d34f480cba118d1835a02488a97 by=claude-auditor source=A:rem:generalrank@d7d2976d856eb17cca4f2ce81183317ed11c078bb8c7bf4a7d4da20f32b3da6d -->

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

<!-- spec-review: Dissertation.PaperSpec.A.lem_lawflow ed839d34f480cba1090c1a53f2a6cf7f by=claude-author source=A:lem:lawflow@b61210309cec8802a77053643f14f17525726292aaf8f26f098a3e85223633b5 -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.lem_lawflow--claude-reviewer--2026-10-17T12_27_30Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.lem_lawflow ed839d34f480cba1090c1a53f2a6cf7f by=claude-reviewer source=A:lem:lawflow@b61210309cec8802a77053643f14f17525726292aaf8f26f098a3e85223633b5 -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.lem_lawflow--claude-auditor--2026-10-19T03_36_15Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.lem_lawflow ed839d34f480cba1090c1a53f2a6cf7f by=claude-auditor source=A:lem:lawflow@b61210309cec8802a77053643f14f17525726292aaf8f26f098a3e85223633b5 -->
<!-- spec-review: Dissertation.PaperSpec.A.lem_lawflow_invariant ed839d34f480cba184c9d1f8d6f2b814 by=claude-author source=A:lem:lawflow@b61210309cec8802a77053643f14f17525726292aaf8f26f098a3e85223633b5 -->
Review by claude-reviewer: broader (report `reports/Dissertation.PaperSpec.A.lem_lawflow_invariant--claude-reviewer--2026-10-17T16_03_53Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.lem_lawflow_invariant ed839d34f480cba184c9d1f8d6f2b814 by=claude-reviewer source=A:lem:lawflow@b61210309cec8802a77053643f14f17525726292aaf8f26f098a3e85223633b5 -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.lem_lawflow_invariant--claude-auditor--2026-10-19T03_38_36Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.lem_lawflow_invariant ed839d34f480cba184c9d1f8d6f2b814 by=claude-auditor source=A:lem:lawflow@b61210309cec8802a77053643f14f17525726292aaf8f26f098a3e85223633b5 -->

## Lemma A.1, Step 1 of the proof, the left limits, the separability of `H`, the jump channel and the predictable field: `Dissertation.PaperSpec.A.lemA1_leftlim`, `lemA1_separable`, `lemA1_U`, `lemA1_pred`

Manuscript (proof of Lemma `lem:lawflow`, Step 1, lines 25–42): "*Step 1 (the field).* The left
limits `X₋, Y₋` are predictable and agree with `X, Y` `dt ⊗ dP`-a.e., as càdlàg paths jump at
countably many times, so `∫_0^T 1{X_{t−} ≠ X_t} dt = 0` almost surely; the hypothesis on `X, Y`
thus passes to them, and `H` is separable because `L²(ν)` is. The `Z`-coordinate is predictable
and square-integrable by assumption. For the `U`-coordinate, the integrability hypothesis and the
Fubini isometry (2.4) give `U ∈ L²([0, T] × Ω × E) ≅ L²([0, T] × Ω; L²(ν))`, so the induced map
`(t, ω) ↦ U_t(ω, ·)` admits a predictable, strongly measurable `L²(ν)`-valued representative.
`Θ⁻` is therefore a predictable, hence jointly measurable, `H`-valued field with
`𝔼 ∫_0^T ‖Θ⁻_t‖²_H dt < ∞`, that is, `Θ⁻ ∈ L²([0, T] × Ω; H)`." The claim `A:lemA1:pettis` is
pinned at line 48, in the last sentence of Step 1 (lines 43–51); these four clauses read the
sentences before it, as the claim's scope note records.

Propositions (each, except `lemA1_separable`, under `CadlagPredTuple ℱ P ν T X Y Z U`, the
hypotheses of Lemma A.1 verbatim from `lem_lawflow`, the setting of `lemA1_L2`):

* `lemA1_leftlim`: (i) every coordinate of `leftLimProc X` and of `leftLimProc Y` is
  `Predictable ℱ`; (ii) for every coordinate and every `ω`, the set `{t | X_{t−}(ω) ≠ X_t(ω)}` is
  countable and `∫⁻_{[0, T]} 1_{{t | X_{t−}(ω) ≠ X_t(ω)}}(t) dt = 0`, and the same for `Y`;
  (iii) for `dt|_{[0, T]} ⊗ P`-almost every `(t, ω)`, `X_{t−}(ω) = X_t(ω)` and
  `Y_{t−}(ω) = Y_t(ω)` in every coordinate; (iv) every coordinate of `X₋` and of `Y₋` has finite
  energy on `[0, T]`.
* `lemA1_separable`: for `ν` σ-finite on a countably generated `E` and all `n, m, d`, the spaces
  `Lp (EuclideanSpace ℝ (Fin m)) 2 ν` (`L²(ν; ℝᵐ)`) and `TupleL2 …` (`H` with its Hilbert norm)
  are separable.
* `lemA1_U`: `((t, ω), e) ↦ (U_{k,t}(ω, e))_k` lies in `L²` of `(dt|_{[0, T]} ⊗ P) ⊗ ν` with the
  Euclidean norm; and there is `V : Ω → ℝ → L²(ν; ℝᵐ)` with `Predictable ℱ V`,
  `(t, ω) ↦ V_t(ω)` in `L²(dt|_{[0, T]} ⊗ P; L²(ν; ℝᵐ))` (`MemLp … 2`), and, for
  `dt|_{[0, T]} ⊗ P`-almost every `(t, ω)`, `V_t(ω) = (e ↦ (U_{k,t}(ω, e))_k)` `ν`-almost
  everywhere.
* `lemA1_pred`: `(t, ω) ↦ toL2 (Θ⁻_t(ω))` is `Predictable ℱ`, with
  `Θ⁻_t(ω) = tupleAt ν (leftLimProc X) (leftLimProc Y) Z U t ω`, as in `lemA1_L2`.

Readings:

* The setting is that of `lemA1_L2`: the processes are indexed by `ℝ`, `X, Y` adapted with every
  path right-continuous with left limits on all of `ℝ`, `Z` predictable, `U` marked predictable,
  each of finite energy on `[0, T]`. A tuple of the paper, given on `[0, T]`, is extended to `ℝ`
  (`X, Y` constant before `0` and after `T`, `Z` and `U` zero off `(0, T]`). The marked
  predictable σ-algebra is generated by rectangles over times `(r, q]` with `r ≥ 0`, so a marked
  predictable `U` takes a single value at all times `≤ 0`: the paper's `U_0`, which is only
  measurable for `ℱ₀ ⊗ 𝓔`, is replaced by that value. The change is on the Lebesgue-null time `0`
  and leaves every `dt`-integral and every `L²` class unchanged. It leaves the conclusions of
  `lemA1_leftlim` and `lemA1_U` unchanged because they are statements `dt ⊗ dP`-almost
  everywhere ((iii) and the representative `V`) or do not involve `U` ((i), (ii), (iv)). For
  `lemA1_pred` that is not the reason: its conclusion, the predictability of the field, holds at
  every point and involves `U` at the time `0`. The change is harmless there because the paper
  asserts only that the induced map `(t, ω) ↦ U_t(ω, ·)` admits some predictable representative
  and that `Θ⁻` built with it is predictable; the canonical section of the version `U 1_{t > 0}`
  is such a representative (it differs from `U_t(ω, ·)` only at the time `0`, so
  `dt ⊗ dP`-almost nowhere), and the proposition is the predictability of `Θ⁻` built with it.
* The instantiation that gives the printed claims. `lemA1_leftlim`, `lemA1_U` and `lemA1_pred`
  are broader than the printed sentences in generality only: they hold on every probability
  space, for every filtration indexed by `ℝ` (no usual conditions, no Brownian–Poisson
  structure), for all `n, m, d : ℕ` and `T : ℝ`, and (ii) states the countability of the jump set
  on all of `ℝ`. The printed claims are their instance at the standing filtration of §2 extended
  by `ℱ₀` on `(−∞, 0]`, at `n, m, d ≥ 1` and `T > 0`, with the paper's `X, Y` on `[0, T]` extended
  by `X_0`, `Y_0` before `0` (so the left limit at `0` is the convention `X_{0−} = X_0`) and by
  `X_T`, `Y_T` after `T`, `Z` zero off `(0, T]`, and `U` taken in its version `U 1_{t > 0}`, as in
  the first reading.
* "Predictable": `LevyStochCalc.Probability.Predictable ℱ`, strong measurability on `ℝ × Ω` for the
  predictable σ-algebra generated by `(r, ∞) × A` with `A ∈ ℱ_r` and `(−∞, 0] × A` with `A ∈ ℱ₀`
  (in the closure of `CadlagPredTuple`, reviewed in `definitions.md`); for a real process it is
  measurability. The paper's predictable σ-field on `Ω × [0, T]` is its trace there.
* "agree with `X, Y` `dt ⊗ dP`-a.e.": (iii), for Lebesgue measure on `[0, T]` times `P`.
* "càdlàg paths jump at countably many times, so `∫_0^T 1{X_{t−} ≠ X_t} dt = 0` almost surely":
  (ii), for every `ω`, which is stronger than almost surely; the integral of the indicator is a
  lower integral in `[0, ∞]`.
* "the hypothesis on `X, Y` thus passes to them": the hypothesis is the finite energy of the
  coordinates of `CadlagPredTuple` (the printed `𝔼 ∫_0^T (|X_t|² + |Y_t|² + …) dt < ∞`, read
  coordinatewise); (iv) states it for `X₋, Y₋`.
* "`H` is separable because `L²(ν)` is": `lemA1_separable` states both separabilities, under §2's
  standing assumption on the marks (σ-finite `ν` on a countably generated `E`, which the paper
  gives "so that `L²(ν; ℝʲ)` is separable for every `j ≥ 1`", `sections/02-model-assumptions.tex`
  lines 6–7). `L²(ν)` here is the jump channel `L²(ν; ℝᵐ)` of `H`. The "because" is the proof.
  The representation choices, as the blind audit listed them: (1) the `m × d` channel is
  `EuclideanSpace ℝ (Fin m × Fin d)`, whose norm is the Frobenius norm of the paper; (2) `H` with
  its Hilbert norm is the iterated `WithLp 2` product `TupleL2`, whose norm is
  `(|x|² + |y|² + |z|²_F + ‖u‖²)^{1/2}`, the type the other clauses of the claim use; (3) the
  dimensions range over `ℕ`, `0` included, a trivial extension of `n, m, d ≥ 1`; (4) the paper's
  "for every `j`" is taken at `j = m`, the instance the passage uses for `H`.
* "The `Z`-coordinate is predictable and square-integrable by assumption" restates `Z_pred` and
  `Z_sq` of `CadlagPredTuple` and is not stated separately; the scope note records it.
* The jump channel. "`U ∈ L²([0, T] × Ω × E)`" is the first conjunct of `lemA1_U`, `U` read as an
  `ℝᵐ`-valued function. "`≅ L²([0, T] × Ω; L²(ν))`" is the isometry (2.4), the clause
  `eq_fubiniiso` of `A:eq:fubiniiso`, proved there for every σ-finite base, the predictable
  σ-field with `dt ⊗ dP` included. "The induced map `(t, ω) ↦ U_t(ω, ·)` admits a predictable,
  strongly measurable `L²(ν)`-valued representative" is `V`: `Predictable ℱ V` is literally strong
  measurability for the predictable σ-algebra; `V` lies in `L²([0, T] × Ω; L²(ν))`; and it
  represents the induced map, `V_t(ω) = U_t(ω, ·)` in `L²(ν)` for `dt ⊗ dP`-almost every
  `(t, ω)`, in the form of the proposition of (2.4) (the coercion of `V_t(ω)` is `ν`-almost
  everywhere the section, which makes the section square integrable there).
* "`Θ⁻` is therefore a predictable, hence jointly measurable, `H`-valued field": `lemA1_pred`, in
  `H` with the Hilbert norm. The jump channel of `tupleAt` at `(t, ω)` is the `L²(ν)` class of
  `U_t(ω, ·)` (`uLift`, `0` where the section is not square integrable), the representative `V`
  of the proof of `lemA1_U`. "Hence jointly measurable" and the `L²` bound are `lemA1_L2`.

Proofs (for the reader): `X_{s−}` is the limit of the values of `X` at the dyadic grid points
strictly below `s`, each known before `s`, so `X₋` is predictable
(`measurable_predictableSigma_of_tendsto_leftGridPoint`); the jump set of a càdlàg function is
countable (`countable_setOf_ne_leftLim`), hence Lebesgue-null; (iii) is the almost-everywhere
equality of the tuples (`ae_toL2_tupleAt_leftLim_eq`), and the energies of `X₋` and `X` agree
path by path. `L²(ν; ℝᵐ)` is second countable for a σ-finite `ν` on a countably generated space,
and so are finite products of such spaces. A generator `F × (r, q] × B` of the marked predictable
σ-algebra is the image of `((r, q] × F) × B`, a predictable set times a mark set, so a marked
predictable `U` is measurable for the product of the predictable σ-algebra and the σ-algebra of
the marks (`measurable_swap_markedPredictableSigma`), and the `L²(ν)` class of its sections is
predictable (`stronglyMeasurable_uLift`, through the distances to the points of a countable dense
set, with no Pettis theorem). That class is dominated by `‖toL2 Θ_t(ω)‖`, hence square
integrable, and it is the class of the section wherever the section is square integrable, which
is `dt ⊗ dP`-almost everywhere because the marked energy is finite. The four channels of `Θ⁻`
being predictable, so is `Θ⁻`.

Witnesses: `Dissertation.Acceptance.A.lemA1_coin_hypotheses` for `lemA1_leftlim`, `lemA1_U` and
`lemA1_pred`: on `Bool` with the uniform law and the filtration `coinFiltration` of the fair sign
`ξ` revealed at `t = 1/2` (trivial before `1/2`, so the event `{ξ = 1}` is not known at time `0`),
`n = m = d = 1`, `ν = δ₀` on `ℝ` and `T = 1`, the tuple `X = Y = ξ 1_{t ≥ 1/2}`,
`Z = U = 1_{(0, 1]}` satisfies `CadlagPredTuple`; `X` jumps at `1/2` (the left limit `0` differs
from the value `1` at `ω = true`), `X_1` is not almost surely constant, and `U` does not vanish.
`Dissertation.Acceptance.A.lemA1_polish_hypotheses` for `lemA1_separable`: Lebesgue measure on
`ℝ`, σ-finite of infinite mass on a countably generated space, for which `L²(ν; ℝᵐ)` is
infinite-dimensional when `m ≥ 1`.

Verdict: broader for `lemA1_leftlim`, `lemA1_U` and `lemA1_pred`, in generality only, with the
instantiation recorded above ((ii) holds for every `ω`, stronger than almost surely); faithful
with representation choices for `lemA1_separable`, which holds for every `n, m, d`.

<!-- spec-review: Dissertation.PaperSpec.A.lemA1_leftlim ed839d34f480cba130f1a54fb940f2d9 by=claude-author source=A:lemA1:pettis@4683d66c9de5e151a16b21a1e6cbac952384cffefeb3e0e4b2eb720fb4a0b746 -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.lemA1_leftlim--claude-auditor--2026-10-20T10_33_33Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.lemA1_leftlim ed839d34f480cba130f1a54fb940f2d9 by=claude-auditor source=A:lemA1:pettis@4683d66c9de5e151a16b21a1e6cbac952384cffefeb3e0e4b2eb720fb4a0b746 -->
<!-- spec-review: Dissertation.PaperSpec.A.lemA1_separable ed839d34f480cba1e132af851a6dd7cf by=claude-author source=A:lemA1:pettis@4683d66c9de5e151a16b21a1e6cbac952384cffefeb3e0e4b2eb720fb4a0b746 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.lemA1_separable--claude-auditor--2026-10-20T10_33_33Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.lemA1_separable ed839d34f480cba1e132af851a6dd7cf by=claude-auditor source=A:lemA1:pettis@4683d66c9de5e151a16b21a1e6cbac952384cffefeb3e0e4b2eb720fb4a0b746 -->
<!-- spec-review: Dissertation.PaperSpec.A.lemA1_U ed839d34f480cba1019406c1cc1330d9 by=claude-author source=A:lemA1:pettis@4683d66c9de5e151a16b21a1e6cbac952384cffefeb3e0e4b2eb720fb4a0b746 -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.lemA1_U--claude-auditor--2026-10-20T10_33_33Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.lemA1_U ed839d34f480cba1019406c1cc1330d9 by=claude-auditor source=A:lemA1:pettis@4683d66c9de5e151a16b21a1e6cbac952384cffefeb3e0e4b2eb720fb4a0b746 -->
<!-- spec-review: Dissertation.PaperSpec.A.lemA1_pred ed839d34f480cba136b795f0b638d045 by=claude-author source=A:lemA1:pettis@4683d66c9de5e151a16b21a1e6cbac952384cffefeb3e0e4b2eb720fb4a0b746 -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.lemA1_pred--claude-auditor--2026-10-20T10_33_33Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.lemA1_pred ed839d34f480cba136b795f0b638d045 by=claude-auditor source=A:lemA1:pettis@4683d66c9de5e151a16b21a1e6cbac952384cffefeb3e0e4b2eb720fb4a0b746 -->

## Lemma A.1, Step 1 of the proof, the Fubini isometry and the Pettis step: `Dissertation.PaperSpec.A.lemA1_L2`, `lemA1_fubini`, `lemA1_pettis`

Manuscript (proof of Lemma `lem:lawflow`, Step 1, lines 36–51): "`Θ⁻` is therefore a predictable,
hence jointly measurable, `H`-valued field with `𝔼 ∫_0^T ‖Θ⁻_t‖²_H dt < ∞`, that is,
`Θ⁻ ∈ L²([0, T] × Ω; H)`. The Fubini isometry of [HNVW, Proposition 1.2.24],
`L²([0, T] × Ω; H) ≅ L²(0, T; L²(Ω; H))`, supplies a strongly measurable `L²(Ω; H)`-valued
representative of `t ↦ Θ⁻_t`; by the Pettis measurability theorem [HNVW, Theorem 1.1.6], that map
takes values in a separable closed subspace of `L²(Ω; H)` off a Lebesgue-null set of times, and
therefore admits a Borel version, agreeing with it for a.e. `t`." The claim is pinned at line 48,
in the second sentence; the first sentence is its input.

Propositions:

* `lemA1_L2`: under `CadlagPredTuple ℱ P ν T X Y Z U` (the hypotheses of Lemma A.1, verbatim from
  `lem_lawflow`), `(t, ω) ↦ toL2 (Θ⁻_t(ω))` is strongly measurable on `ℝ × Ω` and lies in
  `L²(dt|_{[0, T]} ⊗ P; H)` (`MemLp … 2`).
* `lemA1_fubini`: for every probability space `(Ω, P)`, every `ν` σ-finite on a countably
  generated `E`, every `n, m, d` and `T`: a linear isometric equivalence
  `Φ : L²(dt|_{[0, T]} ⊗ P; H) ≃ L²(dt|_{[0, T]}; L²(P; H))` with `Φ(f)(t) = f(t, ·)` `P`-a.e.,
  for almost every `t ∈ [0, T]`.
* `lemA1_pettis`: under the same hypotheses as `lemA1_L2`, there is `F : ℝ → L²(P; H)` which is
  strongly measurable, has `F(t) ∈ V` for every `t` for some closed separable submodule `V`, is
  measurable for the Borel σ-algebra of `L²(P; H)`, and satisfies, for almost every `t ∈ [0, T]`,
  `Θ⁻_t ∈ L²(P; H)` and `F(t) = [Θ⁻_t]`.

Readings:

* The hypotheses, `CadlagPredTuple`, are those of Lemma A.1 for processes indexed by `ℝ`: `X, Y`
  adapted with every path right-continuous with left limits on all of `ℝ`, `Z` predictable, `U`
  marked predictable. A tuple of the paper, given on `[0, T]`, is extended to `ℝ` (`X, Y` constant
  before `0` and after `T`, `Z, U` zero off `(0, T]`). The marked predictable σ-algebra
  (`MarkedPredictable`) is generated by rectangles over times `(r, q]` with `r ≥ 0`, so a marked
  predictable `U` takes a single value at all times `≤ 0`, and the paper's `U_0`, only
  `ℱ₀ ⊗ 𝓔`-measurable, is replaced by that value: a change on the Lebesgue-null time `0`, which
  alters no `dt`-integral and no class in `L²([0, T] × Ω; H)`, and no conclusion here, all of
  which hold `dt ⊗ dP`-almost everywhere or for almost every `t`.
* `H` is the tuple space `ℝⁿ × ℝᵐ × ℝ^{m×d} × L²(ν; ℝᵐ)` with its Hilbert norm: the reviewed type
  `TupleL2` of the four channels, into which the reviewed `toL2` maps a tuple. `Θ⁻_t(ω)` is
  `tupleAt ν (leftLimProc X) (leftLimProc Y) Z U t ω`, as in `lem_lawflow`. The maximum norm of
  `TupleH` gives the same measurability and the same square-integrable functions, but another
  isometry, so the Hilbert norm is used in all three propositions.
* "Jointly measurable": strongly measurable on `ℝ × Ω` for `Borel(ℝ) ⊗` the ambient σ-algebra of
  `Ω`, which for the separable `H` is the same as measurable. "`𝔼 ∫_0^T ‖Θ⁻_t‖² dt < ∞`, that is,
  `Θ⁻ ∈ L²([0, T] × Ω; H)`": `MemLp … 2` for Lebesgue measure on `[0, T]` times `P`. The
  predictability of `Θ⁻`, asserted in the same sentence, is not used by the Fubini step; it is the
  clause `lemA1_pred`, reviewed in the section before this one.
* The isometry: `L²([0, T] × Ω; H)` is `Lp H 2 ((volume.restrict [0, T]).prod P)` and
  `L²(0, T; L²(Ω; H))` is `Lp (Lp H 2 P) 2 (volume.restrict [0, T])`; "≅" is a linear isometric
  equivalence, and the section property `Φ(f)(t) = f(t, ·)` identifies it as the Fubini
  identification of HNVW 1.2.24. It is stated for every probability space, with no countable
  generation of `Ω`, as the paper's filtered space requires.
* "Supplies a strongly measurable `L²(Ω; H)`-valued representative of `t ↦ Θ⁻_t`": a map `F`
  with `F(t) = [Θ⁻_t]` for almost every `t`. HNVW's strong measurability for Lebesgue measure (an
  almost-everywhere limit of simple functions) is implied by `StronglyMeasurable F` (an
  everywhere limit).
* "Takes values in a separable closed subspace of `L²(Ω; H)` off a Lebesgue-null set of times":
  a closed separable submodule `V` with `F(t) ∈ V` for every `t`, which is stronger.
* "Admits a Borel version, agreeing with it for a.e. `t`": `F` itself is measurable for the Borel
  σ-algebra of `L²(Ω; H)` (written `borel _`, since `Lp` carries no σ-algebra instance) and equals
  `[Θ⁻_t]` for almost every `t`. The proposition gives one map with the three properties, which is
  what the passage ends with.
* The cited results, HNVW Proposition 1.2.24 and Theorem 1.1.6, enter the passage through their
  conclusions about these spaces and this map; the propositions state those conclusions, not the
  general theorems.

Proofs (for the reader): `Θ⁻ = Θ` `dt ⊗ dP`-almost everywhere, since càdlàg paths meet their left
limits off countably many times, and `𝔼 ∫_0^T ‖Θ_t‖²_H dt` is the sum of the coordinate energies.
The isometry is the section map `fubiniEquiv`, for an arbitrary σ-finite inner space: the
section map is strongly measurable (`stronglyMeasurable_lp_of_section`) by induction over the
measurable rectangles for indicators cut down to sets of finite measure, then for simple
functions and their limits, so neither the separability of `L²(Ω; H)` nor the Pettis theorem is
assumed. `F` is the section map of `Θ⁻`; its range is separable, and `V` is the closure of its
span.

Witnesses: `Dissertation.Acceptance.A.lemA1_hypotheses` for `lemA1_L2` and `lemA1_pettis`: on
`Bool` with the uniform law and the full filtration, `n = m = d = 1`, `ν = δ₀` on `ℝ` and `T = 1`,
the tuple `X = Y = ξ 1_{t ≥ 1/2}` with a fair sign `ξ`, `Z = U = 1_{(0, 1]}` satisfies
`CadlagPredTuple`; the left limit of `X` at `1/2` (`0`) differs from its value (`1` at
`ω = true`), so `Θ⁻ ≠ Θ` there, and `X_1(true) ≠ X_1(false)`.
`Dissertation.Acceptance.A.lemA1_fubini_hypotheses` for `lemA1_fubini`: the uniform law on `Bool`
is a probability measure, and `ν = δ₀` is σ-finite and nonzero on the countably generated `ℝ`.

Verdict: faithful. `lemA1_fubini` holds for every probability space and every `T`; the printed
claim is its instance at the paper's `(Ω, ℱ, P)` and horizon. `lemA1_pettis` asserts the subspace
inclusion at every time, stronger than off a null set.

<!-- spec-review: Dissertation.PaperSpec.A.lemA1_L2 ed839d34f480cba1a6657535c81c9ed1 by=claude-author source=A:lemA1:pettis@4683d66c9de5e151a16b21a1e6cbac952384cffefeb3e0e4b2eb720fb4a0b746 -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.lemA1_L2--claude-auditor--2026-10-20T06_16_50Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.lemA1_L2 ed839d34f480cba1a6657535c81c9ed1 by=claude-auditor source=A:lemA1:pettis@4683d66c9de5e151a16b21a1e6cbac952384cffefeb3e0e4b2eb720fb4a0b746 -->
<!-- spec-review: Dissertation.PaperSpec.A.lemA1_fubini ed839d34f480cba18bb7bf3a9a35bb91 by=claude-author source=A:lemA1:pettis@4683d66c9de5e151a16b21a1e6cbac952384cffefeb3e0e4b2eb720fb4a0b746 -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.lemA1_fubini--claude-auditor--2026-10-20T06_16_50Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.lemA1_fubini ed839d34f480cba18bb7bf3a9a35bb91 by=claude-auditor source=A:lemA1:pettis@4683d66c9de5e151a16b21a1e6cbac952384cffefeb3e0e4b2eb720fb4a0b746 -->
<!-- spec-review: Dissertation.PaperSpec.A.lemA1_pettis ed839d34f480cba176ccc2a6aaf99d7c by=claude-author source=A:lemA1:pettis@4683d66c9de5e151a16b21a1e6cbac952384cffefeb3e0e4b2eb720fb4a0b746 -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.lemA1_pettis--claude-auditor--2026-10-20T06_16_50Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.lemA1_pettis ed839d34f480cba176ccc2a6aaf99d7c by=claude-auditor source=A:lemA1:pettis@4683d66c9de5e151a16b21a1e6cbac952384cffefeb3e0e4b2eb720fb4a0b746 -->

## Lemma A.1, Step 2 of the proof, the Polish space of laws: `Dissertation.PaperSpec.A.lemA1_polish`, and `eq_coupling`

Manuscript (proof of Lemma `lem:lawflow`, Step 2, lines 53–56): "By the synchronous coupling bound
(2.8), the law map `Θ ↦ Law(Θ)` is `1`-Lipschitz from `L²(Ω; H)` into `(P₂(H), W₂)`, which
inherits Polishness from `H` [Villani, Ch. 6]." The claim is pinned at line 55.

Propositions:

* The first assertion is the clause `eq_coupling`, the proposition of (2.8) (reviewed with
  Remark 2.6): for square-integrable random tuples `Θ, Θ'` on one probability space,
  `w2H(Law Θ, Law Θ')² ≤ 𝔼(|δX|² + |δY|² + |δZ|²_F + ‖δU‖²_{L²(ν)}) = 𝔼‖Θ − Θ'‖²_H`. Its square
  root is the `1`-Lipschitz bound `W₂(Law Θ, Law Θ') ≤ ‖Θ − Θ'‖_{L²(Ω; H)}`; `lawP2` depends only
  on the class of `Θ` in `L²(Ω; H)`.
* `lemA1_polish`: for `ν` σ-finite on a countably generated `E` and every `n, m, d`:
  `PolishSpace (TupleH ν n m d)`; `dist μ μ' = 0 → μ = μ'` on `TupleP2WH ν n m d`;
  `CompleteSpace`, `SeparableSpace` and `PolishSpace` for `TupleP2WH ν n m d`.

Readings:

* `(P₂(H), W₂)` is the reviewed `TupleP2WH ν n m d`: the laws of finite second moment on `H` with
  `dist = w2H`, the 2-Wasserstein distance of the Hilbert norm (the `W₂` of §2), and the topology
  of that distance.
* "Polish": Mathlib's `PolishSpace` (second countable and completely metrizable) is weaker than
  what Villani's theorem gives and what the paper uses, that `W₂` itself is a complete separable
  metric. The proposition states both: `W₂` separates laws (the reviewed pseudometric is a
  metric), the space is complete for the uniformity of `W₂` and separable, and it is Polish.
* "Inherits Polishness from `H`": `H` is Polish (`PolishSpace (TupleH …)`; the product topology of
  `TupleH` is that of the Hilbert norm). The proposition states the conclusion for the paper's
  `H`, not an implication from an arbitrary Polish space.

Proof (for the reader): `W₂` separates laws because a coupling of cost below `r³` gives
`μ(B) ≤ ν(B^r) + r` for the open `r`-thickening, so the Lévy–Prokhorov distance vanishes; the
space is complete because near-optimal couplings of a fast Cauchy sequence, chained by the
Ionescu-Tulcea theorem, give random elements that are Cauchy in `L²`, whose limit has the
`W₂`-limit as its law; separability is the quantiser argument of `P2Borel`; and `μ ↦ toL2 # μ` is
an isometric bijection onto the 2-Wasserstein space of the Hilbert space. Villani's result is
proved for this `H`, not cited.

Witnesses: `Dissertation.Acceptance.A.eq_coupling_hypotheses` for the first clause (reviewed with
Remark 2.6), and `Dissertation.Acceptance.A.lemA1_polish_hypotheses` for `lemA1_polish`: Lebesgue
measure on `ℝ`, σ-finite of infinite mass on a countably generated space, the infinite-activity
intensity of §2, for which `L²(ν; ℝᵐ)` and `H` are infinite-dimensional when `m ≥ 1`.

Verdict: faithful. `lemA1_polish` is stronger than the topological reading of "Polish".

<!-- spec-review: Dissertation.PaperSpec.A.lemA1_polish ed839d34f480cba19bbef9c769d701cd by=claude-author source=A:lemA1:polish@cdf7e5fd3a5753faf4d5aaea2d4e017db124558fd0461ec3b81dd52a3f8527cc -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.lemA1_polish--claude-auditor--2026-10-20T06_16_50Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.lemA1_polish ed839d34f480cba19bbef9c769d701cd by=claude-auditor source=A:lemA1:polish@cdf7e5fd3a5753faf4d5aaea2d4e017db124558fd0461ec3b81dd52a3f8527cc -->

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

<!-- spec-review: Dissertation.PaperSpec.A.eq_coeffint ed839d34f480cba13c4b68e5e50bad34 by=claude-author source=A:sec4:coeffint@fb2d9936eeb420107ab775d3d6f5f596ace121471c667bed056241cf5805dad6 source=A:eq:coeffint@b023b2927b3894d8f6323197bfa4a597800d6a73770ec5eecad87a4fb7ae5331 -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.eq_coeffint--claude-reviewer--2026-10-17T12_22_13Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_coeffint ed839d34f480cba13c4b68e5e50bad34 by=claude-reviewer source=A:sec4:coeffint@fb2d9936eeb420107ab775d3d6f5f596ace121471c667bed056241cf5805dad6 source=A:eq:coeffint@b023b2927b3894d8f6323197bfa4a597800d6a73770ec5eecad87a4fb7ae5331 -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.eq_coeffint--claude-auditor--2026-10-19T03_36_47Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_coeffint ed839d34f480cba13c4b68e5e50bad34 by=claude-auditor source=A:sec4:coeffint@fb2d9936eeb420107ab775d3d6f5f596ace121471c667bed056241cf5805dad6 source=A:eq:coeffint@b023b2927b3894d8f6323197bfa4a597800d6a73770ec5eecad87a4fb7ae5331 -->
<!-- spec-review: Dissertation.PaperSpec.A.eq_termg ed839d34f480cba171988e2e6de37794 by=claude-author source=A:sec4:coeffint@fb2d9936eeb420107ab775d3d6f5f596ace121471c667bed056241cf5805dad6 source=A:eq:termg@b366da385f2d0d1704001661042e88366628f72edb9990bc82fba564a2eb90b8 -->
Review by claude-reviewer: faithful (report `reports/Dissertation.PaperSpec.A.eq_termg--claude-reviewer--2026-10-17T16_03_52Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_termg ed839d34f480cba171988e2e6de37794 by=claude-reviewer source=A:sec4:coeffint@fb2d9936eeb420107ab775d3d6f5f596ace121471c667bed056241cf5805dad6 source=A:eq:termg@b366da385f2d0d1704001661042e88366628f72edb9990bc82fba564a2eb90b8 -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.eq_termg--claude-auditor--2026-10-19T03_31_22Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_termg ed839d34f480cba171988e2e6de37794 by=claude-auditor source=A:sec4:coeffint@fb2d9936eeb420107ab775d3d6f5f596ace121471c667bed056241cf5805dad6 source=A:eq:termg@b366da385f2d0d1704001661042e88366628f72edb9990bc82fba564a2eb90b8 -->

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

<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_i_sharp ed839d34f480cba19df1faec1593a821 by=claude-author source=A:ex:concrete@c1a37ef0e0904d01777b03bccdee013a671a60dda2b3a63f5bcfcdc22dd81785 -->
Review by claude-reviewer: faithful (report `reports/Dissertation.PaperSpec.A.ex_concrete_i_sharp--claude-reviewer--2026-10-17T12_17_25Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_i_sharp ed839d34f480cba19df1faec1593a821 by=claude-reviewer source=A:ex:concrete@c1a37ef0e0904d01777b03bccdee013a671a60dda2b3a63f5bcfcdc22dd81785 -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.ex_concrete_i_sharp--claude-auditor--2026-10-19T03_36_07Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_concrete_i_sharp ed839d34f480cba19df1faec1593a821 by=claude-auditor source=A:ex:concrete@1e2bfcc4d0a6c0d3ac3168b0c7042d0db4a93670e277d64901f8076820cef633 -->

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

<!-- spec-review: Dissertation.PaperSpec.A.ex_brownian_not_h0 ed839d34f480cba13fa0ef4acc9fb310 by=claude-author source=A:ex:brownian@73039b50faf59ac9d4c6bfe0d2609ec518c20d4f2edffd1960252336508e71b5 -->
Review by claude-reviewer: faithful (report `reports/Dissertation.PaperSpec.A.ex_brownian_not_h0--claude-reviewer--2026-10-17T12_11_37Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_brownian_not_h0 ed839d34f480cba13fa0ef4acc9fb310 by=claude-reviewer source=A:ex:brownian@73039b50faf59ac9d4c6bfe0d2609ec518c20d4f2edffd1960252336508e71b5 -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.ex_brownian_not_h0--claude-auditor--2026-10-19T03_34_13Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_brownian_not_h0 ed839d34f480cba13fa0ef4acc9fb310 by=claude-auditor source=A:ex:brownian@73039b50faf59ac9d4c6bfe0d2609ec518c20d4f2edffd1960252336508e71b5 -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_brownian_rank_gt ed839d34f480cba154d947c79143fab0 by=claude-author source=A:rem:beta1-dich@ce35242e5c61dc248a5bf9b36f678223d523cf9e6c42793d8e5d2fd12e1df0ea source=A:ex:brownian@73039b50faf59ac9d4c6bfe0d2609ec518c20d4f2edffd1960252336508e71b5 -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.ex_brownian_rank_gt--claude-reviewer--2026-10-17T16_05_52Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_brownian_rank_gt ed839d34f480cba154d947c79143fab0 by=claude-reviewer source=A:rem:beta1-dich@ce35242e5c61dc248a5bf9b36f678223d523cf9e6c42793d8e5d2fd12e1df0ea source=A:ex:brownian@73039b50faf59ac9d4c6bfe0d2609ec518c20d4f2edffd1960252336508e71b5 -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.ex_brownian_rank_gt--claude-auditor--2026-10-19T03_37_10Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_brownian_rank_gt ed839d34f480cba154d947c79143fab0 by=claude-auditor source=A:rem:beta1-dich@20e41bdfd1e0996ebf1050ab15273a783631b8c503a6635284298cc387eea4f4 source=A:ex:brownian@73039b50faf59ac9d4c6bfe0d2609ec518c20d4f2edffd1960252336508e71b5 -->

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

<!-- spec-review: Dissertation.PaperSpec.A.ex_brownian_reduction ed839d34f480cba16ec077c21383f1ee by=claude-author source=A:ex:brownian@73039b50faf59ac9d4c6bfe0d2609ec518c20d4f2edffd1960252336508e71b5 source=A:sec5:overview@85ef567e93b2eddcbd19ae70a2daac18fc886c5303ea56d4b6dc281d39f4f3e9 -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.ex_brownian_reduction--claude-reviewer--2026-10-17T16_05_53Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_brownian_reduction ed839d34f480cba16ec077c21383f1ee by=claude-reviewer source=A:ex:brownian@73039b50faf59ac9d4c6bfe0d2609ec518c20d4f2edffd1960252336508e71b5 source=A:sec5:overview@85ef567e93b2eddcbd19ae70a2daac18fc886c5303ea56d4b6dc281d39f4f3e9 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.ex_brownian_reduction--claude-auditor--2026-10-19T03_36_56Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_brownian_reduction ed839d34f480cba16ec077c21383f1ee by=claude-auditor source=A:ex:brownian@73039b50faf59ac9d4c6bfe0d2609ec518c20d4f2edffd1960252336508e71b5 source=A:sec5:overview@85ef567e93b2eddcbd19ae70a2daac18fc886c5303ea56d4b6dc281d39f4f3e9 -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_brownian_prp ed839d34f480cba1d54de82e0956a03e by=claude-author source=A:ex:brownian@73039b50faf59ac9d4c6bfe0d2609ec518c20d4f2edffd1960252336508e71b5 -->
Review by claude-reviewer: faithful (report `reports/Dissertation.PaperSpec.A.ex_brownian_prp--claude-reviewer--2026-10-17T16_03_52Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_brownian_prp ed839d34f480cba1d54de82e0956a03e by=claude-reviewer source=A:ex:brownian@73039b50faf59ac9d4c6bfe0d2609ec518c20d4f2edffd1960252336508e71b5 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.ex_brownian_prp--claude-auditor--2026-10-19T03_34_12Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_brownian_prp ed839d34f480cba1d54de82e0956a03e by=claude-auditor source=A:ex:brownian@73039b50faf59ac9d4c6bfe0d2609ec518c20d4f2edffd1960252336508e71b5 -->

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

<!-- spec-review: Dissertation.PaperSpec.A.sec3_one_null_set ed839d34f480cba1209a5aa6ac298690 by=claude-author source=A:sec3:one-null-set@14d75cb86a9216c652eee2f0e1f6bebae9651e4f1f55bc1c34aacc8f595b9954 -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.sec3_one_null_set--claude-reviewer--2026-10-17T12_16_14Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.sec3_one_null_set ed839d34f480cba1209a5aa6ac298690 by=claude-reviewer source=A:sec3:one-null-set@14d75cb86a9216c652eee2f0e1f6bebae9651e4f1f55bc1c34aacc8f595b9954 -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.sec3_one_null_set--claude-auditor--2026-10-19T03_35_07Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.sec3_one_null_set ed839d34f480cba1209a5aa6ac298690 by=claude-auditor source=A:sec3:one-null-set@14d75cb86a9216c652eee2f0e1f6bebae9651e4f1f55bc1c34aacc8f595b9954 -->
<!-- spec-review: Dissertation.PaperSpec.A.sec3_HH_inclusion ed839d34f480cba130514b735af5f227 by=claude-author source=A:sec3:HH-banach@a0a1288695334f65fab37e82bdb88887c2310a259b83b80f05dea471d866904f -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.sec3_HH_inclusion--claude-reviewer--2026-10-17T12_15_35Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.sec3_HH_inclusion ed839d34f480cba130514b735af5f227 by=claude-reviewer source=A:sec3:HH-banach@a0a1288695334f65fab37e82bdb88887c2310a259b83b80f05dea471d866904f -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.sec3_HH_inclusion--claude-auditor--2026-10-19T03_34_37Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.sec3_HH_inclusion ed839d34f480cba130514b735af5f227 by=claude-auditor source=A:sec3:HH-banach@a0a1288695334f65fab37e82bdb88887c2310a259b83b80f05dea471d866904f -->
<!-- spec-review: Dissertation.PaperSpec.A.sec3_HH_definite ed839d34f480cba12b4c9985cfe528af by=claude-author source=A:sec3:HH-banach@a0a1288695334f65fab37e82bdb88887c2310a259b83b80f05dea471d866904f -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.sec3_HH_definite--claude-reviewer--2026-10-17T12_14_59Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.sec3_HH_definite ed839d34f480cba12b4c9985cfe528af by=claude-reviewer source=A:sec3:HH-banach@a0a1288695334f65fab37e82bdb88887c2310a259b83b80f05dea471d866904f -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.sec3_HH_definite--claude-auditor--2026-10-19T03_34_14Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.sec3_HH_definite ed839d34f480cba12b4c9985cfe528af by=claude-auditor source=A:sec3:HH-banach@a0a1288695334f65fab37e82bdb88887c2310a259b83b80f05dea471d866904f -->
<!-- spec-review: Dissertation.PaperSpec.A.sec3_cadlag_versions ed839d34f480cba18328d3bafc39f8ed by=claude-author source=A:sec3:one-null-set@14d75cb86a9216c652eee2f0e1f6bebae9651e4f1f55bc1c34aacc8f595b9954 -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.sec3_cadlag_versions--claude-auditor--2026-10-19T05_49_14Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.sec3_cadlag_versions ed839d34f480cba18328d3bafc39f8ed by=claude-auditor source=A:sec3:one-null-set@14d75cb86a9216c652eee2f0e1f6bebae9651e4f1f55bc1c34aacc8f595b9954 -->
<!-- spec-review: Dissertation.PaperSpec.A.sec3_HH_norm ed839d34f480cba140aa5342c14a73fc by=claude-author source=A:sec3:HH-banach@a0a1288695334f65fab37e82bdb88887c2310a259b83b80f05dea471d866904f -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.sec3_HH_norm--claude-auditor--2026-10-19T05_49_14Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.sec3_HH_norm ed839d34f480cba140aa5342c14a73fc by=claude-auditor source=A:sec3:HH-banach@a0a1288695334f65fab37e82bdb88887c2310a259b83b80f05dea471d866904f -->

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

<!-- spec-review: Dissertation.PaperSpec.A.sec3_HH_complete ed839d34f480cba140502fce3ed6073c by=claude-author source=A:sec3:HH-banach@a0a1288695334f65fab37e82bdb88887c2310a259b83b80f05dea471d866904f -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.sec3_HH_complete--claude-reviewer--2026-10-17T12_14_16Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.sec3_HH_complete ed839d34f480cba140502fce3ed6073c by=claude-reviewer source=A:sec3:HH-banach@a0a1288695334f65fab37e82bdb88887c2310a259b83b80f05dea471d866904f -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.sec3_HH_complete--claude-auditor--2026-10-19T03_34_22Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.sec3_HH_complete ed839d34f480cba140502fce3ed6073c by=claude-auditor source=A:sec3:HH-banach@a0a1288695334f65fab37e82bdb88887c2310a259b83b80f05dea471d866904f -->

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

<!-- spec-review: Dissertation.PaperSpec.A.sec4_horizon_not_contractive ed839d34f480cba1fc081d81965ca7e6 by=claude-author source=A:sec4:horizon-not-contractive@3848cfec9527e65f37a2aa7ee50e7c186ffb9d3e89e5d7181ef8045b33f7557a -->
Review by claude-reviewer: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.sec4_horizon_not_contractive--claude-reviewer--2026-10-17T12_08_17Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.sec4_horizon_not_contractive ed839d34f480cba1fc081d81965ca7e6 by=claude-reviewer source=A:sec4:horizon-not-contractive@3848cfec9527e65f37a2aa7ee50e7c186ffb9d3e89e5d7181ef8045b33f7557a -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.sec4_horizon_not_contractive--claude-auditor--2026-10-19T03_35_41Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.sec4_horizon_not_contractive ed839d34f480cba1fc081d81965ca7e6 by=claude-auditor source=A:sec4:horizon-not-contractive@3848cfec9527e65f37a2aa7ee50e7c186ffb9d3e89e5d7181ef8045b33f7557a -->

## §4, the supremum criterion: `Dissertation.PaperSpec.A.sec4_supremum_criterion`

Manuscript (the preamble of §4, lines 30–37): "The maximal estimates use the
Burkholder–Davis–Gundy inequality in quadratic-variation form, at `p = 1` for the zero-mean
arguments and at `p = 2` for squared suprema ([HeWangYan], chapter on `H¹` and BMO; at `p = 2`
Doob's inequality gives the constant `4`), with one universal constant `c_BDG` valid at both
exponents; valid for càdlàg local martingales, the inequality covers the compensated-Poisson
martingales below without a separate jump statement. By localisation and dominated convergence, a
càdlàg local martingale whose running supremum is integrable has zero-mean increments (the
*supremum criterion* below)."

Uses. Proof of Lemma 4.1 (lines 171–172 of `sections/04-proof-wellposedness.tex`), for the
local martingales `M^W_t = ∫_0^t e^s ⟨δY_{s−}, δZ_s dW_s⟩` and
`M^1_t = ∫_0^t ∫_E e^s ⟨δY_{s−}, δU_s(e)⟩ Ñ(ds, de)`, after `𝔼 sup_{t ≤ T} |M^W_t| < ∞` and
`𝔼 sup_{t ≤ T} |M^1_t| < ∞`: "These bounds put the running suprema of `M^W` and `M^1` in `L¹`, so
the supremum criterion gives `𝔼[M_T − M_t] = 0` for `M ∈ {M^W, M^1}`." Proof of Lemma 4.3
(lines 611–612), for the four stochastic integrals of (eq:bdg4), each of the form `∫_0^t`: "The
four suprema in (eq:bdg4) are therefore integrable, so the supremum criterion applies to those four
local martingales", and then "all five terms have zero expectation", that is `𝔼 M_T = 0` with
`M_0 = 0`.

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

Re-reading at `1f67672` (`sections/04-proof-wellposedness.tex` lines 29–37, quoted above; the claim
region is lines 35–37): the preceding sentence on the Burkholder–Davis–Gundy inequality now names
the exponents `p = 1` and `p = 2`, with Doob's constant `4` at `p = 2` and one constant for both,
and the line breaks moved; the sentence of the supremum criterion is unchanged. The proposition
still says what that sentence says, and the BDG sentence is still not stated (scope note). It is
broader than the printed claim in the ways listed in the correspondence; the printed claim is its
instance at the filtration of §2, the processes stopped at `T` and real-valued, as in Lemmas 4.1
(lines 171–172) and 4.3 (lines 611–612).

<!-- spec-review: Dissertation.PaperSpec.A.sec4_supremum_criterion ed839d34f480cba1f588c2071f5242ff by=claude-author source=A:sec4:supremum-criterion@1425729d99cee0bd892c371ff76585d28df00f70fcd26ef5bb10262454ff45a3 -->
<!-- spec-review: Dissertation.PaperSpec.A.sec4_supremum_criterion ed839d34f480cba1f588c2071f5242ff by=claude-author source=A:sec4:supremum-criterion@66f9ea22a06a00e8b6aad28172a7820750d9f1d2f2ddeb8475dddc064283e43b -->
Review by claude-reviewer: faithful (report `reports/Dissertation.PaperSpec.A.sec4_supremum_criterion--claude-reviewer--2026-10-17T16_03_52Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.sec4_supremum_criterion ed839d34f480cba1f588c2071f5242ff by=claude-reviewer source=A:sec4:supremum-criterion@66f9ea22a06a00e8b6aad28172a7820750d9f1d2f2ddeb8475dddc064283e43b -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.sec4_supremum_criterion--claude-auditor--2026-10-19T03_31_21Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.sec4_supremum_criterion ed839d34f480cba1f588c2071f5242ff by=claude-auditor source=A:sec4:supremum-criterion@66f9ea22a06a00e8b6aad28172a7820750d9f1d2f2ddeb8475dddc064283e43b -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.sec4_supremum_criterion--claude-auditor--2026-10-20T11_24_08Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.sec4_supremum_criterion ed839d34f480cba1f588c2071f5242ff by=claude-auditor source=A:sec4:supremum-criterion@1425729d99cee0bd892c371ff76585d28df00f70fcd26ef5bb10262454ff45a3 -->

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

<!-- spec-review: Dissertation.PaperSpec.A.rem_beta1_fibre ed839d34f480cba1c9fa0ba4a3588e95 by=claude-author source=A:rem:beta1-dich@20e41bdfd1e0996ebf1050ab15273a783631b8c503a6635284298cc387eea4f4 -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.rem_beta1_fibre--claude-auditor--2026-10-19T03_26_06Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.rem_beta1_fibre ed839d34f480cba1c9fa0ba4a3588e95 by=claude-auditor source=A:rem:beta1-dich@20e41bdfd1e0996ebf1050ab15273a783631b8c503a6635284298cc387eea4f4 -->
<!-- spec-review: Dissertation.PaperSpec.A.rem_beta1_dich ed839d34f480cba1312ac03d25ff8ea1 by=claude-author source=A:rem:beta1-dich@ce35242e5c61dc248a5bf9b36f678223d523cf9e6c42793d8e5d2fd12e1df0ea source=A:conclusion@c886edc62e0561a1e17a961ffd1d0527a5bae43a5607635ce8e247276c91a829 -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.rem_beta1_dich--claude-auditor--2026-10-19T03_34_36Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.rem_beta1_dich ed839d34f480cba1312ac03d25ff8ea1 by=claude-auditor source=A:rem:beta1-dich@20e41bdfd1e0996ebf1050ab15273a783631b8c503a6635284298cc387eea4f4 source=A:conclusion@c886edc62e0561a1e17a961ffd1d0527a5bae43a5607635ce8e247276c91a829 -->
<!-- spec-review: Dissertation.PaperSpec.A.rem_beta1_zero ed839d34f480cba10a600b0e388b329d by=claude-author source=A:rem:beta1-dich@20e41bdfd1e0996ebf1050ab15273a783631b8c503a6635284298cc387eea4f4 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.rem_beta1_zero--claude-auditor--2026-10-19T03_38_14Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.rem_beta1_zero ed839d34f480cba10a600b0e388b329d by=claude-auditor source=A:rem:beta1-dich@20e41bdfd1e0996ebf1050ab15273a783631b8c503a6635284298cc387eea4f4 -->

## Remark 2.11, the dissipativity margin: `Dissertation.PaperSpec.A.rem_margin_reduce`, `rem_margin_unweighted`, `rem_margin_smaller`, `rem_margin_slack`

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
* `rem_margin_slack`: in the standing setting (any `n, m, d`, `G`, coefficients `C` and
  perturbation `p`), if `C` satisfies (2.12) with the constants `β₁, β₂` and margin `c > 0`
  (`Margin212`) and `p` satisfies (3.4) in the weighted quantity of (2.12) with a constant
  `c_pert`, `0 ≤ c_pert ≤ c` (`PairingBound34W`, reviewed with Remark 3.7), then for almost every
  `t ∈ [0, T]` the perturbed coefficients `C + p` (`Coeffs.perturb`) satisfy (2.7) with the
  constants `β₁, β₂` (`Mono27At`).

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
* "Recording weaker constants turns the difference into slack, which a perturbation raising the
  interior pairing by at most the margin leaves intact" (lines 300–302): `rem_margin_slack`. The recorded
  constants are those of (2.12), `β₁, β₂` with margin `c`; "a perturbation raising the interior
  pairing by at most the margin" is a perturbation `p` of the interior coefficients whose own
  pairing is at most `c_pert` times the weighted quantity of (2.12), with `c_pert ≤ c` (the
  pairing of `C + p` is that of `C` plus that of `p`); "leaves intact" is the bound (2.7) with the
  recorded constants `β₁, β₂` for `C + p`. The perturbation is the one of Corollary 3.6 and
  Remark 3.7 (`C.perturb p`, the interior coefficients added, `g` unchanged), and (3.4) in the
  weighted quantity is the form Remark 3.7 records; `c_pert ≥ 0` and `c > 0` are kept as the
  notions state them (a margin is positive, (3.4) has `c_pert ≥ 0`). The proposition holds with
  no sign condition on `β₁, β₂` and does not assert Assumption 2.5 for `C + p` (its constants'
  admissibility and the terminal inequality are not part of the sentence).

Witnesses: `Dissertation.Acceptance.A.rem_affine_hypotheses` for `rem_margin_reduce` (over a Lévy
driver with `d = 1`, `ν = δ₀`, `𝒢₀ = ⊥`, `T = 1`, Example 5.1(i) with `β₁ = β₂ = 1` satisfies
Assumption 2.5 at `G = 1`, whose interior part is (2.7) with `β̄₁ = β̄₂ = 1`, and
`0 < 1/2 < min{1, 1}`); `Dissertation.Acceptance.A.rem_margin_hypotheses` for
`rem_margin_unweighted` (the same system satisfies (2.12) at `G = 1` with the constants `1/2, 1/2`
and margin `1/2 > 0`; at `G = 1`, `c_G = 1`, so this witness meets the hypotheses without showing
the factor `c_G`); `Dissertation.Acceptance.A.rem_margin_smaller_hypotheses` for
`rem_margin_smaller` (`G = 1/2 ∈ ℝ^{1×1}`, of full rank, with `s_min(G) = 1/2`, so `c_G = 4 > 1`,
and `c = 1`); `Dissertation.Acceptance.A.rem_margin_slack_hypotheses` for `rem_margin_slack`
(the instance of `rem_generalrank_hypotheses`, `n = m = 1`, `G = 1`, `ν = δ₀`: the baseline
Example 5.1(i) with `β₁ = β₂ = 2` satisfies (2.12) with the constants `1, 1` and margin `c = 1`,
and the feedback perturbation with `ε = 1/2` satisfies the weighted (3.4) with `c_pert = 1/2`,
hence with `c_pert = 1 = c`, the case of a perturbation raising the pairing by the whole margin).

Proof of `rem_margin_slack`: the expected pairing of `C + p` is that of `C`, at most
`−β₁ A − β₂ B − c S`, plus that of `p`, at most `c_pert S ≤ c S`, with `S ≥ 0` the weighted
quantity.

Verdict: faithful.

Re-reading at `1f67672` (`sections/02-model-assumptions.tex` lines 288–317, quoted above): the
remark now says that the unweighted margin `c / c_G` "is smaller than `c` when `c_G > 1`", where it
formerly said "not `c`"; the definitions (2.12), (2.13) and the sentences on the reduced
constants and on the channel-by-channel bound are unchanged. `rem_margin_reduce` and
`rem_margin_unweighted` still say what the passage says. `rem_margin_reduce` is broader: it holds
for all `n, m, d` (`0` included), every `T`, every `G` and every coefficient system with (2.7) at
almost every time; the printed claim is its instance at the coefficients of the paper with
`n, m, d ≥ 1`, `T > 0`, whose interior pairing is bounded with `β̄₁, β̄₂` (the interior part of
Assumption 2.5). `rem_margin_unweighted` is the printed implication at `m = n ≥ 1`, `G` of full
rank and `c_G = s_min(G)⁻²`.

<!-- spec-review: Dissertation.PaperSpec.A.rem_margin_reduce ed839d34f480cba15843e0ffe4756126 by=claude-author source=A:rem:margin@288d762606cfb331dfd032a5690173faa203ebddb7048d1201cb0e0fe1a25485 -->
<!-- spec-review: Dissertation.PaperSpec.A.rem_margin_unweighted ed839d34f480cba1ba4163c9b3d796bd by=claude-author source=A:rem:margin@288d762606cfb331dfd032a5690173faa203ebddb7048d1201cb0e0fe1a25485 -->
<!-- spec-review: Dissertation.PaperSpec.A.rem_margin_reduce ed839d34f480cba15843e0ffe4756126 by=claude-author source=A:rem:margin@818715d0c102417894d7fdc0dd695f91b0ee288c7ecc02af05c10a95821a090a -->
<!-- spec-review: Dissertation.PaperSpec.A.rem_margin_unweighted ed839d34f480cba1ba4163c9b3d796bd by=claude-author source=A:rem:margin@818715d0c102417894d7fdc0dd695f91b0ee288c7ecc02af05c10a95821a090a -->
<!-- spec-review: Dissertation.PaperSpec.A.rem_margin_smaller ed839d34f480cba133faa12dcf2189f6 by=claude-author source=A:rem:margin@288d762606cfb331dfd032a5690173faa203ebddb7048d1201cb0e0fe1a25485 -->
<!-- spec-review: Dissertation.PaperSpec.A.rem_margin_slack ed839d34f480cba1fc10bfb5bc98adb1 by=claude-author source=A:rem:margin@288d762606cfb331dfd032a5690173faa203ebddb7048d1201cb0e0fe1a25485 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.rem_margin_slack--claude-auditor--2026-10-19T22_55_55Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.rem_margin_slack ed839d34f480cba1fc10bfb5bc98adb1 by=claude-auditor source=A:rem:margin@288d762606cfb331dfd032a5690173faa203ebddb7048d1201cb0e0fe1a25485 -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.rem_margin_reduce--claude-auditor--2026-10-19T03_34_35Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.rem_margin_reduce ed839d34f480cba15843e0ffe4756126 by=claude-auditor source=A:rem:margin@f098128a01b0fc8e2f2ddbb98e80be357bf141638ca4f28a2161fd38cb98a896 -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.rem_margin_reduce--claude-auditor--2026-10-20T11_24_08Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.rem_margin_reduce ed839d34f480cba15843e0ffe4756126 by=claude-auditor source=A:rem:margin@288d762606cfb331dfd032a5690173faa203ebddb7048d1201cb0e0fe1a25485 -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.rem_margin_unweighted--claude-auditor--2026-10-19T03_34_35Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.rem_margin_unweighted ed839d34f480cba1ba4163c9b3d796bd by=claude-auditor source=A:rem:margin@f098128a01b0fc8e2f2ddbb98e80be357bf141638ca4f28a2161fd38cb98a896 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.rem_margin_unweighted--claude-auditor--2026-10-20T11_24_08Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.rem_margin_unweighted ed839d34f480cba1ba4163c9b3d796bd by=claude-auditor source=A:rem:margin@288d762606cfb331dfd032a5690173faa203ebddb7048d1201cb0e0fe1a25485 -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.rem_margin_smaller--claude-auditor--2026-10-19T18_47_31Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.rem_margin_smaller ed839d34f480cba133faa12dcf2189f6 by=claude-auditor source=A:rem:margin@288d762606cfb331dfd032a5690173faa203ebddb7048d1201cb0e0fe1a25485 -->

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

<!-- spec-review: Dissertation.PaperSpec.A.rem_uniq_initial ed839d34f480cba1fa628ed6b5f5989d by=claude-author source=A:rem:uniq-no-integ@867ca613bdc7ff8b7ff2ba56fd6a8fa9594e1e7b57e69975069db081dd311798 -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.rem_uniq_initial--claude-auditor--2026-10-19T03_34_35Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.rem_uniq_initial ed839d34f480cba1fa628ed6b5f5989d by=claude-auditor source=A:rem:uniq-no-integ@867ca613bdc7ff8b7ff2ba56fd6a8fa9594e1e7b57e69975069db081dd311798 -->
<!-- spec-review: Dissertation.PaperSpec.A.rem_uniq_singular ed839d34f480cba1ba6232c9763ebb54 by=claude-author source=A:rem:uniq-no-integ@867ca613bdc7ff8b7ff2ba56fd6a8fa9594e1e7b57e69975069db081dd311798 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.rem_uniq_singular--claude-auditor--2026-10-19T05_49_14Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.rem_uniq_singular ed839d34f480cba1ba6232c9763ebb54 by=claude-auditor source=A:rem:uniq-no-integ@867ca613bdc7ff8b7ff2ba56fd6a8fa9594e1e7b57e69975069db081dd311798 -->
<!-- spec-review: Dissertation.PaperSpec.A.rem_uniq_translation ed839d34f480cba13b68ad605862c311 by=claude-author source=A:rem:uniq-no-integ@867ca613bdc7ff8b7ff2ba56fd6a8fa9594e1e7b57e69975069db081dd311798 -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.rem_uniq_translation--claude-auditor--2026-10-19T05_49_14Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.rem_uniq_translation ed839d34f480cba13b68ad605862c311 by=claude-auditor source=A:rem:uniq-no-integ@867ca613bdc7ff8b7ff2ba56fd6a8fa9594e1e7b57e69975069db081dd311798 -->

## Remark 3.4, the Lipschitz control of coefficient differences: `Dissertation.PaperSpec.A.eq_uniq_coeff_lip`, `eq_uniq_fwd`, `eq_uniq_bwd_lip`, `rem_uniq_lip_mem`

Manuscript (§3, Remark `rem:uniq-no-integ`, `03-main-results.tex` lines 182–187): "But the
uniqueness only requires Assumptions 2.3–2.5, as we only need to show that the difference
`Θ¹ − Θ²` belongs to `ℍ`, using only the Lipschitz control of coefficient differences." The
argument it refers to is the proof of Theorem 3.3 (lines 110–174), with the objects quoted in the
section of (3.2) and (3.3): "(3.2) `𝔼 ∫_0^T [|δb_t|² + |δσ_t|²_F + ‖δh_t‖²_{L²(ν)} + |δf_t|²] dt
< ∞`. We next show that `Θ¹ − Θ² ∈ ℍ`. Since the two solutions have the same initial condition,
the forward equation is `δX_t = ∫_0^t δb_s ds + ∫_0^t δσ_s dW_s + ∫_0^t ∫_E δh_s(e) Ñ(ds, de)`.
By Cauchy–Schwarz, the BDG inequality and the compensation formula,
`𝔼 sup_{0 ≤ t ≤ T} |δX_t|² ≤ C_T 𝔼 ∫_0^T (|δb_s|² + |δσ_s|²_F + ‖δh_s‖²) ds < ∞` by (3.2), so
`δX ∈ S²(ℝⁿ)`." (lines 139–156), then (3.3) (lines 158–173, quoted in the section of (3.2) and
(3.3)), "therefore `δY ∈ S²(ℝᵐ)`. By (3.2) and (3.3) we have `δΘ ∈ ℍ`." (lines 173–174). The
forward estimate of lines 144–156 lies between the pinned regions of `A:eq:uniq-coeff` and
`A:eq:uniq-bwd`, in neither.

Propositions: each for every horizon `T > 0`, coefficients with (2.3) and Assumption 2.3 with
constant `L`, and `Θ¹, Θ²` solving (1.1) in `ℍ_weak` (`WeakSolution`) from the same initial datum
`ξ₀`, with `δb, δσ, δh, δf, δg` as in `eq_uniq_coeff` and `eq_uniq_bwd`:

* `eq_uniq_coeff_lip`: `∑_i energy(δb_i) + ∑_{i, j} energy(δσ_{ij}) + ∑_i markedEnergy(δh_i)
  + ∑_k energy(δf_k) < ∞` ((3.2)).
* `eq_uniq_fwd`: `∃ K : ℝ → ℝ`, chosen first, such that, for every coordinate `i`: almost every
  path of `δb_i` is integrable on `[0, T]`; `δσ_i` meets the conditions of the Itô integral (as
  data); the jump integrand `δh_i` agrees almost everywhere on `Ω × [0, T] × E` with an integrand
  that meets the conditions of the compensated integral; and for every such integrand `H` and
  every `t ∈ [0, T]`, almost surely, `δX_{i,t} = ∫_{[0, t]} δb_i(s) ds + (∫ δσ_i dW)_t
  + (∫∫ H dÑ)_t`; and `∫⁻ sup_{t ∈ [0, T]} |δX_t|² ≤ ofReal(K(T)) (∑_i energy(δb_i)
  + ∑_{i, j} energy(δσ_{ij}) + ∑_i markedEnergy(δh_i))`, the right side `< ∞`.
* `eq_uniq_bwd_lip`: `∃ C_BP : ℝ → ℝ`, chosen first, such that
  `∫⁻ sup_{t ∈ [0, T]} |δY_t|² ≤ ofReal(C_BP(T)) (∫⁻ |δg_T|² + ∑_k energy(δf_k))` and
  `∫⁻ |δg_T|² + ∑_k energy(δf_k) < ∞` ((3.3)).
* `rem_uniq_lip_mem`: `supSize(Θ¹ − Θ²) < ∞`, that is `Θ¹ − Θ² ∈ ℍ`.

Readings:

* "Using only the Lipschitz control of coefficient differences": the hypotheses are (2.3),
  Assumption 2.3 and two solutions in `ℍ_weak` with the same initial condition, with neither
  Assumption 2.2 nor Assumptions 2.4–2.5. The remark's claim is that the argument of the proof
  of Theorem 3.3, up to `δΘ ∈ ℍ`, needs no more; the four propositions are that argument's
  conclusions under these hypotheses. Under the hypotheses of Theorem 3.3 they are the printed
  (3.2), forward estimate, (3.3) and `δΘ ∈ ℍ` (`eq_uniq_coeff`, `eq_uniq_bwd` state the first and
  third there).
* `C_T` and `C_BP` are constants of `T`: `K` and `C_BP` are functions of `T` chosen before
  everything else. "`< ∞`" is `< ⊤` of the right side, which with a real constant also bounds the
  left side. `δX ∈ S²` and `δY ∈ S²` are the finiteness of the suprema, which the bounds give.
* The forward difference is the difference of the forward equations of (1.1) at the two
  solutions, from the common initial condition, read at each time almost surely, the form in
  which (1.1) is stated. The jump integrand `δh` is the coefficient at the predictable tuples
  through `coeffJump`, which is defined pointwise and is not asked to be predictable; the
  proposition therefore states that it agrees almost everywhere with an integrand of the
  library's class and that the identity holds with every such integrand, whose compensated
  integrals agree almost surely. "By Cauchy–Schwarz, the BDG inequality and the compensation
  formula" names the proof.
* `Θ¹ − Θ² ∈ ℍ` is the finiteness of the squared norm of `ℍ`, `supSize` (reviewed with Lemma
  4.3): `𝔼 sup |δX|² + 𝔼 sup |δY|² + 𝔼 ∫_0^T (|δZ|²_F + ‖δU‖²)`. The differences are adapted
  and càdlàg because the solutions are.
* The expectations are lower integrals in `[0, ∞]`; the objects are those of the section of (3.2)
  and (3.3) (`driftProc`, `diffusionProc`, `driverProc`, `terminalVal`, `leftLimProc`,
  `coeffJump`, all reviewed).

Proofs: as for `eq_uniq_coeff_ae`, the difference of the two solutions, extended off `[0, T]`, is
a difference system with coupling matrix `0` (`PaperWeakSolutionForcedInt.exists_pairDiff_lip`),
which needs Assumption 2.3 alone. (3.2) is the finite energy of its integrands, with the jump
coefficient identified almost everywhere
(`PaperWeakSolutionInt.markedEnergy_coeffJump_sub_leftLim_eq`). The forward difference is its
forward equation, with the integrand `γ¹ − γ²` replaced by any integrand equal to it almost
everywhere (`compensatedIntegral_congr_of_markedEnergy`), and the bound is the `S²` bound of its
forward coordinates (`PairDiff.lintegral_biSup_fwd_le`, `K(T) = 3T + 12`). (3.3) is Lemma 4.1 for
its backward coordinates (`LinearBSDEJ.brownianPoisson_estimate`, `C_BP(T) = 13 e^T + 3T`), summed
over the coordinates. `Θ¹ − Θ² ∈ ℍ` is `supSize_lt_top_of_linear` for the forward and backward
coordinates, the extensions agreeing with the solutions on `[0, T]`.

Witness: `Dissertation.Acceptance.A.rem_uniq_lip_hypotheses`, described with `eq_uniq_coeff_ae`:
the system of Example 5.1(i) with `β₁ = −1`, `β₂ = 1`, `σ_c = h_c = 0` (`b = y`, `σ = z`,
`h = u`, `f = x`, `g = x`) on `[0, π/4]` satisfies (2.3) and Assumption 2.3 with `L = 1`, has the
two solutions `(sin t, cos t, 0, 0)` and `0` from the initial datum `0`, with `δX_t = sin t` and
`δY_t = cos t`, and satisfies Assumption 2.5 for no `G` of full rank, so the uniqueness of
Theorem 3.3 does not apply and the solutions differ. By hand, every bound has a nonzero left
side: `δb = cos t`, `δf = sin t`, `δg_T = sin(π/4)` give positive energies in (3.2) and positive
data in (3.3); `𝔼 sup_{t ≤ π/4} |δX_t|² = 1/2`, `𝔼 sup |δY_t|² = 1` and `supSize(Θ¹ − Θ²) = 3/2`.

Verdict: faithful; the hypotheses are those of the remark, and under the hypotheses of Theorem 3.3
the four propositions are the printed steps of its proof.

<!-- spec-review: Dissertation.PaperSpec.A.eq_uniq_coeff_lip ed839d34f480cba1e3e9c0b07e55c27c by=claude-author source=A:rem:uniq-no-integ@867ca613bdc7ff8b7ff2ba56fd6a8fa9594e1e7b57e69975069db081dd311798 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.eq_uniq_coeff_lip--claude-auditor--2026-10-20T15_30_04Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_uniq_coeff_lip ed839d34f480cba1e3e9c0b07e55c27c by=claude-auditor source=A:rem:uniq-no-integ@867ca613bdc7ff8b7ff2ba56fd6a8fa9594e1e7b57e69975069db081dd311798 -->
<!-- spec-review: Dissertation.PaperSpec.A.eq_uniq_fwd ed839d34f480cba1001605cc82c2788b by=claude-author source=A:rem:uniq-no-integ@867ca613bdc7ff8b7ff2ba56fd6a8fa9594e1e7b57e69975069db081dd311798 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.eq_uniq_fwd--claude-auditor--2026-10-20T15_30_04Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_uniq_fwd ed839d34f480cba1001605cc82c2788b by=claude-auditor source=A:rem:uniq-no-integ@867ca613bdc7ff8b7ff2ba56fd6a8fa9594e1e7b57e69975069db081dd311798 -->
<!-- spec-review: Dissertation.PaperSpec.A.eq_uniq_bwd_lip ed839d34f480cba184495619099e147e by=claude-author source=A:rem:uniq-no-integ@867ca613bdc7ff8b7ff2ba56fd6a8fa9594e1e7b57e69975069db081dd311798 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.eq_uniq_bwd_lip--claude-auditor--2026-10-20T15_30_04Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.eq_uniq_bwd_lip ed839d34f480cba184495619099e147e by=claude-auditor source=A:rem:uniq-no-integ@867ca613bdc7ff8b7ff2ba56fd6a8fa9594e1e7b57e69975069db081dd311798 -->
<!-- spec-review: Dissertation.PaperSpec.A.rem_uniq_lip_mem ed839d34f480cba1db72bd0880b4abb9 by=claude-author source=A:rem:uniq-no-integ@867ca613bdc7ff8b7ff2ba56fd6a8fa9594e1e7b57e69975069db081dd311798 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.rem_uniq_lip_mem--claude-auditor--2026-10-20T15_30_04Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.rem_uniq_lip_mem ed839d34f480cba1db72bd0880b4abb9 by=claude-auditor source=A:rem:uniq-no-integ@867ca613bdc7ff8b7ff2ba56fd6a8fa9594e1e7b57e69975069db081dd311798 -->

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

<!-- spec-review: Dissertation.PaperSpec.A.cor_margin_channels ed839d34f480cba14127298d8cc156d9 by=claude-author source=A:sec3:margin-paragraph@10e392992d5cc46ba3cbfa36215cf105187e98df0ba0aafcb83d6ba4e1501b17 -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.cor_margin_channels--claude-auditor--2026-10-19T03_34_36Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.cor_margin_channels ed839d34f480cba14127298d8cc156d9 by=claude-auditor source=A:sec3:margin-paragraph@10e392992d5cc46ba3cbfa36215cf105187e98df0ba0aafcb83d6ba4e1501b17 -->
<!-- spec-review: Dissertation.PaperSpec.A.cor_margin_additive ed839d34f480cba19075028a95edf84d by=claude-author source=A:sec3:margin-paragraph@10e392992d5cc46ba3cbfa36215cf105187e98df0ba0aafcb83d6ba4e1501b17 -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.cor_margin_additive--claude-auditor--2026-10-19T03_34_35Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.cor_margin_additive ed839d34f480cba19075028a95edf84d by=claude-auditor source=A:sec3:margin-paragraph@10e392992d5cc46ba3cbfa36215cf105187e98df0ba0aafcb83d6ba4e1501b17 -->
<!-- spec-review: Dissertation.PaperSpec.A.cor_margin_finite ed839d34f480cba15e05ed8a37017606 by=claude-author source=A:sec3:margin-paragraph@10e392992d5cc46ba3cbfa36215cf105187e98df0ba0aafcb83d6ba4e1501b17 -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.cor_margin_finite--claude-auditor--2026-10-19T03_34_36Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.cor_margin_finite ed839d34f480cba15e05ed8a37017606 by=claude-auditor source=A:sec3:margin-paragraph@10e392992d5cc46ba3cbfa36215cf105187e98df0ba0aafcb83d6ba4e1501b17 -->
<!-- spec-review: Dissertation.PaperSpec.A.cor_margin_continuous ed839d34f480cba1bd840ffee2f6a13b by=claude-author source=A:sec3:margin-paragraph@10e392992d5cc46ba3cbfa36215cf105187e98df0ba0aafcb83d6ba4e1501b17 -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.cor_margin_continuous--claude-auditor--2026-10-19T03_34_36Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.cor_margin_continuous ed839d34f480cba1bd840ffee2f6a13b by=claude-auditor source=A:sec3:margin-paragraph@10e392992d5cc46ba3cbfa36215cf105187e98df0ba0aafcb83d6ba4e1501b17 -->
<!-- spec-review: Dissertation.PaperSpec.A.cor_margin_separate ed839d34f480cba1b90f9a7b02bff832 by=claude-author source=A:sec3:margin-paragraph@10e392992d5cc46ba3cbfa36215cf105187e98df0ba0aafcb83d6ba4e1501b17 -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.cor_margin_separate--claude-auditor--2026-10-19T03_26_48Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.cor_margin_separate ed839d34f480cba1b90f9a7b02bff832 by=claude-auditor source=A:sec3:margin-paragraph@10e392992d5cc46ba3cbfa36215cf105187e98df0ba0aafcb83d6ba4e1501b17 -->
<!-- spec-review: Dissertation.PaperSpec.A.cor_margin_findim ed839d34f480cba153b1b629e759bb45 by=claude-author source=A:sec3:margin-paragraph@10e392992d5cc46ba3cbfa36215cf105187e98df0ba0aafcb83d6ba4e1501b17 -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.cor_margin_findim--claude-auditor--2026-10-19T03_34_36Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.cor_margin_findim ed839d34f480cba153b1b629e759bb45 by=claude-auditor source=A:sec3:margin-paragraph@10e392992d5cc46ba3cbfa36215cf105187e98df0ba0aafcb83d6ba4e1501b17 -->

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
* `ex_fulllaw_wp`: there is a function `C_stab` of `(T, L, ‖G‖, c_G, α, β₁, β₂)`, quantified
  before everything else, such that, with these data and a baseline `C` with datum `ξ₀` satisfying
  (2.3), Assumptions 2.2–2.5 (`L₀`, `G` of full rank, `α, β₁, β₂`) and (2.13) with `c_diss > 0`:
  under (5.1) the perturbed system `C.perturb (ex54Pert …)` satisfies (2.3), Assumption 2.2 with
  `ξ₀`, Assumption 2.3 with some `L`, Assumption 2.5 with the baseline's `G, α, β₁, β₂` and (2.13)
  with margin `c_diss − ‖G‖ L_p`, has a `Solution`, any two `Solution`s are equal in `ℍ`, and for
  every `L` with which it satisfies Assumption 2.3, (3.1) holds with the constant
  `C_stab(T, L, ‖G‖, s_min(G)⁻², α, β₁, β₂)` for its solutions against the solutions of every
  system `2` with (2.3) and Assumptions 2.2–2.3. The last conjunct is that of `cor_robust_wp`,
  with `p = ex54Pert …`.
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
  Theorems 3.1, 3.3 and 3.5 ((2.3) and Assumptions 2.2–2.5) and (2.13) with that margin, has the
  conclusion of Theorem 3.5 (a solution in `ℍ`, unique in `ℍ`, as in `thm_cwp`), and satisfies
  the estimate (3.1) of Theorem 3.1 as `cor_robust_wp` states it: `C_stab` a function of
  `(T, L, ‖G‖, c_G, α, β₁, β₂)` chosen first, `L` any constant with which the perturbed system
  satisfies Assumption 2.3, the perturbed system as system `1` against every system `2` with (2.3)
  and Assumptions 2.2–2.3, and the `δh` of (3.1) along `Θ²⁻`, as in `thm_stab`. The uniqueness of
  Theorem 3.3 in the larger class `ℍ_weak` is not restated; `cor_robust_wp` states it for every
  perturbation of the corollary, this one included. (5.1) is as printed.
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

* `Dissertation.Acceptance.A.ex_fulllaw_jump_hypotheses` for `ex_fulllaw_lip`, `ex_fulllaw_pert`
  and `ex_fulllaw_wp`: over a Lévy driver with `d = 1`, `ν = δ₀` on `ℝ`, `𝒢₀ = ⊥`, `n = 1`,
  `T = 1`, the baseline Example 5.1(i) with `β₁ = β₂ = 2`, `σ_c = h_c = 0` and datum `0`
  (`L₀ = 2`, `G = 1`, `α = β₁ = β₂ = 1`, margin `c_diss = 1`), the baseline the example names;
  `ε = 1/8`, `𝔮 = 𝔮̃ = 𝔮̂ = min{|·|, 1}`, `Q(s) = min{|s₁|, 1}`, `φ₁(u) = min{‖u‖, 1}`,
  `w₀ = w₁ = v₀ = e₁ ∈ ℝ¹` and `ĥ = e₁ ∈ L²(δ₀; ℝ¹)`, all Lipschitz constants `1`, so
  `L_p = 4/8 = 1/2` and (5.1) reads `1/2 < 1`. The theorem proves `w₀ ≠ 0`, `w₁ ≠ 0`, `v₀ ≠ 0` and
  `ĥ ≠ 0` (`‖ĥ‖ = 1`), so all four perturbations, the jump perturbation of `h` among them, are
  present. It replaces `ex_fulllaw_hypotheses` (`ε = 1/4`, `ĥ = 0`, `L_p = 3/4`), in which the
  jump direction vanished.
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
bounded Lipschitz features. `ex_fulllaw_wp` reads "well-posed" as Theorem 3.5 does: a solution in
`ℍ`, unique in `ℍ`, depending on the data through (3.1).

Restatement of `ex_fulllaw_wp` at `1f67672`. The proposition formerly ended at existence and
uniqueness in `ℍ`, and this review read the estimate (3.1) as following from `thm_stab`, not
restated. The example's "well-posed" is that of Corollary 3.6, "by Theorems 3.1, 3.3 and 3.5 it
is well-posed", and Theorem 3.5 includes the dependence on coefficients and data "in the sense of
the estimate (3.1)"; without (3.1) the proposition was narrower than the printed claim, as an
independent re-reading judged. The stability conjunct of `cor_robust_wp` was appended, with
`C_stab` quantified first; the other conjuncts are unchanged. The proof
(`Dissertation.Acceptance.A.ex_fulllaw_wp`) takes `C_stab` from `cor_robust_wp` and that
conjunct at `p = ex54Pert …`, with `L_p` as above and `c_pert = ‖G‖ L_p` from `ex_fulllaw_pert`,
under (5.1).

Re-reading at `1f67672` (`sections/05-examples.tex` lines 274–348, quoted above, with the
overview of §5 at lines 9–22 and Remark 5.7 at lines 549–553): the example's only change is that
the fibre `L²(ν)` of the `Q`-term is no longer called "infinite-dimensional"; the overview and
Remark 5.7 are unchanged. Each proposition still says what the passage says (`ex_fulllaw_wp` as
restated). The instantiations that give the printed claims:

* `ex_fulllaw_lip`: the proposition holds for all `n, m, d, J` and every σ-finite `ν`, without
  the bounds on the profiles, on `Q` and on the features; the printed claim is its instance at
  `m = n`, `ν ≠ 0` (the overview of §5) and bounded data.
* `ex_fulllaw_pert`: it holds for every `G`; the printed claim is its instance at bounded data,
  `ν ≠ 0` and the `G` of full rank of the baseline.
* `ex_fulllaw_wp`: it holds for every baseline of Corollary 3.6 and every σ-finite `ν`; the
  printed claim is its instance at bounded data, `ν ≠ 0` and the baseline the example names
  (Example 5.1(i)) or a law-dependent dissipative one ("works identically").
* `ex_fulllaw_beyond_radial`: it holds for all `m`, every σ-finite `ν` and every `φ` integrable
  against every law of `P₂(H)`; the printed claim is its instance at `m = n`, `ν ≠ 0` and the `φ`
  of the expectation and two-point-kernel interactions of Examples 5.1–5.3 and of the linear
  jump-integrand expectations, each such a function.
* `ex_fulllaw_beyond_U_corr`: the same, with `m = n ≥ 1` and `ν ≠ 0` giving its hypothesis
  `L²(ν; ℝᵐ) ≠ {0}`.
* `ex_fulllaw_beyond_Q`: it does not assume `Q` bounded; the printed claim is its instance at
  bounded `Q`, `m = n` and `ν ≠ 0`, against the same `φ'`.
* `ex_fulllaw_affineQ`: it does not assume the features bounded; the printed claim is its
  instance at bounded Lipschitz features, `m = n` and `ν ≠ 0`.

<!-- spec-review: Dissertation.PaperSpec.A.ex_fulllaw_lip ed839d34f480cba11fea7903ed24f9f8 by=claude-author source=A:ex:fulllaw@5f21b4ec1722cc0bcf4a3113d8782610d06e4e035be63d4b232c314fbc92da38 -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_fulllaw_pert ed839d34f480cba1e9dade95deb0a071 by=claude-author source=A:ex:fulllaw@5f21b4ec1722cc0bcf4a3113d8782610d06e4e035be63d4b232c314fbc92da38 source=A:rem:regimes@2fd005374f04e994d90588bd134885c30eabc9f355464ae64a4c76eeda7b97a5 -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_fulllaw_wp ed839d34f480cba10404c6cf3a0cc0d0 by=claude-author source=A:ex:fulllaw@5f21b4ec1722cc0bcf4a3113d8782610d06e4e035be63d4b232c314fbc92da38 source=A:rem:regimes@2fd005374f04e994d90588bd134885c30eabc9f355464ae64a4c76eeda7b97a5 -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_fulllaw_beyond_radial ed839d34f480cba1fc87ff54d30df5ad by=claude-author source=A:ex:fulllaw@5f21b4ec1722cc0bcf4a3113d8782610d06e4e035be63d4b232c314fbc92da38 source=A:rem:regimes@2fd005374f04e994d90588bd134885c30eabc9f355464ae64a4c76eeda7b97a5 source=A:sec5:overview@85ef567e93b2eddcbd19ae70a2daac18fc886c5303ea56d4b6dc281d39f4f3e9 -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_fulllaw_beyond_U_corr ed839d34f480cba193f328d7c8c243ea by=claude-author source=A:ex:fulllaw@5f21b4ec1722cc0bcf4a3113d8782610d06e4e035be63d4b232c314fbc92da38 source=A:sec5:overview@85ef567e93b2eddcbd19ae70a2daac18fc886c5303ea56d4b6dc281d39f4f3e9 -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_fulllaw_beyond_Q ed839d34f480cba12be9f13eb8df21c1 by=claude-author source=A:ex:fulllaw@5f21b4ec1722cc0bcf4a3113d8782610d06e4e035be63d4b232c314fbc92da38 -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_fulllaw_affineQ ed839d34f480cba1b7c4d4b7307e74ea by=claude-author source=A:ex:fulllaw@5f21b4ec1722cc0bcf4a3113d8782610d06e4e035be63d4b232c314fbc92da38 -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_fulllaw_lip ed839d34f480cba11fea7903ed24f9f8 by=claude-author source=A:ex:fulllaw@c6dac94442298fb91021e9410980558e1c560d7da7bb03b9fe21e4542a37e683 -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.ex_fulllaw_lip--claude-auditor--2026-10-19T03_34_36Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_fulllaw_lip ed839d34f480cba11fea7903ed24f9f8 by=claude-auditor source=A:ex:fulllaw@4176ca3d18b96f9c52b91a364a4ddab7da82df540496d303cc1ccabf2366be8b -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.ex_fulllaw_lip--claude-auditor--2026-10-20T11_24_09Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_fulllaw_lip ed839d34f480cba11fea7903ed24f9f8 by=claude-auditor source=A:ex:fulllaw@5f21b4ec1722cc0bcf4a3113d8782610d06e4e035be63d4b232c314fbc92da38 -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_fulllaw_pert ed839d34f480cba1e9dade95deb0a071 by=claude-author source=A:ex:fulllaw@c6dac94442298fb91021e9410980558e1c560d7da7bb03b9fe21e4542a37e683 source=A:rem:regimes@8628790b3f61760d63f6a1cb8711d6fb055f4a005b160d92c994e6a8185b1c0c -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.ex_fulllaw_pert--claude-auditor--2026-10-19T03_34_36Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_fulllaw_pert ed839d34f480cba1e9dade95deb0a071 by=claude-auditor source=A:ex:fulllaw@4176ca3d18b96f9c52b91a364a4ddab7da82df540496d303cc1ccabf2366be8b source=A:rem:regimes@2fd005374f04e994d90588bd134885c30eabc9f355464ae64a4c76eeda7b97a5 -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.ex_fulllaw_pert--claude-auditor--2026-10-20T11_24_09Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_fulllaw_pert ed839d34f480cba1e9dade95deb0a071 by=claude-auditor source=A:ex:fulllaw@5f21b4ec1722cc0bcf4a3113d8782610d06e4e035be63d4b232c314fbc92da38 source=A:rem:regimes@2fd005374f04e994d90588bd134885c30eabc9f355464ae64a4c76eeda7b97a5 -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_fulllaw_wp ed839d34f480cba173d663ff51153197 by=claude-author source=A:ex:fulllaw@c6dac94442298fb91021e9410980558e1c560d7da7bb03b9fe21e4542a37e683 source=A:rem:regimes@8628790b3f61760d63f6a1cb8711d6fb055f4a005b160d92c994e6a8185b1c0c -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.ex_fulllaw_wp--claude-auditor--2026-10-19T03_34_36Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_fulllaw_wp ed839d34f480cba173d663ff51153197 by=claude-auditor source=A:ex:fulllaw@4176ca3d18b96f9c52b91a364a4ddab7da82df540496d303cc1ccabf2366be8b source=A:rem:regimes@2fd005374f04e994d90588bd134885c30eabc9f355464ae64a4c76eeda7b97a5 -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.ex_fulllaw_wp--claude-auditor--2026-10-20T12_42_56Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_fulllaw_wp ed839d34f480cba10404c6cf3a0cc0d0 by=claude-auditor source=A:ex:fulllaw@5f21b4ec1722cc0bcf4a3113d8782610d06e4e035be63d4b232c314fbc92da38 source=A:rem:regimes@2fd005374f04e994d90588bd134885c30eabc9f355464ae64a4c76eeda7b97a5 -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_fulllaw_beyond_radial ed839d34f480cba1fc87ff54d30df5ad by=claude-author source=A:ex:fulllaw@c6dac94442298fb91021e9410980558e1c560d7da7bb03b9fe21e4542a37e683 source=A:rem:regimes@8628790b3f61760d63f6a1cb8711d6fb055f4a005b160d92c994e6a8185b1c0c source=A:sec5:overview@85ef567e93b2eddcbd19ae70a2daac18fc886c5303ea56d4b6dc281d39f4f3e9 -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.ex_fulllaw_beyond_radial--claude-auditor--2026-10-19T03_37_07Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_fulllaw_beyond_radial ed839d34f480cba1fc87ff54d30df5ad by=claude-auditor source=A:ex:fulllaw@4176ca3d18b96f9c52b91a364a4ddab7da82df540496d303cc1ccabf2366be8b source=A:rem:regimes@2fd005374f04e994d90588bd134885c30eabc9f355464ae64a4c76eeda7b97a5 source=A:sec5:overview@85ef567e93b2eddcbd19ae70a2daac18fc886c5303ea56d4b6dc281d39f4f3e9 -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.ex_fulllaw_beyond_radial--claude-auditor--2026-10-20T11_24_09Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_fulllaw_beyond_radial ed839d34f480cba1fc87ff54d30df5ad by=claude-auditor source=A:ex:fulllaw@5f21b4ec1722cc0bcf4a3113d8782610d06e4e035be63d4b232c314fbc92da38 source=A:rem:regimes@2fd005374f04e994d90588bd134885c30eabc9f355464ae64a4c76eeda7b97a5 source=A:sec5:overview@85ef567e93b2eddcbd19ae70a2daac18fc886c5303ea56d4b6dc281d39f4f3e9 -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_fulllaw_beyond_U_corr ed839d34f480cba193f328d7c8c243ea by=claude-author source=A:ex:fulllaw@c6dac94442298fb91021e9410980558e1c560d7da7bb03b9fe21e4542a37e683 source=A:sec5:overview@85ef567e93b2eddcbd19ae70a2daac18fc886c5303ea56d4b6dc281d39f4f3e9 -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.ex_fulllaw_beyond_U_corr--claude-auditor--2026-10-19T03_37_48Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_fulllaw_beyond_U_corr ed839d34f480cba193f328d7c8c243ea by=claude-auditor source=A:ex:fulllaw@4176ca3d18b96f9c52b91a364a4ddab7da82df540496d303cc1ccabf2366be8b source=A:sec5:overview@85ef567e93b2eddcbd19ae70a2daac18fc886c5303ea56d4b6dc281d39f4f3e9 -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.ex_fulllaw_beyond_U_corr--claude-auditor--2026-10-20T11_24_09Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_fulllaw_beyond_U_corr ed839d34f480cba193f328d7c8c243ea by=claude-auditor source=A:ex:fulllaw@5f21b4ec1722cc0bcf4a3113d8782610d06e4e035be63d4b232c314fbc92da38 source=A:sec5:overview@85ef567e93b2eddcbd19ae70a2daac18fc886c5303ea56d4b6dc281d39f4f3e9 -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_fulllaw_beyond_Q ed839d34f480cba12be9f13eb8df21c1 by=claude-author source=A:ex:fulllaw@c6dac94442298fb91021e9410980558e1c560d7da7bb03b9fe21e4542a37e683 -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.ex_fulllaw_beyond_Q--claude-auditor--2026-10-19T03_38_27Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_fulllaw_beyond_Q ed839d34f480cba12be9f13eb8df21c1 by=claude-auditor source=A:ex:fulllaw@4176ca3d18b96f9c52b91a364a4ddab7da82df540496d303cc1ccabf2366be8b -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.ex_fulllaw_beyond_Q--claude-auditor--2026-10-20T11_24_10Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_fulllaw_beyond_Q ed839d34f480cba12be9f13eb8df21c1 by=claude-auditor source=A:ex:fulllaw@5f21b4ec1722cc0bcf4a3113d8782610d06e4e035be63d4b232c314fbc92da38 -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_fulllaw_affineQ ed839d34f480cba1b7c4d4b7307e74ea by=claude-author source=A:ex:fulllaw@4176ca3d18b96f9c52b91a364a4ddab7da82df540496d303cc1ccabf2366be8b -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.ex_fulllaw_affineQ--claude-auditor--2026-10-19T03_37_37Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_fulllaw_affineQ ed839d34f480cba1b7c4d4b7307e74ea by=claude-auditor source=A:ex:fulllaw@4176ca3d18b96f9c52b91a364a4ddab7da82df540496d303cc1ccabf2366be8b -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.ex_fulllaw_affineQ--claude-auditor--2026-10-20T11_24_10Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_fulllaw_affineQ ed839d34f480cba1b7c4d4b7307e74ea by=claude-auditor source=A:ex:fulllaw@5f21b4ec1722cc0bcf4a3113d8782610d06e4e035be63d4b232c314fbc92da38 -->

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

<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_potential ed839d34f480cba1c2e5952133294af3 by=claude-author source=A:ex:dealer@3dfd46a5ffe721a5c7560c057227552960a29e63ca7af022a17dd6989f44556c -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.ex_dealer_potential--claude-auditor--2026-10-19T03_27_12Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_potential ed839d34f480cba1c2e5952133294af3 by=claude-auditor source=A:ex:dealer@08e7f11942ef37bd28c33d6517d5be2e155483a056ed1db445cfd0e697e7f90b -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_crowd ed839d34f480cba1542ac74da98a0887 by=claude-author source=A:ex:dealer@3dfd46a5ffe721a5c7560c057227552960a29e63ca7af022a17dd6989f44556c -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.ex_dealer_crowd--claude-auditor--2026-10-19T03_27_20Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_crowd ed839d34f480cba1542ac74da98a0887 by=claude-auditor source=A:ex:dealer@08e7f11942ef37bd28c33d6517d5be2e155483a056ed1db445cfd0e697e7f90b -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_coeffs ed839d34f480cba17c7bbab57e15328e by=claude-author source=A:ex:dealer@08e7f11942ef37bd28c33d6517d5be2e155483a056ed1db445cfd0e697e7f90b -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.ex_dealer_coeffs--claude-auditor--2026-10-19T03_27_20Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_coeffs ed839d34f480cba17c7bbab57e15328e by=claude-auditor source=A:ex:dealer@08e7f11942ef37bd28c33d6517d5be2e155483a056ed1db445cfd0e697e7f90b -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_ham ed839d34f480cba18d97e926abe7317b by=claude-author source=A:ex:dealer@08e7f11942ef37bd28c33d6517d5be2e155483a056ed1db445cfd0e697e7f90b -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.ex_dealer_ham--claude-auditor--2026-10-19T03_27_20Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_ham ed839d34f480cba18d97e926abe7317b by=claude-auditor source=A:ex:dealer@08e7f11942ef37bd28c33d6517d5be2e155483a056ed1db445cfd0e697e7f90b -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer ed839d34f480cba1e2c74601c0086824 by=claude-author source=A:ex:dealer@08e7f11942ef37bd28c33d6517d5be2e155483a056ed1db445cfd0e697e7f90b -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.ex_dealer--claude-auditor--2026-10-19T03_34_36Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer ed839d34f480cba1e2c74601c0086824 by=claude-auditor source=A:ex:dealer@08e7f11942ef37bd28c33d6517d5be2e155483a056ed1db445cfd0e697e7f90b -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_mono ed839d34f480cba17aa9ad92a733a79a by=claude-author source=A:ex:dealer@08e7f11942ef37bd28c33d6517d5be2e155483a056ed1db445cfd0e697e7f90b source=A:rem:regimes@2fd005374f04e994d90588bd134885c30eabc9f355464ae64a4c76eeda7b97a5 source=A:abstract@3e98e9839e7e2470c7619601cd0e8f5468477dfdc4dc1f5681314fc4ca1483a9 source=A:sec5:overview@85ef567e93b2eddcbd19ae70a2daac18fc886c5303ea56d4b6dc281d39f4f3e9 -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.ex_dealer_mono--claude-auditor--2026-10-19T03_34_36Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_mono ed839d34f480cba17aa9ad92a733a79a by=claude-auditor source=A:ex:dealer@08e7f11942ef37bd28c33d6517d5be2e155483a056ed1db445cfd0e697e7f90b source=A:rem:regimes@2fd005374f04e994d90588bd134885c30eabc9f355464ae64a4c76eeda7b97a5 source=A:abstract@3e98e9839e7e2470c7619601cd0e8f5468477dfdc4dc1f5681314fc4ca1483a9 source=A:sec5:overview@85ef567e93b2eddcbd19ae70a2daac18fc886c5303ea56d4b6dc281d39f4f3e9 -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_wp ed839d34f480cba1382a433c842b2a2c by=claude-author source=A:ex:dealer@08e7f11942ef37bd28c33d6517d5be2e155483a056ed1db445cfd0e697e7f90b source=A:rem:regimes@2fd005374f04e994d90588bd134885c30eabc9f355464ae64a4c76eeda7b97a5 source=A:abstract@3e98e9839e7e2470c7619601cd0e8f5468477dfdc4dc1f5681314fc4ca1483a9 source=A:sec5:overview@85ef567e93b2eddcbd19ae70a2daac18fc886c5303ea56d4b6dc281d39f4f3e9 -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.ex_dealer_wp--claude-auditor--2026-10-19T03_34_36Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_wp ed839d34f480cba1382a433c842b2a2c by=claude-auditor source=A:ex:dealer@08e7f11942ef37bd28c33d6517d5be2e155483a056ed1db445cfd0e697e7f90b source=A:rem:regimes@2fd005374f04e994d90588bd134885c30eabc9f355464ae64a4c76eeda7b97a5 source=A:abstract@3e98e9839e7e2470c7619601cd0e8f5468477dfdc4dc1f5681314fc4ca1483a9 source=A:sec5:overview@85ef567e93b2eddcbd19ae70a2daac18fc886c5303ea56d4b6dc281d39f4f3e9 -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_twopoint ed839d34f480cba10e7a45835d5244c0 by=claude-author source=A:ex:dealer@3dfd46a5ffe721a5c7560c057227552960a29e63ca7af022a17dd6989f44556c -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.ex_dealer_twopoint--claude-auditor--2026-10-19T03_27_19Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_twopoint ed839d34f480cba10e7a45835d5244c0 by=claude-auditor source=A:ex:dealer@08e7f11942ef37bd28c33d6517d5be2e155483a056ed1db445cfd0e697e7f90b -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_mean_corr ed839d34f480cba18bab6ae8a6c6a027 by=claude-author source=A:ex:dealer@3dfd46a5ffe721a5c7560c057227552960a29e63ca7af022a17dd6989f44556c -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.ex_dealer_mean_corr--claude-auditor--2026-10-19T03_27_19Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_mean_corr ed839d34f480cba18bab6ae8a6c6a027 by=claude-auditor source=A:ex:dealer@08e7f11942ef37bd28c33d6517d5be2e155483a056ed1db445cfd0e697e7f90b -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_marks ed839d34f480cba140a65f520ffefa33 by=claude-author source=A:ex:dealer@3dfd46a5ffe721a5c7560c057227552960a29e63ca7af022a17dd6989f44556c source=A:abstract@3e98e9839e7e2470c7619601cd0e8f5468477dfdc4dc1f5681314fc4ca1483a9 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.ex_dealer_marks--claude-auditor--2026-10-19T03_27_26Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_marks ed839d34f480cba140a65f520ffefa33 by=claude-auditor source=A:ex:dealer@08e7f11942ef37bd28c33d6517d5be2e155483a056ed1db445cfd0e697e7f90b source=A:abstract@3e98e9839e7e2470c7619601cd0e8f5468477dfdc4dc1f5681314fc4ca1483a9 -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_not_mean_corr ed839d34f480cba1d76cfc2366e08961 by=claude-author source=A:ex:dealer@08e7f11942ef37bd28c33d6517d5be2e155483a056ed1db445cfd0e697e7f90b source=A:rem:regimes@2fd005374f04e994d90588bd134885c30eabc9f355464ae64a4c76eeda7b97a5 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.ex_dealer_not_mean_corr--claude-auditor--2026-10-19T03_27_19Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_not_mean_corr ed839d34f480cba1d76cfc2366e08961 by=claude-auditor source=A:ex:dealer@08e7f11942ef37bd28c33d6517d5be2e155483a056ed1db445cfd0e697e7f90b source=A:rem:regimes@2fd005374f04e994d90588bd134885c30eabc9f355464ae64a4c76eeda7b97a5 -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_affine ed839d34f480cba14f86326a4c8f6eab by=claude-author source=A:ex:dealer@08e7f11942ef37bd28c33d6517d5be2e155483a056ed1db445cfd0e697e7f90b -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.ex_dealer_affine--claude-auditor--2026-10-19T03_27_20Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_affine ed839d34f480cba14f86326a4c8f6eab by=claude-auditor source=A:ex:dealer@08e7f11942ef37bd28c33d6517d5be2e155483a056ed1db445cfd0e697e7f90b -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_riccati ed839d34f480cba122071b255b506300 by=claude-author source=A:ex:dealer@08e7f11942ef37bd28c33d6517d5be2e155483a056ed1db445cfd0e697e7f90b -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.ex_dealer_riccati--claude-auditor--2026-10-19T03_27_19Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_riccati ed839d34f480cba122071b255b506300 by=claude-auditor source=A:ex:dealer@08e7f11942ef37bd28c33d6517d5be2e155483a056ed1db445cfd0e697e7f90b -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_inert ed839d34f480cba141c76d0c8dddc879 by=claude-author source=A:ex:dealer@08e7f11942ef37bd28c33d6517d5be2e155483a056ed1db445cfd0e697e7f90b -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.ex_dealer_inert--claude-auditor--2026-10-19T03_34_36Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_inert ed839d34f480cba141c76d0c8dddc879 by=claude-auditor source=A:ex:dealer@08e7f11942ef37bd28c33d6517d5be2e155483a056ed1db445cfd0e697e7f90b -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_spec_marks ed839d34f480cba1efd7d1ab7e3204fd by=claude-author source=A:ex:dealer@08e7f11942ef37bd28c33d6517d5be2e155483a056ed1db445cfd0e697e7f90b -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.ex_dealer_spec_marks--claude-auditor--2026-10-19T03_26_36Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_spec_marks ed839d34f480cba1efd7d1ab7e3204fd by=claude-auditor source=A:ex:dealer@08e7f11942ef37bd28c33d6517d5be2e155483a056ed1db445cfd0e697e7f90b -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_zero ed839d34f480cba1fbee3842d146d0f8 by=claude-author source=A:ex:dealer@08e7f11942ef37bd28c33d6517d5be2e155483a056ed1db445cfd0e697e7f90b -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.ex_dealer_zero--claude-auditor--2026-10-19T03_34_36Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_zero ed839d34f480cba1fbee3842d146d0f8 by=claude-auditor source=A:ex:dealer@08e7f11942ef37bd28c33d6517d5be2e155483a056ed1db445cfd0e697e7f90b -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_symm ed839d34f480cba11753a45d7d37cdc6 by=claude-author source=A:ex:dealer@08e7f11942ef37bd28c33d6517d5be2e155483a056ed1db445cfd0e697e7f90b -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.ex_dealer_symm--claude-auditor--2026-10-19T03_27_19Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_symm ed839d34f480cba11753a45d7d37cdc6 by=claude-auditor source=A:ex:dealer@08e7f11942ef37bd28c33d6517d5be2e155483a056ed1db445cfd0e697e7f90b -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_active ed839d34f480cba11684a792fea39139 by=claude-author source=A:ex:dealer@08e7f11942ef37bd28c33d6517d5be2e155483a056ed1db445cfd0e697e7f90b source=A:rem:regimes@2fd005374f04e994d90588bd134885c30eabc9f355464ae64a4c76eeda7b97a5 source=A:abstract@3e98e9839e7e2470c7619601cd0e8f5468477dfdc4dc1f5681314fc4ca1483a9 source=A:sec5:overview@85ef567e93b2eddcbd19ae70a2daac18fc886c5303ea56d4b6dc281d39f4f3e9 -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.ex_dealer_active--claude-auditor--2026-10-19T03_34_35Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_active ed839d34f480cba11684a792fea39139 by=claude-auditor source=A:ex:dealer@08e7f11942ef37bd28c33d6517d5be2e155483a056ed1db445cfd0e697e7f90b source=A:rem:regimes@2fd005374f04e994d90588bd134885c30eabc9f355464ae64a4c76eeda7b97a5 source=A:abstract@3e98e9839e7e2470c7619601cd0e8f5468477dfdc4dc1f5681314fc4ca1483a9 source=A:sec5:overview@85ef567e93b2eddcbd19ae70a2daac18fc886c5303ea56d4b6dc281d39f4f3e9 -->
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_depends ed839d34f480cba1d5b82af653b55a54 by=claude-author source=A:ex:dealer@08e7f11942ef37bd28c33d6517d5be2e155483a056ed1db445cfd0e697e7f90b -->
Review by claude-auditor: broader (report `reports/Dissertation.PaperSpec.A.ex_dealer_depends--claude-auditor--2026-10-19T05_49_14Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.ex_dealer_depends ed839d34f480cba1d5b82af653b55a54 by=claude-auditor source=A:ex:dealer@08e7f11942ef37bd28c33d6517d5be2e155483a056ed1db445cfd0e697e7f90b -->

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

Re-reading at `1f67672` (`sections/05-examples.tex` lines 532–546, quoted above): the remark now
gives the argument for the unavoidable pointwise `u`-dependence (the symmetric sign `ξ`, the
tuples with `U = ξ w` and `U' = −ξ w`, one law, the left side of (2.7) zero against the right side
`−4 β₁ ‖G* w‖² < 0`). The argument proves the assertion the proposition states; it adds no other
claim. The proposition still says what the passage says: two diagonal inputs with one law and the
same `(X, Y, Z)` at which `h` differs, which is what the argument exhibits (with `δX = δY = δZ = 0`
the left side of (2.7) is the jump pairing alone, so it is `h` that must read `u` pointwise). The
proof's symmetric factor is a Brownian increment in place of the sign, as recorded above.

<!-- spec-review: Dissertation.PaperSpec.A.rem_freelaw ed839d34f480cba105f02a9629cb6b98 by=claude-author source=A:rem:freelaw@f13ee0338a04a13ffc7c298c326bbddd96efa2f48c9dc8e2a7281612c39beecb -->
<!-- spec-review: Dissertation.PaperSpec.A.rem_freelaw ed839d34f480cba105f02a9629cb6b98 by=claude-author source=A:rem:freelaw@e2204cd5268c52bf28ead0e1dd0321d0914e8ca0c49f13ab56fa690ca4815fea -->
Review by claude-auditor: faithful (report `reports/Dissertation.PaperSpec.A.rem_freelaw--claude-auditor--2026-10-19T03_34_36Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.rem_freelaw ed839d34f480cba105f02a9629cb6b98 by=claude-auditor source=A:rem:freelaw@c2b143b44403046035d85f7e9d730c306f0b5cb52b01f72f3a72ded8e56980b7 -->
Review by claude-auditor: faithful with representation choices (report `reports/Dissertation.PaperSpec.A.rem_freelaw--claude-auditor--2026-10-20T11_24_08Z.md`).
<!-- spec-review: Dissertation.PaperSpec.A.rem_freelaw ed839d34f480cba105f02a9629cb6b98 by=claude-auditor source=A:rem:freelaw@f13ee0338a04a13ffc7c298c326bbddd96efa2f48c9dc8e2a7281612c39beecb -->

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
