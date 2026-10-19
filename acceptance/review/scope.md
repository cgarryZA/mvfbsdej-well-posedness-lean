# The scope decisions of paper A, reviewed

Reviewer: `claude-auditor`, a model of the same family as the author of the decisions. Paper:
"Well-posedness of fully coupled McKean–Vlasov FBSDEs with jumps under full-tuple law
dependence", revision `f598204`. The blind decisions (`pass1.json`) were taken from the
manuscript alone, before the recorded scopes, `claims.json` or any Lean file were opened. The
comparison is in `pass2.json`.

## Account

The frozen inventory has 109 claims. The recorded scopes are 47 `formal`, 29 `proof-step`,
17 `part-of`, 11 `definition` and 5 `duplicate`, with no `expository` or `literature`. The
blind decision agreed with the recorded one on 86 claims, counting the host of a `part-of` or
`duplicate`. Of the 23 differences, the recorded decision is right in 16, the blind one in none,
and either is defensible in 7.

The differences follow two patterns.

* **Summary prose.** The recorded inventory scopes the abstract, the conclusion, the §5
  overview and Remark 5.7 as `formal`, with the propositions of the claims they summarise as
  clauses; the blind pass called them expository. A summary that restates claims of several
  results cannot be a one-host `duplicate`, and it does make mathematical claims, so the
  recorded representation is the faithful one.
* **Claims that are not exposition.** The blind pass missed precise claims in Example 5.2 (setting
  `h ≡ 0` is not a reduction; the reduction at `ν = 0`), in Remark 5.6 (a pointwise
  `u`-dependence that no measure argument sees, which needs a pair of inputs with one law and is
  not literally Remark 2.10), in the §4 sentence on the horizon (a falsifiable claim, given a
  witness), in the §5 preamble (the inference that dissipativity cannot be traded for Lipschitz
  continuity), and in the comparison with Li–Min. It also scoped as proof steps two facts stated
  outside any proof environment: the supremum criterion, and the bounds (4.2)–(4.3). It treated
  the cited Fubini isometry (2.4) as literature, inconsistently with its own `formal` for the
  equally cited representation property.

The seven differences where either decision is defensible are the direction of a duplicate
((2.5), and (1.1) against its prose), definitional displays scoped as definitions or as parts of
their host ((2.12), (2.13), (4.1)), and the relation of Assumption 2.5 to [RSZ]/[BYZ], which is
mostly about cited work but whose checkable part is the `ν = 0` reduction of Example 5.2.

**Clause coverage.** All 47 recorded-`formal` claims were checked against the propositions in
`Dissertation/PaperSpec/A/`. Five assertions are not covered by any clause of their claim:

1. `A:sec3:one-null-set`: "Both sides of each identity are càdlàg in $t$, so the exceptional null
   set may be taken independent of $t$." `sec3_one_null_set` assumes a process `M` with almost
   surely right-continuous paths in place of the Brownian integral, and `Solution` requires such
   a version as part of its definition. The implementation's Brownian integral is an
   `L²`-limit at each time, with no regularity of paths. So no clause states that the Brownian
   side of (1.1) has a càdlàg version. LevyStochCalc's `exists_everywhere_cadlag_vectorIntegral`
   would supply that fact.
2. `A:sec3:HH-banach`: "Under this identification $\|\cdot\|_{\mathbb S}$ is a norm rather than a
   seminorm." `sec3_HH_definite` states only definiteness. The triangle inequality and absolute
   homogeneity are not stated anywhere. They are presupposed by the sentence and used by the
   fixed-point arguments of Lemmas 4.2 and 4.4. This one is minor.
3. `A:abstract`: "we show that expected diagonal monotonicity is strictly weaker than pointwise
   monotonicity." The clauses are `rem_diag_mono` and `prop_strict`, and `prop_strict` is about
   the drift pairing alone. The failure of the converse for a coefficient system satisfying
   Assumption 2.5 is `rem_diag_mono_converse`, a clause of `A:rem:diag-mono` that the abstract
   does not list.
4. `A:conclusion`: "Proposition 3.8 shows that expected diagonal $G$-monotonicity is strictly
   weaker than its pointwise form (Remark 2.8)." The gap is the same as in item 3.
5. `A:sec5:overview`: "Examples 5.2 and 5.3 recover the Brownian [BYZ] and the
   expectation-functional [LiMin] subclasses as special cases." The clauses chosen are
   `ex_brownian` and `ex_expfunc`. The reduction of the assumptions and solution notions at
   `ν = 0` (`ex_brownian_reduction`) and the embedding of the Li–Min kernels
   (`ex_expfunc_limin`) are what "recover as special cases" asserts, and neither is among the
   overview's clauses.

Items 3–5 are covered elsewhere in the inventory. The gap is only in which propositions the
summary claims list, and adding the named propositions closes each one. Item 1 needs a clause,
or a lemma brought to the acceptance layer, for the càdlàg version of the Brownian integral.

**Extraneous clauses.** None. Three readings are close to the line and were judged faithful:

* `rem_margin_sharp` reads "yields the margin $c/c_G$, not $c$" as a counterexample to margin `c`.
* `ex_dealer_inert` says "every solution" where the passage says "the tuple … solves". This
  matches "inert along the solution" and holds by Theorem 3.3.
* Several existential remarks are stated through concrete witnesses: `rem_uniq_singular`,
  `rem_beta1_zero`, `rem_diag_mono_converse`, `cor_margin_findim` and
  `sec4_horizon_not_contractive`. The last of these is a witness at `ν = 0` that uses only the
  `z`-dependence of `σ`.

One naming slip: the docstring of `rem_uniq_singular` calls a `β₂ = 0` system "the system of
Example 5.1(i)", but the example takes `β₁, β₂ > 0`.

**Hosts.** Every `part-of` and `duplicate` host covers its claim except one. `A:sec4:coeffint`
is recorded as a duplicate of `A:eq:coeffint`, which covers (4.2) only; the terminal bound (4.3)
of the same passage is the separate claim `A:eq:termg`. Nothing is lost from the target, but the
host does not cover the whole passage.

**Scope notes.** Two notes omit cited material that is not stated, though nothing is
mis-scoped:

* Example 5.1(ii) is attributed to [LiMin, Ex. 3.1, (H3.2)].
* Example 5.2 compares its reduced hypotheses with [BYZ, (A1)], and the note of `A:ex:brownian`
  is empty.

## Decisions that differed

| Claim | Recorded | Blind | Resolution | Note |
|---|---|---|---|---|
| `A:rem:G-pairing` | duplicate `A:ass:G` | expository | recorded | Restates the bounds derived in Assumption 2.4; `ass_G` covers them. |
| `A:ex:brownian` | formal | expository | recorded | Precise claims: `h ≡ 0` is not a reduction; the assumptions, solutions and PRP at `ν = 0`; both rank branches. |
| `A:rem:freelaw` | formal | expository | recorded | Forced pointwise `u`-dependence invisible to the law (`rem_freelaw`); not literally Remark 2.10. |
| `A:rem:regimes` | formal | expository | recorded | Summary of two examples; no single host; clauses cover it. |
| `A:abstract` | formal | expository | recorded | Mathematical claims made elsewhere, no single host; one sentence partly covered. |
| `A:intro:limin-comparison` | formal | literature | recorded | The claims about this paper (Theorem 3.5's scope, Example 5.3) are its own; Li–Min's description is cited. |
| `A:intro:rsz-extension` | part-of `A:ex:brownian` | literature | both | Mostly cited work; its checkable part is the `ν = 0` reduction in the host. |
| `A:sec2:fubini-iso` | duplicate `A:eq:fubiniiso` | literature | recorded | (2.4) is a labelled claim in the paper's setting that the proofs rely on. |
| `A:sec2:coefmeas` | duplicate `A:eq:coefmeas` | formal | both | Direction of the duplicate only. |
| `A:sec4:horizon-not-contractive` | formal | expository | recorded | Falsifiable claim; witness at `ν = 0`. |
| `A:sec4:supremum-criterion` | formal | proof-step | recorded | Stated outside any proof environment; used by two proofs. |
| `A:sec4:coeffint` | duplicate `A:eq:coeffint` | proof-step | recorded | A claim, not a proof step; the host covers (4.2) only, and (4.3) is `A:eq:termg`. |
| `A:sec:examples` | formal | literature | recorded | "Cannot be traded for Lipschitz continuity" is this paper's inference; `E ξ₀ ≠ 0` is a needed precision. |
| `A:sec5:overview` | formal | expository | recorded | Summary, no single host; one sentence partly covered. |
| `A:conclusion` | formal | expository | recorded | As for the abstract; one sentence partly covered. |
| `A:eq:mvfbsdej` | definition | duplicate `A:intro:mvfbsdej` | both | Two definition records of (1.1) against one duplicate. |
| `A:eq:fubiniiso` | formal | duplicate `A:sec2:fubini-iso` | recorded | As `A:sec2:fubini-iso`. |
| `A:eq:coefmeas` | formal | duplicate `A:sec2:coefmeas` | both | Direction of the duplicate only. |
| `A:eq:monomargin` | definition | part-of `A:rem:margin` | both | Definitional display (`Margin212`). |
| `A:eq:monomarginu` | definition | part-of `A:rem:margin` | both | Definitional display (`Margin213`). |
| `A:eq:forced` | definition | part-of `A:sec4:WP-def` | both | Definitional display (`ForcedSolution`). |
| `A:eq:coeffint` | formal | part-of `A:sec4:coeffint` | recorded | (4.2), stated outside any proof environment. |
| `A:eq:termg` | formal | part-of `A:sec4:coeffint` | recorded | (4.3), likewise. |

## Changes made after the review

* Items 1 and 2: `A:sec3:one-null-set` has the clause `sec3_cadlag_versions` (each stochastic
  integral of (1.1) along a tuple of `ℍ_weak` has an adapted version with every path càdlàg), and
  `A:sec3:HH-banach` the clause `sec3_HH_norm` (the triangle inequality and the absolute
  homogeneity of `‖·‖_ℍ`).
* Items 3–5: `A:abstract` and `A:conclusion` list `rem_diag_mono_converse`, and `A:sec5:overview`
  lists `ex_brownian_reduction` and `ex_expfunc_limin`.
* The docstring of `rem_uniq_singular` names "the affine coefficients of Example 5.1(i) taken at
  `β₁ = 1`, `β₂ = 0`", not the system of the example.
* `A:sec4:coeffint` is `formal` with the clauses `eq_coeffint` and `eq_termg`, covering (4.2) and
  (4.3), which are also the claims `A:eq:coeffint` and `A:eq:termg`.
* The scope notes of `A:ex:concrete` and `A:ex:brownian` record the attribution of (ii) to
  [LiMin, Ex. 3.1] and the comparison with [BYZ, (A1)] as statements about cited work.
* `A:eq:bwdyoung`, the Young bound (4.25) in Step 4 of the proof of Lemma 4.3, recorded as a
  `proof-step`, is `formal`: an external review found the printed bound, for every `ε > 0` with
  `C` independent of `ε`, false. Its clauses are the printed reading `eq_bwdyoung`, refuted, and
  the reading for `0 < ε ≤ 1`, the range the proof uses, `eq_bwdyoung_corr`; its source region is
  extended to the sentence that governs the display (lines 724–731 of
  `04-proof-wellposedness.tex`).
