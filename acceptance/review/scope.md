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
* The manuscript is pinned at `1f67672`, the corrections of a proof-step check of `f598204`. (4.25) is printed
  for `0 < ε ≤ 1`: `A:eq:bwdyoung` has the one clause `eq_bwdyoung`, the former corrected
  reading, and the refuted reading is gone. Remark 2.11 no longer says that the margin `c` fails
  in (2.13); its third clause is `rem_margin_smaller` (`c / c_G < c` when `c_G > 1`), in place
  of `rem_margin_sharp`. (2.9) is printed at `X_T`, Remark 5.6 gives the argument for its
  pointwise dependence, Example 5.4 drops "infinite-dimensional", and the §4 preamble cites BDG
  at `p = 1` and `p = 2`: the clauses are unchanged, the scope note of
  `A:sec4:supremum-criterion` names both exponents, and its source region is the whole sentence
  (lines 35–37 of `04-proof-wellposedness.tex`). The proof of Theorem 3.3 takes `δh` at the
  predictable tuples, a proof step with no clause.
* `A:eq:itoY2` ((4.5), the pathwise Itô identity for `e^t |δY_t|²` in the proof of Lemma 4.1) and
  `A:eq:Gid-path` ((4.17), the pathwise identity for `⟨G δX, δY⟩` in the proof of Lemma 4.3) stay
  `proof-step`; their scope notes, formerly "a step of a printed proof", now say why: each is used
  only through its expectation. What Lemma 4.1 draws from the expectation of (4.5) is `eq_supE`,
  from the library's weighted second-moment identity for Itô–Lévy processes
  (`Ito.SecondMoment.integral_exp_mul_self_eq_of_isItoLevyProcess`), with the zero means of the
  stochastic terms the clauses of `A:lem4.1:M2-infinite-activity`; Step 2 of Lemma 4.3 uses
  (4.19), `eq_Gid`, from the bilinear identity
  (`Ito.SecondMoment.integral_mul_eq_of_isItoLevyProcess`), with the bounds behind the zero means
  the clauses of `A:eq:bdg4`. The pathwise identities are not stated: they would need an
  every-time Itô–Lévy formula with local stochastic integrals. `scope_reviewed` is `false` for
  both until the notes are reviewed.


## The scope decisions of the proof steps, reviewed at `1f67672`

Reviewer: `claude-auditor`, a model of the same family as the author of the decisions under
review. Manuscript: revision `1f67672`, sources in `manuscript/paper/`.

The review covers the 28 claims of the inventory whose scope decision was not yet reviewed:
26 recorded `formal`, which are steps of the proofs of Theorem 3.3, Lemmas 4.1–4.3, Theorem 3.5
and Lemma A.1 together with the paragraph before Lemma 4.4, and 2 recorded `proof-step`, the
pathwise identities (4.5) and (4.17). Each scope was decided from the manuscript alone before the
recorded scope, its note and its clauses were compared with it.

### Scope

All 28 blind decisions agree with the recorded scopes (26 `formal`, 2 `proof-step`).
Resolutions: agree 28, recorded right 0, blind right 0, both 0.

Three of the agreements are close. The difference equations (4.15) and (4.16) follow from (4.1)
by linearity, and (4.20) is Assumption 2.5 applied along the two solutions, so `proof-step` would
have been equally defensible for these three. Recording them as `formal` costs nothing.

The clauses of (3.2) and (3.3) carry the hypotheses of Theorem 3.3 (Assumptions 2.3–2.5 and full
rank of `G`). Under these hypotheses the theorem gives `Θ¹ = Θ²`, so both clauses follow from
Theorem 3.3 with both sides zero. The argument of the two steps uses Assumption 2.3 alone, and
Remark 3.4 asserts that the membership `Θ¹ − Θ² ∈ ℍ` needs "only the Lipschitz control of
coefficient differences". `A:rem:uniq-no-integ` maps that sentence to Theorem 3.3, so no claim
states the Lipschitz-only form. The gap is in the coverage of Remark 3.4, which lies outside this
subset. It is not a gap in these two passages, which are asserted under the theorem's hypotheses.

### The two proof steps

(4.17). Every statement of the note is accurate. The identity is referenced only at lines 579
and 625 of Section 4. Step 2 inserts (4.20) and (4.21) into (4.19), not into (4.17). (4.19) is
`A:eq:Gid`, stated and with an acceptance theorem, obtained from the library's bilinear
second-moment identity. That identity exists, and Lemma 4.3's hypotheses supply its hypotheses
through Assumption 2.3 and `Θ¹ − Θ² ∈ ℍ`. The zero means of the five stochastic terms are the
clauses of `A:eq:bdg4`. The expectation of (4.17) is itself a printed display, (4.19), so
nothing the proof takes from (4.17) is left unstated.

(4.5). Every statement of the note is accurate except one. The identity is referenced only at
lines 139 and 189. The proof takes expectations at each `t`. The bound on `𝔼 sup|δY|²`
(lines 219–245) does not use (4.5). The zero means are clauses of
`A:lem4.1:M2-infinite-activity`. The library's weighted second-moment identity exists, and at
weight `e^s` its difference between the horizons `T` and `t` is the expectation of (4.5). A
pathwise statement would need local stochastic integrals. The inaccurate statement is "What the
proof draws from the expectation is stated and proved: eq_supE (the bound at every time and
(4.6))". What the proof draws first is the weighted inequality of lines 193–199, and `eq_supE`
does not state it. The `proof-step` decision is sound once that display is a clause of
`A:eq:supE` (item 3 below).

### Scope notes

Six formal claims of the subset carry a scope note. Every statement in them checks against the
text except one. The note of `A:eq:coerc` places the display that inserts (4.20) and (4.21) into
(4.19) at lines 669–680, but it is at lines 670–680; line 669 closes the display defining `𝒩′` and
`𝒦`. The note of `A:eq:contract` is accurate but says nothing about lines 445–454 (item 6).

### Uncovered assertions

No clause of its claim and no other claim of the inventory states the following eleven
assertions, which fall in nine claims. Each is a display or sentence of the same proof step as
its claim, next to the pinned display. For `A:eq:fwddiff`, `A:eq:coerc` and `A:eq:bdg4` the
inventory already reads such neighbouring displays as part of the passage, and for `A:eq:supE` it
does so for the bound by `R`. Paths are relative to `manuscript/paper/sections/`.

1. `A:eq:uniq-coeff`, `03-main-results.tex`, lines 133–138. This bound holds for almost every
   time with a constant independent of `t`, and (3.2) is its time integral. It is stronger than
   (3.2).
   ```latex
   Hence Assumption~\ref{ass:lip} yields
   \E\big[|\delta b_t|^2+|\delta\sigma_t|_F^2+\Lnorm{\delta h_t}^2+|\delta f_t|^2\big]
   \le C\,\E|\delta\Theta_t|_{\mathcal H}^2
   for a.e.\ $t$, where $C$ is independent of $t$.
   ```
2. `A:eq:uniq-bwd`, `03-main-results.tex`, lines 158–163. This is the backward difference
   equation to which Lemma 4.1 is applied to give (3.3). Its counterpart in Lemma 4.3 is the
   formal claim `A:eq:dY`.
   ```latex
   For the backward equation,
   \delta Y_t=\delta g_T+\int_t^T\delta f_s\,\diff s-\int_t^T\delta Z_s\,\diff W_s
   -\int_t^T\!\!\int_E\delta U_s(e)\,\Nt(\diff s,\diff e),
   where $\delta g_T:=g(X^1_T,\Law(X^1_T))-g(X^2_T,\Law(X^2_T))$.
   ```
3. `A:eq:supE`, `04-proof-wellposedness.tex`, lines 188–199. This is the expectation of (4.5)
   after Young's inequality, and the paper uses (4.5) through this display alone. It implies the
   bound by `R` that the clause states, but the converse fails.
   ```latex
   Taking expectations in \eqref{eq:itoY2} therefore removes the three martingale terms, and
   bounding the drift term by Young's inequality,
   $2\inner{\delta Y_s}{\phi_s}\le|\delta Y_s|^2+|\phi_s|^2$, cancels the $|\delta Y_s|^2$
   integrals on the two sides:
   \E e^{t}|\delta Y_t|^2+\E\int_t^T e^{s}\big(|\delta Z_s|_F^2+\Lnorm{\delta U_s}^2\big)\diff s
   \le\E e^{T}|\delta\xi|^2+\E\int_t^T e^{s}|\phi_s|^2\diff s .
   ```
4. `A:eq:coeffdiff`, `04-proof-wellposedness.tex`, lines 333–337. This bound holds for almost
   every `s`, and the first link of (4.9) is its integral, so it is stronger than that link. The
   pointwise bound of lines 329–332 is Assumption 2.3 itself and is not listed.
   ```latex
   Squaring, using Cauchy--Schwarz in $\R^5$, taking expectations, and bounding the deterministic
   Wasserstein term by \eqref{eq:coupling} give
   \E\,S_s^2\le 10L^2\,\E\big[|\delta X_s|^2+|\delta Y_s|^2+|\delta Z_s|_F^2+\Lnorm{\delta U_s}^2\big].
   ```
5. `A:eq:bwddiff`, `04-proof-wellposedness.tex`, lines 391–397. This is the backward difference
   that brings Lemma 4.1 to bear. Its forward twin is the clause `eq_fwddiff_identity` of
   `A:eq:fwddiff`, so the two halves of the contraction are treated differently.
   ```latex
   Taking the difference of \eqref{eq:frozenbwd} at $\Theta^1$ and $\Theta^2$, the terms $q^g_T$
   and $q^f$ cancelling,
   \delta\bar Y_t=\delta\bar\xi+\int_t^T\!\lambda\,\delta f_s\,\diff s
   -\int_t^T\!\delta\bar Z_s\,\diff W_s-\int_t^T\!\!\int_E\delta\bar U_s(e)\,\Nt(\diff s,\diff e) ,
   which is \eqref{eq:dYlin} with $\delta\xi=\delta\bar\xi$ and $\phi_s=\lambda\,\delta f_s$.
   ```
6. `A:eq:contract`, `04-proof-wellposedness.tex`, lines 445–454. This sentence fixes the printed
   threshold and states the contraction by `1/2`. `lem_small` leaves `λ*` an unspecified
   function of `(T, L)`, so neither fact is stated anywhere.
   ```latex
   Setting \lambda_*:=(2\sqrt{C_\Phi})^{-1}\in(0,\tfrac12] gives $C_\Phi\lambda^2\le\tfrac14$ for
   $\lambda\in[0,\lambda_*]$, so that \eqref{eq:contract} reads
   \|\Phi_\lambda(\Theta^1)-\Phi_\lambda(\Theta^2)\|_{\HH}
   \le\tfrac12\,\|\Theta^1-\Theta^2\|_{\HH},\qquad\lambda\in[0,\lambda_*] .
   ```
7. `A:eq:fwd`, `04-proof-wellposedness.tex`, lines 697–709. This chain holds at every `t ≤ T`
   and is the input to Grönwall. The clause states only its consequence (4.23).
   ```latex
   \E\sup_{s\le t}|\delta X_s|^2
   \le C\Big(\E|\delta\xi_0|^2+\E\!\int_0^t\!\big(|\delta b_s|^2+|\delta\sigma_s|_F^2+\Lnorm{\delta h_s}^2\big)\diff s+P\Big)
   \le C\Big(\E|\delta\xi_0|^2+\E\!\int_0^t\!\big(|\delta X_s|^2+|\delta Y_s|^2+|\delta Z_s|_F^2+\Lnorm{\delta U_s}^2\big)\diff s+P\Big)
   \le C\Big(\int_0^t\!\E\sup_{r\le s}|\delta X_r|^2\,\diff s
   +\E\!\int_0^T\!\big(|\delta Y_s|^2+|\delta Z_s|_F^2+\Lnorm{\delta U_s}^2\big)\diff s+P\Big) .
   ```
8. `A:eq:fwd`, `04-proof-wellposedness.tex`, lines 710–711, in the sentence of (4.23) itself.
   The assertion is trivial, since `Θ¹ − Θ² ∈ ℍ`.
   ```latex
   The map $t\mapsto\E\sup_{s\le t}|\delta X_s|^2$ is nondecreasing and finite, since
   $\Theta^1-\Theta^2\in\HH$
   ```
9. `A:eq:wgt`, `04-proof-wellposedness.tex`, lines 735–744. This is the display obtained by
   inserting (4.25) into (4.24).
   ```latex
   \E\,e^{\kappa t}|\delta Y_t|^2
   +\E\!\int_t^T\!e^{\kappa s}\Big[\big(\kappa-\tfrac{C}{\varepsilon}\big)|\delta Y_s|^2
   +(1-\varepsilon)\big(|\delta Z_s|_F^2+\Lnorm{\delta U_s}^2\big)\Big]\diff s
   \le\E\,e^{\kappa T}|\lambda\delta g_T+q^g_T|^2
   +\tfrac{C}{\varepsilon}\,\E\!\int_t^T\!e^{\kappa s}\big(|\delta X_s|^2+|q^f_s|^2\big)\diff s .
   ```
10. `A:eq:wgt`, `04-proof-wellposedness.tex`, lines 745–752. This bound holds at every `t`, its
    right side depends on `t`, and (4.26) follows from it. It is stronger than (4.26).
    ```latex
    Take $\varepsilon<1$ and $\kappa>C/\varepsilon$. The $\delta Y$-integral on the left is then
    nonnegative and may be dropped, and the weights satisfy $1\le e^{\kappa s}\le e^{\kappa T}$
    on $[0,T]$, so
    \E|\delta Y_t|^2+\E\!\int_t^T\!\big(|\delta Z_s|_F^2+\Lnorm{\delta U_s}^2\big)\diff s
    \le C\Big(\E|\lambda\delta g_T+q^g_T|^2
    +\E\!\int_t^T\!\big(|\delta X_s|^2+|q^f_s|^2\big)\diff s\Big).
    ```
11. `A:eq:bwd`, `04-proof-wellposedness.tex`, lines 761–772, the first two links. These are the
    forward-form BDG bound and the Lipschitz step. (4.27) implies the conclusion of the chain but
    not these links.
    ```latex
    \E\sup_{t\le T}|\delta Y_t|^2
    \le C\Big(\E|\delta Y_0|^2+\E\!\int_0^T\!|\lambda\,\delta f_s+q^f_s|^2\diff s
    +\E\!\int_0^T\!\big(|\delta Z_s|_F^2+\Lnorm{\delta U_s}^2\big)\diff s\Big)
    \le C\Big(\E|\delta Y_0|^2
    +\E\!\int_0^T\!\big(|\delta X_s|^2+|\delta Y_s|^2+|\delta Z_s|_F^2+\Lnorm{\delta U_s}^2\big)\diff s+P\Big)
    ```

One more printed estimate lies between two passages of this subset and in neither of them. In
the proof of Theorem 3.3 (`03-main-results.tex`, lines 144–156), the forward difference
equation and the bound
`𝔼 sup|δX_t|² ≤ C_T 𝔼∫(|δb|² + |δσ|²_F + ‖δh‖²) < ∞` lead to `δX ∈ S²`. No claim states
them.

### Extraneous clauses

None. Four clauses state more than their passage literally prints, and each is justified:

* `A:lem4.1:M2-infinite-activity` states `M²` as a martingale on `[0, T]` where the text says
  local martingale. The note records this, and it is true because the compensator is
  integrable.
* `A:eq:coerc` states that `𝒩′` and `P` are finite. This follows from `Θ¹ − Θ² ∈ ℍ` and is
  needed for the `[0, ∞]` reading.
* `A:eq:frozenbwd` states that `Θ̄` is unique in `ℍ`. This is what "`Φ_λ` is well defined"
  means, and the converse paragraph of the proof (lines 463–483) uses it.
* `A:eq:terdiff` is stated for any two square-integrable terminal values. The printed inequality
  is an instance.

### Decisions that differed

| Claim | Recorded | Blind | Resolution | Note |
|---|---|---|---|---|
| — | — | — | — | No decision differed. |


## Regions of the claims without clauses, widened to their sentences

Author: `claude-author`, the session that keeps the inventory; this records changes of region, not
a review. Manuscript: revision `1f67672`.

The final check of the pinned regions found 20 claims without clauses (16 `part-of`, 2
`duplicate`, 2 `proof-step`) whose region was one line, or a label-anchored display, inside a
longer sentence. Each region is now the sentence or passage its title asserts, pinned as a span of
whole lines inside its host's environment where it has one; no numbered environment is crossed
and no environment pin was converted. No review rests on these claims, so no marker changed. A
`part-of` or `duplicate` claim names only its host in `scope_note` (the check reads that note as
the host's id), so what the added lines are is recorded here; the two `proof-step` claims record
their lead-ins in their notes as well. Line numbers are those of the file named in the second
column.

| Claim | Scope, file | Region | Added lines |
|---|---|---|---|
| `A:intro:rsz-extension` | part-of `A:ex:brownian`, `01-introduction.tex` | 95 → 95–97 | 96–97, the rest of the sentence: that the condition of [RSZ, (H.1)(1)], like [BYZ, (A1)], is posed on the joint law of `(X, Y, Z)` with a rectangular full-rank `G`, a statement about cited work (the host's note names only [BYZ, (A1)]). Line 97 also begins the next sentence (lines 97–99: the measure argument is the law of the full tuple, `ν` σ-finite), which restates the setting of (1.1) pinned in `A:intro:mvfbsdej` (lines 14–16, 40–48). |
| `A:sec2:fubini-iso` | duplicate `A:eq:fubiniiso`, `02-model-assumptions.tex` | 115 → 112–123, the host's region | 112–114, the lead-in and the predictable σ-field `𝒫`; 117–121, the citation of [HNVW, Propositions 1.2.24–1.2.25], the representative unique up to null sets and the reading of every Poisson integral through it, all asserted by the title; 121–123, the consequence for pointwise formulas `u(e)` and the first words of (2.5), the host's content as its note records. |
| `A:sec2:coefmeas` | duplicate `A:eq:coefmeas`, `02-model-assumptions.tex` | 123 → 123–131 | 124–131, the display (2.5) the title asserts. Line 123 also ends the reading convention of (2.4), pinned in `A:eq:fubiniiso`. |
| `A:ex:concrete(ii)` | part-of `A:ex:concrete`, `05-examples.tex` | 112 → 112–193 | 113–193, the passage (ii) the title summarises: the coefficients and marginal means (113–133), Assumption 2.3 with `L = 2` and Assumption 2.2 (135–148), Assumption 2.5 with `α = β₁ = β₂ = 2` (150–188), and the attribution to [LiMin, Example 3.1, (H3.2)] (190–193), cited work; the host's content, as its note records. |
| `A:eq:lipT` | part-of `A:ass:lip`, `02-model-assumptions.tex` | 156–158 (display) → 149–159 | 149–155 and 159: `L ≥ 0`, the interior bound along `𝒟_t`, the terminal values `X_T, X'_T ∈ L²(Ω, ℱ_T; ℝⁿ)` and 'almost surely'; the host's content (Assumption 2.3, lines 148–160). |
| `A:eq:mono` | part-of `A:ass:mono`, `02-model-assumptions.tex` | 189–193 (display) → 184–193 | 184–188: the terminal inequality and 'for a.e. `t ∈ [0, T]` and all `(Θ, μ), (Θ', μ') ∈ 𝒟_t`'; the host's content (Assumption 2.5, lines 183–199). |
| `A:eq:coupling` | part-of `A:rem:wasserstein-bounds`, `02-model-assumptions.tex` | 204–208 (display) → 201–209 | 201–203: the pair `(Θ, Θ')` realises a coupling of `(μ, μ')`, so the `W₂`-infimum, with the citation of its definition [Villani, Definition 6.1], is bounded by the synchronous transport cost; 209: (2.9) is the `X`-marginal case of (2.8) at `T`; the host's content (Remark 2.6, lines 200–232). |
| `A:eq:couplingT` | part-of `A:rem:wasserstein-bounds`, `02-model-assumptions.tex` | 204–208 (display) → 201–209 | As for `A:eq:coupling`, the same sentence. |
| `A:eq:lipfun` | part-of `A:rem:wasserstein-bounds`, `02-model-assumptions.tex` | 215–221 (display) → 211–221 | 211–214: `K` a separable Hilbert space, `φ̄` Lipschitz, the law functional `W₂`-Lipschitz with the same constant, the optimal coupling `π`, the Lipschitz bound and Jensen; the host's content. |
| `A:eq:margproj` | part-of `A:rem:wasserstein-bounds`, `02-model-assumptions.tex` | 226–231 (display) → 222–231 | 222–225: marginal projection is 1-Lipschitz for `W₂`, the `U`-marginal `μ^U`, the image of `π` a coupling of `(μ^U, μ'^U)`; the host's content. |
| `A:eq:stab` | part-of `A:thm:stab`, `03-main-results.tex` | 57–65 (display) → 52–67 | 52–56: the hypotheses on systems 1 and 2 and the solutions `Θᵏ ∈ ℍ`; 66–67: `C_stab` depends only on `T, L, ‖G‖, c_G, α, β₁, β₂` and `c_BDG`; the host's content (Theorem 3.1, lines 51–71). Line 67 also begins the sentence on the dependence on system 1 alone (lines 67–68), the host's content. |
| `A:eq:pertpair` | part-of `A:cor:robust`, `03-main-results.tex` | 215–219 (display) → 210–219 | 210–214: the perturbations with the origin-integrability and diagonal Lipschitz conditions, `c_pert ≥ 0`, a.e. `t` and all pairs of `𝒟_t`; the host's content (Corollary 3.6, lines 207–236). Line 210 also ends the sentence on the baseline (lines 208–210), the host's content. |
| `A:eq:pertlip` | part-of `A:cor:robust`, `03-main-results.tex` | 230–232 (display) → 229–235 | 229: the perturbations independent of `θ` and `W₂`-Lipschitz; 233–235: a.e. `t`, all pairs of `𝒟_t`, and (3.4) with `c_pert = ‖G‖ L_p`; the host's content. |
| `A:eq:bmean` | part-of `A:prop:strict`, `03-main-results.tex` | 302–305 (display) → 300–314 | 300–301 and 306–314: `n = m = 1`, `d ≥ 1`, `G = 1`, `β₁ > 0`, `0 < ε < β₁`, `m_Y`, the free-measure `W₂`-Lipschitz bound, (3.7) and the failure of the pointwise bound; the host's content (Proposition 3.8, lines 299–315). |
| `A:eq:diagdrift` | part-of `A:prop:strict`, `03-main-results.tex` | 309–311 (display) → 300–314 | 300–308 and 312–314: the setting, the drift (3.6), its Lipschitz bound, 'along all pairs of `𝒟_t`', and the failure of the pointwise bound; the host's content. |
| `A:eq:dYlin` | part-of `A:lem:bpbsde`, `04-proof-wellposedness.tex` | 92–94 (display) → 90–95 | 90–91 and 95: `δY` càdlàg adapted, `δZ ∈ H²_W`, `δU ∈ H²_N`, `δξ ∈ L²(ℱ_T)`, `φ ∈ L²(Ω × [0, T])`; the host's content (Lemma 4.1, lines 89–102). Line 95 also begins the conclusion of the lemma ('Then', lines 95–101), the host's content. |
| `A:eq:itoY2` | proof-step, `04-proof-wellposedness.tex` | 128–137 (display) → 126–137 | 126–127: the lead-in 'Itô's formula for `e^t\|δY_t\|²` then gives the pathwise identity', named in the claim's note. |
| `A:eq:contpert` | part-of `A:lem:pert`, `04-proof-wellposedness.tex` | 500–506 (display) → 491–508 | 491–499: Assumptions 2.3–2.5, `λ̲ ∈ (0, 1]`, `λ ∈ [λ̲, 1]`, the solutions of (4.1) with their data, forcings and integrability, `Θ¹ − Θ² ∈ ℍ`, and `δ· = ·¹ − ·²`; 507–508: the dependence of `C_B`; the host's content (Lemma 4.3, lines 490–509). |
| `A:eq:Gid-path` | proof-step, `04-proof-wellposedness.tex` | 565–578 (display) → 563–578 | 563–564: the lead-in 'Itô's product formula for `⟨G δX_t, δY_t⟩`, integrated over `[0, T]` and using `δX₀ = δξ₀`, then gives the pathwise identity', named in the claim's note. |
| `A:eq:fulllaw-eps` | part-of `A:ex:fulllaw`, `05-examples.tex` | 341–344 (display) → 338–344 | 338–340: by (3.5) and Corollary 3.6, (3.4) holds with `c_pert = ‖G‖ L_p`, so the perturbed system is well-posed, with margin `c_diss − ‖G‖ L_p`, whenever (5.1) holds; the host's content (Example 5.4, lines 274–348). |

One entry is new: `A:intro:contributions` (`01-introduction.tex` lines 101–116), the contribution
list of the introduction, which restates Theorems 3.1, 3.3 and 3.5, Corollary 3.6, Remark 3.7 and
Proposition 3.8 and was pinned by no claim. Like `A:abstract` and `A:conclusion` it is `formal`,
with the clauses `thm_stab`, `thm_uniq`, `thm_cwp`, `cor_robust_wp`, `rem_generalrank_wp`,
`rem_diag_mono`, `prop_strict` and `rem_diag_mono_converse`; its note names every sentence and
what states it. Its scope decision is reviewed in the next section.


## Pinned regions and the remaining scope decisions, reviewed at `1f67672`

Reviewer: `claude-auditor`, a model of the same family as the author of the decisions under
review. Manuscript: revision `1f67672`, sources in `manuscript/paper/`.

* **Uncovered assertions.** The assertions the review of the proof steps found stated by no clause
  are now clauses (the steps of the proof of Theorem 3.3 under Assumption 2.3 alone, which is what
  Remark 3.4 claims, and the steps of the proofs of Lemmas 4.1–4.3 and Theorem 3.5), each proved,
  witnessed at an instance with the relevant objects nonzero, and reviewed blind.
* **Regions.** A verifier read the region of every claim against the manuscript and found 65 that
  held less than their claim asserts (37 displays pinned without the sentence that carries their
  hypotheses or conclusion, 23 single lines of a longer passage, 5 others), and 29 passages that
  formal claims rest on but that lay wholly or partly outside every region (the standing setting of
  §2, the notation of the introduction, the conventions of §4, the set-ups of the proofs). Every
  region now starts and ends at a sentence boundary, crosses no sectioning command, and holds what
  its claim asserts; every sentence in it is stated by a clause or named in the scope note (for a
  `part-of` or `duplicate` claim, whose note names its host, in the table of the author's section
  above). A numbered environment stays pinned at its environment; the notation printed before
  Definition 2.1 and Theorem 3.1 is pinned by three definition entries,
  `A:sec2:tuple-notation`, `A:sec2:difference-notation` and `A:sec3:two-system-notation`, whose
  scopes and readings were reviewed independently. The contribution list of the introduction,
  which restates the main results, is the formal claim `A:intro:contributions`.
* **Reviews at the widened passages.** Widening a region changes its passage digest. Every
  proposition and definition reviewed at a narrower passage was read again at the widened one, by
  the author and independently; no reading changed. The independent readings are recorded in
  `rereads.md`, each with its marker at the widened passage's digest.
* **The contribution list.** `A:intro:contributions` was added after the final check. Each of
  its eight clauses was read against the list and confirmed the earlier independent reading of its
  proposition (`rereads.md`). The same reading found that the clauses state every mathematical
  assertion of the list and that the note names the rest: the cited work of lines 101–102 and the
  description of the method, which points to §4.5 and Lemmas 4.2 and 4.4.
* **Final check.** A last check of all 112 claims found every region of a formal or definition
  claim sound and every standing passage pinned; the 20 regions it found too narrow, all of claims
  without clauses, were widened as it proposed.

Every claim's scope decision is recorded as reviewed (`scope_reviewed`).
