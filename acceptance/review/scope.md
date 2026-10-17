# The scope decisions of paper A, reviewed

Every claim of `acceptance/claims.json` carries a scope decision (`acceptance/README.md`). This file
records an independent review of all 109 of them by `claude-reviewer`, a model of the same family as
the author of the decisions. The reviewer first decided every claim's scope from the manuscript
alone, without seeing the recorded decisions; it then compared each blind decision with the recorded
one, and for a formal claim checked that the names of its clauses cover every mathematical assertion
of the passage.

Result: 89 blind decisions agree with the recorded ones. Of the 20 that differ, the reviewer
resolved 8 in favour of the recorded decision, judged 12 defensible either way, and found none of
the recorded decisions wrong. One formal claim had an assertion that no clause covered:

* `A:rem:uniq-no-integ` (Remark 3.4). "However, the existence requires Assumption 2.2", set against
  "the uniqueness only requires Assumptions 2.3–2.5", says that Assumption 2.2 cannot be dropped
  from the existence theorem. The clauses had read it only as a necessary condition for every system
  with a solution, which is false, and recorded the claim as refuted as printed. The claim now
  states and proves the reading the sentence makes, and no longer lists the necessity reading as a
  printed clause; the system with the singular drift, which shows that the necessity reading is
  false, remains as the remark's example of uniqueness without Assumption 2.2.

The reviewer also asked for two scope notes to be made precise, and both were changed: that the
derivation of (1.1) from the control problem in Example 5.1 is cited work, and that the uniqueness
along the homotopy is a step of the argument of Section 4 rather than of a printed proof.

## The decisions that differed

| Claim | Recorded | Blind | Resolution | Note |
|---|---|---|---|---|
| `A:rem:G-pairing` | duplicate | part-of | both defensible | Recorded duplicate of A:ass:G, mine part-of A:ass:G: same host. The remark restates in words the 'Then' bounds of Assumption 2.4 (forward control when m>=n, backward incl. Z, U when n>=m), so 'duplicate' fits as well as 'part-of'; ass_G covers every bound, the Z/U extension included. |
| `A:rem:uniq-no-integ` | formal | part-of | the recorded decision | Scope: recorded right. My part-of A:thm:uniq was wrong: the remark restates Remark 3.2 (not a clause of Theorem 3.3) and adds a sentence about existence, so no single host covers it. Coverage defect: the clause 'the existence requires Assumption 2.2, as printed' is formalised as the universal necessity 'every system with a solution in S satisfies Ass 2.2' and refuted by a t^(-1/2) drift; the 'corrects' clause (rem_uniq_singular) only restates that counterexample, so it is the refutation rather than a corrected statement. The natural reading of 'However, the existence requires Assumption 2.2' (contrasting with 'uniqueness only requires 2.3-2.5') is that Ass 2.2 cannot be dropped from Theorem 3.5. That reading is true (sigma = sigma0(t) - beta1 z with sigma0 not in L2(0,T) satisfies (2.3), Ass 2.3-2.5 and has no solution) and no clause states it. Also, 'refuted as printed' rests on the less charitable reading; the review should record the reading dispute. |
| `A:rem:freelaw` | formal | expository | the recorded decision | My expository reading was wrong: besides meta-commentary on the proofs, the remark asserts that u-dependence of the coefficients is unavoidable whenever beta1>0. Remark 2.10 states strict U-dissipativity, not this consequence, and the claim is false as printed at nu=0. The recorded formal scope (printed clause refuted, nu != 0 correction, and (2.8) for the first sentence) is right. The 'nothing is gained by restricting to the (X,Y,Z)-marginal' sentence is exposition. |
| `A:rem:regimes` | formal | expository | the recorded decision | My expository reading ('summary of Ex 5.4, 5.5') was wrong. The remark adds a characterisation proved nowhere else: Example 5.5 is 'a genuinely nonlinear U-law interaction'. The crowding correction A_lambda(u) = int gradV(u-v) lambda(dv) is affine in the law (a two-point-kernel interaction in the sense of Example 5.3), so under the natural reading the claim is false. The recorded clauses refute it and prove the corrected facts (affine in the law, no function of the mean, nonlinear in u). The reading is debatable ('nonlinear' jointly in (u, law) would make it true), but the corrected clause covers both facts. |
| `A:abstract` | formal | expository | the recorded decision | My expository was wrong: the abstract asserts mathematical results ('we prove existence, uniqueness, stability', 'we show ... strictly weaker'). They duplicate several hosts, and a single-host 'duplicate' cannot record that. Formal clauses that reuse the body propositions keep every one in the target at no extra cost. Coverage checked: every assertion of the abstract maps to a clause (Thms 3.1/3.3/3.5, Rem 2.8, Prop 3.8, Ex 5.5 monotonicity, well-posedness and marks). |
| `A:intro:mvfbsdej` | definition | duplicate | both defensible | Recorded definition, mine duplicate of A:eq:mvfbsdej: both carry the same object (system (1.1) and its solution notion); reviewing it as a definition twice is harmless. |
| `A:intro:limin-comparison` | formal | literature | the recorded decision | My literature label dropped the half of the sentence that is about this paper ('the present theorem removes all three restrictions ... Example 5.3 details the embedding'). Recorded formal (thm_cwp at full generality + ex_expfunc_limin), with the description of Li-Min left as literature, is the correct split. The sentence makes no claim that Li-Min's (H3.2) implies Assumption 2.5, so no clause is missing. |
| `A:intro:rsz-extension` | part-of | literature | both defensible | Recorded part-of A:ex:brownian, mine literature. The mathematical core is the Brownian reduction (Assumption 2.5 without its jump term is G-monotonicity on the (X,Y,Z)-law), which ex_brownian_reduction covers. The identification with RSZ (H.1)(1) / BYZ (A1) is a statement about cited work and stays unformalised under either scope. |
| `A:sec2:fubini-iso` | duplicate | formal | both defensible | Host swapped: recorded makes the equation (2.4) formal and the prose claim its duplicate; I did the reverse. The formal clause covers the isometry, the P x E representative and its uniqueness; the 'read every Poisson integral through it' sentence is a convention. |
| `A:sec2:coefmeas` | duplicate | formal | both defensible | Host swapped with A:eq:coefmeas; the two recorded clauses cover both lines of (2.5). |
| `A:sec4:coeffint` | duplicate | formal | both defensible | Host swapped: recorded duplicate of A:eq:coeffint; I made the prose claim the host. Nothing is lost because (4.3) is formal under A:eq:termg. Minor: the scope note should name A:eq:termg as well, since this prose claim covers (4.2) and (4.3). |
| `A:sec4:uniqueness-along-homotopy` | proof-step | formal | both defensible | Recorded proof-step, mine formal. The paragraph is a step of the Section 4 continuation argument ('It remains to prove existence'), not inside a proof environment. Its content is Lemma 4.3 with zero difference data plus the uniqueness in Lemma 4.2's WP, both formal, so proof-step drops nothing. I chose formal out of caution only. The recorded note 'a step of a printed proof' is loosely worded (section-level proof). |
| `A:sec:examples` | formal | literature | the recorded decision | My literature reading was too narrow: the non-existence is 'shown there', but the paper draws its own mathematical conclusion from it (dissipativity cannot be traded for Lipschitz continuity alone). The binding rule puts that existence-of-counterexample claim in the target. sec5_limin (Lipschitz + (2.3) + Ass 2.2, no solution at T=3pi/4 from a datum of nonzero mean) is a faithful, slightly sharpened version. |
| `A:sec5:overview` | formal | expository | the recorded decision | My expository was wrong: the overview asserts properties of the examples (every assumption met at arbitrary activity, subclasses recovered, Ex 5.4 beyond them, Ex 5.5 well posed at every strength). Some of them are false as printed at nu=0 and are refuted/corrected in the clauses. Coverage complete; the cylindrical term is not needed for the existential 'carries the law dependence beyond' claim. |
| `A:conclusion` | formal | expository | the recorded decision | My expository was wrong for the same reason as the abstract: it restates Thms 3.1/3.3/3.5, Cor 3.6, Prop 3.8 (with Rem 2.8) and Rem 2.10, which are mathematical claims; the clauses reuse the host propositions, including the nu != 0 correction of Rem 2.10. The open-questions sentence is exposition. |
| `A:eq:fubiniiso` | formal | part-of | both defensible | Host swap with A:sec2:fubini-iso (see there). |
| `A:eq:coefmeas` | formal | duplicate | both defensible | Host swap with A:sec2:coefmeas (see there). |
| `A:eq:forced` | definition | part-of | both defensible | Recorded definition, mine part-of A:sec4:WP-def (itself a definition); either way the forced system is a reviewed definition. |
| `A:eq:coeffint` | formal | part-of | both defensible | Host swap with A:sec4:coeffint (see there). |
| `A:eq:termg` | formal | part-of | both defensible | Host swap with A:sec4:coeffint (see there). |
