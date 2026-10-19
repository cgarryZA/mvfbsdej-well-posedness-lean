### A:abstract, A:ass:lip, A:conclusion, A:cor:robust, A:eq:coeffint, A:eq:coefmeas, A:eq:hborel, A:eq:termg, A:ex:brownian, A:ex:concrete, A:ex:dealer, A:ex:expfunc, A:ex:fulllaw, A:intro:limin-comparison, A:lem:cont, A:lem:lawflow, A:lem:pert, A:lem:small, A:prop:strict, A:rem:beta1-dich, A:rem:cwp-class, A:rem:diag-mono, A:rem:freelaw, A:rem:generalrank, A:rem:intrinsic, A:rem:regimes, A:rem:uniq-no-integ, A:rem:wasserstein-bounds, A:sec2:hborel-derivation, A:sec4:horizon-not-contractive, A:sec5:overview, A:sec:examples, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: Dissertation.Law.w2sq
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash 6e694fea4529496c920fecf03305481e (pl-fp-v1:d3aa0e1f510976fa085cc60bef508780f5008737acd70612955a2f361565a445)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:27:45Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:13:55Z):
Reading of def:Dissertation.Law.w2sq.

Paper notion. The squared quadratic Wasserstein distance, i.e. the optimal quadratic transport
cost: W_2(mu,mu')^2 = inf_{pi in Pi(mu,mu')} int |x-y|^2 d pi (Villani Def. 6.1; Remark 2.6
eq:coupling / eq:couplingT bound W_2^2 by the synchronous cost E|Theta-Theta'|^2).

Faithful Lean definition: w2sq mu mu' := infimum over pi with IsCoupling pi mu mu' of
transportCostSq pi, e.g. sInf {c | exists pi, IsCoupling pi mu mu' /\ transportCostSq pi = c}
or iInf over the coupling subtype, real- or ENNReal-valued. Edge cases: real sInf of an empty set
or of a set unbounded below is 0 in Mathlib; couplings of probability measures always exist
(product), and costs are >= 0, so for probability measures the real infimum is the genuine one,
provided the cost values themselves are not junk (see transportCostSq: for P_2 marginals no
junk). For non-P_2 marginals a real-valued version can be junk (e.g. a Bochner-junk 0 cost),
harmless only if never used outside P_2. ENNReal iInf has no junk.
Comparison (verdict recorded 2026-10-19T03:18:45Z):
def:Dissertation.Law.w2sq (Dissertation/Law/Wasserstein.lean:108-111):
  w2sq μ ν := ⨅ γ, ⨅ _ : IsCoupling μ ν γ, transportCostSq γ   (ℝ≥0∞).
Against the reading: the infimum over all couplings γ (measures on E × E with marginals μ, ν) of
the ENNReal quadratic cost; an ENNReal iInf has no junk (the empty infimum is ⊤, the correct value
of an infimum over no couplings, which in any case does not arise for probability measures, where
the product coupling exists — isCoupling_prod). This is Villani's W_2². Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-19T03:27:24Z): none
