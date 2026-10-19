### A:abstract, A:ass:lip, A:conclusion, A:cor:robust, A:eq:coeffint, A:eq:coefmeas, A:eq:hborel, A:eq:termg, A:ex:brownian, A:ex:concrete, A:ex:dealer, A:ex:expfunc, A:ex:fulllaw, A:intro:limin-comparison, A:lem:cont, A:lem:lawflow, A:lem:pert, A:lem:small, A:prop:strict, A:rem:beta1-dich, A:rem:cwp-class, A:rem:diag-mono, A:rem:freelaw, A:rem:generalrank, A:rem:intrinsic, A:rem:regimes, A:rem:uniq-no-integ, A:rem:wasserstein-bounds, A:sec2:hborel-derivation, A:sec4:horizon-not-contractive, A:sec5:overview, A:sec:examples, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: Dissertation.Law.w2
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash d92ca7948d3f7f2f101d7b3c9f02c50c (pl-fp-v1:a917a944db723ad465f4934b940b2b3d71274fb1b3c45615ab0216ca8fa556ef)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:27:45Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:13:55Z):
Reading of def:Dissertation.Law.w2.

Paper notion. The quadratic Wasserstein distance (Villani Def. 6.1):
  W_2(mu, mu') = ( inf_{pi coupling of (mu,mu')} int |x-y|^2 d pi )^{1/2}
for mu, mu' in P_2(S); finite and attained on Polish S. Used in Assumption 2.3 (Lipschitz in
W_2(mu,mu') and W_2(rho,rho')), Remark 2.6, Prop. 3.8, Ex. 5.4 (W_2(mu,mu_0), W_2(mu^U,
Lambda_0)), Ex. 5.5 (Lipschitz bound of A).

Faithful Lean definition: w2 mu mu' := Real.sqrt (w2sq mu mu') (or the ENNReal analogue then
toReal), with w2sq the infimum of transportCostSq over all couplings (IsCoupling). On P_2
measures: the set of couplings is nonempty (product measure) and costs are finite and >= 0, so a
real sInf/iInf is the genuine infimum. Edge cases: for measures outside P_2 a real-valued
definition may return junk (e.g. 0 from sInf of an empty/unbounded set or Bochner junk); this is
harmless only if w2 is applied only to P_2 measures (as in the paper). The norm on S must be the
paper's one (Hilbert norm on H).
Comparison (verdict recorded 2026-10-19T03:18:45Z):
def:Dissertation.Law.w2 (Dissertation/Law/Wasserstein.lean:113-115):
  w2 μ ν := Real.sqrt (w2sq μ ν).toReal.
Against the reading: √ of the optimal quadratic cost. When w2sq μ ν < ⊤ — always for two P_2 laws
(w2sq_ne_top, product coupling) — this is exactly W_2(μ,ν). When w2sq μ ν = ⊤ (laws at infinite
distance, possible only outside P_2) toReal gives 0, so w2 = 0: a junk value. The module docstring
records this ("every real-valued statement carries a hypothesis forcing the squared distance to be
finite"); w2P and P2W apply w2 only to P_2 laws. Real.sqrt has no junk on toReal ≥ 0.
Verdict: faithful with representation choices (junk 0 at infinite distance).
Witness: —
Verdict: faithful with representation choices — w2 = √((w2sq μ ν).toReal). For two laws of finite second moment w2sq is finite, so w2 is exactly
the paper's W₂. For laws at infinite W₂-distance (only possible outside P₂), toReal ⊤ = 0 makes
w2 = 0, a junk value. The paper applies W₂ only to P₂ laws, and the project's w2P/P2W apply w2 only
to P2 elements; any direct use on arbitrary measures would have to carry a finiteness hypothesis,
which is a matter for the propositions that use it.
Disagreements with the author's review (shown 2026-10-19T03:27:24Z): Only a classification difference: the earlier review says faithful; I record "faithful with
representation choices" because w2 = √((w2sq).toReal) has the junk value 0 for two laws at infinite
squared distance (toReal ⊤ = 0), possible only outside P₂. The module docstring acknowledges this, and
w2P/P2W apply w2 only to P₂ laws, so the meaning is right wherever the paper uses W₂. Any direct
use of w2 on arbitrary measures needs a finiteness hypothesis.
