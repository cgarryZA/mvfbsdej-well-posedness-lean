### A:rem:diag-mono, A:abstract, A:conclusion: Dissertation.PaperSpec.A.rem_diag_mono
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba146c1633f8e03b86c (pl-fp-v1:64f834769da042adf20dfb54f477d15ff842e5f91be6f37be61a2f15a8533751)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:34:01Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:15:37Z):
Reading (locked before any Lean): spec rem_diag_mono, Remark 2.8, clause "the pointwise condition
gives Assumption 2.5, under (2.3) and Assumption 2.3; pointwise monotonicity gives expected
diagonal monotonicity".

Paper content. The pointwise G-monotonicity condition: the inequality of (2.7) without
expectations, at every fixed theta, theta' in H and mu, mu' in P_2(H) (free measures):
  <b(t,theta,mu)-b(t,theta',mu'), G^T dy> + <dsigma, G^T dz>_F + <-df, G dx>
   + int_E <dh(e), G^T du(e)> nu(de)
  <= -beta1 (|G^T dy|^2 + |G^T dz|_F^2 + ||G^T du||^2) - beta2 |G dx|^2
(for a.e. t, or every t). Applying it at theta = Theta(omega), theta' = Theta'(omega),
mu = Law Theta, mu' = Law Theta' and taking expectations yields the interior inequality of
Assumption 2.5 along all diagonal pairs (for the same set of t). "So the pointwise condition is the
stronger one." The terminal half of Assumption 2.5 is not mentioned by the pointwise condition
(the remark speaks of "the inequality of (2.7)"); a formal "gives Assumption 2.5" either concerns
the interior inequality only, or assumes also a pointwise/expected terminal condition and the
constant constraints (alpha,beta1,beta2 >= 0, alpha+beta1>0, beta1+beta2>0, rank conditions).
"The converse fails" is Prop 3.8, not this clause.

A faithful formal statement must contain:
- standing setting (any basis, any sigma-finite nu, any dims, G any m x n matrix (full rank not
  needed for this implication)), deterministic jointly Borel coefficients;
- hypothesis: the pointwise inequality at every theta, theta', mu, mu' (free) for the t's in
  question (a.e. t or all t), with constants beta1, beta2;
- conclusion: for those t (a.e. t) and all diagonal pairs (Theta,Law Theta),(Theta',Law Theta')
  with Theta, Theta' in L2(Omega,F_t;H), the expected interior inequality with the same constants.
- Integrability: the paper's "taking expectations" is implicitly in the extended sense (the
  pointwise right side is integrable and <=0, so the left side has an expectation in [-inf,0]).
  A Lean Bochner-integral formulation needs the left side integrable to avoid the junk value 0;
  the clause adds (2.3) (Borel measurability of h into L2(nu)) and Assumption 2.3 (diagonal
  Lipschitz) as hypotheses, which give measurability and square-integrability of the coefficient
  differences along L2 inputs. This is an added hypothesis relative to the printed remark, but
  harmless in the paper's context, where joint Borel measurability is standing and Assumption 2.3
  accompanies Assumption 2.5 in every use. I would accept it as a representation choice provided
  it only serves integrability (and say so); a hypothesis that does more work would be narrowing.
- If the conclusion is the full Assumption 2.5 (terminal part too), the statement must assume the
  terminal condition and constant constraints as well, otherwise it would claim more than the
  remark.
Comparison (verdict recorded 2026-10-19T03:18:50Z):
Comparison: spec rem_diag_mono (Sec2Remarks.lean:44-77) against my locked reading.

Setting: arbitrary Ω, 𝒢₀ independent of the driver, E countably generated, ν σ-finite, dims
n, m, d, LevyDriver, filtration enlJoint (the standing augmented filtration). T, β₁, β₂, G (any
m×n matrix, no rank condition — fine, the implication does not need it), coefficients C with
JointBorel T C ((2.3), standing in the paper).

Hypothesis: for a.e. t ∈ [0,T], for all θ, θ' ∈ H and all μ, μ' ∈ P₂(H) (free laws), the
pointwise (2.7): pairing27 G C t θ θ' μ μ' ≤ −β₁(|Gᵀδy|² + |Gᵀδz|²_F + ‖Gᵀδu‖²) − β₂|Gδx|².
pairing27 is exactly ⟨δb, Gᵀδy⟩ + ⟨δσ, Gᵀδz⟩_F + ⟨−δf, Gδx⟩ + ∫⟨δh(e), Gᵀδu(e)⟩ν(de). "a.e. t"
in the hypothesis is at least as weak as the paper's (unspecified, presumably every/a.e.) t —
harmless.

Conclusion, part 1 (only (2.3) assumed): for a.e. t and all diagonal pairs in 𝒟_t,
∫⁻ (pairing)⁺ dP < ∞ (the expectation exists in [−∞, ∞)), and if the pairing is integrable its
expectation satisfies (2.7). This is the extended-real reading of the paper's "taking
expectations gives (2.7)": when the pairing is not integrable its expectation is −∞ and (2.7) is
trivial, so the Lean statement says exactly what the paper says while avoiding the Bochner junk
value 0. Part 2: if moreover Assumption 2.3 holds with some L, then for a.e. t Mono27At, i.e.
the Lean form of the interior Assumption 2.5 (integrability of the pairing plus (2.7)) along 𝒟_t.
The clause name ("under (2.3) and Assumption 2.3") refers to this second part; the Lipschitz
hypothesis only supplies the integrability that the Lean form of Assumption 2.5 demands, and
part 1 already gives the content without it.

Scope: interior inequality only; the remark's pointwise condition is "the inequality of (2.7)",
so the terminal half of Assumption 2.5 is not part of the claim (as my reading anticipated).
Witness rem_affine_hypotheses (Acceptance/A/Sec2Remarks.lean:263) exhibits Example 5.1(i)
(ν = δ₀, n = m = d = 1, β₁ = β₂ = 1) satisfying JointBorel, Assumption 2.3 and the pointwise
hypothesis: hypotheses are met at an intended instance; not vacuous.

Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless:
1. The paper's "taking expectations" is in the extended sense; the Lean conclusion encodes it as
   "the positive part has finite expectation, and the inequality holds whenever the pairing is
   integrable" (the non-integrable case has expectation −∞, where (2.7) is trivial). This avoids
   the Bochner junk value 0 and says the same thing.
2. A second conjunct adds Assumption 2.3 as a hypothesis to conclude the Lean form Mono27At of
   the interior Assumption 2.5, whose definition demands integrability of the pairing; Lipschitz
   only supplies that integrability. The first conjunct gives the claim without it, so nothing is
   lost.
3. Only the interior inequality (2.7) is concluded, matching the remark's pointwise condition,
   which is "the inequality of (2.7)"; the pointwise hypothesis is imposed for a.e. t (no stronger
   than the paper's).
Disagreements with the author's review (shown 2026-10-19T03:33:35Z): Labelling only, no disagreement of substance. The other review calls the proposition "broader",
treating the first conjunct (positive part of the pairing integrable; (2.7) whenever the pairing
is integrable, without Assumption 2.3) as an extra strengthening and the second conjunct as the
printed claim. I read the first conjunct as the extended-real form of the remark itself, since
the remark's "taking expectations" assumes no Lipschitz bound, and the second as the Lean form of
Assumption 2.5 with the integrability that Assumption 2.3 supplies. Hence my label "faithful with
representation choices". The review's other point, that beta1 and beta2 range over all reals, is
a harmless broadening that I did not list; it supports their label. Both labels are in the
matching group, and we agree that the interior-only conclusion and the a.e.-t pointwise hypothesis
are right.
