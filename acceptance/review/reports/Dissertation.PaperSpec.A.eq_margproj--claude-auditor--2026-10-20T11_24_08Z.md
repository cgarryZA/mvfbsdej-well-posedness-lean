### A:rem:wasserstein-bounds: Dissertation.PaperSpec.A.eq_margproj
Pins: manuscript A None; project d3e594defeeeb94a6d05c33c666bcb870d584302; hash ed839d34f480cba1c19abbad6d02050c (pl-fp-v1:add2ab479c715c283f0abfd1c91ccd82e4d32f1549b9881808c8e64365d6745b)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-20T11:24:08Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-20T11:09:24Z):
# Reading: eq_margproj — (2.11) of Remark 2.6

Setting. H with its l2-product norm; P_2(H), P_2(L^2(nu)) (L^2(nu) = L^2(nu; R^m), Euclidean
on R^m), W_2 on each as the coupling infimum. mu^U := the image of mu under the projection
theta = (x,y,z,u) |-> u (the U-marginal).

Hypotheses. mu, mu' in P_2(H).

Conclusion. W_2(mu^U, mu'^U)^2 <= W_2(mu, mu')^2 (equivalently W_2(mu^U, mu'^U) <= W_2(mu, mu')):
marginal projection P_2(H) -> P_2(L^2(nu)) is 1-Lipschitz for W_2. Implicit: mu^U is in
P_2(L^2(nu)) (finite second moment, since ||u|| <= |theta|_H).

The intermediate steps through the optimal coupling pi are proof steps. Faithfulness points:
the projection must be onto the U-component (not another one); norms as above; W_2 genuine (no
junk) on both spaces. A statement for a general product of (pseudo)metric spaces with an
l2-type / dominating norm that specialises to H -> L^2(nu) would be broader and acceptable,
provided the instance is the U-projection of H.
Comparison (verdict recorded 2026-10-20T11:23:00Z):
# Decision: spec:Dissertation.PaperSpec.A.eq_margproj (Dissertation/PaperSpec/A/Sec2.lean)

Verdict: faithful with representation choices.

Comparison with the locked reading.
- μ, μ' range over `P2 (TupleH ν n m d)`, all of P_2(H), for every σ-finite ν on a countably
  generated space and all n, m, d.
- `μ.margU` (Dissertation/Law/TupleMarginal.lean) is `μ.map measurable_projUH norm_projUH_le`,
  the image of μ under `projUH θ = θ.2.2.2`, the projection onto the U-channel
  L^2(ν; R^m); the bundling in `P2` records that μ^U has finite second moment, i.e. μ^U is in
  P_2(L^2(ν)), the printed codomain of the projection.
- Left side: `w2P μ.margU μ'.margU`, W_2 on P_2(L^2(ν; R^m)) for the norm of L^2(ν; R^m)
  (Euclidean on R^m pointwise). Right side: `w2H μ μ'`, W_2 on P_2(H) for the Hilbert norm. Both
  are genuine (finite squared distances on P2 laws, so the real square roots are not junk).
- Conclusion: W_2(μ^U, μ'^U) <= W_2(μ, μ'), equivalent to the printed squared form since both
  sides are nonnegative.
Representation choices (detail file): H as the Lean product with the sup norm and W_2 taken via
`toL2`; laws as `P2`; the unsquared form.

Current text. Read at 1f67672 (Remark 2.6: "Marginal projection P_2(H) -> P_2(L^2(ν)) is
1-Lipschitz for W_2 by the same argument"). I have not seen the earlier text; the proposition
states the current (2.11).

Witness. `Dissertation.Acceptance.A.eq_margproj_hypotheses` (Dissertation/Acceptance/A/
WitnessHyp.lean): ν = δ_0 ≠ 0, n = m = d = 1, and the Dirac masses at 0 and at θ₁ = (1,1,1,1)
are P_2 laws with distinct U-marginals. The proposition has no hypotheses beyond the standing
ones on ν; the witness shows the conclusion is not trivially 0 <= something at that instance.

Coverage (claim A:rem:wasserstein-bounds): see the eq_coupling decision; the four clauses state
every mathematical assertion of Remark 2.6 at this revision and nothing beyond it.
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless:
1. H is the Lean product `TupleH` carrying the sup norm; the right-hand side uses `w2H`, the W_2
   of the paper's Hilbert norm (images under `toL2`), and P_2(H) membership is the same for both
   norms.
2. The U-marginal is the bundled pushforward `μ.margU` along the projection onto the jump channel;
   its `P2` structure records that μ^U lies in P_2(L^2(ν; R^m)).
3. The inequality is stated unsquared, W_2(μ^U, μ'^U) <= W_2(μ, μ'), equivalent to the printed
   squared form as both sides are nonnegative.
Disagreements with the author's review (shown 2026-10-20T11:23:13Z): Disagreement in the verdict label only. The earlier review records "faithful"; I record "faithful
with representation choices", listing that H is realised as the Lean product with the sup norm and
W_2(μ, μ') taken for the Hilbert norm via `toL2` (`w2H`), that μ^U is the bundled pushforward
`μ.margU` in P_2(L^2(ν; R^m)), and that the inequality is stated unsquared. These choices are
harmless, so the substance agrees.
