### A:rem:wasserstein-bounds: Dissertation.PaperSpec.A.eq_lipfun
Pins: manuscript A None; project d3e594defeeeb94a6d05c33c666bcb870d584302; hash ed839d34f480cba187b5540277706218 (pl-fp-v1:cadfdb4b31fcb2639bbf5e06ecc4470b9019e5c6744b338cdfe4ab607d38bb09)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-20T11:24:07Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-20T11:09:24Z):
# Reading: eq_lipfun — (2.10) of Remark 2.6

Setting. H as in the standing setting (l2-product Hilbert norm, Frobenius, Euclidean R^m inside
L^2(nu; R^m)); P_2(H) and W_2 on it (coupling infimum). K a separable (real) Hilbert space.

Hypotheses. phibar : H -> K Lipschitz (constant Lip(phibar)); mu, mu' in P_2(H).

Conclusion. | int_H phibar dmu - int_H phibar dmu' |_K <= Lip(phibar) * W_2(mu, mu').
(The integrals are Bochner integrals; they exist because a Lipschitz map has linear growth and
P_2 measures have finite first moment.) The printed chain (the equality through an optimal
coupling pi, the Lipschitz bound, Jensen) are proof steps; the claim is the end-to-end inequality,
i.e. "the law functional mu |-> int phibar dmu is W_2-Lipschitz with the same constant".

Acceptable representation choices: any Lipschitz constant L of phibar in place of the best
constant (the best constant is itself a Lipschitz constant, so the two forms are equivalent);
K any real Hilbert / complete normed space (broader); H generalised to a separable Hilbert
space (broader, with H as instance). Not acceptable: a sup norm on H (changes both the
Lipschitz hypothesis and W_2), a W_2 with junk values reachable for mu in P_2, integrals that
are junk 0 because of missing integrability, or an extra hypothesis such as existence of an
optimal coupling being assumed rather than available.
Comparison (verdict recorded 2026-10-20T11:23:00Z):
# Decision: spec:Dissertation.PaperSpec.A.eq_lipfun (Dissertation/PaperSpec/A/Sec2.lean)

Verdict: faithful with representation choices.

Comparison with the locked reading.
- H, norms, W_2: as in the eq_coupling decision (TupleH with Euclidean, Frobenius and L^2(ν; R^m)
  channels; `w2H` the W_2 of the Hilbert norm through `toL2`; P_2 membership equivalent for the two
  norms). The setting quantifies over every σ-finite ν on a countably generated space and every
  n, m, d, which is the paper's H in all its instances.
- K: `[NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K] [SeparableSpace K]`, a
  separable real Hilbert space, as printed.
- Lipschitz hypothesis: `‖φ θ - φ θ'‖ ≤ L * ‖toL2 θ - toL2 θ'‖` for all θ, θ', i.e. φ is
  L-Lipschitz for the Hilbert norm of H, with `0 ≤ L`. The paper uses the best constant Lip(φ̄);
  the proposition holds for every Lipschitz constant L, in particular for L = Lip(φ̄) (the best
  constant of a Lipschitz map is itself a Lipschitz constant), and conversely the printed bound
  with Lip(φ̄) implies it for every L >= Lip(φ̄). Equivalent.
- Integrals: Bochner integrals `∫ θ, φ θ ∂μ.law`. They are genuine: φ is Lipschitz, hence
  continuous for the product topology (the Hilbert and sup norms are equivalent), hence Borel
  measurable; TupleH is second countable (L^2(ν) is, for ν σ-finite on a countably generated
  space), so the product σ-algebra is the Borel one and φ is strongly measurable into the
  separable K; and a Lipschitz map is integrable against a law of finite second moment
  (`integrable_of_norm_sub_le`, Dissertation/Law/P2.lean). No junk value is reachable.
- Conclusion: `‖∫φ dμ - ∫φ dμ'‖ ≤ L * w2H μ μ'` for all μ, μ' in P_2(H): the printed end-to-end
  inequality |∫φ̄ dμ - ∫φ̄ dμ'|_K <= Lip(φ̄) W_2(μ, μ'). The printed chain through an optimal
  coupling π is proof, not claim.
Representation choices (harmless): (1) an arbitrary Lipschitz constant L >= 0 in place of
Lip(φ̄), equivalent as explained; (2) H realised as a product carrying the sup norm with the
Lipschitz hypothesis and W_2 both taken for the Hilbert norm via `toL2`; (3) laws as the bundled
type `P2`.

Current text. Read at 1f67672 (Remark 2.6). I have not seen the earlier text; the proposition
states the current (2.10) ("the law functional mu |-> int phibar dmu is W_2-Lipschitz with the
same constant").

Witness. `Dissertation.Acceptance.A.eq_lipfun_hypotheses` (Dissertation/Acceptance/A/
Witness.lean): ν = δ_0, n = m = d = 1, K = R^1 (separable Hilbert), φ = the projection θ |-> y,
L = 1, a nonzero Lipschitz map. Genuine instance; the conclusion then is the W_2-Lipschitz bound
of the Y-mean, which the paper itself uses (Proposition 3.8, Example 5.1(ii)).

Coverage (claim A:rem:wasserstein-bounds): see the eq_coupling decision; the four clauses state
every mathematical assertion of Remark 2.6, nothing beyond it, under the hypotheses in force.
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless:
1. The Lipschitz constant is any L >= 0 with ‖φ θ - φ θ'‖ <= L ‖toL2 θ - toL2 θ'‖ rather than the
   best constant Lip(φ̄). Equivalent: Lip(φ̄) is itself such an L, and the printed bound with
   Lip(φ̄) gives the bound for every larger L.
2. H is the Lean product `TupleH` (sup norm), with the Lipschitz hypothesis and W_2 (`w2H`) both
   taken for the paper's Hilbert norm through `toL2`; P_2(H) membership is the same for both
   norms.
3. Laws are elements of the bundled type `P2` (probability measure with finite second moment);
   the integrals are genuine Bochner integrals (φ is continuous hence strongly measurable into the
   separable K, and integrable against P_2 laws by its linear growth).
Disagreements with the author's review (shown 2026-10-20T11:23:13Z): none
