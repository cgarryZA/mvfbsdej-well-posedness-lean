### A:lemA1:polish: Dissertation.PaperSpec.A.lemA1_polish
Pins: manuscript A None; project 6d403c197bfb10fe8808933c6e525ee0ae544fb1; hash ed839d34f480cba19bbef9c769d701cd (pl-fp-v1:4b68a15bdbeca91d4b6519c76e75db13611819ae10bb881504a1208de6dc0d3d)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-20T06:16:50Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-20T06:10:05Z):
Reading of the clause (manuscript/paper/sections/09-appendix.tex, proof of Lemma A.1, Step 2: "the
law map ... into (P_2(H), W_2), which inherits Polishness from H [Villani 2009, Ch. 6]").

This is a cited fact (Villani, Theorem 6.18: if (X, d) is Polish, then the Wasserstein space
(P_p(X), W_p) is Polish), stated for the paper's H.

Setting: n, m, d >= 1 (any n, m, d is a harmless broadening), nu sigma-finite on a countably
generated (E, E) (the standing hypothesis that makes L^2(nu; R^j) separable), and
H = R^n x R^m x R^{m x d} x L^2(nu; R^m) with the Hilbert norm
|theta|_H^2 = |x|^2 + |y|^2 + |z|_F^2 + ||u||_{L^2(nu)}^2. No hypothesis beyond the standing ones
(a statement for any separable Hilbert/Polish space is a broadening whose instance is the paper's H).

Objects. P_2(H): Borel probability measures mu on H with int |theta|_H^2 mu(dtheta) < infinity.
W_2(mu, mu') = (inf over couplings pi of (mu, mu') of int |theta - theta'|_H^2 dpi)^{1/2}
(Villani Def. 6.1), for the Hilbert norm of H. (W_2 for an equivalent sup-type norm is a different,
bi-Lipschitz-equivalent metric with the same Polishness; the clause insists on the Hilbert norm,
which is the metric the paper uses in (coupling) and in the Lipschitz hypotheses.)

Conclusion (what a faithful statement contains):
(a) H is Polish (complete separable metrisable), for its norm topology;
(b) (P_2(H), W_2) is a metric space: W_2 is finite on P_2(H), symmetric, satisfies the triangle
    inequality, and separates laws (W_2(mu, mu') = 0 implies mu = mu');
(c) it is complete: every W_2-Cauchy sequence in P_2(H) converges in W_2 to an element of P_2(H);
(d) it is separable: a countable W_2-dense subset of P_2(H) exists.
The clause name lists "W_2 separates laws, and the space is complete and separable" for (b)-(d);
if symmetry/triangle inequality are not stated, they must be built into the structure the
statement uses (e.g. a metric-space structure whose distance is W_2), otherwise the clause covers
only part of "Polish metric space". The topology/completeness must be the W_2 one, not the weak
topology.
Comparison (verdict recorded 2026-10-20T06:16:10Z):
Comparison of `Dissertation.PaperSpec.A.lemA1_polish` (Dissertation/PaperSpec/A/AppASteps.lean) with my
locked reading of manuscript/paper/sections/09-appendix.tex, Step 2 of the proof of Lemma A.1
("(P_2(H), W_2), which inherits Polishness from H [Villani, Ch. 6]").

Definitions read: `TupleH` (Dissertation/WellPosedness/System/Tuple.lean, with the scoped Borel
instance `lpMeasurableSpace` on L^2(ν)); `TupleL2`, `toL2`, `w2H`
(Dissertation/WellPosedness/System/HilbertW2.lean); `P2WH`, `lawToL2`,
`P2WH.instPseudoMetricSpace`, `TupleP2WH` (Dissertation/WellPosedness/System/HilbertW2Space.lean);
`P2`, `secondMoment`, `IsCoupling`, `transportCostSq`, `w2sq`, `w2`, `w2P`, `P2W`,
`P2W.instPseudoMetricSpace`, `P2.mapOfLe` (Dissertation/Law/).

Setting: ν sigma-finite on a countably generated E (exactly the standing hypothesis), any
n, m, d ∈ ℕ (0 allowed: harmless broadening). No other hypothesis. Matches.

Objects.
- H: `TupleH ν n m d` = ℝ^n × ℝ^m × ℝ^{m×d} × L^2(ν; ℝ^m) as a product (Euclidean channels, the
  matrix channel Euclidean on Fin m × Fin d = Frobenius). The product carries the max of the
  channel norms, but `PolishSpace` is a topological property and the product topology is the
  Hilbert-norm topology. Matches (a).
- P_2(H): `P2 (Tuple …)` = probability measures on H (product of Borel σ-algebras, which is the
  Borel σ-algebra of H since every channel is second countable under the standing hypotheses) with
  ∫ ||θ||^2 dμ < ∞ (`secondMoment`, for the max norm; equivalent to the Hilbert-norm second moment
  within a factor 4). Matches the Wasserstein space of order 2.
- W_2: the distance of `TupleP2WH` is induced by μ ↦ toL2 # μ from `P2W (TupleL2 …)`, whose distance
  is `w2` = sqrt of the infimum over couplings γ (measures on the product with the two marginals)
  of ∫ ||x − y||^2 dγ, in the Hilbert norm of `TupleL2`. Since toL2 is a measurable linear
  bijection with measurable inverse, couplings correspond and this is W_2 for the Hilbert norm of
  H (Villani Def. 6.1), as the clause insists. The real-valued `w2` sends ∞ to 0, but on P_2 the
  squared distance is finite (`w2sq_ne_top`), so no junk value enters.

Conclusion.
- `PolishSpace (TupleH ν n m d)`: (a).
- Metric structure: the instance is a `PseudoMetricSpace` (induced), so symmetry and the triangle
  inequality are built in (proved in `P2W.instPseudoMetricSpace` via `w2P_comm`, `w2P_triangle`)
  and finiteness is automatic for a real distance; separation is stated explicitly,
  `∀ μ μ', dist μ μ' = 0 → μ = μ'` (equality in `P2`, i.e. equal laws). Together: W_2 is a
  metric on P_2(H). Matches (b).
- `CompleteSpace (TupleP2WH ν n m d)`: completeness for the uniformity of the W_2 pseudometric —
  W_2-Cauchy sequences converge in W_2 within P_2(H). Matches (c) (the W_2 topology, not the weak
  one).
- `SeparableSpace (TupleP2WH ν n m d)`: a countable W_2-dense subset. Matches (d).
- `PolishSpace (TupleP2WH ν n m d)`: Polishness of that topology, which also gives the
  separation; redundant with the previous three items but harmless.
Quantifiers: universal over the setting, no constants. Matches.

Witness `Dissertation.Acceptance.A.lemA1_polish_hypotheses`: the instance hypotheses hold at
Lebesgue measure on ℝ (sigma-finite, infinite mass, ℝ countably generated), an instance the paper
intends (infinite activity, L^2(ν) infinite-dimensional). Not vacuous; the only hypotheses are the
standing ones.

Representation choices (harmless): `TupleP2WH` is a type synonym of P_2 of the max-norm product
with the Hilbert-norm W_2 transported through `toL2`; separation stated separately because the
metric instance is a pseudometric; dimensions in ℕ.

Coverage (claim A:lemA1:polish in acceptance/claims.json; clauses eq_coupling and this one;
scope_reviewed false). The passage (line 55, the first sentence of Step 2, lines 53–56) asserts:
by the coupling bound (2.8), the law map Θ ↦ Law(Θ) is 1-Lipschitz from L^2(Ω; H) into
(P_2(H), W_2) — clause eq_coupling, "W_2(Law Θ, Law Θ')^2 <= E||Θ − Θ'||_H^2" by its name (its Lean
is not in my chunk and I do not judge it); and (P_2(H), W_2) inherits Polishness from H — this
clause, with H Polish made explicit. The two clauses together state every mathematical assertion
of that sentence; this clause states nothing the passage does not claim (H Polish is presupposed
by "inherits", and "W_2 separates laws, complete and separable" is what Polish metric space means).
The hypotheses in force at that point for this assertion are only the standing ones (ν
sigma-finite on a countably generated E, so that H is separable); the clause has exactly those —
no more, no fewer. (The rest of Step 2 — composing with the Borel version to get μ⁻, uniqueness,
μ = μ⁻ a.e. — is not in this claim; it is the content of Lemma A.1's own clauses, A:lem:lawflow.)
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless: (1) P_2(H) is `TupleP2WH ν n m d`, a type synonym of P_2 of the
product `TupleH` (max of the channel norms), whose distance is W_2 of the images under `toL2`, i.e.
the 2-Wasserstein distance of the Hilbert norm of H that the paper uses; the max-norm second-moment
condition is equivalent to the Hilbert-norm one. (2) The metric instance is a pseudometric
(symmetry and the triangle inequality built in), so separation of laws is stated as a separate
conjunct; with it W_2 is a metric. (3) H Polish is stated for the product topology, which is the
Hilbert-norm topology. (4) n, m, d range over ℕ (0 allowed), a trivial broadening whose instance
n, m, d >= 1 is the printed claim.
Disagreements with the author's review (shown 2026-10-20T06:16:14Z): No substantive disagreement. I agree that the proposition states the metric reading of "Polish"
(W_2 separates laws, complete for the W_2 uniformity, separable) as well as Mathlib's topological
`PolishSpace`, for the Hilbert-norm W_2. I also agree that H is Polish for the product topology.
Label only: I record `faithful with representation choices` rather than `faithful`. The choices
are these. `TupleP2WH` is a type synonym of P_2 of the max-norm product, with W_2 transported
through `toL2`. Separation is a separate conjunct because the instance is a pseudometric. n, m, d
range over ℕ. All of these are harmless. I do not assess the companion clause `eq_coupling`,
which is outside my chunk.
