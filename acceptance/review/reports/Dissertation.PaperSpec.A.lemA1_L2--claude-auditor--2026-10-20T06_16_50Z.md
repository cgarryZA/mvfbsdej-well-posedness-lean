### A:lemA1:pettis: Dissertation.PaperSpec.A.lemA1_L2
Pins: manuscript A None; project 6d403c197bfb10fe8808933c6e525ee0ae544fb1; hash ed839d34f480cba1a6657535c81c9ed1 (pl-fp-v1:cc46a93f0cfd1047cb1e5cec87b937880c2cc692e115135e1626f7965ae2310a)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-20T06:16:50Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-20T06:10:05Z):
Reading of the clause (manuscript/paper/sections/09-appendix.tex, proof of Lemma A.1, Step 1, the
display "E int_0^T ||Theta_t^-||_H^2 dt < infinity, that is, Theta^- in L^2([0,T] x Omega; H)").

Setting. A probability space (Omega, F, P) with a filtration (F_t) on [0,T], T > 0 (the standing
basis of Section 2; nothing of the Brownian/Poisson structure is used in Step 1, so a statement
over an arbitrary filtered probability space is a harmless broadening). Dimensions n, m, d >= 1
(a statement for all n, m, d is broader and harmless). A sigma-finite measure nu on a countably
generated measurable space (E, E). The state space H = R^n x R^m x R^{m x d} x L^2(nu; R^m) with
the Hilbert norm |theta|_H^2 = |x|^2 + |y|^2 + |z|_F^2 + ||u||_{L^2(nu)}^2 (Euclidean norms on R^j,
Frobenius on matrices). A product carrying a sup-type norm is an equivalent norm, so the finiteness
of E int ||Theta^-||^2 is unaffected, but the clause says "H with its Hilbert norm"; I accept
either as long as the norm is equivalent, but note the choice.

Hypotheses (those of Lemma A.1):
- X : [0,T] x Omega -> R^n and Y : [0,T] x Omega -> R^m adapted with cadlag paths (every path, the
  usual convention; "a.s. cadlag" would be broader);
- Z : [0,T] x Omega -> R^{m x d} predictable;
- U : [0,T] x Omega x E -> R^m measurable for (predictable sigma-field) (x) E (a "predictable
  version");
- E int_0^T ( |X_t|^2 + |Y_t|^2 + |Z_t|_F^2 + int_E |U_t(e)|^2 nu(de) ) dt < infinity.
Nothing more (in particular no finiteness of nu, no continuity, no bound on sup_t |X_t|).

Object. Theta^-_t(omega) = (X_{t-}(omega), Y_{t-}(omega), Z_t(omega), [U_t(omega, .)]) in H, where
X_{t-} is the left limit (with some convention at t = 0, irrelevant on a null set) and
[U_t(omega,.)] is the class in L^2(nu; R^m) of e -> U_t(omega, e), defined where it is
square-integrable; elsewhere (a dt x dP-null set by the hypothesis) any junk value (e.g. 0) is
harmless. The paper says "the induced map admits a predictable, strongly measurable
L^2(nu)-valued representative", so the U-coordinate may be such a representative.

Conclusion (what must be stated):
(a) the H-valued field (t, omega) -> Theta^-_t(omega) is jointly strongly measurable on
    [0,T] x Omega (for B([0,T]) (x) F; the paper in fact says predictable, hence jointly
    measurable; a.e.-strong measurability for dt x dP alone would be a weaker conclusion);
(b) E int_0^T ||Theta^-_t||_H^2 dt < infinity, i.e. Theta^- in L^2([0,T] x Omega, Leb x P; H)
    (MemLp 2 for the restricted Lebesgue measure on [0,T] times P).
The proposition is universally quantified over all the data above, with the hypotheses as
premises. A witness should exhibit an instance (e.g. the zero processes, or any bounded
processes on some filtered probability space with some sigma-finite nu) meeting all hypotheses.
Comparison (verdict recorded 2026-10-20T06:14:49Z):
Comparison of `Dissertation.PaperSpec.A.lemA1_L2` (Dissertation/PaperSpec/A/AppASteps.lean) with my
locked reading of manuscript/paper/sections/09-appendix.tex, proof of Lemma A.1, Step 1.

Definitions read: `CadlagPredTuple`, `leftLimProc` (Dissertation/WellPosedness/System/LawFlow.lean);
`TupleH`, `uLift`, `tupleAt` (Dissertation/WellPosedness/System/Tuple.lean); `TupleL2`, `toL2`
(Dissertation/WellPosedness/System/HilbertW2.lean); `Predictable`, `predictableSigma`,
`MarkedPredictable`, `markedPredictableSigma`, `energy`, `markedEnergy` (LevyStochCalc).

Setting.
- Probability space and filtration: any `Ω`, `mΩ`, `ℱ : Filtration ℝ mΩ`, probability measure `P`.
  The paper's standing basis (usual conditions, Brownian motion, Poisson measure) is one instance;
  Step 1 uses none of that structure. Broader, harmless.
- Marks: `ν` sigma-finite on a countably generated `E`: exactly the standing hypothesis.
- Dimensions `n m d : ℕ` (0 allowed) and `T : ℝ` (any real): broader than n, m, d >= 1, T > 0;
  harmless (T <= 0 makes [0, T] null or a point).
- H: `toL2 (tupleAt …)` lands in `TupleL2 (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m))
  (EuclideanSpace ℝ (Fin m × Fin d)) (Lp (EuclideanSpace ℝ (Fin m)) 2 ν)`, the nested `WithLp 2`
  product, whose norm squared is |x|^2 + |y|^2 + |z|^2 + ||u||^2 (`norm_toL2_sq`); the `m × d`
  channel is Euclidean on `Fin m × Fin d`, i.e. Frobenius. This is the paper's Hilbert norm, as
  the clause requires.

Hypotheses (`CadlagPredTuple ℱ P ν T X Y Z U`).
- X, Y coordinatewise (`Fin n → ℝ → Ω → ℝ`), adapted, every path right-continuous with left
  limits at every t ∈ ℝ: the paper's "càdlàg adapted", with processes indexed by ℝ.
- Z: each coordinate `Predictable ℱ` (strongly measurable for the σ-algebra on ℝ × Ω generated by
  (−∞, 0] × A, A ∈ ℱ 0, and (r, ∞) × A, A ∈ ℱ r). On [0, ∞) × Ω this is the usual predictable
  σ-field (cells {0} × A and (s, t] × A). Matches.
- U: each coordinate `MarkedPredictable ℱ ν` (measurable for the σ-algebra generated by
  F × (r, q] × B, r >= 0, F ∈ ℱ r, ν B < ∞). With ν sigma-finite this is P ⊗ E on Ω × (0, ∞) × E;
  it carries no information at times t <= 0, so a marked-predictable U is constant there.
  A paper U (P ⊗ E-measurable on [0, T]) therefore has to be modified at the single time t = 0
  (and extended past T) to meet it; this is a Lebesgue-null set of times, invisible to every
  conclusion (MemLp over Leb|[0,T] ⊗ P; and measurability at the slice {0} × Ω is trivial).
- Energies: each coordinate of X, Y, Z has finite `energy P T` (= E ∫_[0,T] |·|^2), and each
  coordinate of U finite `markedEnergy` (= E ∫_[0,T] ∫_E |·|^2 dν). The sum is finite iff each
  term is. Matches the integrability hypothesis.
- Nothing else is assumed. No hypothesis is added beyond the paper's (modulo the ℝ-indexing).

Instantiation for the printed claim: given the paper's X, Y, Z, U on [0, T] over (F_t), extend
the filtration by F_0 on (−∞, 0) and F_T on (T, ∞); extend X, Y by X_0 before 0 and X_T after T
(still càdlàg and adapted; the left limit at 0 is then X_0, the usual convention X_{0−} = X_0);
extend Z, U by 0 outside (0, T] (Z may keep its F_0-measurable value at 0; U is set to 0 at 0).
Predictability and the energies are preserved, and Θ⁻ changes only on {0} × Ω.

Object. `toL2 (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U t ω)` =
(X_{t−}(ω), Y_{t−}(ω), Z_t(ω), class of e ↦ U_t(ω, e) in L^2(ν; ℝ^m)), `leftLimProc` being the
genuine left limit (`Function.leftLim` on ℝ, where 𝓝[<] t ≠ ⊥), and `uLift` taking the junk
value 0 where the mark section is not square integrable (a dt ⊗ dP-null set under the
hypotheses). Matches Θ⁻ = (X_−, Y_−, Z, U) with U read as an L^2(ν)-valued field.

Conclusion.
(a) `StronglyMeasurable` of (t, ω) ↦ Θ⁻_t(ω) on ℝ × Ω for Borel(ℝ) ⊗ mΩ: everywhere joint strong
    measurability, on all of ℝ × Ω, which contains the clause's "jointly strongly measurable on
    [0, T] × Ω" (restriction). It is the paper's "predictable, hence jointly measurable" without
    the predictability, as the clause (and the claim's scope note) states.
(b) `MemLp … 2 ((volume.restrict (Icc 0 T)).prod P)`: Θ⁻ ∈ L^2([0, T] × Ω; H), i.e.
    E ∫_0^T ||Θ⁻_t||_H^2 dt < ∞ (with a.e.-strong measurability). Matches.

Quantifiers: everything universally quantified, hypotheses as premise; no constants. Matches.

Witness `Dissertation.Acceptance.A.lemA1_hypotheses` (Dissertation/Acceptance/A/AppASteps.lean):
on the fair coin with the full filtration, n = m = d = 1, ν = δ₀ on ℝ, T = 1, X = Y a random sign
switched on at t = 1/2 (a genuine jump, left limit ≠ value, X_1 not a.s. constant), Z = U =
1_{(0, 1]}. All fields of `CadlagPredTuple` hold. This is an instance the paper intends (finite ν
is admitted as a special case). The hypotheses are satisfiable; the proposition is not vacuous.

Coverage (claim A:lemA1:pettis in acceptance/claims.json, three clauses: lemA1_L2,
lemA1_fubini, lemA1_pettis; scope_reviewed false). The scope note delimits the passage as the
sentence of lines 43–51 together with its input from lines 36–42 (Θ⁻ ∈ L^2([0, T] × Ω; H)).
The assertions of that passage are: Θ⁻ jointly measurable and in L^2 (this clause); the
Fubini isometry of HNVW Prop. 1.2.24 (lemA1_fubini); it supplies a strongly measurable
L^2(Ω; H)-valued representative of t ↦ Θ⁻_t, which by Pettis is separably valued off a null set
and has a Borel version agreeing a.e. (lemA1_pettis, which states the final version with all
these properties). So the clauses together state every assertion of the delimited passage, and
none states something the passage does not claim. Not stated, by the scope note's choice: the
predictability of Θ⁻ (lines 36–38; not used by lines 43–51), and the earlier assertions of Step 1
(lines 25–36: X_−, Y_− predictable and equal to X, Y dt ⊗ dP-a.e.; H separable; the U-coordinate
in L^2([0, T] × Ω × E) ≅ L^2([0, T] × Ω; L^2(ν)) with a predictable strongly measurable
representative). No other proof-step claim of the inventory covers lines 25–42, so those
intermediate assertions are stated nowhere as such (the a.e. equality Θ⁻ = Θ resurfaces in the
clauses of Lemma A.1 itself, A:lem:lawflow). The hypotheses of this clause (and of lemA1_pettis)
are exactly those in force in Step 1, Lemma A.1's: X, Y càdlàg adapted, Z, U predictable, the
integrability bound, on the standing setting (broadened to any filtered probability space and
represented on ℝ as above); no more, no fewer.
Witness: —
Verdict: broader — Broader than the printed clause, harmlessly: any filtered probability space (no usual conditions,
no Brownian/Poisson structure), any T ∈ ℝ and any n, m, d ∈ ℕ. Instantiation giving the printed
claim: the paper's standing basis, T > 0, n, m, d >= 1, with the paper's [0, T]-indexed data
extended to ℝ (filtration F_0 before 0 and F_T after T; X, Y frozen at X_0, Y_0 before 0 and at
X_T, Y_T after T; Z, U set to 0 outside (0, T], which for U also replaces its value at t = 0, as
`MarkedPredictable` forces a constant at times <= 0). These changes touch Θ⁻ only on {0} × Ω, a
Leb ⊗ P-null slice, so both conclusions transfer to the paper's Θ⁻. Representation choices, all
harmless: coordinatewise real processes and coordinatewise energies (finite sum finite iff each
term finite); the L^2(ν) channel as `uLift` with junk value 0 off square integrability (a null
set); H's Hilbert norm via `toL2` into the nested `WithLp 2` product (Frobenius = Euclidean on
Fin m × Fin d); joint strong measurability asserted on all of ℝ × Ω, which restricts to
[0, T] × Ω.
Disagreements with the author's review (shown 2026-10-20T06:16:13Z): No disagreement on the substance: the proposition says what the passage says, with the paper's
Hilbert norm, Lemma A.1's hypotheses, joint strong measurability and MemLp 2 over Leb|[0,T] ⊗ P.
Points where I differ from or add to the author's review:
1. Verdict label. I record `broader`, not `faithful`: the proposition quantifies over every
   filtered probability space (no usual conditions, no Brownian/Poisson structure), every T ∈ ℝ
   and every n, m, d ∈ ℕ, and its processes are indexed by ℝ. The printed claim is obtained by
   instantiating at the standing basis with the paper's [0, T]-indexed data extended to ℝ
   (filtration F_0 before 0 and F_T after T, X and Y frozen outside [0, T], Z and U set to 0
   outside (0, T]). The author's review calls the hypotheses "verbatim from lem_lawflow" and does
   not spell out this instantiation.
2. Unrecorded representation choice. `MarkedPredictable` is generated by rectangles
   F × (r, q] × B with r >= 0, so a marked-predictable U is constant at all times t <= 0. A paper U
   whose value at t = 0 depends on ω meets the hypothesis only after modification at the single
   time 0. That time is Lebesgue-null, and both conclusions transfer, but the review should record
   it, as it should record that X and Y must be càdlàg and adapted on the whole real line.
3. Minor wording. The joint σ-algebra is Borel(ℝ) ⊗ mΩ, the ambient σ-algebra of Ω. It is not
   "the product of the Borel σ-algebra and ℱ", since ℱ is a filtration.
