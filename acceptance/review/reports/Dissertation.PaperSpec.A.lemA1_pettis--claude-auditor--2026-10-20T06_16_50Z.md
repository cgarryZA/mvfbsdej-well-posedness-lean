### A:lemA1:pettis: Dissertation.PaperSpec.A.lemA1_pettis
Pins: manuscript A None; project 6d403c197bfb10fe8808933c6e525ee0ae544fb1; hash ed839d34f480cba176ccc2a6aaf99d7c (pl-fp-v1:9aaf53a77ade3938e572bca7bb0c4b878d9bcedf03920b1fe533274be51bc6f0)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-20T06:16:50Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-20T06:10:05Z):
Reading of the clause (manuscript/paper/sections/09-appendix.tex, proof of Lemma A.1, end of Step 1:
"supplies a strongly measurable L^2(Omega;H)-valued representative of t -> Theta_t^-; by the Pettis
measurability theorem [HNVW, Thm 1.1.6], that map takes values in a separable closed subspace of
L^2(Omega;H) off a Lebesgue-null set of times, and therefore admits a Borel version, agreeing with
it for a.e. t").

Setting and hypotheses: exactly those of Lemma A.1 (as for the L^2 clause): a filtered probability
space (Omega, F, (F_t), P), T > 0, n, m, d >= 1, a sigma-finite nu on a countably generated
(E, E), H = R^n x R^m x R^{m x d} x L^2(nu; R^m) (Hilbert norm or an equivalent one); X, Y
adapted with cadlag paths; Z predictable; U predictable (P (x) E-measurable); the integrability
E int_0^T (|X|^2 + |Y|^2 + |Z|_F^2 + int_E |U|^2 dnu) dt < infinity. No further hypothesis.

Object: Theta^-_t = (X_{t-}, Y_{t-}, Z_t, [U_t]) as in the L^2 clause; for a.e. t the random
variable omega -> Theta^-_t(omega) is in L^2(Omega, F, P; H), so t -> [Theta^-_t] is an a.e.-defined
map [0,T] -> L^2(Omega; H).

Conclusion: there is F : [0,T] -> L^2(Omega; H) such that
(i) F is strongly measurable;
(ii) F takes values in a closed separable subspace V of L^2(Omega; H) (everywhere, as F is the
     modified version; "off a null set" for the HNVW representative);
(iii) F is Borel measurable (for the Borel sigma-algebra of the norm topology of L^2(Omega; H));
(iv) for a.e. t in [0,T], omega -> Theta^-_t(omega) is in L^2(Omega; H) and F(t) equals its class.
The a.e. is for Lebesgue measure on [0,T]. F defined on all of R (with the properties on [0,T]) is
an equivalent representation. Note L^2(Omega, F, P; H) need not be separable (F need not be
countably generated), so (ii) and (iii) are genuine content and not automatic.
A witness should exhibit the hypotheses of Lemma A.1 at some instance (e.g. zero processes).
Comparison (verdict recorded 2026-10-20T06:16:10Z):
Comparison of `Dissertation.PaperSpec.A.lemA1_pettis` (Dissertation/PaperSpec/A/AppASteps.lean) with my
locked reading of manuscript/paper/sections/09-appendix.tex, end of Step 1 of the proof of
Lemma A.1.

Setting and hypotheses: identical to `lemA1_L2` — any filtered probability space
`(Ω, mΩ, ℱ : Filtration ℝ mΩ, P)`, ν sigma-finite on a countably generated E, any n, m, d ∈ ℕ and
T ∈ ℝ, and `CadlagPredTuple ℱ P ν T X Y Z U` (X, Y adapted with càdlàg paths on ℝ, Z predictable,
U marked-predictable, finite coordinate energies on [0, T]). These are Lemma A.1's hypotheses,
those in force in Step 1; the same remarks apply (ℝ-indexed representation, U forced constant at
times <= 0 so that a paper U is modified at t = 0, a Lebesgue-null time; broadened setting).

Object: `toL2 (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U t ω)` = Θ⁻_t(ω) in H with its Hilbert
norm (`TupleL2 …`), as in `lemA1_L2`.

Conclusion: `∃ F : ℝ → Lp H 2 P` with
(i) `StronglyMeasurable F` (for Borel ℝ): F strongly measurable. Matches (i), on all of ℝ (a
    function on [0, T] extends by 0, so this is no stronger in substance).
(ii) `∃ V : Submodule ℝ (Lp H 2 P), IsClosed V ∧ IsSeparable V ∧ ∀ t, F t ∈ V`: F takes values,
    everywhere, in a closed separable linear subspace of L^2(Ω; H). Matches (ii).
(iii) `@Measurable ℝ (Lp H 2 P) _ (borel _) F`: Borel measurable for the norm topology's Borel
    σ-algebra of L^2(Ω; H). Matches (iii). (L^2(Ω, mΩ, P; H) is not assumed separable — mΩ is
    arbitrary — so (ii) and (iii) are not automatic from the setting; they follow from (i), which
    is exactly the Pettis step the paper cites.)
(iv) `∀ᵐ t ∂(Leb|[0,T]), ∃ h : MemLp (fun ω => Θ⁻_t(ω)) 2 P, F t = h.toLp _`: for a.e. t ∈ [0, T],
    Θ⁻_t ∈ L^2(Ω; H) and F(t) is its class. Matches (iv).
The L^2(Ω; H) is `Lp … 2 P` over the full σ-algebra mΩ of Ω, as in the paper.

Is anything stronger than the paper? The paper's Borel version is obtained by changing the
strongly measurable representative on a null set of times; the clause asks it to be strongly
measurable, separably valued everywhere and Borel. A Borel version obtained that way (redefined,
e.g., as 0 on the exceptional null Borel set) has all three properties, so the conjunction is what
the paper's chain of sentences delivers, not more. Not weaker either: every property the paper
names for the final object is stated.

Witness `Dissertation.Acceptance.A.lemA1_hypotheses` (the coin-flip tuple with a genuine jump,
ν = δ₀, T = 1): the hypotheses `CadlagPredTuple` are met at an intended instance; not vacuous.

Coverage (claim A:lemA1:pettis in acceptance/claims.json; clauses lemA1_L2, lemA1_fubini, this
one; scope_reviewed false). The delimited passage (scope note: lines 43–51 with the input of
lines 36–42) asserts: Θ⁻ ∈ L^2([0, T] × Ω; H) (lemA1_L2); the Fubini isometry (lemA1_fubini); a
strongly measurable L^2(Ω; H)-valued representative of t ↦ Θ⁻_t, separably valued off a null set
by Pettis, hence a Borel version agreeing a.e. (this clause, which states the final version with
every named property; the intermediate representative is subsumed). So the clauses together state
every assertion of the delimited passage, and none states something it does not claim. Left out by
the scope note: the predictability of Θ⁻ (lines 36–38, unused in lines 43–51) and the earlier
assertions of Step 1 (lines 25–36), which no other proof-step claim of the inventory states. The
hypotheses of this clause are exactly those in force at that point of the printed proof
(Lemma A.1's), no more, no fewer.
Witness: —
Verdict: broader — Broader than the printed clause, harmlessly: any filtered probability space, any T ∈ ℝ, any
n, m, d ∈ ℕ, and F defined on all of ℝ. Instantiation giving the printed claim: the standing basis,
T > 0, n, m, d >= 1, the paper's [0, T]-indexed X, Y, Z, U extended to ℝ as for `lemA1_L2`
(filtration F_0 before 0 and F_T after T; X, Y frozen outside [0, T]; Z, U set to 0 outside
(0, T], which also resets U at t = 0, since `MarkedPredictable` forces a constant at times <= 0);
this changes Θ⁻_t only at t = 0, so the a.e.-in-t conclusion (iv) holds for the paper's Θ⁻, and
F restricted to [0, T] is the printed Borel version. Representation choices: H with its Hilbert
norm as `TupleL2 …`; the L^2(ν) channel as `uLift` with junk value 0 off square integrability (a
dt ⊗ dP-null set); coordinatewise processes and energies.
Disagreements with the author's review (shown 2026-10-20T06:16:14Z): No disagreement on the substance. I agree with the reading of the four properties of F. I also agree
that requiring F(t) ∈ V at every t is stronger in form than "off a null set" but is what the
Borel version delivers, so it is no overclaim. Points where I differ from or add to the author's
review:
1. Verdict label. I record `broader`, not `faithful`. As with `lemA1_L2`, the proposition is
   stated over every filtered probability space, every T ∈ ℝ and every n, m, d ∈ ℕ, with
   ℝ-indexed processes and F defined on all of ℝ. The printed claim is its instance at the
   standing basis with the paper's data extended to ℝ. The review does not spell out that
   instantiation.
2. Unrecorded representation choice, shared with `lemA1_L2`. `MarkedPredictable` forces U to be a
   constant at times <= 0, so a paper U with an ω-dependent value at t = 0 must be modified at
   that Lebesgue-null time before the hypothesis applies. Conclusion (iv) is a.e. in t and is
   unaffected, but the review should record this.
