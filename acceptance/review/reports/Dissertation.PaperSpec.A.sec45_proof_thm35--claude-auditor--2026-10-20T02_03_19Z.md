### A:sec4:proof-thm35: Dissertation.PaperSpec.A.sec45_proof_thm35
Pins: manuscript A None; project 6d403c197bfb10fe8808933c6e525ee0ae544fb1; hash ed839d34f480cba1227f3637481e69e0 (pl-fp-v1:0f524c3ec667869e4fc06cff00b10e7a751bceab3af5020e58a2ec0f0c64e9a3)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-20T02:03:19Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-20T01:52:26Z):
Reading of the passage (manuscript/paper/sections/04-proof-wellposedness.tex, lines 939-952, §4.5 proof
of Theorem 3.5).

Setting and hypotheses in force: Theorem 3.5's hypotheses — the standing setting of §2, horizon T > 0,
Assumptions 2.2-2.5 (integrability at origin, Lipschitz, coupling matrix, monotonicity). WP(lambda)
(lines 66-68): the forced system (4.1) at lambda has a unique solution in S for every square-integrable
forcing q (with the measurability of lines 41-53). At this point of the proof the following are in force:
Lemma 4.2's conclusion: lambda_* in (0,1] and WP(lambda) for every lambda in [0, lambda_*]; Lemma 4.4's
conclusion: zeta_0 > 0 such that for lambda_0 in [lambda_*, 1] with WP(lambda_0), WP(lambda_0 + zeta)
holds for every zeta in [0, zeta_0] with lambda_0 + zeta <= 1. (The dependence of lambda_*, zeta_0 on
the parameters is not used in §4.5.)

Definitions: lambda_k := min{lambda_* + k zeta_0, 1}, k >= 0 (k natural).

Conclusions of the passage:
 (a) lambda_0 = lambda_*;
 (b) lambda_{k+1} - lambda_k <= zeta_0 for all k (also implicitly >= 0 and lambda_k in [lambda_*, 1],
     needed to apply Lemma 4.4);
 (c) lambda_k = 1 for every k >= ceil((1 - lambda_*)/zeta_0) (ceiling of a nonnegative real, natural
     number);
 (d) WP(lambda) for lambda in [0, lambda_*] (restated from Lemma 4.2);
 (e) WP(lambda_k) for every k (induction: Lemma 4.4 carries WP(lambda_k) to WP(lambda_{k+1}));
 (f) WP(1);
 (g) (last sentence) taking q = 0 gives a unique solution of (1.1) in S. The unit's clause list names
     (a)-(f); (g) may be another clause of the claim.

A faithful statement may be either
 - concrete: under the setting and Assumptions 2.2-2.5, with WP the paper's well-posedness predicate
   of the forced system, given lambda_* in (0,1] with WP on [0,lambda_*] and zeta_0 > 0 with the
   continuation step (as hypotheses: they are the lemmas' conclusions in force at this point), the
   conclusions (a)-(f); or
 - abstract: for an arbitrary predicate WP on reals (or on [0,1]) and arbitrary lambda_* in (0,1],
   zeta_0 > 0 satisfying the two hypotheses, (a)-(f). That is broader; the instantiation is WP := the
   paper's WP(lambda), lambda_*, zeta_0 from Lemmas 4.2 and 4.4.
Quantifiers: lambda_* and zeta_0 are fixed before k; the threshold ceil((1-lambda_*)/zeta_0) is a
function of them. The hypothesis on zeta_0 must be the printed continuation step: for all lambda_0 in
[lambda_*, 1], WP(lambda_0) implies for all zeta in [0, zeta_0] with lambda_0 + zeta <= 1,
WP(lambda_0 + zeta). A stronger hypothesis (e.g. continuation from any lambda_0 in [0,1], or without
the constraint lambda_0 >= lambda_*) would make the statement narrower; that is a difference to flag.
lambda_* <= 1 must be part of the hypotheses (lambda_* in (0,1]); lambda_* > 0 is not needed for the
argument but is part of Lemma 4.2. If lambda_* were allowed > 1, lambda_0 = lambda_* would fail
(min{lambda_*,1} = 1).

Vacuity: hypotheses must be satisfiable (e.g. WP := True with lambda_* = 1/2, zeta_0 = 1; or the paper's
setting where Lemmas 4.2/4.4 hold). If concrete, WP must mean the paper's notion (unique solution in S
for every admissible forcing), with S the paper's space, and the witness should instantiate it.

Is this claimed at this revision? Yes (lines 942-951).
Comparison (verdict recorded 2026-10-20T02:02:37Z):
Comparison for Dissertation.PaperSpec.A.sec45_proof_thm35 (Dissertation/PaperSpec/A/Sec4Continuation.lean)
against my locked reading.

Shape. `∃ lamStar : ℝ → ℝ → ℝ, ∃ zeta0 : ℝ⁸ → ℝ, ∀ setting, ∀ T > 0, ∀ L α β₁ β₂ G C ξ₀,
JointBorel → Assumption22 → Assumption23 → full rank → Assumption25 → [conclusions]`. My reading allowed
a concrete form taking the constants of Lemmas 4.2/4.4 with their properties as hypotheses, or an
abstract form over any predicate WP. The proposition takes a third, equivalent-in-content route: the
constants are bound existentially, as functions of exactly the parameters the lemmas allow
(lambda_* = lamStar(T, L); zeta_0 = zeta0(T, L, ||G||, c_G, alpha, beta_1, beta_2, lambda_*), with
c_G = (s_min(G)^2)^{-1}, Dissertation/WellPosedness/System/FullRank.lean, and c_BDG a universal constant),
chosen before the setting, and their lemma properties are conjuncts of the conclusion:
 - `0 < lamStar T L ∧ lamStar T L ≤ 1` and `∀ lam ∈ [0, λ*], WP(lam)` (Lemma 4.2's conclusion, restated
   in §4.5: "By Lemma 4.2, WP(lambda) holds for lambda in [0, lambda_*]");
 - `0 < ζ₀` and the continuation step `∀ lam0 ∈ [λ*, 1], WP(lam0) → ∀ ζ ∈ [0, ζ₀], lam0 + ζ ≤ 1 →
   WP(lam0 + ζ)` (Lemma 4.4's conclusion, used in §4.5: "With zeta_0 from Lemma 4.4", "Lemma 4.4
   carries WP(lambda_k) to WP(lambda_{k+1})"), exactly the printed step, not a stronger one;
 - `min (λ* + 0·ζ₀) 1 = λ*` (lambda_0 = lambda_*);
 - `∀ k, min (λ* + (k+1)ζ₀) 1 − min (λ* + kζ₀) 1 ≤ ζ₀`;
 - `∀ k, ⌈(1 − λ*)/ζ₀⌉₊ ≤ k → min (λ* + kζ₀) 1 = 1` (Nat.ceil of a nonnegative real);
 - `∀ k, WP(min (λ* + kζ₀) 1)`; and `WP(1)`.
So every conclusion of my reading, (a)-(f), is present, with lambda_k = min{lambda_* + k zeta_0, 1} written
out. Consequence of the existential packaging: the proposition contains the content of Lemmas 4.2 and
4.4 (it is not provable from the combinatorics alone), and it asserts the sequence facts and WP(lambda_k)
for the chosen constants rather than for every pair of constants with the lemma properties. The
universal form ("for any lambda_*, zeta_0 with these properties ...") is a trivial induction and is
implied for the chosen pair; the substantive content of the step - that with the lemmas' constants WP(1)
follows - is what is stated. The paper claims every conjunct at this revision (the lemma properties are
the statements of Lemmas 4.2 and 4.4, invoked in §4.5). I regard this as a representation choice, not a
narrowing or a mismatch.

Hypotheses. Exactly those of Theorem 3.5 (the claim of which §4.5 is the proof): the standing setting
(G_0 independent of the driver, E countably generated, nu sigma-finite, n, m, d >= 1, filtration enlJoint),
T > 0, the Borel measurability (2.3), Assumption 2.2 (`Assumption22`: xi_0 strongly F_0-measurable and in
L^2, origin values in L^2(0,T)), Assumption 2.3, full rank of G (Assumption 2.4) and Assumption 2.5. These
are the hypotheses in force in §4.5, no more and no fewer (Lemma 4.2 uses 2.2-2.3, Lemma 4.4 uses
2.2-2.5).

WP. `Dissertation.PaperSpec.A.WP` (Dissertation/PaperSpec/A/Setting.lean): for every PredForcing q
(q^b, q^sigma, q^f progressive, q^h marked predictable, square integrable, q^g in L^2(F_T)), a
`ForcedSolution` of (4.1) at lambda exists (a WeakForcedSolution with E sup|X|^2, E sup|Y|^2 finite, i.e.
in S), and any two are equal in S (X, Y indistinguishable on [0,T], zero energy of the Z- and U-
differences). This is the paper's WP(lambda) ("a unique solution in S for every such forcing q"), the
uniqueness being equality of equivalence classes of §3. Not trivially true.

Constants. lambda_* depends only on (T, L) and zeta_0 only on (T, L, ||G||, c_G, alpha, beta_1, beta_2,
lambda_*), both chosen before every other datum, as Lemmas 4.2 and 4.4 say (the universal c_BDG needs no
argument). lambda_* <= 1 is part of the conclusion, so lambda_0 = lambda_* is meaningful. The junk
(0)^{-1} = 0 in c_G cannot arise since full rank gives s_min(G) > 0.

Witness. Dissertation.Acceptance.A.thm_cwp_hypotheses (Dissertation/Acceptance/A/Witness.lean): Example
5.1(i) at nu = delta_0, n = m = d = 1, T = 1, xi_0 = 0, L = 1, G = 1, alpha = beta_1 = beta_2 = 1 satisfies
(2.3) and Assumptions 2.2-2.5. An instance the paper intends; the hypotheses can be met, so the
conclusions (WP(1) in particular) are not vacuous.

Is it claimed at this revision? Yes, sections/04-proof-wellposedness.tex lines 941-951.

Coverage of claim A:sec4:proof-thm35 (acceptance/claims.json): clauses sec45_proof_thm35 (this unit) and
thm_cwp ("with q = 0, (1.1) has a unique solution in S (Theorem 3.5)"; Dissertation/PaperSpec/A/Sec3.lean,
existence of a Solution and uniqueness in S under the same hypotheses). The passage asserts: WP on
[0, lambda_*] by Lemma 4.2; the definition of lambda_k and its three properties; the step
WP(lambda_k) => WP(lambda_{k+1}) by Lemma 4.4; WP(1); and, taking q = 0, a unique solution of (1.1) in S.
The two clauses state all of these (the last through thm_cwp, which states the conclusion of the q = 0
step, i.e. Theorem 3.5's existence and uniqueness, rather than the implication from WP(1) to it; the
conclusion is what the passage asserts). Neither clause states something the passage does not claim:
the lemma properties inside sec45_proof_thm35 are the printed Lemmas 4.2 and 4.4, which the passage
invokes. The hypotheses of both clauses are Theorem 3.5's, those in force in §4.5 (no more, no fewer).
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless: (1) the constants lambda_* "from Lemma 4.2" and zeta_0 "from Lemma
4.4" are bound existentially as functions lamStar(T, L) and zeta0(T, L, ||G||, c_G, alpha, beta_1, beta_2,
lambda_*) quantified before the setting, with the lemma properties (lambda_* in (0,1], WP on [0, lambda_*],
zeta_0 > 0 and the printed continuation step) as conjuncts of the conclusion instead of hypotheses; the
proposition thus also contains Lemmas 4.2 and 4.4 (claimed by the paper and invoked in §4.5) and states
the sequence facts and WP(lambda_k), WP(1) for the chosen constants (the version "for every admissible
pair" is a trivial induction and adds no mathematical content); (2) lambda_k = min{lambda_* + k zeta_0, 1}
written out inline, k : N, the threshold as Nat.ceil of (1 - lambda_*)/zeta_0; (3) c_G as
(sMin G ^ 2)^{-1}, positive under full rank; (4) WP is Dissertation.PaperSpec.A.WP, unique solvability
in S of (4.1) for every PredForcing, uniqueness as equality of the equivalence classes of §3.
Disagreements with the author's review (shown 2026-10-20T02:02:54Z): 1. Verdict: the author records "faithful"; I record "faithful with representation choices". The
   existential packaging - lambda_* and zeta_0 bound as functions chosen before the setting, with the
   properties of Lemmas 4.2 and 4.4 as conjuncts of the conclusion instead of hypotheses - is a choice the
   review should name: it makes the proposition contain the content of Lemmas 4.2 and 4.4 (so it is not
   provable from the induction alone), and it states the sequence facts, WP(lambda_k) and WP(1) for the
   chosen constants rather than for every pair of constants with the lemma properties (that universal form
   is a trivial induction, so nothing of mathematical substance is lost). The author's review describes the
   readings accurately but presents them as no choice at all.
2. Otherwise none: I agree with the author's account of the hypotheses (those of Theorem 3.5), the
   dependence of the constants (c_BDG universal, c_G = s_min(G)^{-2}), the natural-number ceiling, the
   continuation step in exactly the printed form, the witness, and the split of the last sentence of §4.5
   into the clause thm_cwp.
