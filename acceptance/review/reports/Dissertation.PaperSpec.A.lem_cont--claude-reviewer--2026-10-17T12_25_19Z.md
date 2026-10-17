### A:lem:cont: Dissertation.PaperSpec.A.lem_cont
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash ed839d34f480cba15f6eb38f12c8d372 (pl-fp-v1:d11b2d38f5f18a28c2f9963e544bf04c0892ed192488ded686e8fe3f4b22060b)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T12:25:19Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:24:11Z):
Reading of Lemma 4.4 (lem:cont).
Constant first: zeta_0 = zeta_0(T, L, ||G||, c_G, alpha, beta1, beta2, lambda_*) (c_BDG universal), a function
of these parameters only, chosen before everything else, and STRICTLY POSITIVE (at least whenever
the hypotheses can hold: T > 0, L >= 0, admissible alpha, beta1, beta2, lambda_* in (0,1]). A zeta_0 that
may be 0 would make the lemma trivial, so positivity must be in the statement.
lambda_*: "the small-coupling threshold of Lemma 4.2" (a number in (0,1] depending on T, L, c_BDG).
The proof uses lambda_* only as the lower bound underline-lambda of Lemma 4.3 for lambda_0 >= lambda_*,
so a statement for every lambda_* in (0,1] (with zeta_0 depending on lambda_*) is a broader, faithful
reading; the printed lemma is its instance at the threshold of Lemma 4.2.
Setting: standing setting, n, m, d >= 1, T > 0.
Hypotheses: coefficients with (2.3)-Borel measurability and initial datum xi0 satisfying
Assumptions 2.2-2.5 (L, G full rank, alpha, beta1, beta2); lambda_0 in [lambda_*, 1]; WP(lambda_0): the
lambda_0-forced system (4.1) has a unique solution in S for every square-integrable forcing q (q^b,
q^sigma, q^f progressively measurable, q^h predictable, all square integrable, q^g_T in L2(F_T)).
Conclusion: for every zeta in [0, zeta_0] with lambda_0 + zeta <= 1, WP(lambda_0 + zeta) holds.
Quantifier order: exists zeta_0 (function), forall setting, coefficients, lambda_0, (WP lambda_0) ->
forall zeta ... -> WP(lambda_0 + zeta).
Comparison (verdict recorded 2026-10-17T12:25:07Z):
Comparison: lem_cont vs Lemma 4.4.
Constant: exists zeta0 : R^8 -> R first, applied to (T, L, ||G||, c_G, alpha, beta1, beta2, lambda_*);
the conclusion includes 0 < zeta0(...) under the hypotheses. Matches ("there is zeta_0 > 0, depending
only on ..."; c_BDG universal).
lambda_*: universally quantified in (0, 1]; the printed lemma fixes lambda_* as the threshold of
Lemma 4.2 (a number in (0, 1]); the proposition is the broader statement for every lambda_* in (0,1],
the printed claim its instance. Matches my reading.
Setting/hypotheses: standing setting, n, m, d > 0, T > 0; JointBorel, Assumption22 C xi0,
Assumption23 L, full-rank G, Assumption25. Matches "Let Assumptions 2.2-2.5 hold".
Conclusion: for all lambda_0 in [lambda_*, 1] with WP(lambda_0), for all zeta in [0, zeta0] with
lambda_0 + zeta <= 1, WP(lambda_0 + zeta). Matches.
WP (Setting.lean): for every forcing in PredForcing (q^b, q^sigma, q^f jointly and progressively
measurable, finite energy; q^h marked predictable with finite marked energy; q^g F_T-measurable L2;
all normalised to vanish off [0,T]) there is a ForcedSolution of (4.1) in S, and any two
ForcedSolutions are equal in S. PaperSolutionForced writes (4.1) with integrands lambda psi + q^psi
(lambda h + q^h for the jump integral, equal to lambda int h dN~ + int q^h dN~ by linearity) and
terminal value lambda g(X_T, Law X_T) + q^g_T. Matches the definition of WP(lambda).
Witness thm_cwp_hypotheses: the coefficient hypotheses at Example 5.1(i). The inductive hypothesis
WP(lambda_0) is not exhibited by the witness; it holds at that instance by the paper's argument
(Lemma 4.2 and the lemma itself), so the hypotheses are satisfiable, but the witness covers only
the coefficient part.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — 1. lambda_* is quantified over (0, 1] instead of being the specific threshold of Lemma 4.2: broader
   (the printed lemma is the instance lambda_* = threshold), and zeta_0 depends on lambda_* as printed.
2. WP(lambda) is encoded with forcings normalised to vanish off [0,T] and the jump forcing marked
   predictable; (4.1) is written with combined integrands lambda psi + q^psi (linearity).
3. Shared solution-notion encodings (as in thm_cwp) for the forced solutions.
4. The witness exhibits the coefficient hypotheses only; WP(lambda_0) is the lemma's inductive
   hypothesis, satisfiable by the paper's results but not exhibited in Lean.
Disagreements with the author's review (shown 2026-10-17T12:25:07Z): none (minor: the premise WP(lambda_0) is met at lambda_0 = lambda_* only via lem_small, a separate proposition, not by the linked witness itself).
