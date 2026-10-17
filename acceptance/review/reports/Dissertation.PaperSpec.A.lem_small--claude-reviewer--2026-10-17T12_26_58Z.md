### A:lem:small: Dissertation.PaperSpec.A.lem_small
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash ed839d34f480cba12f6a12214671fd14 (pl-fp-v1:1bfa7ca8c569a48a41882963525fb17c2548c974895451fd53b2baebd0cdf559)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T12:26:58Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:26:41Z):
Reading of Lemma 4.2 (lem:small).
Constant first: lambda_* = lambda_*(T, L) (c_BDG universal) — a function of T and L only, chosen before
everything else (independent of n, m, d, nu, the space, the coefficients beyond their Lipschitz
constant, and of xi0), with lambda_*(T, L) in (0, 1] (at least for T > 0, L >= 0).
Setting: standing setting, n, m, d >= 1, T > 0.
Hypotheses: coefficients with (2.3)-Borel measurability and initial datum xi0 satisfying Assumptions
2.2 (xi0 in L2(F_0), origin values in L2(0,T)) and 2.3 (Lipschitz with L >= 0). No G, no monotonicity.
Conclusion: lambda_*(T, L) in (0,1], and WP(lambda) holds for every lambda in [0, lambda_*]: for every
square-integrable forcing q (q^b, q^sigma, q^f progressive; q^h predictable; q^g_T in L2(F_T)) the
lambda-forced system (4.1) has a unique solution in S.
Comparison (verdict recorded 2026-10-17T12:26:51Z):
Comparison: lem_small vs Lemma 4.2.
Constant: exists lamStar : R -> R -> R first, applied to (T, L): matches "lambda_* depending only on T,
L and c_BDG" (c_BDG universal); independent of n, m, d, nu, xi0, the space.
Setting: standing setting, n, m, d > 0, T > 0.
Hypotheses: JointBorel, Assumption22 C xi0, Assumption23 L C (Assumptions 2.2-2.3; no G or
monotonicity). Matches.
Conclusion: 0 < lamStar(T, L) <= 1 and WP(lam) for every lam in [0, lamStar(T, L)]. WP as in Setting.lean
(for every PredForcing, existence of a ForcedSolution of (4.1) in S and uniqueness among
ForcedSolutions). Matches.
Witness thm_cwp_hypotheses: Example 5.1(i) meets (2.3), 2.2, 2.3. Satisfiable.
Verdict: faithful with representation choices (WP and forced-solution encodings as in lem_cont).
Witness: —
Verdict: faithful with representation choices — 1. WP(lambda) is encoded with forcings in the normal form of PredForcing (vanishing off [0,T], q^h
   marked predictable) and forced solutions in S given by PaperSolutionForced (combined integrands
   lambda psi + q^psi; shared solution-notion encodings).
2. lambda_* is a function of (T, L) chosen first; its membership in (0,1] is part of the conclusion.
Disagreements with the author's review (shown 2026-10-17T12:26:51Z): none
