### A:abstract, A:conclusion, A:cor:robust, A:eq:forced, A:eq:mvfbsdej, A:ex:brownian, A:ex:concrete, A:ex:dealer, A:ex:fulllaw, A:intro:limin-comparison, A:intro:mvfbsdej, A:lem:bpbsde, A:lem:cont, A:lem:pert, A:lem:small, A:rem:cwp-class, A:rem:generalrank, A:rem:regimes, A:rem:uniq-no-integ, A:sec3:HH-banach, A:sec4:WP-def, A:sec4:horizon-not-contractive, A:sec5:overview, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: Dissertation.WellPosedness.Stability.esq
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 6cf496fa6f75fac11490c95295dbf617 (pl-fp-v1:4580dca10d2516153ccfbc75bbe7c41b18eee2b8f71e8bd03805b78dcb3f52bd)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:50:55Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T15:41:47Z):
Reading for def:Dissertation.WellPosedness.Stability.esq.

Paper notion (inferred from the name, in the Stability module): the expected square E|V|^2 of a
random variable V (possibly Banach/Hilbert-valued, e.g. R^n, R^m, H, L^2(nu)); the paper's
stability estimate (3.1) and (4.13) are built from terms E|delta xi_0|^2, E|delta g_T|^2,
E sup_t |delta X_t|^2, E int_0^T |.|^2 dt.

Faithful Lean: esq V = E |V|^2 with the paper's norm on the codomain. Edge cases: if esq is a
real-valued Bochner integral, it has junk value 0 on non-square-integrable V; then a stability
inequality LHS <= C * RHS with esq terms would (a) be trivial when the LHS is non-integrable and
(b) be STRONGER than the paper when an RHS term is non-integrable (paper: RHS = infinity, so the
estimate is trivially true). That is harmless only if the propositions that use esq impose square
integrability of every random variable fed to it (which the paper's setting provides: solutions in
S, differences square integrable). An ENNReal lintegral of ||V||_e^2 is the faithful version with
no junk. The norm must be the paper's (Euclidean / Frobenius / L^2(nu) / Hilbert l^2 on H).
If esq instead denotes E sup |.|^2 or E int |.|^2, it must match that paper quantity exactly.
Comparison (verdict recorded 2026-10-17T15:50:03Z):
Comparison for def:Dissertation.WellPosedness.Stability.esq (Stability/PairDiff.lean:57-59):
esq x = sum_i (||x i||_+)^2 in ENNReal, for x : iota -> R with iota finite.

My locked reading guessed (from the name) that esq might be the expectation E|V|^2; it is instead the
squared Euclidean norm of a coordinate vector, |x|^2 = sum_i x_i^2, in ENNReal. Against the paper's
notion it stands for (|v|^2, the squared Euclidean norm, used e.g. as esq (fun i => X i t omega)
inside lintegrals/suprema to form E sup_t |X_t|^2 in Sec3Rem34): ||x i||_+ = |x_i|, so the value is
exactly sum x_i^2, with no junk (ENNReal, finite sum). The ENNReal valuation is the safe form my
reading asked for (expectations built from it are lintegrals). Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-17T15:50:11Z): none (the author's entry shown is empty; I find esq = sum_i x_i^2 in ENNReal, the squared Euclidean
norm, faithful).
