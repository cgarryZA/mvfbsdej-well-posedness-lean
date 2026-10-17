### A:ex:concrete: Dissertation.PaperSpec.A.ex_concrete_i_sharp
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash ed839d34f480cba19df1faec1593a821 (pl-fp-v1:53d4773c7a96ad003d755703e3596aa8e67e114500661c002c108bd49106a962)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T12:17:25Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:17:11Z):
# Reading: ex_concrete_i_sharp

Paper: "The identity is sharp for the constants beta1, beta2" (Ex 5.1(i)), i.e. the interior
inequality (2.7) for the affine system cannot hold with larger constants.
Faithful formal statement:
- Setting/data as in ex_concrete_i (standing basis, n = m = d = 1, G = 1, any sigma-finite nu,
  T > 0, beta1, beta2 > 0, sigma_c, h_c).
- For all real beta1', beta2': if (2.7) holds for the affine system with G = 1 and constants
  (beta1', beta2') -- in the paper's form: for a.e. t in [0,T] and all diagonal inputs, the
  expectation form -- then beta1' <= beta1 and beta2' <= beta2.
- The hypothesis must be the actual (2.7) (diagonal, a.e. t), not a pointwise or every-t
  version (a stronger hypothesis would make the claim weaker); T > 0 matters since for T = 0 the
  a.e.-t condition is empty.
- Whether the admissibility of constants is required of (beta1', beta2') does not matter much;
  requiring only the inequality is the strongest form.
Comparison (verdict recorded 2026-10-17T12:17:20Z):
# Comparison: ex_concrete_i_sharp

Lean (Sec5Sharp.lean:30): setting of ex_concrete_i (any sigma-finite nu, d = 1, G0 independent,
T > 0, beta1, beta2 > 0, sigma_c, h_c); for all real beta1', beta2': if for a.e. t in [0,T]
Mono27At (the interior (2.7) along diagonal inputs, with integrability) holds for affineCoeffs
with G = 1 and (beta1', beta2'), then beta1' <= beta1 and beta2' <= beta2.

Against my reading: identical -- the hypothesis is the paper's (2.7) form (a.e. t, diagonal,
expectation), with no admissibility requirement on the primed constants (strongest form),
T > 0 present. The hypothesis is satisfiable (by beta1' = beta1, beta2' = beta2, by
ex_concrete_i), so the implication is not vacuous; witness ex_concrete_hypotheses for the basis.

Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-17T12:17:20Z): none
