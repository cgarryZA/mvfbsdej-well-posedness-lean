### A:abstract, A:ass:mono, A:conclusion, A:cor:robust, A:ex:brownian, A:ex:concrete, A:ex:dealer, A:ex:fulllaw, A:intro:limin-comparison, A:lem:cont, A:lem:pert, A:rem:beta1-dich, A:rem:diag-mono, A:rem:freelaw, A:rem:generalrank, A:rem:intrinsic, A:rem:regimes, A:rem:uniq-no-integ, A:sec4:horizon-not-contractive, A:sec5:overview, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: Dissertation.WellPosedness.Constants
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash 523a9f9cc9be2abd0000000000000000 (pl-fp-v1:774cc4aab71fd127407611d8c74b17fb04b31edfcab7353ee9551228316b58af)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:28:16Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:15:19Z):
Reading of def:Dissertation.WellPosedness.Constants.

Paper notion. The constants of the hypotheses and of the estimates: Assumption 2.3 (L >= 0),
Assumption 2.4 (G full rank, ||G||, s_min(G), c_G = s_min(G)^{-2}), Assumption 2.5 (alpha,
beta_1, beta_2 >= 0, alpha + beta_1 > 0, beta_1 + beta_2 > 0, beta_1 > 0 if m < n, alpha,
beta_2 > 0 if m > n), the horizon T > 0 and the universal BDG constant c_BDG. Theorem 3.1:
"C_stab depends only on T, L, ||G||, c_G, alpha, beta_1, beta_2 and c_BDG ... Neither the
dimensions n,m,d nor the total mass nu(E) appears"; Section 4: "C denotes a positive constant ...
depending only on T, L, ||G||, c_G, alpha, beta_1, beta_2 and c_BDG"; Lemma 3.2/4.2 lambda_*
depends only on T, L, c_BDG; Lemma 4.3 C_B also on lambda_underline; Lemma 4.4 zeta_0 also on
lambda_*.

Faithful Lean definition: a record of exactly the parameters on which the paper's constants may
depend (T, L, ||G||, c_G, alpha, beta_1, beta_2; c_BDG may be omitted since it is universal, or
included as a field), so that "a constant depending only on these" is a function of this record
chosen before the coefficients, the dimensions, nu, the forcing and the solutions. It must not
contain the dimensions n, m, d, nu, nu(E), the coefficients or G itself beyond ||G|| and c_G (that
would allow dependence the paper excludes); if it also carries constraints (positivity,
Assumption 2.5's sign conditions, T > 0), they must be the paper's (not stronger, e.g. alpha > 0
always, nor weaker in a way that admits degenerate records used with a different meaning). If ||G||
and c_G are fields, any link to the actual G (||G|| = operator norm, c_G = s_min(G)^{-2}, or the
inequalities |Gv| <= ||G|| |v|, |x|^2 <= c_G |Gx|^2) belongs to the claim hypotheses.
Comparison (verdict recorded 2026-10-19T03:26:34Z):
def:Dissertation.WellPosedness.Constants (Dissertation/WellPosedness/Assumptions.lean:119-137):
a Prop-structure on (n m : ℕ) (α β₁ β₂ : ℝ) with fields 0 ≤ α, 0 ≤ β₁, 0 ≤ β₂, 0 < α + β₁,
0 < β₁ + β₂, m < n → 0 < β₁, n < m → 0 < α ∧ 0 < β₂.
My reading considered two candidates: a record of the parameters on which constants may depend,
or the constraint set of Assumption 2.5. The Lean is the latter: it is a predicate (Prop), not a
data record, so the "depends only on" concern does not arise here, and its dependence on n, m is
exactly what the rank conditions need. Against Assumption 2.5: "α, β₁, β₂ ≥ 0, α + β₁ > 0,
β₁ + β₂ > 0, with β₁ > 0 if m < n and α, β₂ > 0 if m > n" — field by field identical (m = backward
dimension, n = forward dimension as in the paper; m > n ↔ n < m). Nothing stronger (no α > 0 in
general) and nothing weaker. Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-19T03:27:50Z): none
