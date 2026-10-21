### A:eq:contract: Dissertation.PaperSpec.A.eq_contract
Pins: manuscript A None; project 6d403c197bfb10fe8808933c6e525ee0ae544fb1; hash ed839d34f480cba1410aaf91d78575ad (pl-fp-v1:a750d7bee66df939bc2b91b1b8995dd30779dfacd7dbde8a021718213b82b108)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-20T04:27:45Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-20T04:17:59Z):
Reading of (4.13) (eq:contract), Step 5 of the proof of Lemma 4.2 (lem:small),
manuscript/paper/sections/04-proof-wellposedness.tex.

Setting: the standing setting of Section 2 (as for (4.10), (4.12)).

Hypotheses in force: those of Lemma 4.2 (Assumptions 2.2 and 2.3 with constant L >= 0;
lambda in [0,1]; square-integrable forcing q with the Section 4 measurability; xi_0 in
L^2(F_0)); trials Theta^1, Theta^2 in S; images Thetabar^k = Phi_lambda(Theta^k) with Xbar^k
the frozen forward process (4.7) and (Ybar^k, Zbar^k, Ubar^k) the solution of the frozen linear
BSDE (4.8) in S^2 x H^2_W x H^2_N (equivalently, every such solution, by uniqueness).

Conclusion (the chain):
 (o)   ||Phi_lambda(Theta^1) - Phi_lambda(Theta^2)||_S^2 = E sup_{t<=T} |deltaXbar_t|^2
       + E sup_{t<=T} |deltaYbar_t|^2 + E int_0^T (|deltaZbar_s|_F^2 + ||deltaUbar_s||^2) ds
       (the definition of the S-norm applied to the difference of the images);
 (i)   <= (C_X + C_Y) lambda^2 ||Theta^1 - Theta^2||_S^2      [(4.10) and (4.12)];
 (ii)  <= C_Phi lambda^2 ||Theta^1 - Theta^2||_S^2,  C_Phi = max{1, C_X + C_Y},
with C_X = 3 max{T, c_BDG} Lstar^2, Lstar^2 = 10 L^2 max{T,1}, C_g = 4 L^2,
C_BP = 2 e^T (5 + 4 c_BDG) + 4T, C_Y = C_BP (C_g C_X + Lstar^2). The text after the display
also records the dependencies C_Phi = C_Phi(T, L, c_BDG) (automatic for explicit formulas).
Link (ii) is trivial algebra (max), link (o) is an identity that depends on the S-norm being the
one of Section 3 (sum of the three expected quantities) and on Phi_lambda(Theta^1) -
Phi_lambda(Theta^2) = (deltaXbar, deltaYbar, deltaZbar, deltaUbar). Expectations are true
expectations (finite here, or in [0, infinity]); no junk-value readings.

Constants: c_BDG the paper's single universal BDG constant, the same value in C_X and inside
C_Y (through C_X and C_BP). "exists c_0 > 0, for all c >= c_0" is faithful if c_0 precedes
every datum (T, dimensions, space, coefficients, lambda, q, trials). Not faithful if c_0 can
depend on the data.

Breadth: lambda in [0,1] at least; extra hypotheses beyond Lemma 4.2's are a narrowing;
witness: a Lipschitz instance (e.g. linear coefficients) with trials in S.
Comparison (verdict recorded 2026-10-20T04:24:26Z):
Comparison for Dissertation.PaperSpec.A.eq_contract (Dissertation/PaperSpec/A/Sec4Contraction.lean)
against (4.13), manuscript/paper/sections/04-proof-wellposedness.tex lines 429-439.

Constants and their place. `∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, c₀ ≤ c → ∀ {Ω} ...`: c₀ is the first
quantifier, universal. With the one value c: C_X = `3 * max T c * (10 * L ^ 2 * max T 1)`,
C_BP = `2 * Real.exp T * (5 + 4 * c) + 4 * T`, C_Y = C_BP (4L² C_X + Lstar²) (= C_BP (C_g C_X +
Lstar²), C_g = 4L²), C_Phi = `max 1 (C_X + C_Y)`. All match the paper's (4.9)-(4.13) formulas.

Setting and hypotheses. Identical to those of eq_fwddiff and eq_bwddiff (standing setting,
`JointBorel`, Assumptions 2.2 and 2.3 with L, lambda in [0,1], a forcing of the class of (4.1),
trials in S, their frozen steps with the same lambda, xi_0, q). These are the Lemma 4.2
hypotheses in force at Step 5; nothing added, nothing missing.

Conclusion.
 (o) `supSize(Θ̄¹ − Θ̄²) = ∫⁻ ⨆ esq(δX̄) + ∫⁻ ⨆ esq(δȲ) + (ΣΣ energy(δZ̄) + Σ markedEnergy(δŪ))`:
     the identity ‖Φ_λ(Θ¹) − Φ_λ(Θ²)‖²_S = E sup|δX̄|² + E sup|δȲ|² + E∫(|δZ̄|_F² + ‖δŪ‖²),
     with the S-norm of Section 3 (`supSize`, the size of the coordinatewise difference of the
     images); in Lean it is the definition of `supSize`, as in the paper it is the definition of
     the norm. Matches.
 (i) `≤ ofReal((C_X + C_Y) λ²) supSize(Θ¹ − Θ²)`: matches the first inequality.
 (ii) `≤ ofReal(max{1, C_X + C_Y} λ²) supSize(Θ¹ − Θ²)`: matches C_Phi λ² ‖Θ¹ − Θ²‖²_S.
Expectations in [0, infinity], no junk values. The dependence C_Phi = C_Phi(T, L, c_BDG) stated
after the display holds by the explicit formula.

Representation choices (harmless; as for eq_fwddiff and eq_bwddiff): expectations as lintegrals
in [0, infinity]; the norm of the difference of the images as `supSize` of the coordinatewise
differences; trials, frozen steps and forcings as everywhere-cadlag versions cut off outside
[0,T]; Phi_lambda(Theta) as any solution of (4.7)-(4.8) in S, unique by eq_frozenbwd.

BDG constant. "There is c₀ > 0 such that for every c ≥ c₀", c₀ the first quantifier, with the
same c inside C_X and C_Y: the faithful reading of the paper's one universal c_BDG, valid at
every step (admissible BDG constants are up-closed, and the constants are increasing in it).
Being universal, c₀ cannot trivialise the chain.

Witness. `Dissertation.Acceptance.A.frozen_pair_hypotheses` (Dissertation/Acceptance/A/
WitnessContraction.lean), the Example 5.1(i) instance with two distinct trials and their frozen
steps: every hypothesis met by an instance the paper intends. Not vacuous.

Coverage. The claim A:eq:contract has one clause, this proposition; the pinned region is the
display (4.13) (lines 429-439). The clause states the identity, both inequalities and the
constant C_Phi: every mathematical assertion of the display. The sentence after it (the first
inequality by (4.10) and (4.12); L⋆ = L⋆(T, L), C_X = C_X(T, L, c_BDG), C_g = C_g(L),
C_BP = C_BP(T, c_BDG), so C_Phi = C_Phi(T, L, c_BDG)) is outside the pinned region; its dependence
assertions are implied by the explicit formulas of the clause. Nothing is stated beyond the
passage. The hypotheses are those in force at Step 5 of the proof of Lemma 4.2, no more, no
fewer.

Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless:
1. Expectations as lintegrals in [0, infinity] of nonnegative quantities (no junk values); the
   S-norm squared of the difference of the images as `supSize` of the coordinatewise
   differences, so the identity of (4.13) is definitional, as in the paper.
2. Trials, frozen steps and forcings as everywhere-cadlag versions cut off outside [0,T]; the
   filtration is complete.
3. Phi_lambda(Theta) as any solution of (4.7)-(4.8) in S (exists, unique by eq_frozenbwd).
4. c_BDG as "exists c_0 > 0, for all c >= c_0", c_0 the first quantifier (universal), with one c
   in C_X, C_BP, C_Y and C_Phi: the faithful reading of the paper's single universal BDG constant.
Disagreements with the author's review (shown 2026-10-20T04:27:38Z): No disagreement on substance: the reading of the identity as the definition of `supSize` of the
differences of the images, of the explicit constants C_X, C_Y and C_Phi = max{1, C_X + C_Y}, of
c_BDG (c₀ first, at least those of (4.10) and (4.12), one c throughout) and of the hypotheses agree
with mine; the witness values (2 and 2) check.

One difference of classification only: I record "faithful with representation choices" rather
than "faithful", for the same harmless choices as in (4.10) and (4.12) (everywhere-cadlag
versions cut off outside [0,T], Phi_lambda(Theta) as any solution of (4.7)-(4.8) in S,
expectations in [0, infinity]).
