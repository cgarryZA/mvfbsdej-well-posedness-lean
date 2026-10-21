### A:eq:contract: Dissertation.PaperSpec.A.eq_contract_half
Pins: manuscript A None; project 53a4ee4fc8767ba8884b5732431dded9772b47df; hash ed839d34f480cba1a63dc37c47701d1d (pl-fp-v1:e20e334b152fd69fde30b45ddb0bb1bf6a262abf51b209c8d6438e8520602855)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-20T15:31:29Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-20T15:21:24Z):
Reading of the clause "lambda_* := (2 sqrt C_Phi)^{-1} in (0,1/2], C_Phi lambda^2 <= 1/4 for
lambda in [0,lambda_*], and the 1/2-contraction" of claim A:eq:contract
(manuscript/paper/sections/04-proof-wellposedness.tex, proof of Lemma lem:small, Step 5,
lines 426-454).

Setting and hypotheses in force: standing basis; Assumptions ass:integ (xi_0 in L^2(F_0), origin
values square-integrable) and ass:lip with constant L >= 0; coefficients deterministic, jointly
Borel; a square-integrable forcing q; Phi_lambda : S -> S the map of the proof (frozen forward
process (4.7), frozen BSDE (4.8) solved by predictable representation), for lambda in [0,1].

Constants (all explicit, chosen before q, the trial tuples, and anything but T, L, c_BDG):
  C_0 = 2 e^T, C_BP = C_0 (5 + 4 c_BDG) + 4T, L_*^2 = 10 L^2 max{T,1},
  C_X = 3 max{T, c_BDG} L_*^2, C_g = 4 L^2, C_Y = C_BP (C_g C_X + L_*^2),
  C_Phi = max{1, C_X + C_Y},   lambda_* = (2 sqrt C_Phi)^{-1}.
c_BDG is the one universal BDG constant fixed in the section (valid at p = 1 and p = 2).

Conclusions:
(a) lambda_* in (0, 1/2] (since C_Phi >= 1);
(b) for every lambda in [0, lambda_*]: C_Phi lambda^2 <= 1/4;
(c) for every lambda in [0, lambda_*], every forcing q, every Theta^1, Theta^2 in S:
    ||Phi_lambda(Theta^1) - Phi_lambda(Theta^2)||_S <= (1/2) ||Theta^1 - Theta^2||_S,
with ||Theta||_S^2 = E sup|X|^2 + E sup|Y|^2 + E int (|Z|_F^2 + ||U||^2).

Faithful formal statement: lambda_* given by (2 sqrt C_Phi)^{-1} with C_Phi = max{1, C_X+C_Y}
(either the explicit formula above, or at least a C_Phi >= 1 depending only on T, L, c_BDG for
which (4.13) holds); (a), (b) about that number; (c) for every coefficient system satisfying
ass:integ-ass:lip with the constant L, every q, every lambda in [0, lambda_*] and every pair of
trial tuples, the contraction of the genuine Phi_lambda (or of any tuples satisfying the frozen
equations (4.7)-(4.8), which is equivalent by uniqueness). (c) must not take (4.13) as a
hypothesis, nor be stated for an abstract map with a Lipschitz hypothesis; that would be a
different (weaker) claim. If lambda_* is existentially chosen, it must depend only on T, L, c_BDG
and be chosen before the coefficients, q and the tuples. A witness should show coefficients
with L > 0 and trial tuples with Theta^1 != Theta^2 (so the contraction is not 0 <= 0).
Comparison (verdict recorded 2026-10-20T15:27:06Z):
Comparison of Dissertation.PaperSpec.A.eq_contract_half (Dissertation/PaperSpec/A/Sec4ProofSteps.lean)
with the locked reading (Step 5 of the proof of Lemma lem:small, lines 426-454).

Constants and their order. The proposition opens with "exists c_0 > 0, for all c >= c_0", c
standing for c_BDG, BEFORE the probability space, the driver, T, L, the coefficients and all data.
Then, after the hypotheses, C_Phi and lambda_* are bound by explicit formulas:
  C_Phi = max{1, 3 max{T,c} (10 L^2 max{T,1})
              + (2 e^T (5 + 4c) + 4T) (4 L^2 (3 max{T,c} (10 L^2 max{T,1})) + 10 L^2 max{T,1})},
  lambda_* = (2 sqrt C_Phi)^{-1}.
Unfolding: L_*^2 = 10 L^2 max{T,1}, C_X = 3 max{T,c} L_*^2, C_BP = C_0 (5 + 4c) + 4T with
C_0 = 2 e^T, C_g = 4 L^2, C_Y = C_BP (C_g C_X + L_*^2), C_Phi = max{1, C_X + C_Y}: every formula
of the proof, checked term by term. C_Phi and lambda_* are functions of (T, L, c) only, as the
sentence after (4.13) asserts; they are fixed before q, the trials and their images. Match.

c_BDG. The paper fixes "one universal constant c_BDG valid at both exponents" without giving
its value. The proposition states the claim for every c above an (existential) threshold c_0.
This implies the reading "there is a universal constant for which the claim holds" and keeps the
constant before all data; it does not say the claim holds at every constant for which the BDG
inequalities happen to be valid if that constant lies below c_0. Since the paper neither
specifies c_BDG nor defines validity beyond the BDG inequalities used in the proof, and larger
values of c only make lambda_* smaller, I take this as a representation of an unspecified
universal constant, not a narrowing. (It is the convention the claim's scope note records for
the constants of (4.10), (4.12) and (4.13).)

Setting and hypotheses: standing basis; n, m, d > 0, T > 0; JointBorel, Assumption22 (xi_0),
Assumption23 with L: those of Lemma lem:small. For every lambda in [0, lambda_*], every forcing
of the class of (4.1) (PredForcing), every two trials of S (HTuple) and every pair of frozen
steps (FrozenStep with the same T, lambda, C, xi_0, q): the relational form of Phi_lambda
(equivalent to the construction by uniqueness of the frozen step in S, clause eq_frozenbwd).
Match.

Conclusions.
(a) 0 < lambda_* and lambda_* <= 1/2. Match.
(b) for every lambda in [0, lambda_*], C_Phi lambda^2 <= 1/4. Match.
(c) supSize(Thetabar^1 - Thetabar^2)^{1/2} <= (1/2) supSize(Theta^1 - Theta^2)^{1/2} in
    [0, infinity], supSize = E sup_{[0,T]} |dX|^2 + E sup_{[0,T]} |dY|^2 + sum E int_0^T |dZ_kj|^2
    + sum E int_0^T int |dU_k|^2 dnu: the squared S-norm of the difference, so (c) is
    ||Phi_lambda(Theta^1) - Phi_lambda(Theta^2)||_S <= (1/2) ||Theta^1 - Theta^2||_S. Match.
The contraction is a conclusion about the genuine frozen steps, not an assumption, and (4.13)
is not a hypothesis. The quantifier order (lambda before q and the trials) matches "for
lambda in [0, lambda_*]".

Representation choices (harmless): c_BDG as "every c above some c_0" (discussed above);
C_Phi, lambda_* bound by equations; Phi_lambda relational (FrozenStep); the S-norm as the square
root of supSize in [0, infinity] (finite here since both trials and both images lie in S);
coordinates.

Witness. Dissertation.Acceptance.A.frozen_pair_window_lam_hypotheses: for EVERY lambda in [0,1],
an instance with Example 5.1(i) (b = -y, sigma = -z, h = -u, f = x, g = x; L = 1; n = m = d = 1;
nu = Dirac mass at 0; T = 1; xi_0 = 0; zero forcing), the two trials 0 and (1, 1, 1_{(0,1]},
1_{(0,1]}) in S, and frozen steps at lambda for both, with delta b, delta sigma, delta h of energy
1. Since it is available at every lambda in [0,1], it covers every lambda in (0, lambda_*] for any
c, and the trials differ, so ||Theta^1 - Theta^2||_S > 0 and the contraction is not 0 <= 0 (for
lambda > 0 the images differ as well). It is an instance the paper intends.

Coverage. Claim A:eq:contract has two clauses: eq_contract ((4.13): the identity of the squared
norm and the chain <= (C_X + C_Y) lambda^2 ||.||^2 <= C_Phi lambda^2 ||.||^2 with
C_Phi = max{1, C_X + C_Y}, for every c_BDG >= c_0) and this one. The dependences of the
sentence after (4.13) are carried by the explicit formulas in both clauses; this clause states
lambda_*, (a), (b) and the 1/2-contraction of lines 445-454. Together they state every
mathematical assertion of lines 426-454 (the Banach fixed point and what follows belong to
other claims). Nothing beyond the passage is stated, and the hypotheses are those in force. The
clause reads lines after the pinned region (429-439), so a change to lines 445-454 would not by
itself reopen the review.
Witness: —
Verdict: faithful with representation choices — Representation choices: (1) the paper's unspecified universal constant c_BDG is represented as
"there is c_0 > 0 such that for every c >= c_0", quantified before all data; this implies the
existential reading of "one universal constant c_BDG", keeps the constant before everything
else, and is harmless because the paper never fixes its value (larger c only shrinks lambda_*);
it does not assert the claim at a valid BDG constant below c_0, which the paper does not single
out; (2) C_Phi and lambda_* are bound by equations to the explicit formulas of the proof
(L_*, C_X, C_BP with C_0 = 2e^T, C_g = 4L^2, C_Y, C_Phi = max{1, C_X + C_Y}), all checked;
(3) Phi_lambda is characterised relationally by FrozenStep, equivalent to the construction by
uniqueness of the frozen step in S; (4) the S-norm is the square root of supSize in [0, infinity];
(5) coordinates. The three conclusions (lambda_* in (0,1/2], C_Phi lambda^2 <= 1/4 and the
1/2-contraction for every lambda in [0, lambda_*]) and the hypotheses of Lemma lem:small match.
Disagreements with the author's review (shown 2026-10-20T15:30:43Z): Agreement on the formulas (C_X, C_BP with C_0 = 2e^T, C_g = 4L^2, C_Y, C_Phi = max{1, C_X + C_Y},
lambda_* = (2 sqrt C_Phi)^{-1}), the three conclusions, the quantifier order and the witness. One
point the review passes over: it reads c_BDG as "quantified before the data as for (4.13)", i.e.
"there is c_0 > 0 such that for every c >= c_0". That is a representation of the paper's
unspecified universal constant and I accept it as harmless (it implies the existential reading, keeps
the constant before everything else, and larger c only shrinks lambda_*), but it should be recorded
as a choice: the proposition does not assert the claim at a constant for which the BDG inequalities
are valid if that constant lies below c_0, so it is not the reading "for every valid c_BDG". Hence my
label "faithful with representation choices" rather than "faithful" (other choices: C_Phi,
lambda_* bound by equations; Phi_lambda relational via FrozenStep; the S-norm as supSize^{1/2} in
[0, infinity]). Procedural remark: the clause reads lines 445-454, after the pinned region (429-439).
