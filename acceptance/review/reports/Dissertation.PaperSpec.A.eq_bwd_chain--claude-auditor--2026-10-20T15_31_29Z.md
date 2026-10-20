### A:eq:bwd: Dissertation.PaperSpec.A.eq_bwd_chain
Pins: manuscript A None; project 53a4ee4fc8767ba8884b5732431dded9772b47df; hash ed839d34f480cba1bd5456c76b6d343a (pl-fp-v1:c6ecb7c8099eaf514ff9963554e55a8bfc7df338615e2c8424304c99408c5587)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-20T15:31:29Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-20T15:21:24Z):
Reading of the clause "the first two links of the chain before (4.27)" of claim A:eq:bwd
(manuscript/paper/sections/04-proof-wellposedness.tex, proof of Lemma lem:pert, Step 4,
lines 761-770).

Setting and hypotheses in force: as in Lemma lem:pert (standing basis; ass:lip, ass:G, ass:mono;
lambdalow in (0,1], lambda in [lambdalow,1]; Theta^1, Theta^2 solve (4.1) at lambda with the same
coefficients, F_0-measurable initial data and square-integrable forcings q^k; X^k, Y^k cadlag
adapted with E int (|X^k|^2 + |Y^k|^2) < infinity, X^k_T in L^2, Z^k in H^2_W, U^k in H^2_N,
Theta^1 - Theta^2 in S). q := delta q; P as defined in the proof (initial difference, terminal
and running forcing differences). (4.16): dY written forward from dY_0:
dY_t = dY_0 - int_0^t (lambda df_s + q^f_s) ds + int_0^t dZ dW + int_0^t int_E dU Ntilde.
df_t = f(t, Theta^1_t, mu^1_t) - f(t, Theta^2_t, mu^2_t), mu^k_t = Law Theta^k_t.

Constant: C > 0 depending only on T, L, ||G||, c_G, alpha, beta_1, beta_2, c_BDG (for these two
links, only T, L, c_BDG), chosen before lambda, the solutions and the forcings; the two C may
differ ("not necessarily the same at each occurrence").

Conclusion:
  (i)  E sup_{t<=T} |dY_t|^2 <= C (E|dY_0|^2 + E int_0^T |lambda df_s + q^f_s|^2 ds
                                   + E int_0^T (|dZ_s|_F^2 + ||dU_s||^2) ds);
  (ii) the bracket of (i) is <= C (E|dY_0|^2 + E int_0^T (|dX_s|^2 + |dY_s|^2 + |dZ_s|_F^2
                                   + ||dU_s||^2) ds + P)
       (as a chain: C B <= C'' B' with admissible constants; equivalently B <= C''' B').
The third link (with (4.26)) is not part of this clause.

Faithful formal statement: exists constant(s) depending only on the listed parameters such that
for all lambda in [lambdalow,1] (or [0,1], broader) and all solution pairs and forcings
satisfying the hypotheses, (i) and (ii). A single C with A <= C B and B <= C B' is equivalent;
a literal C B <= C B' (B <= B') would be stronger than printed. lambdalow is not in the
section's default dependence list for C (only C_B of Lemma lem:pert depends on it), and these
two links need no lambdalow dependence (lambda <= 1); a constant depending on lambdalow would
be a slight weakening, harmless for the proof since C_B may depend on it. Expectations must be genuine (finite). A witness should
exhibit nonzero dY (e.g. nonzero forcing difference).
Comparison (verdict recorded 2026-10-20T15:30:30Z):
Comparison of Dissertation.PaperSpec.A.eq_bwd_chain (Dissertation/PaperSpec/A/Sec4ProofSteps.lean)
with the locked reading (Step 4 of the proof of Lemma lem:pert, lines 761-770).

Constants and their order. "exists K_1 K_2 : R^7 -> R" before everything else; C_i =
K_i(T, L, ||G||, c_G, alpha, beta_1, beta_2) (||G|| the operator norm of GX G, c_G = s_min(G)^{-2}).
No dependence on lamLow, lambda, t, the dimensions, the solutions, the forcings or the data;
c_BDG absorbed (one universal number). The two links have the form A <= C_1 B and
C_1 B <= C_2 B' (the printed chain, constants "not necessarily the same at each occurrence"; no
literal B <= B'). Match.

Setting and hypotheses: identical to eq_fwd_chain and to Lemma lem:pert as printed: (2.3),
ass:lip with L, G of full rank, ass:mono; lamLow in (0,1], lambda in [lamLow, 1]; F_0-measurable
initial data; forcings of the paper's class; both solutions in H_weak with X_T in L^2
(WeakForcedSolution); Theta^1 - Theta^2 in S (finite supSize). Match.

Conclusion.
(i)  E sup_{t in [0,T]} |dY_t|^2 <= C_1 (E|dY_0|^2 + sum_k E int_0^T |lam df_k + dq^f_k|^2 ds
     + E int_0^T (|dZ|_F^2 + ||dU||^2) ds), df the driver difference at (Theta^k_s, Law Theta^k_s)
     (driverProc), q = delta q. Match.
(ii) C_1 (that bracket) <= C_2 (E|dY_0|^2 + E int_0^T (|dX|^2 + |dY|^2 + |dZ|_F^2 + ||dU||^2) ds + P),
     P = dataSize of the differences of the data (the proof's P with q = delta q). Match.
Expectations in [0, infinity] (lintegral, energies), so no junk values; the third link (by
(4.26)) is not part of the clause, as my reading required.

Representation choices (harmless): constants as functions of the parameter tuple with c_BDG
absorbed and ofReal(K_i) as multipliers; coordinates; [0, infinity] expectations; the S-membership
of the difference as finite supSize.

Witness. Dissertation.Acceptance.A.lem_pert_backward_window_hypotheses (Example 5.1(i), L = 1,
G = 1, alpha = beta_1 = beta_2 = 1, lam = lamLow = 1; difference dX = 1, dY = M^W + M^N,
dZ = dU = 1_{(0,1]}, initial difference 1): all hypotheses supplied; E sup |dY|^2 > 0 and the
brackets are positive, so the chain is not 0 <= 0. An instance the paper intends.

Coverage. Claim A:eq:bwd has two clauses: eq_bwd ((4.27): E sup |dY|^2 + E int (|dZ|^2 + ||dU||^2)
<= C (E|dX_T|^2 + E int |dX|^2 + P), C a function of (T, L, ||G||, c_G, alpha, beta_1, beta_2)) and
this one (the first two links of lines 765-769). The third link (line 770) is implied by
eq_bwd's conclusion, and the sentence "the first term of (4.26) may be replaced" is (4.27)
itself, so together the clauses state every mathematical assertion of lines 761-778. Nothing
beyond the passage is stated and the hypotheses are those in force. The clause reads lines
before the pinned region (775-778), so a change to lines 761-770 would not by itself reopen the
review.
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless: (1) the two constants are values K_i(T, L, ||G||, c_G,
alpha, beta_1, beta_2) of functions chosen before everything else, in the form A <= C_1 B,
C_1 B <= C_2 B' (the printed two links with "C not necessarily the same at each occurrence");
c_BDG, one universal number, is absorbed, which makes the statement at least as strong as the
printed dependence; (2) expectations are lower Lebesgue integrals in [0, infinity] with ofReal(K_i)
as multipliers; (3) coordinates; (4) Theta^1 - Theta^2 in S as finite supSize of the difference.
Hypotheses (those of Lemma lem:pert), the quantities (dY_0, lambda df + q^f with q = delta q, the
(Z, U) energies, P) and the two links match the printed step.
Disagreements with the author's review (shown 2026-10-20T15:30:49Z): No disagreement on substance: same hypotheses, the two links stated as printed with one constant
per link chosen first as functions of (T, L, ||G||, c_G, alpha, beta_1, beta_2) and no lamLow
dependence, the third link left to eq_bwd, and a nondegenerate witness. Verdict label: I record
"faithful with representation choices" (c_BDG absorbed into the functions K_i; coordinates;
[0, infinity] expectations with ofReal multipliers; Theta^1 - Theta^2 in S as finite supSize).
Procedural remark: the clause reads lines 761-770, before the pinned region (775-778).
