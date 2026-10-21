### A:rem:wasserstein-bounds: Dissertation.PaperSpec.A.eq_couplingT
Pins: manuscript A None; project d3e594defeeeb94a6d05c33c666bcb870d584302; hash ed839d34f480cba1b0b3c75b14edd5d3 (pl-fp-v1:1a693cb2c3538754b4113a944316473dbc55b8b812343163a2d2c5be76e92385)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-20T11:24:07Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-20T11:09:24Z):
# Reading: eq_couplingT — (2.9) of Remark 2.6

Setting. Standing probability space (any probability space is a harmless broadening). R^n with
the Euclidean norm. W_2 on P_2(R^n): coupling infimum of squared Euclidean distance.

Hypotheses. X_T, X'_T in L^2(Omega, F_T; R^n) (measurable, square-integrable);
rho = Law(X_T), rho' = Law(X'_T) (the induced terminal laws, in P_2(R^n)).

Conclusion. W_2(rho, rho')^2 <= E |X_T - X'_T|^2.

The paper notes it is the X-marginal case of (2.8) at time T; any formal route is fine.
Faithfulness points: Euclidean (not sup) norm on R^n; square-integrability as hypothesis (or
lintegral form) so a Bochner junk 0 cannot appear; Law as pushforward of a measurable map; W_2 the
genuine infimum on P_2(R^n).
Comparison (verdict recorded 2026-10-20T11:23:00Z):
# Decision: spec:Dissertation.PaperSpec.A.eq_couplingT (Dissertation/PaperSpec/A/Sec2.lean)

Verdict: broader.

Comparison with the locked reading.
- Space. `EuclideanSpace ℝ (Fin n)`: R^n with the Euclidean norm, as in the paper.
- W_2. `w2P` (Dissertation/Law/P2.lean) is `w2` of the underlying laws: the square root of the
  infimum over couplings of the lintegral of the squared Euclidean distance; on `P2` laws the
  squared distance is finite (`w2sq_ne_top`), so the real value is genuine, not the junk 0.
- Laws. `lawP2 P X`, `lawP2 P X'` are the image measures, since the hypotheses `MemLp X 2 P`,
  `MemLp X' 2 P` hold (Dissertation/Law/LawP2.lean, `lawP2_law`); these are ρ and ρ'.
- Right-hand side. `∫ ω, ‖X ω - X' ω‖ ^ 2 ∂P`, integrable under the hypotheses, is E|X_T - X'_T|^2.
- Conclusion: W_2(ρ, ρ')^2 <= E|X_T - X'_T|^2, the printed (2.9).
Broader in the same harmless ways as (2.8): any probability space, and X, X' need only be square
integrable, not F_T-measurable. The printed claim is the instance in the detail file. The paper's
remark that (2.9) is the X-marginal case of (2.8) at time T is a derivation route, not a separate
assertion; the proposition states (2.9) directly, which is what the passage displays.

Current text. Read at 1f67672 (Remark 2.6). I have not seen the earlier text, so I cannot say what
changed; the proposition says what the current (2.9) says.

Witness. `Dissertation.Acceptance.A.eq_couplingT_hypotheses` (Dissertation/Acceptance/A/
WitnessHyp.lean): on Bool with the uniform law, X = 1_{true} e₁ and X' = 1_{false} e₁ in R^1,
square integrable and not a.s. equal. A genuine nonzero instance (n = 1).

Coverage (claim A:rem:wasserstein-bounds). As recorded in the eq_coupling decision: the four
clauses (2.8)-(2.11) state every mathematical assertion of Remark 2.6 at this revision; the
optimal coupling inside the printed chains is a cited proof device; no clause states something
the passage does not claim, and the hypotheses are those in force (square-integrable terminal
states on one probability space).
Witness: —
Verdict: broader — Broader than the printed claim: the proposition holds over every probability space and every pair
of square-integrable random vectors of R^n. The printed (2.9) is the instance Ω = the standing
space, X = X_T, X' = X'_T in L^2(Ω, F_T; R^n) (so MemLp holds), where lawP2 P X_T = ρ and
lawP2 P X'_T = ρ' and w2P is W_2 on P_2(R^n) for the Euclidean norm.
Disagreements with the author's review (shown 2026-10-20T11:23:13Z): Disagreement in the verdict label only. The earlier review records "faithful"; I record
"broader", because the proposition holds over every probability space and every pair of
square-integrable random vectors of R^n, not only F_T-measurable terminal states on the standing
basis; the printed (2.9) is the instance. No substantive disagreement about the meaning (Euclidean
norm, genuine W_2 on P_2(R^n), image laws, genuine expectation).
