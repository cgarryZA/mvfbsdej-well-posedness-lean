### A:eq:coerc: Dissertation.PaperSpec.A.eq_coerc_blocks
Pins: manuscript A None; project 6d403c197bfb10fe8808933c6e525ee0ae544fb1; hash ed839d34f480cba17bd256e67c544535 (pl-fp-v1:bf2f2536242a3fd4deda132e49eab73b0759b788051a605287a98909cc644cec)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-20T02:03:19Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-20T01:52:26Z):
Reading of the passage (manuscript/paper/sections/04-proof-wellposedness.tex, lines 657-695, Step 2 of
the proof of Lemma 4.3 (lem:pert), equation (4.22) = eq:coerc and the sentence after it: "Each
coercive block present on the left of (4.22) is therefore at most K").

Setting and hypotheses in force (Lemma 4.3, lines 490-509): the standing setting of §2 (filtered
space with usual conditions, augmented filtration of W, N, F_0; PRM N with sigma-finite intensity
dt nu(de) on countably generated E; nu(E) = infinity allowed); deterministic Borel coefficients
b, sigma, h, f, g with signatures of §2; Assumption 2.3 (Lipschitz, constant L >= 0, diagonal form),
Assumption 2.4 (full rank G in R^{m x n}), Assumption 2.5 (terminal and interior expected diagonal
G-monotonicity with alpha, beta_1, beta_2 >= 0, alpha + beta_1 > 0, beta_1 + beta_2 > 0, beta_1 > 0 if
m < n, alpha, beta_2 > 0 if m > n). Assumption 2.2 (integrability at origin) is NOT assumed by Lemma 4.3.
Fix lambda_ in (0,1], lambda in [lambda_, 1]. Theta^1, Theta^2 solve the forced system (4.1) at
parameter lambda with F_0-measurable initial data xi_0^k and forcings q^k = (q^{b,k}, q^{sigma,k},
q^{h,k}, q^{f,k}, q^{g,k}_T) (square-integrable, progressive / predictable as stated at lines 41-53);
for each k, X^k, Y^k cadlag adapted with E int (|X^k|^2 + |Y^k|^2) < infinity, X^k_T in L^2(F_T),
Z^k in H_W, U^k in H_N; and Theta^1 - Theta^2 in S. In the proof, q denotes delta q = q^1 - q^2
(line 511-512), and P := E|delta xi_0|^2 + E|delta q^g_T|^2 + E int (|delta q^b|^2 + |delta q^sigma|_F^2
+ ||delta q^h||^2 + |delta q^f|^2) dt.

Definitions at this point: N' := E|delta X_T|^2 + E|delta Y_0|^2 + E int_0^T (|delta X_t|^2 +
|delta Y_t|^2 + |delta Z_t|_F^2 + ||delta U_t||^2) dt; K := eta N' + (||G||^2 / (4 eta)) P for eta > 0
(||G|| the operator norm).

Conclusion (for every eta > 0, and for every lambda, Theta^k as above; eta is quantified after the
data, any order of eta versus the data is fine since nothing is chosen depending on eta):
 (1) lambda alpha E|G delta X_T|^2 <= K;
 (2) lambda beta_2 E int_0^T |G delta X_t|^2 dt <= K;
 (3) lambda beta_1 E int_0^T (|G^T delta Y_t|^2 + |G^T delta Z_t|_F^2 + ||G^T delta U_t||_{L^2(nu)}^2) dt
     <= K.
(The paper's (4.22) itself also asserts the chain LHS-sum <= cross-term sum <= K; the unit states the
block consequence. Each block is nonnegative since lambda, alpha, beta_i >= 0, so the sum bound gives
each block bound.) G^T delta U_t is applied pointwise in e; delta Z, delta U are the differences of the
predictable integrands; E|.|^2 are genuine (finite) expectations; the expectations and integrals are
finite under Theta^1 - Theta^2 in S, so junk values (Bochner integral of a non-integrable function is
0 in Lean) must not be what makes the inequality true or false.

The stochastic content (the G-energy identity (4.19), the zero-mean of the five martingale terms,
the monotonicity insertion (4.20)-(4.21)) is part of what is claimed up to this point; a faithful
statement must take only the hypotheses of Lemma 4.3 (no more), i.e. the solution property of the
forced system with the genuine stochastic integrals, not the identity (4.19) or the intermediate
inequality as additional hypotheses. A statement that adds as hypotheses consequences derived earlier
in the proof (e.g. the inequality at lines 673-679 or (4.19)) would be narrower than the printed step
(the printed step being "(4.22) follows under the Lemma's hypotheses"); one that drops hypotheses of
Lemma 4.3 is broader and fine if still true.

Constants: none to choose; alpha, beta_1, beta_2, G given by the assumptions; eta arbitrary positive.

Vacuity: hypotheses must be satisfiable, e.g. Theta^1 = Theta^2 a solution of a monotone linear
system (or the trivial system with zero coefficients when allowed by Assumption 2.5) with zero
forcings, or any instance of the paper's examples.

Is this claimed at this revision? Yes: (4.22) and the sentence "Each coercive block present on the left
of (4.22) is therefore at most K" (lines 694-695), again used at line 786.
Comparison (verdict recorded 2026-10-20T02:02:37Z):
Comparison for Dissertation.PaperSpec.A.eq_coerc_blocks (Dissertation/PaperSpec/A/Sec4Difference.lean)
against my locked reading.

Setting. The standing setting as in the other §4 propositions: G_0 independent of the LevyDriver D,
E countably generated, nu sigma-finite, n, m, d >= 1, T > 0, filtration enlJoint (usual augmentation of
the filtration of W, N, G_0). Matches.

Hypotheses (identical to the binder list of Lemma 4.3's proposition lem_pert, Dissertation/PaperSpec/A/
Sec4.lean, which I compared line by line):
- `JointBorel T C` (the standing Borel measurability (2.3) of the coefficients), `Assumption23` (L >= 0,
  diagonal interior and terminal Lipschitz bounds), `G.rank = min m n` (Assumption 2.4, full rank),
  `Assumption25` (terminal and interior expected diagonal G-monotonicity, with `Constants`:
  alpha, beta_1, beta_2 >= 0, alpha + beta_1 > 0, beta_1 + beta_2 > 0, beta_1 > 0 if m < n, alpha, beta_2 > 0
  if m > n) - Assumptions 2.3-2.5 and no Assumption 2.2, as in Lemma 4.3 (Dissertation/WellPosedness/Spec/
  Assumptions.lean, Dissertation/WellPosedness/Assumptions.lean).
- lamLow in (0,1], lam in [lamLow, 1].
- xi_1, xi_2 measurable for enlJoint at time 0 (F_0-measurable initial data; no L^2 assumed, as printed).
- two forcings `PredForcing` (q^b, q^sigma, q^f jointly and progressively measurable, q^h marked
  predictable, all square integrable, zero off [0,T], q^g F_T-measurable in L^2) - the forcing class of §4.
- Theta^k `WeakForcedSolution` at lam (Dissertation/PaperSpec/A/Setting.lean): X^k, Y^k adapted, cadlag
  on [0,T] (right-continuous every path, left limits), E int |.|^2 < infinity, Z^k in H_W, U^k in H_N,
  X^k_T in L^2, and both identities of (4.1) a.s. for every t with h at the predictable tuple.
- `supSize … δ… < ⊤`: Theta^1 - Theta^2 in S.
These are exactly the hypotheses of Lemma 4.3 in force at (4.22) - no more, no fewer. In particular the
G-energy identity (4.19), the zero-mean facts and the insertions (4.20)-(4.21) are NOT taken as
hypotheses, as my reading required.

Conclusion. `∀ η > 0`, three inequalities, each with right-hand side
`η * N'.toReal + ‖GX G‖^2/(4η) * P.toReal` where
N' = ∫⁻|δX_T|² + ∫⁻|δY_0|² + Σ energy(δX_i) + Σ energy(δY_k) + ΣΣ energy(δZ_kj) + Σ markedEnergy(δU_k)
(= E|dX_T|^2 + E|dY_0|^2 + E int_0^T (|dX|^2 + |dY|^2 + |dZ|_F^2 + ||dU||^2) dt; energy and markedEnergy are
the lower integrals of squares over Omega x [0,T] (x E)), P = dataSize of (xi_1 - xi_2, q_1 - q_2)
(= E|d xi_0|^2 + E|d q^g|^2 + E int (|d q^b|^2 + |d q^sigma|_F^2 + ||d q^h||^2 + |d q^f|^2)), so q = delta q
as in the proof, and ‖GX G‖ the operator norm of x |-> Gx on Euclidean spaces. Left-hand sides:
 (1) lam * alpha * E[(G dX_T).(G dX_T)] = lambda alpha E|G dX_T|^2;
 (2) lam * beta_2 * E int_[0,T] |G dX_s|^2 ds;
 (3) lam * beta_1 * E int_[0,T] (|G^T dY_s|^2 + sum_j |G^T dZ_s e_j|^2 + int_E |G^T dU_s(e)|^2 nu(de)) ds,
     the middle sum being |G^T dZ|_F^2 and G^T applied pointwise in e.
Matches the three blocks and K = eta N' + ||G||^2/(4 eta) P, for every eta > 0.

Junk-value check. The left-hand sides are Bochner integrals: they would be 0 for a non-integrable or
non-measurable integrand, which would make the inequalities trivial. Under the hypotheses they are
genuine: dX_T, dX, dY, dZ, dU are square integrable (supSize < ⊤ and X_T in L^2), the processes are
adapted with right-continuous paths, hence progressively and jointly measurable, Z, U are (marked)
predictable, and |G^T v| <= ||G|| |v|; for a.e. (omega, s) the inner nu-integral is that of an integrable
function. The right-hand sides use `.toReal` of ENNReal sums; N' < ⊤ follows from supSize < ⊤
(E|dX_T|^2, E|dY_0|^2 are bounded by the suprema, and the dt-integrals by T times them), and P < ⊤ from the
forcings' square integrability and d xi_0 = dX_0 a.s. (so E|d xi_0|^2 <= E sup |dX|^2); both finiteness
facts are stated as conclusions of the sibling clause eq_coerc. So `.toReal` is
not a junk 0 here (and if it were, it would only strengthen the conclusion). Nonnegativity of
lam, alpha, beta_i (from lamLow > 0 and `Constants`) makes each block nonnegative, so the block bounds are
what the sentence after (4.22) asserts.

Witness. Dissertation.Acceptance.A.lem_pert_two_data_hypotheses (Dissertation/Acceptance/A/
WitnessSec4.lean): Example 5.1(i) at nu = delta_0, n = m = d = 1, T = 1, G = 1, alpha = beta_1 = beta_2 = 1,
lambda = lamLow = 1, zero forcings, initial data 0 and e_1, two solutions of Theorem 3.5 whose difference
lies in S and data size 1. A non-degenerate instance the paper intends; the hypotheses can be met.

Representation choices: coordinates as real functions; expectations of squares written as ENNReal lower
integrals in N' and P (with toReal) and as Bochner integrals of dot products on the left; |.|_F^2 as the
sum over columns; the solution notion WeakForcedSolution and the forcing class PredForcing as reviewed
definitions of the closure; time interval [0,T] closed (Lebesgue-null difference).

Is it claimed at this revision? Yes: sections/04-proof-wellposedness.tex lines 694-695, "Each coercive
block present on the left of (4.22) is therefore at most K", used again at line 786. The proposition
states the bound for all three blocks; a block whose constant is zero is 0 <= K, so stating all three is
the same claim.

Coverage of claim A:eq:coerc (acceptance/claims.json): clauses eq_coerc ("(4.22): N' and P finite, the
sum of the blocks <= the six pairings in absolute value <= K for every eta > 0") and eq_coerc_blocks
(this unit). The pinned region (lines 683-693) asserts the chain of (4.22): LHS <= the six absolute
pairings <= K; eq_coerc states both inequalities (and the finiteness of N' and P that makes K a real
number); the sentence after the display (lines 694-695) is this clause. Together they state every
mathematical assertion of the passage; neither states something the passage does not claim (the
finiteness of N' and P is implicit in the passage's use of K as a real bound and is true under the
hypotheses). Not in the claim, being outside its pinned region: the preceding unnumbered display of
lines 670-680 (insertion of (4.20)-(4.21) into (4.19)) and the definitions of N', K of lines 663-669;
I found no other claim with a clause stating that intermediate display (A:eq:Gid, A:eq:intmono,
A:eq:termmono state its three ingredients). Hypotheses: both clauses carry exactly Lemma 4.3's
hypotheses, the ones in force at (4.22) (no more, no fewer).
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless: (1) coordinates as real functions (Fin n -> R -> Omega -> R etc.)
with |.|^2 as dot products and |G^T dZ|_F^2 as the sum over the d columns; (2) N' and P are ENNReal lower
integrals of squares (energy, markedEnergy, dataSize) converted with toReal, both finite under the
hypotheses (supSize < ⊤, square-integrable forcings, d xi_0 = dX_0 a.s.), so no junk 0 enters; (3) the
blocks are Bochner integrals of integrable, measurable integrands under the hypotheses, so no junk 0
enters; (4) ||G|| is the operator norm of GX G : R^n -> R^m; (5) q is delta q = q^1 - q^2 as in the proof;
(6) the hypotheses are those of Lemma 4.3 exactly, the solution notion being WeakForcedSolution and the
forcing class PredForcing, with processes extended by zero off [0,T].
Disagreements with the author's review (shown 2026-10-20T02:02:53Z): 1. The recorded author review of this unit (acceptance/review/A.md, line 1299) is a single line citing a
   claude-auditor report on the sibling proposition Dissertation.PaperSpec.A.eq_coerc, not on
   eq_coerc_blocks. As recorded it is not a review of this unit. I agree with its verdict (faithful with
   representation choices), but the review should be recorded for eq_coerc_blocks or cite a report of it.
2. Points a review should record and the cited line does not: the hypotheses are exactly Lemma 4.3's
   (the binder list of lem_pert), not (4.19) or the display before (4.22) as extra hypotheses; q is delta q;
   the Bochner integrals of the blocks and the toReal of N' and P are genuine (integrable and finite under
   supSize < ⊤ and the forcing hypotheses), so no junk value decides the inequality; nonnegativity of lambda,
   alpha, beta_i (Constants) is what makes "each block <= K" the sentence of lines 694-695; the witness is
   Dissertation.Acceptance.A.lem_pert_two_data_hypotheses.
3. Coverage (not a disagreement with the verdict): the unnumbered display of lines 670-680 (insertion of
   (4.20)-(4.21) into (4.19)) is outside the claim's pinned region and is stated by no clause I could find.
