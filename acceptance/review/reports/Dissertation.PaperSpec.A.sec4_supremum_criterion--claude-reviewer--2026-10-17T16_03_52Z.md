### A:sec4:supremum-criterion: Dissertation.PaperSpec.A.sec4_supremum_criterion
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash ed839d34f480cba1f588c2071f5242ff (pl-fp-v1:668939571700f8b456579ffca8e5ba6bd4a5ecc7ce80e70d20901f671b16ef0c)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T16:03:52Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T15:47:46Z):
Reading of spec sec4_supremum_criterion ("By localisation and dominated convergence, a cadlag
local martingale whose running supremum is integrable has zero-mean increments").

Setting: a filtered probability space (Omega, F, (F_t), P) (the standing one satisfies the
usual conditions; a statement for an arbitrary filtered probability space is broader and
fine), horizon T > 0 (time set [0,T] or R_+). M real-valued (the uses are real-valued
pairings; vector-valued would be broader).

Hypotheses:
 - M is a local martingale w.r.t. (F_t): there are stopping times tau_k increasing to infinity
   (or >= T eventually) a.s. with each stopped process M^{tau_k} a martingale (possibly
   M - M_0 or with M_0 integrable; the standard variants are fine);
 - M has cadlag paths (adapted);
 - E sup_{t <= T} |M_t| < infinity (running supremum integrable).
Conclusion: zero-mean increments: for all 0 <= s <= t <= T, E[M_t - M_s] = 0 (equivalently
E M_t = E M_s; for M_0 = 0, E M_t = 0). A stronger conclusion (M is a true martingale on
[0,T]: E[M_t | F_s] = M_s) is fine (broader).
No constants. The hypothesis must be satisfiable by genuine local martingales (e.g. a constant
or a square-integrable martingale), so non-vacuous. Narrower would be: requiring M to be a
square-integrable martingale already, or continuous paths, or the usual conditions being
replaced by something stronger; or concluding only E M_T = E M_0 instead of all increments.
(The use at (4.x) needs E[M_T] = 0 for M_0 = 0, but the printed claim is all increments.)
Comparison (verdict recorded 2026-10-17T16:01:28Z):
Comparison, sec4_supremum_criterion (Sec4Supremum.lean:32-44).
Setting: any probability space, any filtration indexed by R>=0 (broader than the standing
basis with usual conditions; time [0, infinity) instead of [0,T], with the horizon T a
parameter). M : R>=0 -> Omega -> R real-valued.
Hypotheses: Adapted; a.s. cadlag (right-continuous at every t and left limits at every t; at
t = 0 the left-limit condition is vacuous along the empty filter - harmless); Locally Martingale
(Mathlib's local property: a localizing sequence tau_n with the stopped processes of
1_{tau_n > 0} M martingales - the standard definition of a local martingale, allowing
non-integrable M_0); lintegral of sup_{u <= T} |M_u| < infinity (running supremum integrable).
Conclusion: M t integrable for t <= T and int (M t - M s) dP = 0 for all s <= t <= T: zero-mean
increments on [0,T]. Matches my reading (not the stronger martingale conclusion, which is not
printed).
Witness sec4_supremum_criterion_hypotheses: a coin-flip jump process M_t = xi 1_{t >= 1} that is
a genuine (non-constant) martingale satisfying all hypotheses - non-vacuous.
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-17T16:01:35Z): none
