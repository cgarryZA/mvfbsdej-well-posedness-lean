### A:rem:margin: Dissertation.PaperSpec.A.rem_margin_smaller
Pins: manuscript A None; project 41c425269e86e5256d3fe5eb969b63186bcd80a2; hash ed839d34f480cba133faa12dcf2189f6 (pl-fp-v1:5cb9106616368814fa98002328b875b673d3e6bdc96744ba4b4a8738326070d4)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T18:47:31Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T18:41:21Z):
# Reading of Remark 2.11 (rem:margin), clause "the unweighted margin c/c_G is smaller than c when
# c_G > 1" (sections/02-model-assumptions.tex:288ff.), locked before any Lean

## The passage
"When m=n both G and G^T are injective, so the bounds of Assumption 2.4 (ass:G), applied channel by
channel, give c(|G^T dY|^2+|G^T dZ|_F^2+||G^T dU||^2+|G dX|^2) >= (c/c_G)(|dY|^2+...+|dX|^2).
A margin c in (monomargin) therefore yields the margin c/c_G, which is smaller than c when
c_G > 1, in the unweighted form ..."

The clause under review is only the comparison "c/c_G is smaller than c when c_G > 1". (The
"yields the margin c/c_G in the unweighted form" part is a separate clause, rem_margin_unweighted.)

## Notions
- c > 0: the margin of (monomargin) (a positive real).
- c_G := s_min(G)^{-2} for a full-rank G in R^{m x n} (Assumption 2.4); here m = n so G is
  invertible and s_min(G) > 0, c_G > 0 finite. c_G > 1 iff s_min(G) < 1.

## What a faithful formal statement must contain
- Hypotheses: c > 0; c_G > 1. Either c_G an arbitrary real (then the statement is the bare
  arithmetic fact and covers every paper instance c_G = s_min(G)^{-2}; conversely every real
  c_G > 1 arises from some square full-rank G, e.g. G = c_G^{-1/2} I, so this is equivalent, a
  representation choice), or c_G := s_min(G)^{-2} for a full-rank square (m = n) real matrix G,
  with s_min the smallest singular value.
- Conclusion: the STRICT inequality c / c_G < c. A non-strict c/c_G <= c would be weaker than
  printed ("smaller"); an "iff" would be stronger than printed (the paper only says "when").
- If c_G is built from G in Lean: check the definition of s_min / c_G (e.g. via eigenvalues of
  G^T G, operator-norm of inverse, sInf of |Gx| over unit sphere), check junk: s_min = 0 gives
  0^{-2} = 0 in Lean (0^{-1} = 0), so c_G = 0 would not satisfy c_G > 1 - harmless; check that
  the case m = n is included (a statement restricted to, say, m > n would lose the paper's case).
- The sign of c matters: for c <= 0 the conclusion fails (c/c_G >= c), so c > 0 must be a
  hypothesis (the paper has margin c > 0). c_G > 1 also needed (c_G = 1 gives equality).
- No constants, no probabilistic setting is needed; a statement that embeds this in the full
  setting (coefficients, G, (monomargin) hypotheses) would be fine as long as it still concludes
  c/c_G < c and its hypotheses can be met (witness: e.g. c = 1, G = (1/2) I_n, c_G = 4).
- Is it a claim of the paper at this revision: yes, the sentence "which is smaller than c when
  c_G>1" is in Remark 2.11 as vendored.
- Coverage of the claim A:rem:margin (to be checked after show): the passage's mathematical claims
  as I read them are (i) definition of "holds with margin c" (monomargin) and of the unweighted
  form (monomarginu) (definitions, not claims); (ii) reduction: if the interior pairing is bounded
  with constants bar-beta_1, bar-beta_2, then for every 0 < c < min{bar-beta_1, bar-beta_2} the same
  bound is (monomargin) with beta_i := bar-beta_i - c and margin c; (iii) the prose "recording weaker
  constants turns the difference into slack, which a perturbation raising the interior pairing by
  at most the margin leaves intact" (a perturbation claim: if the pairing of a perturbed system
  exceeds the original by at most c E[sum of G-weighted squares], it still satisfies the
  monotonicity with beta_i); (iv) when m = n, c(weighted sum) >= (c/c_G)(unweighted sum)
  pointwise, hence a margin c in (monomargin) yields margin c/c_G in (monomarginu);
  (v) c/c_G < c when c_G > 1.
Comparison (verdict recorded 2026-10-19T18:46:57Z):
# Comparison: Dissertation.PaperSpec.A.rem_margin_smaller vs Remark 2.11, clause "the unweighted
# margin c/c_G is smaller than c when c_G > 1" (02-model-assumptions.tex:288ff.)

Reviewer: claude-auditor (same model family as the statements' author).

Lean:
  forall (n : N) (G : Matrix (Fin n) (Fin n) R) (c : R), 0 < n -> G.rank = min n n -> 0 < c ->
    1 < (sMin G ^ 2)^{-1} -> c / (sMin G ^ 2)^{-1} < c

Item by item against my locked reading:
- Context m = n: G is square n x n, n >= 1 (standing n >= 1), full rank (Assumption 2.4 with m = n).
  The passage's sentence is in its "When m = n" case, which is the only case in which the margin
  c/c_G is produced; nothing of the passage is lost.
- c_G: `(sMin G ^ 2)^{-1}` = s_min(G)^{-2}, the paper's definition (Assumption 2.4). `sMin G` is the
  square root of the least eigenvalue of G^T G (branch n <= m, taken here since m = n), i.e. the
  smallest singular value; for n >= 1 the infimum is over a nonempty finite index set, so no junk.
  Junk check: a singular G would give sMin = 0 and (0^2)^{-1} = 0 in Lean, which fails 1 < c_G, so
  the full-rank hypothesis is even redundant; no spurious instances.
- Hypotheses c > 0 (margin is positive) and c_G > 1: present, exactly the "when".
- Conclusion: strict `c / c_G < c`, the paper's "smaller than c". Not weakened to <=, not
  strengthened to an iff.
- No constants or quantifier-order issues; no probabilistic setting is needed for this clause (the
  "yields the margin c/c_G in the unweighted form" part is the separate clause
  rem_margin_unweighted, which uses the same c/(sMin G^2)^{-1}).
- Breadth: over all square full-rank G with c_G > 1 and all c > 0 - exactly the paper's range
  (every real c_G > 1 occurs, e.g. G = c_G^{-1/2} I). Neither broader nor narrower.
- Witness `Dissertation.Acceptance.A.rem_margin_smaller_hypotheses`: n = 1, G = (1/2) I_1 (full rank,
  c_G = 4 > 1), c = 1 > 0; these are exactly the statement's hypotheses, at a coupling matrix the
  paper's Assumption 2.4 admits. Non-vacuous.
- Claimed at this revision: yes, "which is smaller than c when c_G>1" is in Remark 2.11 as vendored
  (rv.py says revision f598204, the Lean header cites 1f67672; I read the vendored sources).

Verdict: faithful.

## Coverage of A:rem:margin (clauses rem_margin_reduce, rem_margin_unweighted, rem_margin_smaller)
Read from acceptance/claims.json after show. The passage's mathematical content at this revision:
(a) the definitions of "(2.7) holds with margin c" (2.12) and of the unweighted form (2.13) -
definitions, carried by Margin212 / Margin213; (b) the reduction "a bound with constants
bar-beta_1, bar-beta_2 is (2.12) with beta_i = bar-beta_i - c and margin c for every
0 < c < min{bar-beta_1, bar-beta_2}" - clause rem_margin_reduce; (c) for m = n, G and G^T injective and
channel by channel c(weighted sum) >= (c/c_G)(unweighted sum), hence margin c in (2.12) yields margin
c/c_G in (2.13) - clause rem_margin_unweighted (its pointwise inequality and the injectivity are the
justification of that clause, not separate claims); (d) c/c_G < c when c_G > 1 - clause
rem_margin_smaller. One assertion is not a clause: "recording weaker constants turns the difference
into slack, which a perturbation raising the interior pairing by at most the margin leaves intact",
i.e. if a perturbed system's interior pairing exceeds the original's by at most
c E[|G^T dY|^2 + |G^T dZ|_F^2 + ||G^T dU||^2 + |G dX|^2], it still satisfies (2.7) with beta_i. It is a
one-line consequence of (2.12) (add the two inequalities), worded as motivation, and its quantitative
use is in the perturbation result of section 3 (which, per PairingBound34, uses the unweighted
form); I would accept it as expository, but the inventory should record that decision (a scope note
on the claim) rather than leave it implicit. No clause states something the passage no longer
claims: all three clause names match sentences present in the vendored Remark 2.11.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-19T18:47:22Z): No disagreement with the verdict (faithful), but the review shown for this unit is not a review of
it. The entry at acceptance/review/A.md:2233 reads only "Review by claude-auditor: faithful (report
reports/Dissertation.PaperSpec.A.rem_margin_unweighted--claude-auditor--...md)": it names the report
of a different proposition, rem_margin_unweighted, and records nothing about rem_margin_smaller
itself - no passage, no item-by-item reading (square G for the m = n case, c_G = (sMin G^2)^{-1},
hypotheses c > 0 and c_G > 1, strict conclusion), and no witness
(Dissertation.Acceptance.A.rem_margin_smaller_hypotheses, G = (1/2) I_1, c_G = 4, c = 1). If the marker
for rem_margin_smaller rests on that entry, it points at evidence for another statement and should
be replaced by a review of this proposition (e.g. this report). (I did not open the cited report,
as the protocol forbids reading acceptance/review/reports/.)
