### A:cor:robust, A:ex:fulllaw, A:rem:regimes: Dissertation.WellPosedness.System.Coeffs.TupleIndep
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash bb2f84e84c27fd8b0000000000000000 (pl-fp-v1:c0f2579dfd96ec2ea3d8308384eaa6db6c267b6690eb583297b00466aee85c01)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:50:56Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T15:41:48Z):
Reading for def:Dissertation.WellPosedness.System.Coeffs.TupleIndep.

Paper notion (Cor 3.6 second part, Ex 5.4): the perturbations p_b, p_sigma, p_h, p_f are
"independent of theta": p_psi(t, theta, mu) = p_psi(t, mu) for all t, theta, mu (functions of time
and the measure argument only). g is not perturbed in Cor 3.6 (the perturbed system keeps g).

Faithful Lean: a predicate on a coefficient system c: for all t, theta, theta', mu,
c.b t theta mu = c.b t theta' mu, and likewise for sigma, h, f (pointwise, everywhere). Edge cases:
if it also demands that g be independent of x, this is an extra constraint on the perturbation's g
field -- harmless only if the perturbation's g is unused by the perturbed system (the perturbed
system keeps the baseline g) and the propositions can choose it freely (e.g. g = 0). If it is
weaker (e.g. only along diagonal inputs or a.e.), it would make the second clause of Cor 3.6
broader -- acceptable only if the claim still holds (it would, as the proof uses only that delta p
is deterministic along diagonal pairs) -- to be compared with the paper's literal reading.
Comparison (verdict recorded 2026-10-17T15:50:04Z):
Comparison for def:Dissertation.WellPosedness.System.Coeffs.TupleIndep (Robustness/Perturb.lean:94-104):
structure with four fields: for all t theta theta' mu, p.b t theta mu = p.b t theta' mu, and the same
for sigma, h, f. Exactly my reading: pointwise, everywhere, for the four interior coefficients; g is
not constrained (consistent with Cor 3.6, whose perturbed system keeps the baseline g, see
Coeffs.perturb). Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-17T15:50:12Z): none
