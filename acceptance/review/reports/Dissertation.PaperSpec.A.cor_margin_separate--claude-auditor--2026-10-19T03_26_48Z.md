### A:sec3:margin-paragraph: Dissertation.PaperSpec.A.cor_margin_separate
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba1b90f9a7b02bff832 (pl-fp-v1:3ec0f6e08a6405f634c7f271408d79bc6f9d8ec16bbf53873800f4d7a53766af)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:26:48Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:15:07Z):
Reading of spec:Dissertation.PaperSpec.A.cor_margin_separate (paragraph after Corollary 3.6,
clause "finitely many continuous functionals cannot separate the points of an
infinite-dimensional space").

Paper (03-main-results.tex:278-288): "When, moreover, L2(nu) is infinite-dimensional, jump
feedback entering through finitely many functionals of u supplies no margin either, since finitely
many continuous functionals cannot separate the points of an infinite-dimensional space; a margin
then needs feedback dissipative on the whole of L2(nu) ... If L2(nu) is finite-dimensional ...
finitely many functionals can determine u and the second obstruction disappears."

The clause is a general fact used as a justification. Faithful statement:
- Setting: an infinite-dimensional real space V; at minimum the fibre L2(nu; R^m) under the
  hypothesis that it is infinite-dimensional (not FiniteDimensional), or more broadly any
  infinite-dimensional real normed / Hilbert space (broader, and the printed use is the instance
  V = L2(nu)).
- Quantifiers: for every finite family (J in N, phi_1, ..., phi_J : V -> R) of continuous
  functionals,
- Conclusion: there exist u != u' in V with phi_j(u) = phi_j(u') for all j (the family is not
  injective / does not separate points).
On the meaning of "functional": the paper says "continuous functionals", and the use (feedback
of h entering through finitely many functionals of u, e.g. bounded-Lipschitz features as in
Example 5.4) concerns arbitrary, possibly nonlinear, continuous real-valued maps; for linear
functionals continuity is irrelevant (finitely many linear functionals, continuous or not, have a
common kernel of finite codimension), so the word "continuous" is load-bearing only in the
nonlinear reading.  The nonlinear statement is true (restrict to a (J+1)-dimensional subspace and
apply Borsuk-Ulam to the sphere).  A Lean statement restricted to continuous LINEAR functionals
proves a strictly weaker fact (a case lost: nonlinear continuous functionals) and would be
narrower than this reading; I would accept it as faithful only if the paper's usage clearly means
linear functionals, which I do not think it does.
A version that drops "infinite-dimensional" (or uses discontinuous maps) would be false.
J = 0 must be allowed or harmless (then any two distinct points work; V is nontrivial).
Comparison (verdict recorded 2026-10-19T03:18:56Z):
Comparison for spec:Dissertation.PaperSpec.A.cor_margin_separate (Sec3Margin.lean:149-154).

Lean: forall (H : Type v) [NormedAddCommGroup H] [NormedSpace R H], not FiniteDimensional R H ->
  forall (k : N) (F : H -> (Fin k -> R)), Continuous F -> not Function.Injective F.

Against my reading:
- Space: every infinite-dimensional real normed space (covers L2(nu; R^m) whenever it is
  infinite-dimensional, the case the paragraph uses). The paper's "an infinite-dimensional space"
  is generic; real normed spaces are the natural reading (the fibre is a Hilbert space).
- Functionals: a family of k continuous functionals phi_1..phi_k : H -> R is the same as a
  continuous F : H -> (Fin k -> R) (product topology), F = (phi_j)_j. Continuous, NOT necessarily
  linear: this is the general (nonlinear) reading I identified as the paper's, not the weaker
  linear one.
- Conclusion: "cannot separate the points" = F is not injective, i.e. there are u != u' with
  phi_j(u) = phi_j(u') for all j. Matches.
- k = 0 is included (F constant; non-injective because H is nontrivial). Fine.
- Hypothesis "not FiniteDimensional" is load-bearing (the statement is false in finite dimension
  for k >= dim) and is the paper's. It can be met: the witness cor_margin_continuous_hypotheses
  proves not FiniteDimensional R (Lp (EuclideanSpace R (Fin 1)) 2 volume), i.e. L2(nu) with nu
  Lebesgue on R, an intended (infinite-activity) instance.
- The statement is true (Borsuk-Ulam on a (k+1)-dimensional sphere), proved in
  Acceptance/A/Sec3MarginContinuous.lean via Dissertation.Topology.not_injective_of_continuous_of_
  infinite_dimensional (not reviewed here, only that the type is the proposition).
- It is something the paper claims at this revision (03-main-results.tex:283-285).
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-19T03:26:36Z): none
