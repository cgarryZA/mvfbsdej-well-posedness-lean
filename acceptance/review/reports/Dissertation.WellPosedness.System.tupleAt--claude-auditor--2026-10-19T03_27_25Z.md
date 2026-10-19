### A:abstract, A:conclusion, A:cor:robust, A:eq:coefmeas, A:eq:forced, A:eq:mvfbsdej, A:ex:brownian, A:ex:concrete, A:ex:dealer, A:ex:fulllaw, A:intro:limin-comparison, A:intro:mvfbsdej, A:lem:cont, A:lem:lawflow, A:lem:pert, A:lem:small, A:rem:cwp-class, A:rem:generalrank, A:rem:regimes, A:rem:uniq-no-integ, A:sec3:one-null-set, A:sec4:WP-def, A:sec4:horizon-not-contractive, A:sec5:overview, A:sec:examples, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: Dissertation.WellPosedness.System.tupleAt
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash 0b900ec4a75a6b31755afe5c94aee280 (pl-fp-v1:2a7c18adf0bf6d8bba70ddaba8b58e0c6486f760f53be280b2a284ac6dd21d4b)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:27:25Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:13:12Z):
Reading for def:Dissertation.WellPosedness.System.tupleAt (locked before any Lean is shown).

Paper notion (sec 1-2): the H-valued random tuple at time t,
  Theta_t = (X_t, Y_t, Z_t, U_t) : Omega -> H,
X_t in R^n, Y_t in R^m, Z_t in R^{m x d}, U_t in L^2(nu;R^m) (at the current time, not left
limits). If U is stored pointwise (t,omega,e) |-> U_t(omega)(e) in R^m, then U_t(omega) must be the
L^2(nu) class of e |-> U_t(omega,e) (requires int |U_t(omega,e)|^2 nu(de) < inf; junk elsewhere,
harmless on a dt x dP-null set, which holds for U in H^2_N via the Fubini isometry (2.fubiniiso)).
A faithful Lean definition: fun omega => (X t omega, Y t omega, Z t omega, U t omega) in the
paper's H (components in the order x, y, z, u, with the Hilbert-sum structure).
Comparison (verdict recorded 2026-10-19T03:25:28Z):
Comparison for def:Dissertation.WellPosedness.System.tupleAt.

Lean: tupleAt nu X Y Z U s omega = (toLp (i |-> X i s omega), toLp (k |-> Y k s omega),
toLp ((k,j) |-> Z k s omega j), uLift nu (e |-> (k |-> U k s omega e))) : TupleH nu n m d.
- order x, y, z, u and dimensions n, m, m x d (entry (k,j) = row k, column j of Z_s), m-valued
  u: OK.
- current time s, no left limits (left limits are obtained by passing leftLimProc X, leftLimProc Y):
  OK.
- U_s(omega) = the L^2(nu) class of e |-> U_s(omega,e) when square integrable in e, 0 otherwise (uLift).
  For U with finite marked energy this holds for dt x dP-a.e. (s,omega); the junk 0 is taken on a
  null set. OK.
- the target type TupleH (max norm; Hilbert norm via toL2) - see TupleH.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices, harmless:
1. The processes are coordinate families (X : Fin n -> R -> Omega -> R, ..., U pointwise in e), packed
   into H at each (s,omega).
2. The jump channel is uLift, the L^2(nu) class of e |-> U_s(omega,e), and 0 when that function is not
   square integrable. This happens only on a dt x dP-null set for U in H^2_N.
3. The target type TupleH carries the max norm. The Hilbert norm is available through toL2 where
   the paper uses it.
Disagreements with the author's review (shown 2026-10-19T03:25:40Z): none
