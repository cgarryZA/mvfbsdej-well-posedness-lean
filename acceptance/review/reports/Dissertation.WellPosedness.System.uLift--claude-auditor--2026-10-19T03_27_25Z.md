### A:abstract, A:conclusion, A:cor:robust, A:eq:coefmeas, A:eq:forced, A:eq:mvfbsdej, A:ex:brownian, A:ex:concrete, A:ex:dealer, A:ex:fulllaw, A:intro:limin-comparison, A:intro:mvfbsdej, A:lem:cont, A:lem:lawflow, A:lem:pert, A:lem:small, A:rem:cwp-class, A:rem:generalrank, A:rem:regimes, A:rem:uniq-no-integ, A:sec3:one-null-set, A:sec4:WP-def, A:sec4:horizon-not-contractive, A:sec5:overview, A:sec:examples, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: Dissertation.WellPosedness.System.uLift
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash 20342aeccd26489f2122117451a2a160 (pl-fp-v1:e386d13184bf79f7ab054f856c9963d00825a5592f446350b4fb573085bb9bee)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:27:25Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:13:12Z):
Reading for def:Dissertation.WellPosedness.System.uLift (locked before any Lean is shown).

Paper notion. The name suggests the lift of a pointwise jump integrand U : [0,T] x Omega x E -> R^m
(P x E-measurable) to the L^2(nu;R^m)-valued process (t, omega) |-> U_t(omega, .) in L^2(nu),
i.e. the Fubini isometry (2.fubiniiso) L^2(P x E) ~= L^2(P; L^2(nu)) read pointwise (Lemma A.1
step 1: "the induced map (t,omega) |-> U_t(omega,.) admits a predictable, strongly measurable
L^2(nu)-valued representative"); or the analogous lift of a pointwise u : E -> R^m to its class
in L^2(nu).
A faithful Lean definition: for (t,omega) with int_E |U_t(omega,e)|^2 nu(de) < inf (and
measurability in e), the nu-a.e. class of e |-> U_t(omega,e) in Lp R^m 2 nu; elsewhere a junk value
(0), harmless when U is square-integrable for dt x dP x nu (the exceptional set is then
dt x dP-null). It must not alter values (no truncation), and must use the same nu as the PRM.
If uLift is instead something else (e.g. lifting a law), the reading is: whatever it is, it must
be the identification above without change of values.
Comparison (verdict recorded 2026-10-19T03:25:28Z):
Comparison for def:Dissertation.WellPosedness.System.uLift.

Lean: uLift nu u = if MemLp (e |-> toLp (u e)) 2 nu then (that MemLp).toLp else 0, for u : E -> R^iota.
This is the second form of my reading (lift of a pointwise u : E -> R^m to its class in L^2(nu));
applied in tupleAt with u = (e |-> U_s(omega,e)) it gives the (t,omega)-indexed lift of the first form.
- class of e |-> u(e) in Lp (EuclideanSpace R iota) 2 nu, same nu: OK; no truncation, values
  unchanged.
- junk 0 when u is not square integrable (or not a.e.-strongly measurable): harmless on the
  dt x dP-null set where it happens for U in H^2_N; proved bound ||uLift u||^2 <= sum_k int u_k^2 with
  equality when square integrable (enorm_uLift_sq_le).
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choice, harmless: uLift returns 0 when e |-> u(e) is not square integrable, and the
exact L^2(nu) class otherwise. Along a jump integrand of finite marked energy the junk branch is
taken only on a dt x dP-null set of (s,omega), and that set does not affect any time integral or
any law at a.e. time.
Disagreements with the author's review (shown 2026-10-19T03:25:40Z): none
