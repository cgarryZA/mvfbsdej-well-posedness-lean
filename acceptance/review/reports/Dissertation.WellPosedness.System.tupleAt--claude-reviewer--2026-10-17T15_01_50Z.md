### A:cor:robust, A:eq:coefmeas, A:eq:forced, A:eq:mvfbsdej, A:ex:concrete, A:intro:mvfbsdej, A:lem:cont, A:lem:lawflow, A:lem:pert, A:lem:small, A:rem:cwp-class, A:rem:generalrank, A:sec2:coefmeas, A:sec3:one-null-set, A:sec4:WP-def, A:sec4:horizon-not-contractive, A:sec:examples, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: Dissertation.WellPosedness.System.tupleAt
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 0b900ec4a75a6b31755afe5c94aee280 (pl-fp-v1:2a7c18adf0bf6d8bba70ddaba8b58e0c6486f760f53be280b2a284ac6dd21d4b)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:01:50Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:34:23Z):
Reading for def:Dissertation.WellPosedness.System.tupleAt (written before seeing any Lean).

Paper notion. Theta_t = (X_t, Y_t, Z_t, U_t), the solution tuple at time t, as an H-valued
random variable omega |-> (X_t(omega), Y_t(omega), Z_t(omega), U_t(omega)) in
H = R^n x R^m x R^{m x d} x L^2(nu;R^m); the coefficients b, sigma, f are evaluated at
(t, Theta_t, mu_t) with mu_t = Law(Theta_t). (The jump coefficient uses the predictable version
Theta_t^- = (X_{t-}, Y_{t-}, Z_t, U_t); "tupleAt" is the non-left-limit version, unless it
takes a parameter.) Inside dt-integrals the two agree dt x dP-a.e. (Section 4 preamble).

A faithful Lean definition must:
- put X_t, Y_t, Z_t, U_t in the X, Y, Z, U slots respectively, all at the same time t;
- take U_t(omega) as the element of L^2(nu;R^m) given by e |-> U_t(omega,e) (via the fibre lift,
  with a junk value where \int|U_t(omega,e)|^2 nu(de) = infinity; this set is dt x dP-null when
  E\int\int|U|^2 < infinity, so harmless for time-integrated or a.e.-t statements, and for the law
  mu_t at a.e. t);
- if it also covers Theta_t^-, use left limits of X and Y only (Z, U untouched).
Comparison (verdict recorded 2026-10-17T12:39:11Z):
Comparison for System.tupleAt.
Lean: tupleAt ν X Y Z U s ω := (toLp (i ↦ X i s ω), toLp (k ↦ Y k s ω), toLp ((k,j) ↦ Z k s ω j),
uLift ν (e ↦ k ↦ U k s ω e)) : TupleH ν n m d, for coordinate processes X : Fin n → ℝ → Ω → ℝ,
Y : Fin m → …, Z : Fin m → ℝ → Ω → Fin d → ℝ, U : Fin m → ℝ → Ω → E → ℝ.
- X_s, Y_s, Z_s, U_s go into the X, Y, Z, U slots, all at the same time s. Matches.
- Z_s ∈ ℝ^{m×d}, with row k and entry j, as EuclideanSpace on Fin m × Fin d (Frobenius). Matches.
- U_s(ω) is the L²(ν;ℝ^m) class of e ↦ (U_{k,s}(ω,e))_k via uLift, and 0 when it is not square
  integrable. As in my reading, the exceptional (s,ω)-set is dt⊗dP-null under
  E∫∫|U|² < ∞, so this is harmless for time-integrated statements and for laws at a.e. s.
  Statements "for every s" about the U-channel would see the junk.
- tupleAt is the non-left-limit Θ_s. Θ_s^- is a separate definition (TupleLeft.lean, not reviewed
  here).
- Time is all of ℝ (no restriction to [0,T]). The coefficient processes restrict to [0,T] by
  indicators (Solves.lean). Harmless.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices. (1) The processes are given as real coordinate processes (X i, Y k, rows
Z k with entries j, U k with marks e) and assembled into H by WithLp.toLp 2 (Euclidean,
Frobenius) and uLift. (2) The jump channel is the L²(ν) class of e ↦ U_s(ω,e), with the junk
value 0 where that function is not square integrable. Under the paper's integrability
E∫_0^T∫_E|U|² dν dt < ∞ this exceptional set is dt⊗dP-null. So it changes neither the
time-integrated identities nor the law μ_s for a.e. s. That is the paper's own reading, through
predictable representatives (eq:fubiniiso, Lemma A.1). (3) Time ranges over ℝ, and the
statements restrict to [0,T].
Disagreements with the author's review (shown 2026-10-17T15:01:22Z): No disagreement on the substance. The author's entry (acceptance/review/definitions.md) records only the review marker and no comparison with the paper, so it does not state what I relied on: the U-channel goes through uLift, with junk 0 on a dt⊗dP-null set under the paper's integrability, and Θ_s^- is a separate definition.
