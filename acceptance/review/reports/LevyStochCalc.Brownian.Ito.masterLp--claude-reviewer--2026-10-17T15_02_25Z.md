### A:cor:robust, A:eq:forced, A:eq:mvfbsdej, A:ex:brownian, A:ex:concrete, A:intro:mvfbsdej, A:lem:bpbsde, A:lem:cont, A:lem:pert, A:lem:small, A:rem:cwp-class, A:rem:generalrank, A:sec2:prp, A:sec4:WP-def, A:sec4:horizon-not-contractive, A:sec:examples, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: LevyStochCalc.Brownian.Ito.masterLp
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash ed9f750f32d4e782710be84c23dfa758 (pl-fp-v1:6d57f8db513cd07ebfd9da0d7eb8f2e4483373d28553505545bd94fb06876627)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:02:25Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:34:25Z):
Reading for def:LevyStochCalc.Brownian.Ito.masterLp (written before seeing any Lean).

Paper notion. Not named in the paper; part of the Ito integral construction: the integrand Z
regarded as an element of the L^2 space of the energy measure dt x dP on [0,T] x Omega (with
the predictable/progressive sigma-algebra), i.e. H^2_W as an L^2 space, in which simple
predictable integrands are dense and the isometry extends. "masterLp" is presumably either (a)
the L^2(P)-element of the limiting integral (the isometric extension of the simple integral from
the dense subspace to the closure, valued in L^2(Omega, F_T, P)), or (b) the Lp class of the
integrand.

A faithful Lean definition must:
- in case (a), be the image of Z under the unique continuous linear (isometric) extension of the
  simple-integral map Z^k |-> int Z^k dW, i.e. the L^2(P)-limit of the simple integrals of an
  approximating sequence, computed at the right time t (or T) — equivalently lim in L^2(P) of
  simpleIntegral of masterApprox;
- in case (b), be the a.e.-class of (t,omega) |-> Z_t(omega) in L^2(energyMeasure);
- junk value for non-square-integrable Z harmless only where guarded.
Comparison (verdict recorded 2026-10-17T15:01:16Z):
Comparison for Ito.masterLp.
Lean: masterLp t n := the L²(P) class of ω ↦ simpleIntegral W (masterApprox n) t ω if
0 ≤ t ≤ n+1, and 0 otherwise. The Itô integral's L² element is
stochasticIntegralBrownianLp t = limUnder atTop (masterLp t ·).
- This is the n-th term of the sequence of L²(P) elements of the simple integrals of the
  approximants, case (a) of my reading but before the limit. The membership in L² uses the
  adaptedness masterApprox_adapt and the Brownian filtration. The sequence is proved Cauchy at each
  t ≥ 0 (masterLp_cauchySeq), and its limit is the integral. Matches the construction.
- Junk 0 for t > n+1. For a fixed t only finitely many n are affected, so the limit is unaffected.
  For t < 0 every term is 0, and so is the integral (convention: ∫_0^t = 0 for negative t, outside
  the paper's range).
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices. masterLp t n is the L²(P) class of the n-th master simple integral at
time t, and 0 when t ∉ [0, n+1]. The junk 0 for t > n+1 affects only finitely many terms at each
fixed t, so it does not change the limit stochasticIntegralBrownianLp t. The value 0 for t < 0 is
a convention outside the paper's time range [0,T].
Disagreements with the author's review (shown 2026-10-17T15:01:53Z): No disagreement on the substance. The author's entry (acceptance/review/definitions.md) records only the review marker, or a section heading, and no comparison with the paper. It does not state the points I relied on: the n-th term is the L² class of the n-th master simple integral at t, with junk 0 for t > n+1 that does not affect the limit at a fixed t.
