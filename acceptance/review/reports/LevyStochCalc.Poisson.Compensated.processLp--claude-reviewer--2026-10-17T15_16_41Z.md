### A:cor:robust, A:eq:forced, A:eq:mvfbsdej, A:ex:brownian, A:ex:concrete, A:intro:mvfbsdej, A:lem:bpbsde, A:lem:cont, A:lem:pert, A:lem:small, A:rem:cwp-class, A:rem:generalrank, A:sec2:prp, A:sec3:one-null-set, A:sec4:WP-def, A:sec4:horizon-not-contractive, A:sec:examples, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: LevyStochCalc.Poisson.Compensated.processLp
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash f8fb86e34b629e10db696374a7fa3068 (pl-fp-v1:4bccea42472b4503009636424d9ee6d6736997f4f85430264d699fae10cfb7ac)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:16:41Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T15:06:20Z):
Reading (locked before any Lean is shown) — def LevyStochCalc.Poisson.Compensated.processLp

Paper notion. The compensated-Poisson stochastic integral at a fixed time t, as an element of
L^2(Ω, F_t, P) (an a.e. class): I_t(U) = ∫_0^t ∫_E U_s(e) Ñ(ds,de), the L^2-limit of
elementary integrals of simple predictable integrands approximating 1_{(0,t]} U in
L^2(dt ⊗ dP ⊗ ν). This is how the paper reads the "almost surely for every t" identities
before taking a càdlàg version.

Faithful Lean definition: for each t, the element of Lp (p=2) of Ω equal to the image of
1_{(0,t]}U (or of U restricted to [0,t]) under the isometric extension of the elementary
compensated integral; so that E|I_t|^2 = E ∫_0^t ||U_s||^2_{L^2(ν)} ds, linear in U, and on
elementary integrands ξ 1_{(a,b]×A} (ξ bounded F_a-measurable, ν(A) < ∞) it equals
ξ (N((a∧t, b∧t] × A) − (b∧t − a∧t) ν(A)). Junk value (e.g. 0) for integrands not in the
class is harmless only if propositions assume the class. Time interval convention (0,t] vs
[0,t]: Lebesgue-null difference, harmless.
Comparison (verdict recorded 2026-10-17T15:15:52Z):
Comparison — processLp (LevyStochCalc/Poisson/CompensatedProcess.lean:98-101)

Lean: processLp t := limUnder atTop (n ↦ stageLp t n) in Lp ℝ 2 P, where stageLp t n is the
L^2 class of the elementary compensated integral up to time t of the stage-n approximant.
stageLp_tendsto (needs hℱ) proves the sequence converges to processLp t; it is Cauchy because
for 2^n ≥ t the difference of stages n ≤ n' has E|·|^2 ≤ 2/(n+1) + 2/(n'+1).

Against my reading:
- The L^2 limit of elementary integrals of simple predictable approximants of 1_{(0,t]}φ —
  matches the isometric extension I required, and it is independent of the choice of
  approximants (isometry).
- Elementary formula: Σ ξ_{ik} Ñ((p_i∧t, p_{i+1}∧t] × B_k), Ñ = N − dt⊗ν: matches.
- t ≤ 0: all stage integrals vanish, limit 0 (process_ae_zero_of_nonpos).
- Junk case: processLp does not itself take hℱ; if ℱ is not a Poisson filtration for N the
  sequence need not converge and limUnder returns an arbitrary element. Every use I found
  (process, stochasticIntegral, and through them the propositions) carries hℱ, so the
  definition is only read where it is the limit.
- Integrand class marked progressive (broader, consistent).
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices of processLp, and why each is harmless:
1. Defined by limUnder of the stage L^2 integrals: where N is a Poisson random measure for ℱ
   (IsPoissonFiltration) the sequence is Cauchy and limUnder is its limit, the L^2-isometric
   integral; without that hypothesis limUnder may be junk, but the definition is used only
   through process / stochasticIntegral, which require IsPoissonFiltration.
2. Integrand class marked progressive (broader than predictable, agreeing with the classical
   integral on predictable integrands); real valued; time ℝ, value 0 at t ≤ 0.
Disagreements with the author's review (shown 2026-10-17T15:15:58Z): The author's review, as shown by rv.py author, consists of the review marker only (no reading text, no item-by-item comparison), so there is no stated position of the author to disagree with on substance.
Not recorded there: processLp takes no IsPoissonFiltration hypothesis, so for a filtration that
is not a Poisson filtration for N its limUnder may be junk; it is meaningful only through
process / stochasticIntegral, which require that hypothesis.
