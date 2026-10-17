### A:cor:robust, A:eq:forced, A:eq:mvfbsdej, A:ex:brownian, A:ex:concrete, A:intro:mvfbsdej, A:lem:bpbsde, A:lem:cont, A:lem:pert, A:lem:small, A:rem:cwp-class, A:rem:generalrank, A:sec2:prp, A:sec3:one-null-set, A:sec4:WP-def, A:sec4:horizon-not-contractive, A:sec:examples, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: LevyStochCalc.Poisson.Compensated.master
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash fe975a59e5bdb39048afe361b1d43cfe (pl-fp-v1:1e1ff443ded58965e921dafaa1dbcabf0f4a93c9c19827df074b80d3d99d8e19)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:16:41Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T15:06:19Z):
Reading (locked before any Lean is shown) — def LevyStochCalc.Poisson.Compensated.master

Paper notion. The paper takes the compensated-Poisson stochastic integral
∫_0^t ∫_E U_s(e) Ñ(ds,de) as standard (Applebaum §4, He–Wang–Yan), for predictable,
P ⊗ E-measurable U with E∫_0^T ||U_s||^2_{L^2(ν)} ds < ∞ (the class HN), and uses: it is a
càdlàg square-integrable (F_t)-martingale; the compensated-Poisson isometry; zero mean; for
U ∈ L^1(dP⊗dt⊗ν) it splits as ∫∫ U dN − ∫∫ U ν(de) ds (used in the proof of Lemma 4.1 for
M^2 and in (eq:compid)/(eq:zeromean)); jumps ΔI_s = U_s(e) at the atoms of N.

The name "master" suggests the master construction of this integral, i.e. the object from
which `process`/`processLp`/`stochasticIntegral` are read off (e.g. a sequence of
approximating stage integrals of simple predictable integrands converging fast, or a
recursive selection of approximants with summable errors, giving an a.s. uniformly
convergent sequence of càdlàg processes). A faithful Lean definition must make the object
it builds, for every integrand of the class HN, converge (in L^2(Ω) at each t, and a.s.
uniformly on [0,T] for the càdlàg version) to the L^2-isometric extension of the elementary
integral Σ ξ_i Ñ((s_i,t_i]×A_i) (ξ_i bounded F_{s_i}-measurable, ν(A_i) < ∞). Junk values
for integrands outside the class (not predictable or not square integrable) are harmless
only if no proposition evaluates the integral there (propositions must assume U ∈ HN or
equivalent). Any choice made (e.g. via Classical.choose of approximants) must not change
the resulting integral beyond a null set / indistinguishability.
Comparison (verdict recorded 2026-10-17T15:15:52Z):
Comparison — master (LevyStochCalc/Poisson/CompensatedApprox.lean:309-320)

Lean: for an integrand φ : Ω → ℝ → E → ℝ that is jointly measurable, marked progressively
measurable for ℱ, and square integrable on every [0,T] (∫⁻ω∫⁻_{[0,T]}∫⁻_E |φ|^2 < ∞), master n
is a level ℓ_n and an ℱ-adapted mark-step integrand on the dyadic grid of [0, 2^n] at level ℓ_n,
chosen (Classical.choose) from exists_stage: stageErr φ P n G < (n+1)^{-1} and ℓ_{n+1} ≥ ℓ_n+1.
MarkStep (MarkStepIsometry.lean:73-112): Σ_i 1_{(p_i,p_{i+1}]}(s) Σ_k ξ_{ik}(ω) 1_{B_k}(e) with
ν(B_k) < ∞, ξ bounded measurable; Adapted: ξ_{ik} is ℱ(p_i)-measurable — these are the simple
predictable integrands of the elementary compensated integral.

Against my reading:
- It is the approximating-sequence construction I expected: simple predictable integrands
  converging in L^2(dP ⊗ dt ⊗ ν) on growing horizons [0,2^n] (→ ∞), squared error < 1/(n+1)
  (→ 0). The stage integrals at fixed t are then Cauchy in L^2(P) (stageLp_cauchySeq, via the
  elementary isometry; bound 2/(n+1)+2/(n'+1)), so the limit is the L^2-isometric extension.
- The choice via Classical.choose does not affect the limit: any two L^2-approximating
  sequences of simple predictable integrands have the same limit integral by the isometry.
- Integrand class: marked progressively measurable (plus joint measurability, plus square
  integrability on every horizon), which is broader than the paper's predictable class HN. On
  predictable integrands the approximants and their limit are the classical ones; for
  progressive integrands the construction gives the integral of their (dt⊗dP⊗ν-a.e. equal)
  predictable version — the standard L^2-closure extension. Consistent with the paper.
- Real-valued integrands; the paper's ℝ^n/ℝ^m-valued integrands are integrated componentwise
  elsewhere. Time domain ℝ; the paper's integrands on [0,T] enter extended (by 0) beyond T.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices of master, and why each is harmless:
1. Choice of approximants by Classical.choose (exists_stage): the integral built from them
   (processLp, process, stochasticIntegral) is independent of the choice, because two
   approximating sequences in L^2(dP⊗dt⊗ν) give the same L^2(P) limit by the elementary isometry.
2. Horizons 2^n with squared error < 1/(n+1) and strictly increasing dyadic levels: horizons
   exhaust [0,∞) and errors tend to 0, which is all the L^2 extension needs; the level growth is
   only used to compare stages on a common refinement.
3. Integrand class = jointly measurable, marked progressively measurable, square integrable on
   every [0,T]: broader than the paper's predictable HN; on predictable integrands it is the
   classical approximation, and on progressive ones it yields the integral of the a.e.-equal
   predictable version (standard L^2-closure extension), so no paper integral changes.
4. Scalar (ℝ-valued) integrands on time ℝ: the paper's vector integrands are handled
   coordinatewise, and integrands on [0,T] are extended by 0.
Disagreements with the author's review (shown 2026-10-17T15:15:58Z): The author's review, as shown by rv.py author, consists of the review marker only (no reading text, no item-by-item comparison), so there is no stated position of the author to disagree with on substance.
I agree that the definition is acceptable, but the review does not record what I consider
needed for it: the approximants are chosen by Classical.choose (harmless because the limit
integral does not depend on the choice), and the integrand class is marked progressively
measurable — broader than the paper's predictable class — on which the construction gives the
integral of the a.e.-equal predictable version.
