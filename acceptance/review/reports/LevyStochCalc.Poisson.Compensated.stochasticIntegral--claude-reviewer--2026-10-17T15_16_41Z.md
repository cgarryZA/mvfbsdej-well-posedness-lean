### A:cor:robust, A:eq:forced, A:eq:mvfbsdej, A:ex:brownian, A:ex:concrete, A:intro:mvfbsdej, A:lem:bpbsde, A:lem:cont, A:lem:pert, A:lem:small, A:rem:cwp-class, A:rem:generalrank, A:sec2:prp, A:sec3:one-null-set, A:sec4:WP-def, A:sec4:horizon-not-contractive, A:sec:examples, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: LevyStochCalc.Poisson.Compensated.stochasticIntegral
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 0f01c66ebd3c9ea16c0e39e9314f702b (pl-fp-v1:6fd30271fc393d5c4a15e6e95925dccacdec5c2a332756d913ac5f1abd17431b)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:16:41Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T15:06:20Z):
Reading (locked before any Lean is shown) — def LevyStochCalc.Poisson.Compensated.stochasticIntegral

Paper notion. The compensated-Poisson stochastic integral ∫∫ U_s(e) Ñ(ds,de) of a predictable
(P ⊗ E-measurable) integrand U ∈ L^2(dt⊗dP⊗ν), with respect to the compensated PRM
Ñ = N − dt ν of (§2), relative to the filtration (F_t). Standard construction: on elementary
integrands U = ξ 1_{(a,b]}(s) 1_A(e), ξ bounded F_a-measurable, ν(A) < ∞, it is
ξ·(N((a,b]×A) − (b−a)ν(A)); linear; isometric E|∫∫U dÑ|^2 = E∫∫|U|^2 ν(de) ds; extended
by continuity (density of elementary integrands in L^2(P⊗E, dt⊗dP⊗ν)). Equivalent pathwise
description for U ∈ L^1 ∩ L^2: ∫∫U dN − ∫∫ U ν(de) ds.

Faithful Lean definition: the continuous linear isometry L^2(markedPredictable, dt⊗dP⊗ν) →
L^2(Ω) agreeing with the elementary formula (or an equivalent characterisation), over the
paper's filtration and PRM; for vector-valued U (values in ℝ^n, ℝ^m) componentwise or
directly in a Hilbert space. Whether it is the whole-line integral or the integral over [0,T]
/ [0,t] must be read from usage. Junk values outside the class harmless only if not used.
The PRM's intensity must be dt ⊗ ν (matching the compensator subtracted).
Comparison (verdict recorded 2026-10-17T15:15:52Z):
Comparison — stochasticIntegral (LevyStochCalc/Poisson/Compensated.lean:81-85)

Lean: stochasticIntegral N ℱ hℱ φ h_meas h_progMeas h_sq_int_global : ℝ → Ω → ℝ is
Classical.choose of exists_cadlag_modification: a process Y adapted to ℱ.rightCont, with
Y t = process t P-a.e. for every t, and P-a.e. path right-continuous with left limits at every
t ∈ ℝ. Integrand φ : Ω → ℝ → E → ℝ real valued, jointly measurable, marked progressively
measurable for ℱ, square integrable on every [0,T]; needs IsPoissonFiltration N ℱ.

Against my reading (the compensated-Poisson integral ∫_0^t∫_E U dÑ of a square-integrable
predictable integrand, càdlàg square-integrable martingale, isometry, compensator dt⊗ν):
- Value at each t: a.s. the L^2-isometric extension of the elementary integral
  ξ(N((a,b]×A) − (b−a)ν(A)) (via process = processLp a.e.) — matches; it is a time-indexed
  process (the argument named T is the time).
- Elementary integrals use Ñ = N − dt⊗ν with the PRM's referenceIntensity — matches.
- Path regularity: a.s. càdlàg modification — matches the paper's use (càdlàg sides of the
  identities, t-independent null set); any two such choices are indistinguishable, so the
  propositions' "a.s. for all t" identities do not depend on the choice.
- Adaptedness: to ℱ.rightCont rather than ℱ. The paper's filtration (enlJoint, the usual
  augmentation) is right-continuous (isRightContinuous_enlJoint), so this is ℱ there.
- Integrand class: marked progressive instead of predictable — broader; on predictable
  integrands it is the classical integral; for progressive ones it is the integral of the
  a.e.-equal predictable version (the standard L^2 extension). The paper's integrands U, q^h and
  h(s,Θ^-_s,e,μ^-_s) are predictable, hence in the class (MarkedPredictable implies marked
  progressive, used as hU.markedProgressivelyMeasurable in the specs).
- Real valued, time ℝ; the paper's vector-valued integrands are integrated componentwise; the
  hypotheses demand square integrability on every horizon, met by integrands vanishing off
  [0,T] (as the specs arrange).
- Time interval (0,t]: equals ∫_0^t (the paper's) — the time 0 point is dt- and N-null.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices of stochasticIntegral, and why each is harmless:
1. A chosen (Classical.choose) a.s.-càdlàg modification of the L^2 integral process: two such
   modifications are indistinguishable, so no statement "a.s., for all t" depends on the choice.
2. Adapted to ℱ.rightCont: equal to ℱ for the paper's right-continuous augmented filtration.
3. Integrand class marked progressively measurable (with joint measurability and square
   integrability on every horizon), broader than the paper's predictable class; it agrees with
   the classical integral on predictable integrands and equals the integral of the a.e.-equal
   predictable version otherwise, so every paper integral keeps its value.
4. Scalar integrands on time ℝ, integral over (0,t]; vector integrands are handled
   componentwise and integrands on [0,T] are extended by 0.
Disagreements with the author's review (shown 2026-10-17T15:15:58Z): The author's review, as shown by rv.py author, consists of the review marker only (no reading text, no item-by-item comparison), so there is no stated position of the author to disagree with on substance.
Not recorded there, and in my view needed: the integral is adapted to ℱ.rightCont (equal to ℱ
only for a right-continuous filtration such as the paper's enlJoint); it is a chosen a.s.-càdlàg
modification (choice-independent up to indistinguishability); the integrand class is marked
progressively measurable rather than predictable (broader, consistent on predictable
integrands); and integrands are scalar and must be square integrable on every horizon.
