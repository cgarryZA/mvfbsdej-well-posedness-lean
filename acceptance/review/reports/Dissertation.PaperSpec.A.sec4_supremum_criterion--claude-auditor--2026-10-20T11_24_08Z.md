### A:sec4:supremum-criterion: Dissertation.PaperSpec.A.sec4_supremum_criterion
Pins: manuscript A None; project d3e594defeeeb94a6d05c33c666bcb870d584302; hash ed839d34f480cba1f588c2071f5242ff (pl-fp-v1:668939571700f8b456579ffca8e5ba6bd4a5ecc7ce80e70d20901f671b16ef0c)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-20T11:24:08Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-20T11:09:24Z):
# Reading: sec4_supremum_criterion — Section 4 preamble ("supremum criterion")

Passage (04-proof-wellposedness.tex, preamble): "By localisation and dominated convergence, a
cadlag local martingale whose running supremum is integrable has zero-mean increments (the
supremum criterion below)." Used for real-valued stochastic integrals M on [0,T] w.r.t. the
standing filtration, to get E[M_T - M_t] = 0.

Faithful statement. Setting: a filtered probability space (the standing one, or any filtered
probability space; the usual conditions are available in the paper), horizon T > 0 (or time
set [0,infinity) restricted to [0,T]). M : [0,T] x Omega -> R (real-valued; vector-valued is a
harmless broadening) adapted with cadlag paths, a local martingale: there are stopping times
tau_k increasing with tau_k -> infinity (or >= T eventually) a.s. such that each stopped process
M^{tau_k} is a martingale (a variant with M - M_0 stopped is equivalent here since the hypothesis
makes M_0 integrable). Hypothesis: E sup_{t <= T} |M_t| < infinity (the running supremum is
integrable). Conclusion: zero-mean increments, E[M_t - M_s] = 0 for all 0 <= s <= t <= T
(at least E[M_T - M_t] = 0 for all t <= T, which is the use). A stronger conclusion (M is a true
martingale on [0,T]) is acceptable as broader.

Faithfulness points: the local-martingale notion must be the genuine one (localising sequence
of stopping times tending to infinity / exhausting [0,T], stopped processes martingales); the
supremum must be over the whole interval [0,T] (measurable or as an lintegral/upper integral);
"zero-mean increments" must be the expectation of the increment, with integrability of M_t
derivable (it is, from the supremum); the cadlag hypothesis may be dropped (broader) only if the
statement is still true. The BDG sentence is not part of this clause.
Comparison (verdict recorded 2026-10-20T11:23:01Z):
# Decision: spec:Dissertation.PaperSpec.A.sec4_supremum_criterion (Dissertation/PaperSpec/A/Sec4Supremum.lean)

Verdict: faithful with representation choices.

Comparison with the locked reading.
- Setting: any probability space (Ω, P) with a filtration 𝓕 indexed by ℝ≥0 (no usual conditions
  needed). The passage states the criterion for càdlàg local martingales in general (it is then
  applied on the standing basis), so a general filtered space is what it says; time [0, ∞) with a
  horizon T >= 0 represents the paper's [0, T] (a process on [0, T] extends by stopping at T,
  keeping the local-martingale property and the running supremum).
- M real-valued, `Adapted 𝓕 M` (each M_t is 𝓕_t-measurable).
- Càdlàg: almost surely, at every t, right-continuous (`ContinuousWithinAt … (Set.Ici t) t`) and
  with a left limit (`Tendsto … (𝓝[<] t) (𝓝 l)` for some l; vacuous at t = 0). "Almost surely
  càdlàg" is the usual reading and no stronger than "càdlàg".
- Local martingale: Mathlib's `Locally (fun X => Martingale X 𝓕 P) 𝓕 M P`
  (Mathlib/Probability/Process/LocalProperty.lean): there is a localizing sequence of stopping
  times (a.s. nondecreasing, a.s. tending to ⊤) such that each stopped process of
  1_{τ_n > 0} M is a martingale. This is the standard definition (the indicator handles a possibly
  non-integrable M_0, the usual convention); Mathlib's `Martingale` is strong adaptedness plus the
  conditional-expectation identity, which forces integrability, so it is the genuine notion.
- Hypothesis: `∫⁻ ω, ⨆ u ≤ T, ‖M u ω‖ₑ ∂P < ∞`, E sup_{u <= T} |M_u| < ∞. The lower Lebesgue
  integral of a possibly non-measurable supremum; since the paths are a.s. càdlàg the supremum
  agrees a.s. with a countable one and the lintegral respects a.e. equality, so this is the
  genuine expectation of the running supremum.
- Conclusion: M_t integrable for t <= T and E[M_t - M_s] = 0 for s <= t <= T: zero-mean
  increments (the use in §4 is E[M_T - M_t] = 0). The integrability conjunct is a by-product the
  paper takes for granted.
Representation choices: time index ℝ≥0 with a horizon T instead of [0, T]; the a.s. càdlàg
encoding; Mathlib's `Locally` convention for local martingales; the supremum as a lintegral; the
added integrability conclusion. None changes the meaning.

Current text. Read at 1f67672 (§4 preamble: "By localisation and dominated convergence, a
càdlàg local martingale whose running supremum is integrable has zero-mean increments (the
supremum criterion below)"). I have not seen the earlier text, so I cannot say what changed; the
proposition states the current sentence, for real-valued processes, which is how §4 uses it (the
scalar processes M^W, M^1 of Lemma 4.1 and the four local martingales of the display eq:bdg4).

Witness. `Dissertation.Acceptance.A.sec4_supremum_criterion_hypotheses` (Dissertation/
Acceptance/A/Sec4Supremum.lean): on Bool with a fair coin, the filtration trivial before time 1 and
full from time 1, M_t = ξ 1_{t >= 1} with ξ = ±1, T = 2: adapted, càdlàg, a (local) martingale
with integrable running supremum, and M_T ≠ M_0 on every path. A nonconstant genuine instance;
the paper's instances are stochastic integrals on the standing basis, but the criterion is stated
for general càdlàg local martingales, so this is an instance the passage covers.

Coverage (claim A:sec4:supremum-criterion, one clause). The passage region also states the BDG
inequality at p = 1 and p = 2 with one constant, Doob's constant 4, and that BDG for càdlàg local
martingales covers the compensated-Poisson martingales; the claim's scope note records these as
cited work (He, Wang and Yan), not stated, which I accept: they are statements of a cited theorem
and of its applicability. The one clause states the only mathematical assertion the passage makes
on its own account; it states nothing more, under the hypotheses the passage gives.
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless:
1. Time ℝ≥0 with a horizon T >= 0 instead of the interval [0, T]; a process on [0, T] extends
   past T by stopping, keeping both hypotheses, and the conclusion concerns only s <= t <= T.
2. Càdlàg is "almost surely right-continuous with left limits at every time".
3. "Local martingale" is Mathlib's `Locally (Martingale · 𝓕 P)`: a localizing sequence with
   each stopped process of 1_{τ_n > 0} M a martingale (the standard convention for a possibly
   non-integrable M_0); Mathlib's martingales are integrable.
4. The integrability of the running supremum is a lintegral of the (a.s. countable) supremum.
5. The conclusion adds the integrability of each M_t, t <= T, a by-product of the hypothesis.
Disagreements with the author's review (shown 2026-10-20T11:23:28Z): none
