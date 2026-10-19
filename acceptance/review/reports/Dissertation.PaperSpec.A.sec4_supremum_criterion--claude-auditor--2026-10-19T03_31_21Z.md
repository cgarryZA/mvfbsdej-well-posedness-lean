### A:sec4:supremum-criterion: Dissertation.PaperSpec.A.sec4_supremum_criterion
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba1f588c2071f5242ff (pl-fp-v1:668939571700f8b456579ffca8e5ba6bd4a5ecc7ce80e70d20901f671b16ef0c)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:31:21Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:16:07Z):
Reading of spec sec4_supremum_criterion (§4 preamble, 04-proof-wellposedness.tex:33-35).
Claim: "a cadlag local martingale whose running supremum is integrable has zero-mean increments" (by
localisation and dominated convergence).
Faithful formal statement: on a filtered probability space (the standing one, or any; generality is fine),
for every real- (or R^k-) valued process M on [0,T] that is adapted, cadlag, and a local martingale
(there are stopping times tau_k increasing to infinity / reaching T such that each stopped process M^{tau_k}
is a martingale), with E sup_{t<=T} |M_t| < infinity, one has E[M_t - M_s] = 0 for all 0<=s<=t<=T
(in particular E[M_T - M_t]=0 for every t<=T, which is the form used). Stronger conclusion (M is a true
martingale) is fine. Integrability of the increments follows from the hypothesis.
Hypotheses must be exactly: local martingale (with the paper's standard localisation notion), cadlag,
integrable running supremum. If the Lean demands more (e.g. M a true martingale, or L^2 bounds, or a
continuous M), it is narrower; dropping cadlag is fine (broader). Witness: any true martingale e.g. constant.
Note: on [0,T] the localising sequence must be allowed to be general stopping times (a localising sequence
that must reach T in finitely many steps or tau_k -> infinity a.s.). The definition of local martingale used
must be the standard one.
Comparison (verdict recorded 2026-10-19T03:29:17Z):
Comparison, sec4_supremum_criterion (Sec4Supremum.lean:32-44) vs reading.
- Setting: any probability space, a filtration indexed by ℝ≥0, a real process M on ℝ≥0, T ≥ 0. The
  paper's processes live on [0,T] of the standing basis; a [0,T]-process is an instance by freezing it
  after T (M_{t∧T}, F_{t∧T}), which keeps adaptedness, càdlàg paths, the local martingale property and
  the running supremum on [0,T]. Generality in the basis is fine.
- Hypotheses: Adapted; a.s. every path right-continuous with left limits at every t (left limit at 0
  vacuous) = a.s. càdlàg; Locally (Martingale) in Mathlib's sense (a localising sequence τ_n, a.s.
  monotone, tending to ⊤, with each stopped process 1_{τ_n>0} M^{τ_n} a martingale) -- the standard
  local-martingale notion; since M_0 is integrable here (sup integrable), the 1_{τ>0} convention is
  equivalent to the usual one (and is in any case weaker as a hypothesis); E sup_{u≤T}|M_u| < ∞ as a
  lintegral of the extended norm sup (a.e. equal to a countable sup for càdlàg paths). Exactly the
  reading's hypotheses; nothing added.
- Conclusion: integrability of M_t for t ≤ T and E[M_t - M_s] = 0 for all s ≤ t ≤ T. Matches (contains
  the used form E[M_T - M_t] = 0).
- Witness sec4_supremum_criterion_hypotheses: a nonconstant (M_T ≠ M_0) process meeting all hypotheses.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices: (1) time ℝ≥0 with a filtration on ℝ≥0 instead of [0,T] of the standing basis
(the paper's [0,T]-process is the instance frozen after T); (2) "local martingale" is Mathlib's
`Locally (Martingale …)` with the 1_{τ_n>0} M^{τ_n} convention, equivalent here because M_0 is integrable;
(3) càdlàg only almost surely, as right-continuity plus existence of left limits; (4) E sup as a
lintegral of the extended norm. All harmless.
Disagreements with the author's review (shown 2026-10-19T03:29:28Z): No disagreement on substance. Label only: the review records "faithful"; I record "faithful with
representation choices" for the time domain ℝ≥0 (the paper's [0,T]-process is the instance frozen after T),
Mathlib's 1_{τ>0} localisation convention, and the almost-sure càdlàg encoding, all of which the review
also describes.
