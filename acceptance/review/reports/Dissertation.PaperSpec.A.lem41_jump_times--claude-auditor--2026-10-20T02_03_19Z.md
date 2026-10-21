### A:lem4.1:M2-infinite-activity: Dissertation.PaperSpec.A.lem41_jump_times
Pins: manuscript A None; project 6d403c197bfb10fe8808933c6e525ee0ae544fb1; hash ed839d34f480cba17f1df52f488747a1 (pl-fp-v1:e067139d1bf4a6441655bb2dd65c129357516501c1ca6d5fd05bbfcadb41e70c)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-20T02:03:19Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-20T01:52:26Z):
Reading of the passage (manuscript/paper/sections/04-proof-wellposedness.tex, lines 148-152, proof of
Lemma 4.1, paragraph "Zero-mean terms"; with sections/02-model-assumptions.tex lines 2-11).

What the paper says. "The three do not share one argument: ... nor, with nu(E) = infinity admitted, does
localisation along jump times, which then fail to exhaust [0,T]." §2 (lines 9-11) states that in the
infinite-activity regime nu(E) = infinity, N has infinitely many atoms on every nondegenerate time
interval. The clause makes the claim precise: jump times tau_k := inf{t >= 0 : N((0,t] x E) >= k},
read in [0, infinity], are all 0 almost surely, hence never exhaust [0,T].

Setting. The standing setting of §2 as far as N is concerned: a probability space carrying a Poisson
random measure N on R_+ x E with intensity dt (x) nu(de), nu a sigma-finite measure on a countably
generated measurable space (E, cal E). (W, F_0, the filtration and the usual conditions play no role
in this assertion; a statement for an arbitrary Poisson random measure with intensity Leb (x) nu is
broader and acceptable, with the setting's N as the instantiation.) N must be a genuine random
measure: for each omega a measure on R_+ x E, N(A) a random variable with values in [0, infinity],
N(A) Poisson(Leb(x)nu(A)) for every measurable A (with the convention that a Poisson variable of
infinite mean is a.s. infinite), or at least for A of finite intensity measure together with
countable additivity and independence on disjoint sets (then sigma-finiteness of nu gives the
infinite-mean case).

Hypothesis. nu(E) = infinity (the case "admitted"). No other hypothesis is needed; in particular no
finiteness of nu on pieces beyond sigma-finiteness of the setting.

Conclusion (all under one "almost surely", i.e. a single null set uniform in t, k, T):
 (i) for every t > 0, N((0,t] x E) = infinity;
 (ii) for every k (k in N; k = 0 harmless), tau_k = 0, where tau_k is the infimum in [0, infinity]
      (ENNReal or EReal, NOT a real-valued sInf with the junk value sInf(empty) = 0, and NOT a real
      iSup that is 0 on unbounded families) of {t >= 0 : N((0,t] x E) >= k};
 (iii) for every T > 0, sup_k tau_k < T (the supremum taken in [0, infinity]); this is the
      "do not exhaust [0,T]" assertion.
Quantifier order: the a.s. event should be quantified outside "for every t > 0", "for every k",
"for every T > 0" (a.s. for each fixed t would be weaker but, by monotonicity in t, equivalent via
rational t; I would accept either only if the stronger uniform form is stated or derivable trivially).
The order of (i)-(iii): (i) is what drives (ii), (ii) gives (iii).

Must not be trivial by junk: if tau_k is a real sInf, sInf of the empty set is 0 and an iSup of an
unbounded real family is 0, so a real-valued formulation could make (ii)/(iii) true without using
nu(E) = infinity. A faithful statement uses [0, infinity]-valued inf/sup (or makes nonemptiness and
boundedness explicit). Also N must be the setting's PRM, not an arbitrary measure-valued map (else
(i) could fail or hold vacuously).

Witness: there must exist a Poisson random measure with sigma-finite intensity of infinite total mass
(e.g. nu = Lebesgue on (0,1) with density 1/e^2, or counting measure on N) so that the hypotheses
are met; the proposition should not be vacuous because the PRM structure is unsatisfiable.

Is this claimed by the paper at this revision? Yes: line 151 claims the jump times fail to exhaust
[0,T] when nu(E) = infinity; (i) is the §2 statement of infinitely many atoms on every nondegenerate
interval; (ii) is the precise content of "fail to exhaust" for the natural jump times.
Comparison (verdict recorded 2026-10-20T02:02:37Z):
Comparison for Dissertation.PaperSpec.A.lem41_jump_times (Dissertation/PaperSpec/A/Sec4BrownianPoisson.lean)
against my locked reading.

Setting. Lean: any probability space (Omega, P), any measurable E with sigma-finite nu, any d : N, and a
LevyStochCalc.Driver.LevyDriver D (a d-dim Brownian motion and a Poisson random measure D.N, sigma(W)
independent of sigma(N)). The N used is D.N.N : Omega -> Measure (R x E), a genuine measure for every
omega. LevyStochCalc.Poisson.PoissonRandomMeasure (.lake/packages/LevyStochCalc/LevyStochCalc/Poisson/
RandomMeasure.lean) has intensity referenceIntensity nu = Leb|[0,inf) (x) nu, measurable evaluations, the
Poisson law on sets of finite intensity, independence on countable disjoint families and, as a field,
`infinite_at_infinite_intensity`: N(B) = infinity a.s. when the intensity of B is infinite (the
convention "Poisson of infinite mean is a.s. infinite" I asked for). The setting's countable generation
of E, d >= 1, the initial sigma-field and the filtration are not assumed: the proposition is broader
than the setting, which is harmless since the assertion concerns N alone (instantiation: the driver D of
the setting, with E countably generated and d >= 1). As in my reading.

Hypothesis. `ν Set.univ = ⊤`, i.e. nu(E) = infinity. Matches; nothing else assumed.

Conclusion. One `∀ᵐ ω ∂P` (a single null set) outside all three parts, as I required:
 (i) `∀ t > 0, D.N.N ω (Ioc 0 t ×ˢ univ) = ⊤` - N((0,t] x E) = infinity for every t > 0. Matches.
 (ii) `∀ k : ℕ, (⨅ t (_ : 0 ≤ t ∧ k ≤ N ω (Ioc 0 t ×ˢ univ)), ENNReal.ofReal t) = 0` - tau_k is the
      infimum in [0, infinity] (ENNReal; the empty infimum is ⊤, not a real junk 0) of the times
      t >= 0 with N((0,t] x E) >= k; since t >= 0, ofReal t is t itself, so this is exactly
      inf{t >= 0 : N((0,t] x E) >= k} read in [0, infinity]. k = 0 is included (tau_0 = 0 trivially).
 (iii) `∀ T > 0, (⨆ k, tau_k) < ENNReal.ofReal T` - sup_k tau_k < T with the supremum in ENNReal (no real
      iSup junk). Matches.
Non-triviality: the conclusions are not true by junk values. If nu(E) < infinity, N((0,t] x E) is a.s.
finite and tau_k > 0 for k >= 1 a.s., so (i)-(ii) genuinely use nu(E) = infinity; the ENNReal reading
excludes the real `sInf ∅ = 0` and unbounded `iSup = 0` conventions I flagged.

Witness. Dissertation.Acceptance.A.sec2_infinite_activity_hypotheses (Dissertation/Acceptance/A/
Sec2Basics.lean): Lebesgue measure on R has infinite total mass and is sigma-finite, and some probability
space carries a LevyDriver with d = 1 and that intensity (LevyDriver.exists). This is an infinite-
activity instance the paper intends (nu(E) = infinity admitted), so the hypotheses can be met.

Representation choices: tau_k written as an iInf of ENNReal.ofReal t over real t >= 0 (equal to the
infimum in [0, infinity]); the PRM is LevyStochCalc's structure (a measure-valued map on R x E with
intensity Leb restricted to [0, infinity) times nu); setting hypotheses irrelevant to N are dropped.

Is it claimed at this revision? Yes: sections/04-proof-wellposedness.tex line 151 ("localisation along
jump times, which then fail to exhaust [0,T]") with sections/02-model-assumptions.tex lines 9-11
(infinitely many atoms on every nondegenerate time interval). The proposition is the precise content.

Coverage of claim A:lem4.1:M2-infinite-activity (acceptance/claims.json). Its scope note limits it to
the sentence of lines 148-152 and the M^2 paragraph of lines 173-187; its clauses are
lem41_M2_no_square_moment (the general-setting reading, refuted at nu = 0), lem41_M2_no_square_moment_corr
(nu != 0), lem41_jump_times, lem41_M2_integrand and lem41_M2_zero_mean (L^1 bound with e^T, integrability
of the Poisson integral and of the compensator over (t,T] x E, and E[M^2_T - M^2_t] = 0, M^2 read
pathwise as N-integral minus compensator). Within lines 148-152 and 173-187 every mathematical assertion
is stated by some clause: "no square moments" (clauses 1-2), "jump times fail to exhaust [0,T]"
(this clause), "predictable and nonnegative" (lem41_M2_integrand), "lies in L^1 with the e^T bound",
"Poisson integral and compensator integrable", "E[M^2_T - M^2_t] = 0" (lem41_M2_zero_mean); the phrases
"the L^2 theory ... does not reach it" and "handled through the compensation formula, which asks only
for integrability" are methodological, not separate assertions. No clause states something the passage
does not claim (the refuted clause is the printed reading, refuted beside a corrected one). Gap with
respect to the whole paragraph of lines 139-187: the assertions about M^W and M^1 (lines 139-148: the
three stochastic terms are local martingales with E[M_T - M_t] = 0; lines 153-172: the BDG/Cauchy-
Schwarz bounds E sup|M^W_t| < infinity and E sup|M^1_t| < infinity, with the compensation-formula
identity in the M^1 chain, and the supremum criterion giving zero mean) are not stated by any clause
of this claim, and I found no other claim in acceptance/claims.json with a clause stating them
(A:eq:itoY2 at line 128 has scope "proof-step" and no clauses). Hypotheses in force: at line 151 the
setting and the hypotheses of Lemma 4.1 hold, and the sentence speaks of the admitted case
nu(E) = infinity; this clause assumes nu(E) = infinity and only the driver (fewer hypotheses than in
force, all of them irrelevant to N: harmless). lem41_M2_integrand and lem41_M2_zero_mean carry exactly
the hypotheses of Lemma 4.1 (the binder list of lem_bpbsde); the two no-square-moment clauses are
existence statements over the setting (plus nu != 0 for the corrected one).
Witness: —
Verdict: broader — Broader than the printed claim only in the setting: the proposition holds for any LevyStochCalc
LevyDriver over any probability space, any measurable mark space E with sigma-finite nu (countable
generation not required) and any d (d = 0 allowed), without the initial sigma-field or the filtration of
§2. Instantiation giving the printed claim: take the driver D of the standing setting (E countably
generated, d >= 1) with nu(E) = infinity. The jump times are read in [0, infinity] (ENNReal infimum of
ofReal t over t >= 0, empty infimum = infinity), as the clause says; no junk value is involved.
Disagreements with the author's review (shown 2026-10-20T02:02:44Z): 1. The recorded author review of this unit (acceptance/review/A.md, line 675) is a single line citing a
   claude-auditor report on a different proposition, Dissertation.PaperSpec.A.lem41_M2_no_square_moment_corr.
   As recorded it is not a review of lem41_jump_times: it contains no reading of the passage (line 151 with
   §2 lines 9-11), no item-by-item comparison, no witness and no statement of how the jump times are read.
   A review of this unit should be recorded for it (or the marker should cite a report of this unit).
2. Verdict: I find the proposition broader, not faithful with representation choices: it holds for every
   LevyDriver over any measurable mark space with sigma-finite nu (countable generation not required) and
   any d (d = 0 allowed), without the initial sigma-field and filtration of §2; the printed claim is its
   instantiation at the driver of the standing setting. Both verdicts are in the "matches" group; the
   difference is the recorded instantiation.
3. Points a review should record and the cited line does not: tau_k is read in [0, infinity] as an ENNReal
   infimum of ofReal t over t >= 0 (empty infimum = infinity), and the supremum likewise, so no real-valued
   sInf/iSup junk value makes the conclusion true; N((0,t] x E) = infinity a.s. rests on the PRM field
   infinite_at_infinite_intensity; a single null set is quantified outside t, k and T; the witness is
   Dissertation.Acceptance.A.sec2_infinite_activity_hypotheses (Lebesgue intensity).
