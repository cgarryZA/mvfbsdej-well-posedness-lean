### A:sec3:one-null-set: Dissertation.PaperSpec.A.sec3_one_null_set
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba1209a5aa6ac298690 (pl-fp-v1:fe8111434b807a2233abbc5f677c0f9a48553de58b2b2157f04319a5c4f2dd2f)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:35:07Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:15:37Z):
Reading (locked before any Lean): spec sec3_one_null_set, §3 solution definition, clause "the
identities of (1.1) holding almost surely for every t hold off one null set for all t".

Paper content. A solution is Theta in HH satisfying both identities of (1.1) a.s. for every
t in [0,T] (the null set a priori depending on t), h at the predictable tuple. "Both sides of each
identity are cadlag in t, so the exceptional null set may be taken independent of t."

A faithful formal statement must contain:
- Setting and data: standing basis, coefficients (b, sigma, h, f, g) (under the standing
  measurability and whatever integrability makes the integrals in (1.1) defined - in the paper
  Assumptions 2.2-2.3 along Theta in HH, (2.16)), Theta in HH (X, Y cadlag adapted, Z, U
  predictable square integrable), xi_0.
- Hypothesis: for every t in [0,T], almost surely the forward identity holds at t, and for every
  t, almost surely the backward identity holds at t.
- Conclusion: almost surely, for all t in [0,T], both identities hold (one null set).
- The argument needs the RHS processes to be cadlag in t: the dt-integrals continuous, the Ito
  integral and compensated Poisson integral processes taken in cadlag versions. In Lean the
  stochastic integral processes must be cadlag (a.s.) versions for the claim to be true; the
  statement may legitimately assume hypotheses guaranteeing the integrals are defined
  (square-integrable integrands) since the paper's identity presupposes them. A statement that
  instead assumes the identities hold on one null set already, or assumes cadlag RHS as a bare
  hypothesis that is not automatically true of the integrals, would beg the question
  (hypothesis doing the work) - narrower/mismatched.
- The conclusion should be about both identities (forward and backward); time interval [0,T]
  closed.
Comparison (verdict recorded 2026-10-19T03:23:30Z):
Comparison: spec sec3_one_null_set (Sec3Space.lean:37-97) against my locked reading.

Hypotheses: standing basis (G0 independent of the driver, enlJoint); arbitrary coefficients C (no
assumption) and xi0; Theta in the weak class (PaperWeakTuple: X, Y adapted, every path
right-continuous on [0,T), a.s. left limits, E int |.|^2 finite; Z predictable, U marked predictable,
finite energies, vanishing off [0,T]); PaperAdmissibleInt: the integrals of (1.1) along Theta exist
(drift and driver jointly/progressively measurable with a.s. integrable paths, diffusion with finite
energy, jump representative gamma with finite marked energy and gamma = h(s, Theta^-_s, ., mu^-_s)
in L2(nu) for a.e. s a.s.). This is broader than the paper's setting (Theta in HH, coefficients under
Assumptions 2.2-2.3 which make the integrals exist).

The Brownian integral is replaced by an arbitrary process M with almost surely right-continuous
paths on [0,T). Conclusion, for each coordinate: [for every t in [0,T], a.s. forward identity with
M_t] <-> [a.s., for all t in [0,T], the forward identity]; likewise for the backward identity
(terminal g(X_T, Law X_T), int_{[t,T]} f, M_T - M_t, Poisson increments). The library Poisson
integrals are cadlag versions, the dt-integrals are continuous in t, X and Y right-continuous, so
both sides are right-continuous in t on [0,T) and the claim is exactly the paper's argument. The
direction <- is trivial; -> is the clause.

Why M instead of the Ito integral: the library Ito integral is defined time by time with no path
regularity, so "one null set for all t" only makes sense for a cadlag version; the paper's
stochastic integrals are cadlag processes by convention. Instantiating M with a cadlag version of
int sigma(s, Theta_s, mu_s) dW (resp. int Z dW), which exists (exists_ae_cadlag_brownianIntegral)
and agrees with the integral a.s. at each t, makes the left side the paper's "a.s. for every t"
identity and the right side the identity on one null set. The quantification over all
right-continuous M is broader, not a hypothesis that does the work: right-continuity is a property
of the cadlag version, not an assumption on the integrals.

Witness sec3_space_hypotheses: a tuple and integrand representative at Example 5.1(i) satisfying
PaperWeakTuple and PaperAdmissibleInt; the hypotheses are met.

Verdict: broader.
Witness: —
Verdict: broader — Broader than the printed claim in three ways: (a) Theta ranges over the weak class with the
integrals of (1.1) existing (PaperWeakTuple + PaperAdmissibleInt), not only over HH under
Assumptions 2.2-2.3; (b) the coefficients are arbitrary; (c) the Brownian integral is replaced by an
arbitrary process M with a.s. right-continuous paths on [0,T). The printed claim is the instance:
Theta in HH with coefficients under (2.3) and Assumptions 2.2-2.3 (so PaperAdmissibleInt holds, by
(4.2)), and M a cadlag version of the Ito integral int_0^t sigma(s, Theta_s, mu_s) dW_s for the
forward identity (resp. of int_0^t Z_s dW_s for the backward one); such a version exists and equals
the integral a.s. at each t, so "for every t, a.s." is the paper's solution identity and the
conclusion is the identity off one null set for all t in [0,T].
Disagreements with the author's review (shown 2026-10-19T03:34:53Z): Labelling only. The review calls the proposition "faithful with representation choices" while
itself describing it as broader (stated on Hweak rather than HH, for any right-continuous M in
place of the cadlag version of the Brownian integral, as an equivalence). I record it as
"broader" for those same reasons, with the instantiation (Theta in HH under Assumptions 2.2-2.3,
M a cadlag version of the Ito integral) in my detail. We agree on the content and that it is
correct; both labels are in the matching group.
