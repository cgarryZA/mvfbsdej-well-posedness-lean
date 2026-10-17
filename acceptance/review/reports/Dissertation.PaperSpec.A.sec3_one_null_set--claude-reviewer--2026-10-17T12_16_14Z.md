### A:sec3:one-null-set: Dissertation.PaperSpec.A.sec3_one_null_set
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash ed839d34f480cba1209a5aa6ac298690 (pl-fp-v1:fe8111434b807a2233abbc5f677c0f9a48553de58b2b2157f04319a5c4f2dd2f)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T12:16:14Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:15:46Z):
Reading of the Section 3 solution-definition claim: "Both sides of each identity are cadlag in t, so
the exceptional null set may be taken independent of t."
Claim: for Theta = (X, Y, Z, U) in S with the integrals of (1.1) along Theta existing (drift/driver
Lebesgue integrals, Ito and compensated Poisson integrals in their cadlag versions), if each identity
of (1.1) holds almost surely for every fixed t in [0,T] (null set possibly depending on t), then it
holds simultaneously for all t in [0,T] outside one null set. The mechanism: both sides are cadlag
(right-continuous suffices) in t, so equality on a countable dense set of times plus T gives
equality at all times.
A faithful formalisation: either (a) the specific statement about the two identities of (1.1) for
tuples in S (with the cadlag versions of the stochastic integrals), or (b) the general lemma: two
processes on [0,T] with a.s. right-continuous paths that agree a.s. at each fixed t in [0,T] agree at
all t in [0,T] off one null set (with the identities of (1.1) as the instance: X_t and its
right-hand side; Y_t and its right-hand side). In (b) the right-continuity hypothesis must be the
property both sides of (1.1) actually have (cadlag paths of X, Y, of the drift integrals, and of the
chosen versions of the stochastic integrals), and the conclusion must quantify all t in [0,T] inside
the almost-sure statement.
Comparison (verdict recorded 2026-10-17T12:16:10Z):
Comparison: sec3_one_null_set vs "the exceptional null set may be taken independent of t".
Statement: in the standing setting, for a tuple of H_weak (PaperWeakTuple: adapted X, Y with every
path right-continuous on [0,T), a.s. left limits, finite energies; predictable Z, U) along which the
integrals of (1.1) exist (PaperAdmissibleInt: drift/driver with a.s. integrable paths, diffusion and
jump representative gamma of finite energy) and for ANY process M with a.s. right-continuous paths
on [0,T) (in the solution predicates M is the cadlag version of the Brownian integral):
 forward: (for all t in [0,T], a.s. X_i(t) = xi0_i + int_{[0,t]} b + M_t + int_0^t int gamma dN~)  iff
          (a.s., for all t in [0,T], the same identity);
 backward: same for Y_k(t) = g_k(X_T, Law X_T) + int_{[t,T]} f - (M_T - M_t) - (int_0^T int U dN~ -
          int_0^t int U dN~).
The right-hand sides are the identities of (1.1) as the solution predicates write them (the Poisson
integral is LevyStochCalc's cadlag version; the drift/driver integrals are continuous in t), so both
sides are a.s. right-continuous: exactly the paper's mechanism. The equivalence (both directions)
contains the printed claim (the forward direction "a.s. for each t => off one null set for all t").
Broader: stated on H_weak rather than S, and for any right-continuous M in place of the Brownian
integral version.
No witness needed beyond satisfiability of PaperWeakTuple/PaperAdmissibleInt, which
sec3_space_hypotheses exhibits.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — 1. The Brownian integral is abstracted to any process M with a.s. right-continuous paths on [0,T)
   (the solution predicates use a cadlag version of the Brownian integral, an instance).
2. Stated for tuples of H_weak with the integrals of (1.1) existing, not only S: broader.
3. Stated as an equivalence; the printed claim is the forward implication.
Disagreements with the author's review (shown 2026-10-17T12:16:10Z): none
