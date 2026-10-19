### A:rem:diag-mono: Dissertation.PaperSpec.A.rem_diag_mono_converse
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba14b5e4594e14d9dc7 (pl-fp-v1:dd404a4e00b0b624cc86cbc8b6fdf323201816e6886dddec90b8b93097a98348)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:36:03Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:16:43Z):
# Reading: spec rem_diag_mono_converse (Remark 2.8, "the converse fails")

Remark 2.8: the pointwise G-monotonicity condition (the inequality of (2.7) without expectations,
at every fixed theta,theta' in H and mu,mu' in P2(H)) implies Assumption 2.5 (expected, along the
diagonal) by evaluating at theta=Theta(omega), mu=Law(Theta) and taking expectations. "The converse
fails": expected diagonal monotonicity does NOT imply pointwise monotonicity (Proposition 3.8).

A faithful formal statement: there EXISTS a coefficient system (in the paper's setting; e.g.
n=m=1, G=1, d>=1, as in Prop 3.8) and constants beta1,beta2 >= 0 (admissible) such that
* the interior inequality (2.7) holds in expectation along all diagonal pairs
  (Theta,Law(Theta)),(Theta',Law(Theta')) with Theta,Theta' in L^2(Omega,F_t;H), for a.e. t in
  [0,T] (on the standing basis; universally over bases, or at least on a basis), and
* the pointwise inequality fails: there exist theta,theta' in H, mu,mu' in P2(H) at which
  <db,G^T dy> + <dsigma,G^T dz>_F + <-df,G dx> + int <dh(e),G^T du(e)> nu(de)
     > -beta1(|G^T dy|^2+|G^T dz|^2+||G^T du||^2) - beta2 |G dx|^2.
  (Failing "for the same constants" is the literal converse; failing for every beta >= 0, as
  Prop 3.8 gives, is stronger and also faithful.)
Equivalently: NOT (for all systems, expected diagonal monotonicity => pointwise monotonicity).
The expected condition must really be the paper's (expectations over the standing probability space,
the measure argument tied to the law of the tuple), and the pointwise one over FREE (theta, mu).
The terminal condition need not be involved (pointwise/expected distinction is about (2.7)); if
included it must be satisfiable.
Non-vacuity: the witness (e.g. the drift (3.6) b = -beta1 y + eps g0(y - m_Y(mu)) with the other
coefficients making the remaining channels harmless) must be exhibited, not assumed.
Comparison (verdict recorded 2026-10-19T03:22:53Z):
# Comparison: rem_diag_mono_converse

Lean (Sec2Remarks.lean): for every standing basis (any sigma-finite nu on a countably generated
E, d = 1, G0 independent of the driver, filtration enlJoint) and every T > 0, there EXIST
coefficients C on H with n = m = d = 1 and constants L, alpha, beta1, beta2 such that
  JointBorel T C, Assumption23 (L), Assumption25 (G = 1, alpha, beta1, beta2: the terminal
  inequality, the interior expected inequality (2.7) for a.e. t over the diagonal inputs at t, and
  the admissible-constant conditions),
and for EVERY beta >= 0 and every real beta' the pointwise inequality
  pairing27 1 C t theta theta' mu mu' <= -beta(|dy|^2 + |dz|^2 + ||du||^2) - beta' |dx|^2
fails: NOT (for a.e. t in [0,T], for all theta, theta' in H and mu, mu' in P2(H)).

Against my reading:
* Existence of a system (n = m = 1, G = 1, as in Prop 3.8) satisfying the expected diagonal
  monotonicity: yes — the full Assumption 2.5 (interior over diagonal inputs, i.e. strongly
  F_t-measurable L^2 tuples with lawP2 their laws, terminal, constants), plus (2.3) and Assumption
  2.3, all as conclusions.
* Pointwise failure: at free points and free laws (all theta, theta', mu, mu'), for every beta >= 0
  and every beta' — stronger than failing with the same constants (beta = beta1 >= 0, beta' = beta2
  is an instance, since admissible constants are >= 0), and the form Prop 3.8 gives ("sign
  -indefinite pointwise pairings"). The pointwise condition is negated as "for a.e. t", the natural
  pointwise counterpart of an a.e.-t assumption; its negation (failure on a non-null set of times)
  is the right one.
* Universality over bases and horizons: stronger than one instance; the coefficients may depend on
  the basis and T, which is fine for an existence claim.
* The expected condition requires the pairing to be integrable (Mono27At), an extra requirement
  that only strengthens the existence claim.
Nothing missing; no hypothesis to be vacuous (only T > 0 and the basis; the witness
ex_concrete_hypotheses supplies a basis).
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-19T03:35:59Z): none
