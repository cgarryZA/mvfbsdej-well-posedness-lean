### A:prop:strict: Dissertation.PaperSpec.A.prop_strict
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash ed839d34f480cba1f1c48950c52ae4f4 (pl-fp-v1:352b5783606ae7d847da4c6771111e34620c8c56d780b384ef2893b7d169310b)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T12:11:02Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:09:53Z):
Reading of Proposition 3.8 (prop:strict), clause main.

Setting: n = m = 1, any d >= 1, G = 1, the tuple space H = R x R x R^{1xd} x L2(nu;R) for nu
sigma-finite on a countably generated E (standing setting); fix beta1 > 0 and any eps with
0 < eps < beta1. The drift is exactly b(t, theta, mu) = -beta1 * y + eps * g0(y - m_Y(mu)) with
g0(r) = max(-1, min(1, r)) (clamp to [-1,1]) and m_Y(mu) = int y mu(dtheta) (the Y-marginal mean of a
law of finite second moment on H). b does not depend on t, x, z, u except through y and mu.
A faithful statement must claim, for all such beta1, eps (and all d, nu, E):
 (a) free-measure W2-Lipschitz with constant beta1 + eps: for every t, all points theta, theta' of
     H and ALL laws mu, mu' in P2(H) (not only diagonal ones),
     |b(t,theta,mu) - b(t,theta',mu')| <= (beta1+eps) (|dy| + W2(mu, mu'))  [the proof's form], or
     the Assumption-2.3 form with |dx|+|dy|+|dz|_F+||du|| + W2 (weaker, also acceptable); W2 is the
     2-Wasserstein distance of the Hilbert norm of H.
 (b) the expected diagonal bound (eq:diagdrift): on the standing basis (or any filtered probability
     space), for (every / a.e.) t and all (Theta,mu), (Theta',mu') in D_t (F_t-measurable L2 tuples
     with their own laws), E<db, dY> <= -(beta1 - eps) E|dY|^2, db = b(t,Theta,Law Theta) -
     b(t,Theta',Law Theta').
 (c) pointwise failure: for every beta >= 0 there are free inputs theta, theta' in H and laws mu, mu'
     in P2(H) with theta in supp mu and theta' in supp mu' such that
     <b(t,theta,mu) - b(t,theta',mu'), y - y'> > -beta |y - y'|^2 (the pointwise bound fails).
     Quantifier order as printed: forall beta exists pair (a single pair for all beta is stronger and
     also acceptable). supp = topological support of the law on H.
Edge cases: m_Y must be the true mean (laws in P2 so the integral exists); the pointwise failure must
use laws whose supports contain the points (not arbitrary laws).
Comparison (verdict recorded 2026-10-17T12:10:55Z):
Comparison: prop_strict vs Proposition 3.8.

Setting: forall E (measurable, countably generated), nu sigma-finite, d > 0, n = m = 1 (TupleH nu 1 1 d
= R^1 x R^1 x R^{1xd} x L2(nu;R^1)), beta1 > 0, 0 < eps < beta1. G = 1 is implicit (the pairing
<db, dY> is the G = 1 pairing). Matches.
Drift: clampDrift beta1 eps t theta mu = -(beta1 * y) + eps * clampVec(y - meanY mu), clampVec the
coordinatewise clamp01 = max(-1, min(1, r)), meanY mu = Bochner integral of theta.2.1 under mu.law (mu in
P2, so the mean exists). Exactly (3.6).
(a) For all t, points theta, theta' and laws mu, mu' in P2(H): ||db|| <= (beta1+eps)(||dy|| + w2H mu mu'),
    w2H the W2 of the Hilbert norm. This is the free-measure Lipschitz bound in the proof's form (only
    |dy|), which implies the Assumption-2.3 form. Matches (stronger form of the printed claim).
(b) For every probability space (Omega, P), every t and all L2 tuples Theta, Theta' with laws lawP2:
    the pairing is integrable and E<db, dY> <= -(beta1-eps) E|dY|^2. The printed claim is over D_t of
    the standing basis; every element of D_t is an L2 tuple with its law, so this is broader (no
    filtration constraint, any probability space) and the printed claim is the instance Omega = the
    standing space, Theta, Theta' F_t-measurable. Integrability is an extra conclusion (stronger).
(c) For all t and beta >= 0 there exist theta, theta', mu, mu' with theta in mu.law.support, theta' in
    mu'.law.support (Mathlib's topological support: every neighbourhood has positive mass) and
    not (<db, dy> <= -beta |dy|^2). Matches the printed forall-beta-exists-pair.
Witness prop_strict_hypotheses: nu = dirac 0 on R, d = 1, beta1 = 2, eps = 1 — an intended instance;
the hypotheses are only numeric/sigma-finiteness and clearly satisfiable.
Representation choices: (b) stated over arbitrary L2 inputs rather than D_t (broader, printed claim
is an instance); G = 1 written out; (a) in the proof's |dy| form. All harmless.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — 1. The expected diagonal bound (3.7) is asserted for all square-integrable tuples Theta, Theta' on an
   arbitrary probability space with their laws, not only for the F_t-measurable ones of D_t: the
   printed claim is the instance on the standing basis (D_t is a subset), so this only strengthens.
2. G = 1 is written out (the pairing <db, dY>); n = m = 1 via TupleH nu 1 1 d.
3. The free-measure Lipschitz bound is stated with |y - y'| + W2 (the proof's form), which implies the
   Assumption-2.3 form with the full channel sum; W2 is the Hilbert-norm W2 (w2H).
4. Integrability of the pairing is added to the conclusion (a stronger statement).
Disagreements with the author's review (shown 2026-10-17T12:10:55Z): none
