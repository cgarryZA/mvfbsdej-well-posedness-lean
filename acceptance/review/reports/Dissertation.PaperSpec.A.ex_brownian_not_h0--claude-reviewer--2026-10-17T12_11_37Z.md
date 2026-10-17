### A:ex:brownian: Dissertation.PaperSpec.A.ex_brownian_not_h0
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash ed839d34f480cba13fa0ef4acc9fb310 (pl-fp-v1:f3ca509922faf1c36c26aae5e5be820d6e132dec8b45c2f21ef3ab25469904e0)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T12:11:37Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:10:58Z):
# Reading: ex_brownian_not_h0

Paper: "Merely setting h = 0 on a Brownian-Poisson basis is not a reduction, since the backward
Poisson integral and its integrand U persist in the representation."

Meaning: on the standing basis with a genuine Poisson channel (nu != 0), taking h = 0 does not
turn the system into the Brownian one: the filtration still carries N, the predictable
representation of square-integrable martingales still needs the compensated Poisson integral, so
the backward component of a solution can have U != 0 and the BSDE cannot be written with Z alone.

Faithful formal statement (one of):
(A) Representation level: for every Brownian-Poisson basis of §2 with nu != 0 (equivalently, some
    A with 0 < nu(A) < infinity, sigma-finite), there is a square-integrable F_T-measurable xi
    (e.g. Ntilde((0,T] x A)) whose martingale E[xi | F_t] has, in the Brownian-Poisson PRP
    M_t = M_0 + int Z dW + int int U dNtilde, a U-part that is not 0 in H^2_N (equivalently xi is
    not M_0 + int_0^T Z dW for any Z in H^2_W).
(B) System level: there is a system with h = 0 (satisfying the standing assumptions) whose
    solution in S has U != 0 (in H^2_N), so U persists.
Either expresses "U persists". Required: the hypothesis nu != 0 (with nu = 0, U is trivial and
the claim is false), quantifier over (every or some) Brownian-Poisson basis with nu != 0; the
non-zero-ness of U measured in H^2_N (E int ||U||^2 > 0), not merely that a function U is not
identically 0 pointwise (a dt dP nu-null modification would be a fake witness).
A statement only about a particular trivial fact (e.g. that the type of tuples still has a
U-coordinate) would be too weak.
Non-vacuity: needs a basis with nu != 0 (witness).
Comparison (verdict recorded 2026-10-17T12:11:31Z):
# Comparison: ex_brownian_not_h0

Lean (Sec5Brownian.lean:36): for every §2 basis (any countably generated E, sigma-finite nu, any
d, G0 independent of the driver) with d > 0 and nu != 0, and every T > 0: there is a real
square-integrable martingale M of the §2 filtration enlJoint such that there is no Z with
RepresentsMart ... T M Z 0, i.e. no predictable finite-energy Z vanishing off [0,T] with
M_t = M_0 + int_0^t Z dW a.s. for every t in [0,T].

Against my reading (A):
- Setting: Brownian-Poisson basis with a genuine Poisson channel (nu != 0) - yes; d >= 1 as in
  the paper's standing setting.
- Conclusion: a square-integrable martingale whose Brownian-Poisson representation cannot have
  U = 0, i.e. not representable by the Brownian integral alone - yes. U = 0 is the literal zero
  function; a representation with U = 0 only dt dP nu-a.e. has a.s. zero Poisson integral and so
  would give one with U = 0 literally, so the negation also excludes a.e.-zero U; together with
  PRP existence (sec2_prp) this is "the representing U is nonzero in H^2_N".
- The statement is coefficient-free, as the paper's justification ("U persists in the
  representation") is about the representation property, hence "whatever the coefficients":
  the BSDE of the system with h = 0 cannot be written in Brownian form in general.
- Quantifiers: universal over the basis, T > 0, existential M: correct order.
- Non-vacuity: witness ex_brownian_not_h0_hypotheses gives a probability space with a Levy driver
  d = 1, nu = dirac 0 on R (nonzero), G0 = bot independent. Good.

Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-17T12:11:31Z): none
