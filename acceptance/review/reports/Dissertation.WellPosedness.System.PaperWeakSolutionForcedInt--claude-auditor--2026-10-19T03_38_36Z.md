### A:lem:pert, A:sec4:WP-def: Dissertation.WellPosedness.System.PaperWeakSolutionForcedInt
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash 879f49cf215ebc960000000000000000 (pl-fp-v1:fa4a1becfe4d7886db95c94d9b3d6e42d020800e2a5cb485ebff132e098d2088)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:38:36Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:15:38Z):
Reading (locked before any Lean): def Dissertation.WellPosedness.System.PaperWeakSolutionForcedInt
- by its name and use (in Lemma 4.3's weak class), the implementation's structure for "Theta is a
weak solution of the forced lambda-system (4.1), with the integrability making the integrals
defined".

Paper notion: exactly as in my reading of WeakForcedSolution (the (4.1) identities at parameter
lambda with initial datum xi_0 and forcing q, Theta in the weak class: X, Y cadlag adapted with
E int(|X|^2 + |Y|^2) < inf, X_T in L2(F_T), Z in H^2_W, U in H^2_N), with "Int" presumably the
integrability of the coefficient/forcing processes along Theta that makes the dt-, Ito and
compensated-Poisson integrals of (4.1) genuine (not junk) - which the paper presupposes when it
says Theta "solves (4.1)".

A faithful Lean structure must have fields that together say: (i) the weak-class membership of
the components (cadlag adapted X, Y with the time-integrated square bound and X_T in L2; Z
predictable square-integrable; U predictable square-integrable in L2(nu)); (ii) integrability
side conditions sufficient for every integral in (4.1) to be the genuine integral (e.g.
coefficient processes along Theta and the forcings in L2(dt dP) / L2(dt dP nu), predictable
measurability of the jump integrand); (iii) the two identities of (4.1) a.s. for every t (or one
null set), with lambda multiplying b, sigma, h, f, g and the forcings added unscaled, h evaluated
at the predictable tuple and law flow. It may contain fields that are consequences of the paper's
notion (harmless) but must not contain fields that are stronger than the paper's notion
(e.g. requiring E sup|X|^2 < inf, i.e. HH membership, which would narrow Lemma 4.3) unless those
fields follow from the others. Integrability fields stronger than what the paper's integrals need
(e.g. coefficient processes in L2 individually, which needs Assumption 2.2) would be a
narrowing for Lemma 4.3/Theorem 3.3's weak class if they are not implied by the weak class plus
Assumption 2.3; I will check whether they are implied (coefficient differences are, single
coefficient processes are not without origin integrability).
Comparison (verdict recorded 2026-10-19T03:33:00Z):
Comparison: def Dissertation.WellPosedness.System.PaperWeakSolutionForcedInt
(System/PaperWeakSolutionForcedInt.lean:55-165) against my locked reading.

The structure is parameterised by a driver D, any filtration F with certificates that every W^j
is an F-Brownian motion and N an F-Poisson random measure (the paper's standing enlJoint is the
instance used), horizon T, lambda, coefficients C, initial datum xi0 (coordinates), forcing q,
tuple (X, Y, Z, U) and jump representative gamma. Fields:
(i) weak-class membership (extends PaperWeakTuple): X, Y adapted on [0,T], every path
    right-continuous on [0,T), a.s. left limits on (0,T], finite energy on [0,T]; Z predictable,
    U marked predictable, finite energies, vanishing off [0,T]; plus XT_sq (X_T in L2). Exactly
    Lemma 4.3's class; no S^2 bound (which would have narrowed the lemma) and no L2 condition on
    xi0 or on the terminal value.
(ii) forcing: Forcing (square-integrable forcing, q^h marked progressive) — the forcing class of
    (4.1), slightly wider for q^h than the paper's predictable class (harmless for a solution
    predicate; the statements add PredForcing).
(iii) integrability side conditions making the integrals of (4.1) genuine: forced drift and
    driver jointly and progressively measurable with a.s. integrable paths (b_meas, b_prog, b_int,
    f_meas, f_prog, f_int); forced diffusion and jump integrands jointly and (marked) progressively
    measurable with finite energy (sigma_*, gamma_*); jump_rep (gamma = h(s, Theta^-_s, .,
    mu^-_s) in L2(nu) for a.e. s, a.s.). These are the existence conditions of the pathwise
    Lebesgue integrals and of the library's L2 stochastic integrals. They are not stronger than
    the paper's notion in the drift and driver (pathwise suffices). In the Brownian channel they
    are implied for paper solutions under Assumption 2.3, and in the jump channel they are the
    paper's L2 framework. Single-coefficient finite energy (which would need Assumption 2.2) is
    not required.
(iv) fwd, bwd: the two identities of (4.1) with lambda on b, sigma, h, f, g, forcings unscaled,
    on one null set for all t in [0,T], cadlag versions M of the Ito integrals tied to the
    library integral at each t, the compensated Poisson integrals of the library.
Junk: every integral carries its integrability certificate; lawP2/uLift fallbacks only on null
sets. Nothing in the fields exceeds the paper's notion, and nothing less than it is asked.

Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless:
1. Coordinates; the filtration is a parameter (with Brownian/Poisson filtration certificates),
   instantiated with the standing augmented filtration in every statement.
2. Combined forced integrands lambda psi + q^psi (equivalent to separate integrals given square-
   integrable q); L2 stochastic integrals and pathwise drift and driver integrals (no loss: see the
   discussion of the Brownian channel; jump channel in the paper's L2 framework).
3. Forcing class with q^h marked progressive (wider than predictable; statements add PredForcing).
4. Cadlag encoded as right-continuity of every path plus a.s. left limits; Z, U vanish off [0,T];
   law flows lawP2 at every time; gamma a marked progressive representative; identities on one
   null set for all t, with cadlag versions of the Ito integrals.
Disagreements with the author's review (shown 2026-10-19T03:38:16Z): none
