### A:lem:pert, A:sec4:WP-def: Dissertation.WellPosedness.System.PaperWeakSolutionForcedInt.mk
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash abbc9a6411f109000000000000000000 (pl-fp-v1:50bbb2aabffcbc4cd62877c5fb003de2adb452bd0820b962a194483038222c70)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:38:45Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:15:38Z):
Reading (locked before any Lean): def PaperWeakSolutionForcedInt.mk - the constructor of the
structure PaperWeakSolutionForcedInt (implementation's weak forced solution of (4.1)).

Paper notion: the same as for the structure (see my reading of PaperWeakSolutionForcedInt and of
WeakForcedSolution): the constructor builds the record from its fields; it is faithful iff its
argument list (the fields: weak-class membership of X, Y, Z, U; integrability side conditions
making the integrals of (4.1) genuine; the two identities of (4.1) at parameter lambda with
initial datum xi_0 and forcing q) is exactly the paper's notion - neither stronger (narrowing the
weak class of Lemma 4.3) nor weaker (letting junk values satisfy the identities). A constructor
introduces no meaning of its own beyond the structure's fields, so its verdict should coincide
with that of the structure, unless the constructor's type exposes a field type the structure
hides (e.g. implicit arguments, universe or instance arguments).
Comparison (verdict recorded 2026-10-19T03:33:17Z):
Comparison: def PaperWeakSolutionForcedInt.mk (constructor) against my locked reading.

The constructor's type takes, with all parameters implicit (Omega, E, nu, n, m, d, P, D, F with
its Brownian/Poisson certificates, T, lam, C, xi0, q, X, Y, Z, U, gamma), exactly the fields of
the structure in order: toPaperWeakTuple, forcing, b_meas, b_prog, b_int, sigma_meas,
sigma_prog, sigma_sq, gamma_meas, gamma_prog, gamma_sq, f_meas, f_prog, f_int, jump_rep, XT_sq,
fwd, bwd, and returns PaperWeakSolutionForcedInt D F hFW hFN T lam C xi0 qb qsigma qh qf qg
X Y Z U gamma. It introduces no meaning beyond the structure; no instance or universe argument
changes the content. The later fields depend on the earlier ones as integrability certificates
(sigma_meas, sigma_prog, sigma_sq, gamma_meas, gamma_prog, gamma_sq feed the integrals in fwd),
as in the structure. Its verdict is the structure's (see my comparison for
PaperWeakSolutionForcedInt): the fields are the paper's notion of a weak solution of (4.1) in
Lemma 4.3's class, with the representation choices listed there.

Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — The constructor carries exactly the structure's fields, so its representation choices are those
of PaperWeakSolutionForcedInt, each harmless:
1. Combined forced integrands lambda psi + q^psi (equivalent to separate integrals given square-
   integrable q); L2 stochastic integrals, pathwise drift and driver integrals.
2. Forcing class with q^h marked progressive (statements add PredForcing).
3. Cadlag encoded as right-continuity of every path plus a.s. left limits; Z, U vanish off [0,T];
   law flows lawP2 at every time; gamma a marked progressive representative; identities on one null
   set for all t with cadlag versions of the Ito integrals; the filtration is a parameter.
Disagreements with the author's review (shown 2026-10-19T03:38:36Z): none
