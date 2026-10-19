### A:ex:brownian: Dissertation.WellPosedness.Spec.BrownianPaperWeakSolution.mk
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash 71b4d5da999e7ef30000000000000000 (pl-fp-v1:d0c429b36f78a9d3b3c7aac93a4064b662518b8dcfcab2fb220282a14661c2e7)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:34:13Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:16:13Z):
Reading of def Spec.BrownianPaperWeakSolution.mk (constructor of the structure of r_17).

Paper notion: building a weak-class Brownian solution from its components and properties; faithful
iff the structure r_17 is; the arguments must be exactly r_17's fields with nothing extra.
Comparison (verdict recorded 2026-10-19T03:32:33Z):
Comparison, Spec.BrownianPaperWeakSolution (BrownianForms.lean:251-328) against my locked reading.

- X, Y: adapted on [0,T], every path right-continuous on [0,T), a.s. left limits on (0,T], finite
  energy E int_0^T |X_i|^2 < inf, E int_0^T |Y_k|^2 < inf (Hweak). No E sup condition. OK.
- XT_sq: X_T in L^2 coordinatewise - the presupposition Law(X_T) in P_2 of the paper (Thm 3.3 proof).
- Z: predictable, vanishing off [0,T], finite energy (H^2_W). OK.
- Coefficient processes: b and f jointly and progressively measurable with a.s. integrable paths
  on [0,T] (pathwise drift/driver integrals - no square integrability required, matching Remark 3.4
  "uniqueness without origin integrability"); sigma jointly/progressively measurable with finite
  energy (needed for the L^2 Ito integral). Under Assumption 2.3 along an Hweak tuple, finite energy
  of sigma is equivalent to sigma(.,0,delta_0) in L^2(0,T), which is also necessary for even a
  local Ito integral of the (deterministic part of the) diffusion; harmless representation of
  "the integrals of (1.1) exist".
- fwd/bwd identities as in the strong class (a.s. simultaneously for t in [0,T], cadlag versions).
- Law flow pointwise as before; terminal law genuine since X_T in L^2.
Verdict: faithful with representation choices.

For the constructor BrownianPaperWeakSolution.mk: its arguments are exactly the fields above; it
adds nothing. Same verdict as the structure.
Witness: —
Verdict: faithful with representation choices — Representation choices: (1) coordinates; processes on R with only [0,T] constrained; Z cut off to
vanish off [0,T]; (2) cadlag as every path right-continuous on [0,T) with a.s. left limits (the
PaperSpec wrapper BrownianWeakSolution asks left limits on every path); (3) identities on one
full-measure set for all t in [0,T] with cadlag versions of the Ito integrals (equivalent for cadlag
processes); (4) pointwise law flow, Dirac junk only on a dt-null set of times; Law(X_T) genuine as
X_T in L^2 is a field (the paper's presupposition); (5) "the integrals exist" is made explicit: b, f
measurable with a.s. integrable paths (pathwise integrals, no origin integrability needed, as in
Remark 3.4), sigma measurable with finite energy (L^2 Ito integral; under Assumption 2.3 along an
Hweak tuple this is equivalent to sigma(.,0,delta_0) in L^2(0,T), which any Ito integral of the
deterministic part requires).
Disagreements with the author's review (shown 2026-10-19T03:32:45Z): none
