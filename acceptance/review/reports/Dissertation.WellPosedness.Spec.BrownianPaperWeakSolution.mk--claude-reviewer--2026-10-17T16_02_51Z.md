### A:ex:brownian: Dissertation.WellPosedness.Spec.BrownianPaperWeakSolution.mk
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 71b4d5da999e7ef30000000000000000 (pl-fp-v1:d0c429b36f78a9d3b3c7aac93a4064b662518b8dcfcab2fb220282a14661c2e7)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T16:02:51Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T15:42:32Z):
Reading for def:Dissertation.WellPosedness.Spec.BrownianPaperWeakSolution.mk (locked before Lean).

Constructor of BrownianPaperWeakSolution: fields (X, Y, Z) on the Brownian basis with X, Y cadlag
adapted, E int_0^T |X|^2 dt < inf, E int_0^T |Y|^2 dt < inf, X_T in L^2 (presupposed by the
terminal law), Z in H^2_W, and the Brownian forward and backward identities a.s. for every t,
mu_s = Law Theta_s. Faithful iff the fields are exactly these (no E sup, nothing missing).
Comparison (verdict recorded 2026-10-17T15:58:56Z):
Comparison for def:Dissertation.WellPosedness.Spec.BrownianPaperWeakSolution.mk (constructor).

The constructor's fields are exactly those of BrownianPaperWeakSolution (Spec/BrownianForms.lean:240-328),
compared in that unit: X, Y adapted on [0,T], every path right-continuous on [0,T), a.s. left limits,
finite energy E int_0^T |.|^2 (no E sup); Z predictable, 0 off [0,T], finite energy; drift and driver
processes jointly/progressively measurable with a.s. integrable paths on [0,T]; diffusion process
measurable, progressive, finite energy; X_T in L^2; the two identities a.s. for all t with cadlag
versions of the Ito integrals.

Against my reading: (X, Y, Z) in the Brownian Hweak with X_T in L^2 and the Brownian identities with own
laws: present; no E sup; nothing missing; the extra fields make the integrals exist.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices (those of BrownianPaperWeakSolution): Brownian reduction at nu = 0;
coordinates; cadlag as every path right-continuous on [0,T) plus a.s. left limits; cadlag versions
of the Ito integrals with the identities on one null set; the existence of the integrals made
explicit (drift and driver pathwise integrable, diffusion of finite energy, measurability of the
coefficient processes); X_T in L^2 explicit; Z extended by 0 off [0,T].
Disagreements with the author's review (shown 2026-10-17T16:02:47Z): none (the author's entry for the constructor is empty, but the review of
BrownianPaperWeakSolution just above it names this constructor and describes its fields).
