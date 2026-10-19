### A:ex:brownian: Dissertation.PaperSpec.A.RepresentsMartBrownian
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash 12cb148176c5045b1b2bd36a25a42656 (pl-fp-v1:baed5214808dfa7d858b465bfdb2ef5fc5ed95f46d02bfae7512bd1bddf33e77)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:34:12Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:16:13Z):
Reading of def PaperSpec.A.RepresentsMartBrownian (Example 5.2: "the representation property is
the Brownian one").

Paper notion. A square-integrable martingale M for the Brownian filtration (augmentation of
sigma(F_0,W)) is represented by Z when M_t = M_0 + int_0^t Z_s dW_s for every t in [0,T] a.s.,
with Z predictable and E int_0^T |Z_s|^2 ds < inf (Z in H^2_W).
A faithful Lean definition: Z predictable (w.r.t. the Brownian filtration) and square-integrable
on [0,T] x Omega, and the identity at every t in [0,T] a.s. with the Ito integral w.r.t. W. Same
junk-value remark as r_07: the integrability of Z must be part of the definition or of every use.
Comparison (verdict recorded 2026-10-19T03:32:33Z):
Comparison, PaperSpec.A.RepresentsMartBrownian (Sec5BrownianReduction.lean:79-90).

- Z : R -> Omega -> Fin d -> R, each coordinate predictable for enlBrownian, vanishing off [0,T],
  finite energy; for every t in [0,T], a.s. M_t = M_0 + sum_j int_0^t Z^j dW^j (multidimensional
  L^2 Ito integral over enlBrownian, using hW). Integrability inside the existential. Matches my
  reading; scalar M.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices: scalar M (componentwise for vector martingales), Z a d-row normalised to
vanish off [0,T]; filtration enlBrownian (usual augmentation of sigma(F_0, W)); predictability,
finite energy and the identity for every t in [0,T] a.s. as in the paper.
Disagreements with the author's review (shown 2026-10-19T03:32:44Z): none
