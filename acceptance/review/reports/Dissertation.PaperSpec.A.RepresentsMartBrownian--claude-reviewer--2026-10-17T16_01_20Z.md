### A:ex:brownian: Dissertation.PaperSpec.A.RepresentsMartBrownian
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 12cb148176c5045b1b2bd36a25a42656 (pl-fp-v1:baed5214808dfa7d858b465bfdb2ef5fc5ed95f46d02bfae7512bd1bddf33e77)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T16:01:20Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T15:42:32Z):
Reading for def:Dissertation.PaperSpec.A.RepresentsMartBrownian (locked before seeing Lean).

Paper notion: the Brownian predictable representation (Ex 5.2: "the representation property is
the Brownian one"; Sec 2 PRP with the Poisson part removed): a square-integrable martingale M on
the Brownian filtration (W, F_0) is represented by Z if
 M_t = M_0 + int_0^t Z_s dW_s   a.s. for every t in [0,T],
with M_0 F_0-measurable and Z predictable (or progressive), E int_0^T |Z|_F^2 < inf (Z in H^2_W).
A def named "RepresentsMartBrownian (M, Z)" must state exactly that (the integral the L^2 Ito
integral against the d-dim W; R^m-valued M with Z in R^{m x d}). The PRP itself (existence and
uniqueness of such Z for every M) is a property, not this def. If the def instead says "every
square-integrable martingale has a representation" it is the PRP statement for the basis.
Requiring equality for each t a.s. or indistinguishably are equivalent for cadlag M.
Comparison (verdict recorded 2026-10-17T15:54:41Z):
Comparison for def:Dissertation.PaperSpec.A.RepresentsMartBrownian.

Lean: RepresentsMartBrownian W hG0 hW T M Z := ∃ (Z predictable for enlBrownian G0 W, each coordinate),
(Z = 0 off [0,T]), (finite energy E int_0^T |Z^j|^2 < inf), ∀ t in [0,T], M_t = M_0 + (int_0^t Z dW)
a.s., with the library multidimensional L^2 Ito integral sum_j int Z^j dW^j over enlBrownian.

Against my reading: "Z represents M": Z in H^2_W (predictable, square integrable) and
M_t = M_0 + int_0^t Z dW a.s. for every t in [0,T]: yes. Filtration: the usual augmentation of the
(W, G0) filtration: yes. Scalar M with Z in R^{1 x d}: an R^m-valued martingale is represented
coordinatewise, so harmless. M_0's F_0-measurability is not part of "represents" (it is a property of
the martingale M, assumed in ex_brownian_prp via Martingale M ...). The PRP itself (existence and
uniqueness for every square-integrable martingale) is the separate proposition ex_brownian_prp, as
my reading anticipated. Z extended by 0 off [0,T]: convention.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices: (1) scalar martingale M with Z in R^{1 x d} (the R^m case is
coordinatewise); (2) Z extended by 0 off [0,T]; (3) the identity a.s. at each t in [0,T] (for
cadlag M equivalent to indistinguishability); (4) the filtration fixed to the usual augmentation
enlBrownian of the (W, G0) filtration, with the library L^2 Ito integral over it.
Disagreements with the author's review (shown 2026-10-17T16:01:16Z): none
