### A:abstract, A:ex:dealer, A:ex:fulllaw, A:rem:regimes, A:rem:wasserstein-bounds, A:sec5:overview: Dissertation.Law.P2.margU
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash 537c6d484c8f0e8b128e7c03175bc3a7 (pl-fp-v1:74fb9d3710f3a218b3c79f33994db8cf4608a2dd998a813e5bd1dead39c7aab4)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:27:45Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:13:54Z):
Reading of def:Dissertation.Law.P2.margU.

Paper notion. Remark 2.6: "write mu^U in P_2(L2(nu)) for the U-marginal of mu"; Ex. 5.4
(W_2(mu^U, Lambda_0), int phi_j d mu^U), Ex. 5.5 (A_{mu^U}(u), "mu^U the U-marginal of the
measure argument", and on the diagonal mu^U = Law(U)). The U-marginal of mu in P_2(H),
H = R^n x R^m x R^{m x d} x L2(nu;R^m), is the image measure (pi_U)_# mu where pi_U(x,y,z,u)=u;
it lies in P_2(L2(nu)) because ||u|| <= |theta|_H.

Faithful Lean definition: margU mu := the element of P2 (L2(nu)) whose underlying measure is
Measure.map (U-coordinate projection) mu, where the U-coordinate is the L2(nu)-valued fourth
component of whatever Lean type represents H. The projection must pick the u-component (not y or
z), and the target must be the paper's L2(nu;R^m) (Mathlib Lp with p=2 of the mark measure nu)
carrying its Borel sigma-algebra. If H is represented with a sup-norm product, the P_2 property
of the marginal still holds; the marginal itself is independent of the norm. The consequence
Law(Theta)^U = Law(U) must hold (pushforward composes).
Comparison (verdict recorded 2026-10-19T03:18:45Z):
def:Dissertation.Law.P2.margU (Dissertation/Law/TupleMarginal.lean:80-84):
  μ.margU := μ.map measurable_projUH norm_projUH_le,
projUH = snd ∘ snd ∘ snd : TupleH ν n m d →L[ℝ] Lp (EuclideanSpace ℝ (Fin m)) 2 ν (projUH θ =
θ.2.2.2), TupleH ν n m d = ℝⁿ × ℝᵐ × ℝ^{m×d} × L²(ν; ℝᵐ) (System/Tuple.lean:134).
Against the reading: value = (π_U)_# μ with π_U(x,y,z,u) = u, the fourth (jump) channel, valued
in Mathlib's L²(ν; ℝᵐ) with its Borel sigma-algebra (scoped lpMeasurableSpace := borel). This is
the paper's μ^U. The norm bound used (‖projUH θ‖ ≤ ‖θ‖ for the max-of-channels norm) is only the
P_2 obligation; the marginal is independent of the norm on H. Measurability of projUH holds for the
product sigma-algebra on TupleH. The consequence Law(Θ)^U = Law(U) is margU_lawP2 in the same
file (pushforward composes). The section variables [SigmaFinite ν] [CountablyGenerated E] are not
in the signature, so the definition does not depend on them. Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-19T03:27:23Z): none
