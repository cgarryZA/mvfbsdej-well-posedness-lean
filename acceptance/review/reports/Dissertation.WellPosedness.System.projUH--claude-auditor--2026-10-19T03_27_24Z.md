### A:abstract, A:ex:dealer, A:ex:fulllaw, A:rem:regimes, A:rem:wasserstein-bounds, A:sec5:overview: Dissertation.WellPosedness.System.projUH
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash 5ed7e50cc9210991ccbb6cdcbcc90dbb (pl-fp-v1:ee12fcdd5d431e67bbb76409a7c6cba2039942cfb55037d2d57829692e70902e)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:27:24Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:13:12Z):
Reading for def:Dissertation.WellPosedness.System.projUH (locked before any Lean is shown).

Paper notion (Remark 2.6 (2.margproj); Examples 5.4, 5.5): the U-marginal projection
  H -> L^2(nu;R^m), theta = (x,y,z,u) |-> u,
and the induced marginal map P_2(H) -> P_2(L^2(nu)), mu |-> mu^U := push-forward of mu under it,
which is 1-Lipschitz for W_2. mu^U is the U-marginal of the measure argument; along diagonal
inputs, mu^U = Law(U).
A faithful Lean definition: the fourth coordinate projection of the paper's H (a continuous
linear 1-Lipschitz map), or the push-forward of a law by it as an element of P_2(L^2(nu)).
It must pick the U component (not Z), with no rescaling.
Comparison (verdict recorded 2026-10-19T03:25:28Z):
Comparison for def:Dissertation.WellPosedness.System.projUH.

Lean: projUH := snd o snd o snd as a continuous linear map TupleH nu n m d ->L Lp (R^m) 2 nu. On
theta = (x,(y,(z,u))): snd -> (y,(z,u)), snd -> (z,u), snd -> u. So theta |-> u, the U-channel
projection. No rescaling; picks u, not z. Linear and 1-Lipschitz (|u| <= max norm <= Hilbert norm).
The induced marginal mu^U is formed elsewhere (margU) by push-forward; this unit is the
coordinate map of my reading. Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-19T03:25:40Z): none
