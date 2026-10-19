### A:ex:brownian, A:rem:beta1-dich, A:sec5:overview: Dissertation.WellPosedness.System.projB
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash f41c30f5a4e6eb53b63a9ca646ce41dd (pl-fp-v1:128a5f3be4b646d7bb11ee2a42cb10dff7bb676cf64a529c4eb94d183ec53bd3)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:26:27Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:15:07Z):
Reading of def:Dissertation.WellPosedness.System.projB.

Paper notion. Example 5.2 deletes the U-coordinate from the tuple: the passage from the full
tuple theta = (x, y, z, u) in H = R^n x R^m x R^{m x d} x L^2(nu;R^m) to the reduced tuple
(x, y, z) in R^n x R^m x R^{m x d}.  The name projB presumably stands for this
"Brownian projection" theta |-> (x, y, z) (Remark 2.10 and Ex. 5.2 use it to compare the
Brownian case with the nu = 0 fibre case).  The paper uses the coordinate projections pi_Psi
(Ex. 5.1(ii), 05-examples.tex:112-114) and marginal projection of laws (Remark 2.6).

What a faithful Lean definition must be. The map H -> ReducedTuple, (x, y, z, u) |-> (x, y, z),
i.e. the coordinate projection forgetting the U-component, with no other change (no rescaling,
no reordering).  It is linear and 1-Lipschitz for the Hilbert norms (|x|^2+|y|^2+|z|_F^2 <=
|theta|_H^2), and an isometry when the fibre is trivial (nu = 0); measurable (continuous).
If it is instead defined in the other direction (an embedding of reduced tuples into H with
u = 0), it stands for the same identification when nu = 0 but must then be that embedding
(x, y, z) |-> (x, y, z, 0) exactly.  If "B" stands for something else (e.g. a projection of a
coefficient system or of a solution), the definition must be the corresponding coordinatewise
forgetting of the U-component; I will check the role against its uses.
Comparison (verdict recorded 2026-10-19T03:17:28Z):
Comparison for def:Dissertation.WellPosedness.System.projB (Examples/Brownian.lean:75-77).

Lean: projB (theta : TupleH nu n m d) : ReducedTuple n m d :=
  WithLp.toLp 2 (theta.1, WithLp.toLp 2 (theta.2.1, theta.2.2.1)).
TupleH = R^n x R^m x R^{m x d} x L2(nu; R^m) as nested products (x, (y, (z, u))), so theta.1 = x,
theta.2.1 = y, theta.2.2.1 = z.  projB theta = (x, (y, z)) in the reduced space.

Against my reading: this is exactly the coordinate projection (x, y, z, u) |-> (x, y, z) forgetting
the U-component, no rescaling or reordering. It is linear (projB_sub, projB_zero), measurable
(measurable_projB), 1-Lipschitz from the Hilbert norm of H to the reduced Hilbert norm
(norm_projB_le_norm_toL2), and an inverse of liftB (x,y,z) |-> (x,y,z,0) at nu = 0
(liftB_projB, projB_liftB). Its role (Ex. 5.2 / Rem. 2.10: identification of H at nu = 0 with the
reduced space, and the map along which reduced laws are taken) is the paper's.
No junk values (total, defined everywhere by coordinates).
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-19T03:26:15Z): none
