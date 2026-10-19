### A:ex:brownian: Dissertation.WellPosedness.Spec.BrownianLipInteriorAt
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash 9e0655ad2249204f58e4f3cc2b928cf1 (pl-fp-v1:55c299c57278da40eb576d0e5d2941476d40d357310dba21aaf266eca7514157)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:34:13Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:16:13Z):
Reading of def Spec.BrownianLipInteriorAt (Assumption 2.3 interior bound at a fixed time t,
Brownian form).

Paper notion. For fixed t and L: for all Theta, Theta' in L^2(Omega, F_t; H_B) (F_t-measurable,
square integrable, H_B = R^n x R^m x R^{m x d} with norm |x|^2+|y|^2+|z|_F^2), with
mu = Law(Theta), mu' = Law(Theta') in P_2(H_B), almost surely (in omega)
  |b(t,Theta(w),mu) - b(t,Theta'(w),mu')| + |sigma(t,Theta(w),mu) - sigma(t,Theta'(w),mu')|_F
  + |f(t,Theta(w),mu) - f(t,Theta'(w),mu')|
     <= L (|X(w)-X'(w)| + |Y(w)-Y'(w)| + |Z(w)-Z'(w)|_F + W_2(mu,mu')).
A faithful Lean definition: exactly this; the measure argument must be the input's own law (not
free); F_t of the Brownian filtration (or of the basis). Norm on the matrix values: Frobenius
(using Lean's default sup/operator norm on matrices would change constants, acceptable only if
the paper's Frobenius norm is used or the difference is argued). W_2 the paper's.
Comparison (verdict recorded 2026-10-19T03:32:33Z):
Comparison, Spec.BrownianLipInteriorAt (BrownianForms.lean:79-86).

For all p, p' in diagonalInputs (0 : Measure E) n m d F P t (p.1 strongly F_t-measurable, MemLp 2,
p.2 = lawP2 P p.1), a.s.:
||b(t,p.1 w,p.2) - b(t,p'.1 w,p'.2)|| + ||dsigma|| + ||df||
  <= L (|dX| + |dY| + |dZ| + w2P (projP2 p.2) (projP2 p'.2)).
Norms: Euclidean on R^n, R^m; EuclideanSpace on Fin n x Fin d / Fin m x Fin d = Frobenius. W_2 on the
reduced laws with the Hilbert norm (equal to w2H at nu = 0). Measure argument = the input's own law.
Matches my reading; tuple in TupleH(0).
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices: the input tuple lives in TupleH at nu = 0 (trivial U-channel) instead of the
reduced space, and W_2 is taken on the projections projP2 of the laws to R^n x R^m x R^{m x d} with
its Hilbert norm - the paper's reduced W_2 (w2P_projP2 = w2H at nu = 0); the filtration is a
parameter.
Disagreements with the author's review (shown 2026-10-19T03:32:44Z): none
