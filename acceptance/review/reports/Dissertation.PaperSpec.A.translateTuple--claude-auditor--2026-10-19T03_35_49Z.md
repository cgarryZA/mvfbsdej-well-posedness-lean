### A:rem:uniq-no-integ: Dissertation.PaperSpec.A.translateTuple
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash 25b128e1a8bd16214207e456ab04981b (pl-fp-v1:fd6b804d04b1282cecb9ddb5b44575c53ed72c5ac818138cbe730cc1f6b23328)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:35:49Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:17:59Z):
Reading of def:Dissertation.PaperSpec.A.translateTuple (Remark 3.4).

Paper notion: "the shift X -> X - 2 sqrt t, applied to the state". 2 sqrt t is the antiderivative
of the singular drift t^{-1/2} vanishing at t=0, so the shift leaves X_0 = xi0 unchanged and
removes the singular drift: if X solves the singular forward equation, X - 2 sqrt t solves a
forward equation with drift b evaluated at the shifted-back point. Only the forward state X is
shifted; Y, Z, U are left unchanged.

A faithful Lean definition must: map a tuple (process or point at time t) Theta=(X,Y,Z,U) to
(X_t - 2 sqrt t, Y_t, Z_t, U_t) (or the inverse shift X_t + 2 sqrt t, depending on the direction
it is used in; either is harmless if used consistently), with a deterministic shift function
equal to 2 sqrt t (or a general deterministic A(t) with A(0)=0 instantiated at 2 sqrt t);
no change to Y, Z, U; the shift acts at every time t (also on left limits: since 2 sqrt t is
continuous, X_{t-} shifts by the same amount). For n>1 the shift must be in R^n (a vector-valued
A(t)); for the n=1 instance a scalar is fine.
Comparison (verdict recorded 2026-10-19T03:34:53Z):
Comparison: def translateTuple (PaperSpec/A/Sec3Rem34.lean:81-85): (x,y,z,u) -> (x + r, y, z, u),
r in R^n.
Reading: shift of the forward coordinate only, by a deterministic amount (2 sqrt t at time t),
either direction if used consistently.
Lean: adds r to the X channel, leaves (Y, Z, U) = theta.2 unchanged. It is used in
translatedCoeffs with r = r_t and in rem_uniq_translation with r_t = 2 sqrt t e, the solution of
the singular system being (X + 2 sqrt t e, Y, Z, U) for Theta = (X,Y,Z,U) a solution of the
translated system -- the inverse of the paper's X -> X - 2 sqrt t, consistent. Point-level
(acting on theta in H) rather than process-level; the process-level shift appears explicitly in
rem_uniq_translation. Nothing else to check (no junk values: total, linear).
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-19T03:35:36Z): none
