### A:abstract, A:ass:lip, A:conclusion, A:cor:robust, A:eq:coefmeas, A:eq:hborel, A:eq:termg, A:ex:brownian, A:ex:concrete, A:ex:dealer, A:ex:fulllaw, A:intro:limin-comparison, A:lem:cont, A:lem:lawflow, A:lem:pert, A:lem:small, A:rem:beta1-dich, A:rem:cwp-class, A:rem:diag-mono, A:rem:generalrank, A:rem:intrinsic, A:rem:regimes, A:rem:uniq-no-integ, A:rem:wasserstein-bounds, A:sec2:hborel-derivation, A:sec4:horizon-not-contractive, A:sec5:overview, A:sec:examples, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: Dissertation.Law.w2P
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash 588aff30f5cf1efb222cb5540209de44 (pl-fp-v1:13ac7e9324519826bd6ccecf1c3542c37dfa38e21498aa8f9aec71ccf3820a55)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:27:45Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:13:55Z):
Reading of def:Dissertation.Law.w2P.

Paper notion. W_2(mu, mu') for mu, mu' in P_2(S) (the paper's W_2 is only ever applied to
elements of P_2): the same quantity as in the reading of w2, restricted to the type P_2(S).

Faithful Lean definition: w2P mu mu' := w2 (underlying measure of mu) (underlying measure of mu')
(or a definition that equals the paper's W_2 of the two underlying measures). Since both
arguments are in P_2, there is no junk: couplings exist and have finite cost. It must be the
distance itself (square root of the optimal cost), not its square, unless named/used as such.
Comparison (verdict recorded 2026-10-19T03:18:45Z):
def:Dissertation.Law.w2P (Dissertation/Law/P2.lean:69-70): w2P μ ν := w2 μ.law ν.law.
Against the reading: W_2 of the two underlying measures of P_2 elements; since both have finite
second moment, w2sq is finite (w2sq_ne_top), so the toReal junk of w2 is never reached and w2P is
exactly W_2 (the distance, not its square), in the norm of E. Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-19T03:27:24Z): none
