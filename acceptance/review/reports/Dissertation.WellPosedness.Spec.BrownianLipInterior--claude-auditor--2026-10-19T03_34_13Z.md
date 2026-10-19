### A:ex:brownian: Dissertation.WellPosedness.Spec.BrownianLipInterior
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash 9e0655ad2249204f740fd58a17e0cae3 (pl-fp-v1:f7e9bc347d0db5d4c0e2468a38d89f624200886580e0f7be895be4582ef556e8)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:34:13Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:16:13Z):
Reading of def Spec.BrownianLipInterior (the interior half of Assumption 2.3, Brownian form).

Paper notion. Given L >= 0 (parameter or existential): for a.e. t in [0,T] and all diagonal inputs
(Theta,mu),(Theta',mu') in D_t (Theta, Theta' in L^2(Omega,F_t;H_B), mu, mu' their own laws),
almost surely
  |b(t,Theta,mu) - b(t,Theta',mu')| + |sigma(...) - sigma(...)|_F + |f(...) - f(...)|
     <= L (|X - X'| + |Y - Y'| + |Z - Z'|_F + W_2(mu,mu')).
A faithful Lean definition: "for a.e. t (Lebesgue on [0,T]) , BrownianLipInteriorAt t" with the
At-predicate as in r_13; a.e. on [0,T] (not on all of R, though a.e. on R restricted to [0,T] is
the same if the predicate is only required for t in [0,T]). The quantifier order: a.e. t first,
then all inputs, then a.s.
Comparison (verdict recorded 2026-10-19T03:32:33Z):
Comparison, Spec.BrownianLipInterior (BrownianForms.lean:91-93).

BrownianLipInterior F P T L C := for a.e. t (volume.restrict (Icc 0 T)), BrownianLipInteriorAt F P t
L C. Exactly the a.e.-t interior half of Brownian Assumption 2.3, quantifier order a.e. t first.
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-19T03:32:44Z): Label only. I recorded "faithful" for the a.e.-t wrapper itself (it is exactly "for a.e. t in
[0,T], BrownianLipInteriorAt"); the nu = 0 realisation of the Brownian reduction that the review
lists sits in the types (Coeffs (0 : Measure E)) and in BrownianLipInteriorAt, where I recorded it.
No disagreement in substance.
