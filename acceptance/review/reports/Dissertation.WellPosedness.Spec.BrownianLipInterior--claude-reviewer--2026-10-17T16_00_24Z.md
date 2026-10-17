### A:ex:brownian: Dissertation.WellPosedness.Spec.BrownianLipInterior
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 9e0655ad2249204f740fd58a17e0cae3 (pl-fp-v1:f7e9bc347d0db5d4c0e2468a38d89f624200886580e0f7be895be4582ef556e8)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T16:00:24Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T15:42:31Z):
Reading for def:Dissertation.WellPosedness.Spec.BrownianLipInterior (locked before seeing Lean).

The interior half of Brownian Assumption 2.3 with a given constant L: for a.e. t in [0,T]
(Lebesgue a.e. on [0,T]), the fixed-time condition BrownianLipInteriorAt(L, t) holds, namely
for all Theta, Theta' in L^2(Omega, F_t; H_B) (F_t the Brownian W,F_0 filtration), a.s.
 |db| + |dsigma|_F + |df| <= L(|dX|+|dY|+|dZ|_F + W2(Law Theta, Law Theta')).
Faithful: "a.e. t" w.r.t. Lebesgue on [0,T] (an "all t" version is stronger; harmless only in
the sense that it narrows the propositions using it); L given as a parameter (or existential in
the Assumption); the quantifier over Theta,Theta' inside the a.e.-t (exceptional time set
independent of the inputs, which "for a.e. t and all ..." means).
Comparison (verdict recorded 2026-10-17T15:47:43Z):
Comparison for def:Dissertation.WellPosedness.Spec.BrownianLipInterior.

Lean: BrownianLipInterior F P T L C := ∀ᵐ t ∂(volume.restrict (Icc 0 T)), BrownianLipInteriorAt F P t L C,
C : Coeffs (0 : Measure E) n m d.
Against my reading: Lebesgue-a.e. t in [0,T] (not all t): yes; L given as a parameter: yes; the
quantifier over inputs is inside BrownianLipInteriorAt, so the exceptional time set does not
depend on the inputs ("for a.e. t and all (Theta,mu),(Theta',mu')"): yes. The fixed-time content
is BrownianLipInteriorAt (diagonal inputs, a.s. bound, Hilbert W2 on (X,Y,Z)-laws), compared in
its own unit; the Brownian setting is the nu = 0 realisation (trivial U channel).
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choice: the Brownian reduction is realised as coefficients at jump intensity
nu = 0 (Coeffs (0 : Measure E) n m d), where L^2(0; .) is a single point, so the U-coordinate and
the jump coefficient are deleted; harmless (the tuple space and its laws are those of
R^n x R^m x R^{m x d}, and the W2 term of the fixed-time condition is the Hilbert-norm W2 of the
(X,Y,Z)-laws). The a.e.-t quantifier itself is exactly the paper's.
Disagreements with the author's review (shown 2026-10-17T16:00:19Z): none
