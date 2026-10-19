### A:rem:uniq-no-integ: Dissertation.PaperSpec.A.translatedCoeffs
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash a6d589d1c49f1879976bb03fd33b7999 (pl-fp-v1:a000dcb172f37524bd8ff84b2fa97a99eeadfbcad40736a725644f9f55b726c6)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:35:50Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:17:59Z):
Reading of def:Dissertation.PaperSpec.A.translatedCoeffs (Remark 3.4).

Paper notion: the system obtained by the shift X -> X - 2 sqrt t "applied to the state and
translating the law argument accordingly". With tau_t(theta) := theta + (A(t),0,0,0), A(t)=2 sqrt t,
the translated coefficients are
  psi~(t,theta,mu) := psi(t, tau_t theta, (tau_t)_# mu),  psi in {sigma, h, f},
  b~(t,theta,mu)   := b(t, tau_t theta, (tau_t)_# mu)  [with the singular drift t^{-1/2}=A'(t)
                      removed, i.e. b~ = b_singular(...) - A'(t) = b_base(...)],
  g~(x,rho)        := g(x + A(T), (x -> x + A(T))_# rho),
so that Theta solves the singular system iff Theta - (A,0,0,0) solves the translated one, and the
translated system satisfies Assumptions 2.2-2.5 (its origin value b(t,(A(t),0,0,0),delta) is in
L^2 by Lipschitz since A is bounded on [0,T]; diagonal pairs map to diagonal pairs, so Lip/mono
constants carry over).

A faithful Lean definition must: evaluate each coefficient at the shifted point AND at the
pushforward of the law argument under the same shift (the law translation is part of the
paper's construction; for a law-free base such as Example 5.1(i) it is immaterial); shift only the
X-coordinate; shift g's state and terminal-law argument by A(T); remove the drift term A'(t) from
b (if it is applied to the singular system) or start from the base system (if applied to it).
The direction of the shift must be consistent with translateTuple.
Comparison (verdict recorded 2026-10-19T03:34:53Z):
Comparison: def translatedCoeffs C r T (PaperSpec/A/Sec3Rem34.lean:87-97).
Lean: psi~(t,theta,mu) = psi(t, theta + (r_t,0,0,0), lawP2 mu.law (translateTuple r_t)) for
psi in {b, sigma, h, f}; g~(x,rho) = g(x + r_T, lawP2 rho.law (. + r_T)).
Reading: each coefficient at the shifted point AND at the pushforward of the law argument under
the same shift; only X shifted; g shifted by A(T) in state and terminal law; the singular drift
removed (start from the base system).
- lawP2 (mu.law) (translateTuple r_t) is the law of the map translateTuple r_t under the
  probability measure mu.law: since mu has finite second moment and the translation is
  continuous with |theta + r| <= |theta| + |r|, the map is in L^2(mu.law), so lawP2 returns the
  genuine pushforward (tau_{r_t})_# mu (no junk value). Same for rho.
- It is applied to the BASE system C (rem_uniq_translation uses translatedCoeffs C (2 sqrt t e)
  with C the system without t^{-1/2}), so b~ contains no singular drift: if Theta~ solves C~,
  X = X~ + 2 sqrt t e satisfies dX = b(t, Theta, Law Theta) dt + t^{-1/2} e dt + ..., with
  Law(Theta_t) = (tau_{r_t})_# Law(Theta~_t) and Theta~^- + r_t = Theta^- (r continuous); the
  terminal g~(X~_T, Law X~_T) = g(X_T, Law X_T). Consistent with translateTuple's direction.
- The terminal law shift uses r_T at the fixed horizon T (a parameter of the def). Matches.
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-19T03:35:36Z): none
