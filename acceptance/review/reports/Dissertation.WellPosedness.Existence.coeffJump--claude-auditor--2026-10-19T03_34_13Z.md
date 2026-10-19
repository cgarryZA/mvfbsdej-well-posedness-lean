### A:abstract, A:conclusion, A:cor:robust, A:rem:generalrank, A:thm3.1:companion, A:thm:cwp, A:thm:stab: Dissertation.WellPosedness.Existence.coeffJump
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash 90dd30b497d4dd12d6d4dda771a35c05 (pl-fp-v1:29fae3d5c341d5bfd94b1ca9e9852331540e6aa621b45fdf7ff46a7ce83300de)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:34:13Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:16:14Z):
Reading of def Existence.coeffJump (the jump coefficient process along a tuple: (1.1)'s
h(s, Theta_s^-, e, mu_s^-), used in the forward equation and in (2.5), (4.1), (3.x)).

Paper notion. Given h : [0,T] x H x P_2(H) -> L^2(nu;R^n) (or pointwise h(t,theta,e,mu)) and a tuple
process Theta = (X,Y,Z,U), the jump integrand is
  (s,omega,e) |-> h(s, Theta_s^-(omega), e, mu_s^-),  Theta_s^- = (X_{s-}, Y_{s-}, Z_s, U_s),
  mu_s^- = Law(Theta_s^-) (Borel representative, equal to Law(Theta_s) for a.e. s),
read through a P (x) E-measurable representative (2.3). The paper explicitly evaluates at the left
limits (predictable tuple) and the predictable law flow.
A faithful Lean definition: evaluates h at (s, (X_{s-}(w), Y_{s-}(w), Z_s(w), U_s(w)), mu_s^-) and
the mark e (or returns the L^2(nu)-valued map (s,w) |-> h(s,Theta_s^-(w),mu_s^-)). Representation
choices: using Theta_s instead of Theta_{s-}, or Law(Theta_s) instead of Law(Theta_s^-), changes the
integrand only on a dt dP(-nu) null set; that is harmless if and only if the Poisson integral is
the L^2-isometric (class-based) one, not a pathwise sum over atoms of N; and predictability must
still hold or be obtainable for the class. Junk: for U_s(w) given as an L^2(nu) element, the
pointwise value at e must come from a representative that is jointly measurable.
Comparison (verdict recorded 2026-10-19T03:32:34Z):
Comparison, Existence.coeffJump (Existence/CoeffBorel.lean:110-113).

coeffJump P T C X Y Z U i s w e = lpRep(1_[0,T](s) C.h s (tupleAt X Y Z U s w) (lawP2 P (tupleAt X Y Z U
s)), e)_i: the i-th coordinate of a jointly measurable representative of h(s, Theta_s(w), ., mu_s),
cut off to [0,T], Theta_s the tuple of the given coordinate processes (U-channel the L^2 class uLift,
0 when not square integrable) and mu_s its law at time s (Dirac junk off L^2).
- The definition is generic in the tuple; at every use in PaperSpec (Sec3.lean thm_stab, Sec3
  Stability, Cor 3.6, Sec3GeneralRank) it is applied to (leftLimProc X, leftLimProc Y, Z, U), i.e.
  the predictable tuple Theta^-_s = (X_{s-}, Y_{s-}, Z_s, U_s) and its law mu^-_s: the paper's
  h(s, Theta^-_s, e, mu^-_s). leftLim at s = 0 reads negative times (unconstrained), a single dt-null
  time.
- Junk values (uLift 0, Dirac law) occur only where U_s(w,.) is not in L^2(nu) or Theta^-_s not in
  L^2, a dt (x) dP-null set / dt-null set of times for the paper's tuples; the integrand is used only
  through energies and L^2 integrals, which do not see null sets.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices: the definition takes the tuple as arguments, and the left limits are
supplied at the use sites (leftLimProc X, leftLimProc Y), giving h(s, Theta^-_s, e, mu^-_s) with
mu^-_s the pointwise law of Theta^-_s; it is the jointly measurable representative lpRep of the
L^2(nu;R^n) value, cut off to [0,T]; the U-channel is the L^2 class uLift (0 where U_s(w,.) is not
square integrable) and the law is lawP2 (Dirac 0 off L^2) - junk only on null sets of (s,w) or of
times for the paper's tuples, which the energies and L^2 integrals in which coeffJump is used do not
see; the value at s = 0 (left limit from negative times) is a dt-null time.
Disagreements with the author's review (shown 2026-10-19T03:32:45Z): Verdict agrees (faithful with representation choices). One disagreement on the review's point 1:
coeffJump does not itself fix the evaluation point. It evaluates h at the tuple of whatever
coordinate processes it is given, with that tuple's law, and every use in Dissertation/PaperSpec
(thm_stab in Sec3.lean, Sec3Stability, Corollary 3.6 in Sec3.lean, Sec3GeneralRank) passes
(leftLimProc X, leftLimProc Y, Z, U). So at the use sites it is evaluated at the predictable tuple
Theta^-_s and its law mu^-_s, exactly as printed, and the "a.e. equal to Theta_s" argument is not
needed there (it is needed only where Theta_s itself is passed). Minor point: the left limit at s = 0
reads the unconstrained values at negative times, but that is a single dt-null time.
