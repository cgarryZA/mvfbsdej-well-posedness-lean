### A:abstract, A:conclusion, A:cor:robust, A:eq:coefmeas, A:eq:forced, A:eq:mvfbsdej, A:ex:brownian, A:ex:concrete, A:ex:dealer, A:ex:fulllaw, A:intro:limin-comparison, A:intro:mvfbsdej, A:lem:cont, A:lem:pert, A:lem:small, A:rem:cwp-class, A:rem:generalrank, A:rem:regimes, A:rem:uniq-no-integ, A:sec3:one-null-set, A:sec4:WP-def, A:sec5:overview, A:sec:examples, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: Dissertation.WellPosedness.System.jumpProc
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash bfa4317d32adaf7b2cab0921e18838d1 (pl-fp-v1:ed914efee604e15d0baf2ec38b4116df10bf7093d55985d2256a986172d53f57)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:27:24Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:13:11Z):
Reading for def:Dissertation.WellPosedness.System.jumpProc (locked before any Lean is shown).

Paper notion ((1.1), (2.coefmeas), sec 2 "The jump terms are evaluated at the predictable
tuple"): the jump coefficient integrand
  (s, omega, e) |-> h(s, Theta_s^-(omega), e, mu_s^-),
  Theta_s^- = (X_{s-}, Y_{s-}, Z_s, U_s),  mu_s^- = Law(Theta_s^-),
values in R^n (or the L^2(nu;R^n)-valued map (s,omega) |-> h(s,Theta_s^-,.,mu_s^-)), predictable;
integrand of the compensated Poisson integral int_0^t int_E ... Ntilde(ds,de).
Crucial: LEFT LIMITS of X and Y (not X_s, Y_s): a compensated-Poisson integral of a non-predictable
integrand h(s, X_s, ...) would differ from the paper's (N charges the jump times of X, which are
atoms of N), so using Theta_s instead of Theta_s^- would change the forward equation. Z, U are
not replaced by left limits. The law argument is the law of Theta_s^- (which equals Law(Theta_s)
for a.e. s, so using Law(Theta_s) in the law slot is harmless; using Theta_s in the point slot is
not). Junk law values on a null set of times harmless as for driftProc.
A faithful Lean definition: fun s omega (e) => h s (leftlim tuple at s, omega) e (law), or the
L^2(nu)-valued version, with h the system's jump coefficient.
Comparison (verdict recorded 2026-10-19T03:25:27Z):
Comparison for def:Dissertation.WellPosedness.System.jumpProc.

Lean: jumpProc T gamma i s omega e = indicator_[0,T](s) * gamma i s omega e - the cut-off to the
horizon of a GIVEN pointwise jump integrand gamma. It does not itself evaluate h. My reading asked
for (s,omega,e) |-> h(s, Theta^-_s(omega), e, mu^-_s) with LEFT LIMITS of X, Y and the law of Theta^-.
In the Lean that content is carried by the gamma supplied at each use:
- in PaperSolution, jump_rep: for a.e. s in [0,T], a.s., e |-> gamma(s,omega,e) = C.h s
  (tupleAt (leftLimProc X) (leftLimProc Y) Z U s omega) (lawP2 P (same tuple)) nu-a.e. - left limits
  of X, Y, untouched Z, U, law of Theta^-_s, as the paper;
- in thm_stab (PaperSpec Sec3), gamma = coeffJump P T C (leftLimProc X2) (leftLimProc Y2) Z2 U2,
  a pointwise representative (lpRep) of C.h at the left-limit tuple and its law (coeffJump_ae_eq).
The Poisson integral is LevyStochCalc's L^2 integral, determined by the dt x dP x nu class of the
integrand, so any representative pinned down a.e. gives the paper's integral of the predictable
representative.
So jumpProc is faithful as what it is (horizon cut-off of a representative of the jump
coefficient); the evaluation at the predictable tuple, required by my reading, sits in the
consumers, where I found it correct.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices, harmless:
1. jumpProc is only the cut-off to [0,T] of a supplied pointwise integrand gamma. The paper's
   h(s,Theta^-_s,e,mu^-_s) is imposed on gamma where jumpProc is used: by PaperSolution.jump_rep
   (gamma represents C.h at tupleAt(leftLimProc X, leftLimProc Y, Z, U) and its law, for a.e. s, a.s.,
   nu-a.e.), or by taking gamma = coeffJump at the left-limit processes (thm_stab). The compensated
   Poisson integral is the L^2 one and depends only on the dt x dP x nu class, so this fixes the
   paper's integral.
2. Off [0,T] the value is 0. This is a normalisation.
Disagreements with the author's review (shown 2026-10-19T03:25:39Z): none
