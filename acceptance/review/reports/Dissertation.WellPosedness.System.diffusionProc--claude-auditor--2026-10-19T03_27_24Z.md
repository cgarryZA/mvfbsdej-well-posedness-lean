### A:abstract, A:conclusion, A:cor:robust, A:eq:coefmeas, A:eq:forced, A:eq:mvfbsdej, A:ex:brownian, A:ex:concrete, A:ex:dealer, A:ex:fulllaw, A:intro:limin-comparison, A:intro:mvfbsdej, A:lem:cont, A:lem:pert, A:lem:small, A:rem:cwp-class, A:rem:generalrank, A:rem:regimes, A:rem:uniq-no-integ, A:sec3:one-null-set, A:sec4:WP-def, A:sec4:horizon-not-contractive, A:sec5:overview, A:sec:examples, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: Dissertation.WellPosedness.System.diffusionProc
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash 38de1bfa70e0d9f65621b71beed53a93 (pl-fp-v1:fd9aff9beb5c0bd26e0e59d9f3ee7c2164e3f1a2485d8caab9e82efe2b0b9bc1)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:27:24Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:13:11Z):
Reading for def:Dissertation.WellPosedness.System.diffusionProc (locked before any Lean is
shown).

Paper notion ((1.1), (2.coefmeas)): the diffusion coefficient process along a tuple Theta,
  (s, omega) |-> sigma(s, Theta_s(omega), mu_s),   mu_s = Law(Theta_s) in P_2(H),
values in R^{n x d}; it is the integrand of int_0^t ... dW_s in the forward equation.
Evaluated at the current tuple Theta_s = (X_s, Y_s, Z_s, U_s) (not left limits; though for the dW
integral left limits would give the same integral since they differ on a dt x dP-null set), and
at the joint law mu_s of the full tuple at time s (Borel representative of s |-> Law(Theta_s),
agreeing with Law(Theta_s) for a.e. s). Progressively measurable along diagonal inputs.
A faithful Lean definition must be: fun s omega => sigma s (Theta_s omega) (law of Theta_s), with
the law being the push-forward of P under Theta_s as an element of P_2(H); at times s where
Theta_s is not square integrable the paper's mu_s is the Borel representative - any junk value
there is harmless provided this happens only on a Lebesgue-null set of times (which is the case
for tuples in the solution class). sigma must be the system's diffusion coefficient (not b, h).
Comparison (verdict recorded 2026-10-19T03:25:27Z):
Comparison for def:Dissertation.WellPosedness.System.diffusionProc.

Lean: diffusionProc P T C X Y Z U (coordinate) = indicator_[0,T](s) * C.sigma s (tupleAt nu X Y Z U s omega)
(lawP2 P (tupleAt nu X Y Z U s)) (coordinate), values R^{n x d}, entry (i,j).
- coefficient: C.sigma, the system's diffusion coefficient. OK.
- point argument: tupleAt at the current time s (X_s, Y_s, Z_s, U_s), not left limits - as the
  paper's sigma(s,Theta_s,mu_s). OK.
- law argument: lawP2 P Theta_s, the exact law of the full tuple at every time (push-forward when
  Theta_s in L^2, Dirac 0 junk otherwise). The paper's mu_s is a Borel representative agreeing with
  Law(Theta_s) for a.e. s; the process is used only as the integrand of the dW integral, which depends only on its
  dt x dP class, and for tuples of the solution class Theta_s is in L^2 for a.e. s (X,Y in S^2,
  Z,U in H^2 with the Fubini argument), so the junk value is taken only on a Lebesgue-null set of
  times. Harmless.
- vanishing off [0,T]: normalisation; only [0,T] enters (1.1).
- coordinates: one real coordinate per call (the vector-valued process is the family). OK.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices, harmless:
1. The law argument is the exact law lawP2 P Theta_s at every time, not a Borel representative.
   It agrees with the paper's mu_s for a.e. s, and its junk value (Dirac 0 when Theta_s is not
   square integrable) is taken only on a Lebesgue-null set of times for tuples of the solution
   class. The process enters only through the integrand of the dW integral, which sees only its dt x dP class.
2. The process is cut off to 0 outside [0,T] and returned coordinatewise. Neither changes
   anything on [0,T].
Disagreements with the author's review (shown 2026-10-19T03:25:39Z): none
