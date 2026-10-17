### A:cor:robust, A:eq:coefmeas, A:eq:forced, A:eq:mvfbsdej, A:ex:concrete, A:intro:mvfbsdej, A:lem:cont, A:lem:pert, A:lem:small, A:rem:cwp-class, A:rem:generalrank, A:sec2:coefmeas, A:sec3:one-null-set, A:sec4:WP-def, A:sec4:horizon-not-contractive, A:sec:examples, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: Dissertation.WellPosedness.System.diffusionProc
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 38de1bfa70e0d9f65621b71beed53a93 (pl-fp-v1:fd9aff9beb5c0bd26e0e59d9f3ee7c2164e3f1a2485d8caab9e82efe2b0b9bc1)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:06:18Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:33:35Z):
Reading for diffusionProc (paper: the coefficient process (s,omega) -> sigma(s, Theta_s(omega), mu_s), (2.3)).
For a candidate tuple Theta = (X,Y,Z,U) and coefficients C, the diffusion process along Theta is
(s,omega) |-> sigma(s, Theta_s(omega), mu_s) in R^{n x d}, entry (i,j), with Theta_s(omega) = (X_s(omega),
Y_s(omega), Z_s(omega), U_s(omega,.)) in H (U_s(omega,.) as its L^2(nu) class) and mu_s = Law_P(Theta_s)
(the Borel representative of Lemma A.1, equal to the true law for a.e. s). Uses Theta_s (not the
left limits). Edge cases: at (s,omega) where U_s(omega,.) is not in L^2(nu), or s where Theta_s is not
in L^2(Omega;H) (law not in P_2), Lean needs a junk value; harmless if those sets are dt dP-null /
Lebesgue-null and only dt-a.e. or integrated claims are made. Restriction to [0,T]: the
process may be cut to [0,T] or not; any claim uses it only on [0,T].
Comparison (verdict recorded 2026-10-17T15:04:15Z):
Comparison for diffusionProc (System/Solves.lean): (Set.Icc 0 T).indicator (fun s => C.sigma s (tupleAt nu X Y Z U s omega)
(lawP2 P (tupleAt nu X Y Z U s)) ...) s -- entry (i,j) of sigma, R^{n x d} as EuclideanSpace on pairs evaluated at the tuple Theta_s(omega) = (X_s, Y_s, Z_s,
uLift U_s(omega,.)) (no left limits) and the law lawP2 P Theta_s of the full tuple at time s under P, cut to
[0,T].
Against my reading ((2.3)-style coefficient process (s,omega) -> sigma(s, Theta_s(omega), mu_s)): matches, with
(i) mu_s the exact law at every s (Dirac 0 when Theta_s is not in L^2) instead of Lemma A.1's Borel
representative -- equal for a.e. s for the paper's tuples, so the processes agree dt dP-a.e.; (ii) the
L^2(nu) channel uLift is 0 where U_s(omega,.) is not square integrable -- a dt dP-null set for U in H^2_N;
(iii) extension by 0 off [0,T] -- only [0,T] enters. Coordinates: tupleAt maps the coordinate
processes into TupleH (Euclidean X, Y; Z rows as the m x d channel; U as its L^2(nu;R^m) class).
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices (harmless):
1. The law argument is lawP2 P Theta_s at every time (the true law when Theta_s is in L^2, Dirac 0
   otherwise) instead of the Borel representative of Lemma A.1; they agree for a.e. s, so the
   process agrees dt dP-a.e. with the paper's and no integral or a.e. claim changes.
2. The jump-integrand channel of the tuple is uLift (the L^2(nu) class of e -> U_s(omega,e), 0 when not
   square integrable): a dt dP-null set for U in H^2_N.
3. The process is extended by 0 off [0,T] (indicator); only [0,T] is used.
Disagreements with the author's review (shown 2026-10-17T15:05:47Z): none (the author's excerpt shown for this unit is a marker and at most a section heading, with no
item-level reading to compare against; my comparison file records the representation choices in
detail).
