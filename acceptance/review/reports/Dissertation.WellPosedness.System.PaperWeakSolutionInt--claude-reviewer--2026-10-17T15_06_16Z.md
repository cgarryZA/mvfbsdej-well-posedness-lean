### A:cor:robust, A:rem:cwp-class, A:rem:generalrank, A:sec:examples, A:thm:uniq: Dissertation.WellPosedness.System.PaperWeakSolutionInt
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 0dd47e8a79576bf20000000000000000 (pl-fp-v1:548810fe1944bd5aaa604f0ac1624282d93688676d2b2723c2d83a963efbd173)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:06:16Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:33:34Z):
Reading for PaperWeakSolutionInt (paper: "Theta in Hweak satisfies (1.1)", Thm 3.3, Rem 3.2).
Theta = (X,Y,Z,U) in Hweak: X (R^n), Y (R^m) cadlag adapted with E int_0^T |X_t|^2 dt < inf,
E int_0^T |Y_t|^2 dt < inf; Z predictable R^{m x d} with E int |Z|_F^2 < inf; U predictable L^2(nu;R^m)
with E int ||U||^2 < inf. Satisfying (1.1) for every t in [0,T] a.s. (both identities), with h at
the predictable tuple and laws mu_t = Law(Theta_t), mu^-_t = Law(Theta^-_t); the terminal term
g(X_T, Law X_T) presupposes Law(X_T) in P_2(R^n), i.e. X_T in L^2 (as the proof of Thm 3.3 notes).
The integrals in (1.1) must exist along Theta (that is what "Int"/admissibility should carry);
no S^2 requirement (that is the conclusion of Rem 3.2), no requirement that the individual
coefficient processes are square integrable beyond what existence of the integrals needs (Thm 3.3
assumes no Ass 2.2; Rem 3.4). With Ass 2.2-2.3, coefficient processes along an Hweak tuple are
square-integrable anyway ((4.2)), so for Rem 3.2 any reasonable integrability requirement is harmless;
for Thm 3.3 (Ass 2.3-2.5 only) a requirement of square-integrable sigma, h would be implied? Under
Lipschitz only, sigma(s,Theta_s,mu_s) is square integrable iff the origin value sigma(s,0,delta_0)
is (square-integrable in s) -- not implied; but for the Ito integral of sigma to exist as an L^2
integral it must be square-integrable, so the paper implicitly requires it for a solution.
Faithful Lean: Hweak + X_T in L^2 + integrals exist + both identities.
Comparison (verdict recorded 2026-10-17T12:41:21Z):
Comparison for PaperWeakSolutionInt (System/PaperWeakSolutionInt.lean:120): extends PaperWeakTuple
(Theta in Hweak) and PaperAdmissibleInt (reviewed: integrals of (1.1) exist, drift/driver pathwise
integrable, diffusion and jump L^2, gamma representing h at the predictable tuple), adds XT_sq (each
coordinate of X_T in L^2) and the identities fwd, bwd, which are exactly those of PaperSolution
(reviewed): a.s. for all t in [0,T], X_t = xi0 + int_{[0,t]} b ds + M_t + int_0^t int gamma Ntilde and
Y_t = g(X_T, Law X_T) + int_{[t,T]} f ds - (M_T - M_t) - (int_0^T - int_0^t) int U Ntilde with cadlag
versions M of the Brownian integrals.
Against my reading: Hweak (not S^2) -- yes; X_T in L^2 (the terminal law in P_2) -- yes, as a field;
integrals exist with no L^2 requirement on the drift/driver -- yes (pathwise integrability), matching
Thm 3.3/Rem 3.4 without Ass 2.2; the L^2 requirement on the diffusion and jump integrands is the
existence of the paper's L^2 stochastic integrals, and is implied under Ass 2.3 for any Hweak tuple
along which the integrals exist; both identities at every t on one null set (equivalent to the
paper's for-every-t, by right continuity). terminalVal uses lawP2 P X_T, the true law since X_T in L^2.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices (harmless): those of PaperWeakTuple and PaperAdmissibleInt (coordinate
encoding; every-path right continuity, a.s. left limits; Z, U vanishing off [0,T]; exact laws at every
time with Dirac-0 junk off L^2; uLift junk on a null set; marked-progressive representative gamma of
the predictable jump integrand; L^2 existence conditions for the stochastic integrals, pathwise for
the Lebesgue ones; junk left limits at time 0) and of PaperSolution's identities (one null set for all
t in [0,T], cadlag versions M of the per-time Brownian L^2 integrals). xi0 is an arbitrary function
(no L^2, as Thm 3.3 has no Ass 2.2).
Disagreements with the author's review (shown 2026-10-17T15:05:45Z): none (the author's excerpt shown for this unit is a marker and at most a section heading, with no
item-level reading to compare against; my comparison file records the representation choices in
detail).
