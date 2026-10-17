### A:lem:pert, A:sec4:WP-def: Dissertation.PaperSpec.A.WeakForcedSolution
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 6d8e8f373c5e26dad42e89a4945d5642 (pl-fp-v1:5f4610c4ad96a71ecde2af741ff414ff5989e20447bb72029b0b044875bf0ab4)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T16:02:24Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T15:42:32Z):
Reading for def:Dissertation.PaperSpec.A.WeakForcedSolution (locked before seeing Lean).

Paper notion (Lemma 4.3 hypotheses): Theta solves (4.1) at parameter lambda with an
F_0-measurable initial datum xi_0 and forcing q, where X, Y are cadlag adapted with
E int_0^T (|X_t|^2 + |Y_t|^2) dt < inf and X_T in L^2(Omega,F_T;R^n), Z in H^2_W, U in H^2_N;
identities of (4.1) a.s. for every t in [0,T] (with h at (Theta^-, mu^-)). Note: Lemma 4.3 asks
only F_0-measurability of xi_0 (not L^2), and the separate hypothesis Theta^1 - Theta^2 in HH is
not part of the single-solution notion. Faithful Lean: these integrability conditions (Hweak plus
X_T in L^2), not E sup; the forced identities as in ForcedSolution. Requiring xi_0 in L^2
inside the def would be narrower than Lemma 4.3 (harmless only if the proposition supplies it).
Comparison (verdict recorded 2026-10-17T15:57:38Z):
Comparison for def:Dissertation.PaperSpec.A.WeakForcedSolution.

Lean (PaperSpec/A/Setting.lean): WeakForcedSolution ... := (∃ gamma, PaperWeakSolutionForcedInt over enlJoint ...)
∧ every path of X and Y has left limits on (0,T]. PaperWeakSolutionForcedInt extends PaperWeakTuple
(X, Y adapted on [0,T], right-continuous paths on [0,T), a.s. left limits, E int_0^T |.|^2 < inf; Z
predictable, U marked predictable, finite energies, 0 off [0,T]) with: q a Forcing; forced drift and
driver integrands measurable, progressive, a.s. pathwise integrable; forced diffusion and jump
integrands measurable, progressive, finite energy; gamma represents h(Theta^-, mu^-); X_T in L^2; the
identities of (4.1) a.s. for all t in [0,T].

Against my reading (Lemma 4.3 hypotheses on each solution):
- X, Y cadlag adapted with E int (|X|^2 + |Y|^2) dt < inf, X_T in L^2(Omega, F_T): yes (adapted on
  [0,T] gives F_T-measurability of X_T).
- Z in H^2_W, U in H^2_N: yes.
- (4.1) identities with lambda on b, sigma, h, f, g and additive forcings, a.s. for every t: yes.
- xi0 only F_0-measurable in Lemma 4.3: the def imposes nothing on xi0 (not even L^2): not narrower.
- Theta^1 - Theta^2 in HH is not part of the single-solution notion: correct, left to the lemma.
- extra conditions: existence of the integrals made explicit (pathwise drift/driver, L^2
  diffusion/jump integrands), as for WeakSolution.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices: as for ForcedSolution, with the Hweak integrability: (1) combined
integrands lambda*psi + q^psi (linearity); (2) Poisson integral through a marked progressive
representative gamma of h(Theta^-, mu^-); (3) the existence of the integrals made explicit: forced
drift and driver integrands measurable with a.s. integrable paths, forced diffusion and jump
integrands measurable and square integrable; (4) X_T in L^2 explicit; (5) coordinates, cadlag
versions, identities on one null set, integrands extended by 0 off [0,T]; nothing imposed on xi0.
Disagreements with the author's review (shown 2026-10-17T16:02:16Z): The author's review entry is empty (no recorded reading). It should record that the def matches
Lemma 4.3's per-solution hypotheses (Hweak with X_T in L^2, nothing imposed on xi0, the
Theta^1 - Theta^2 in HH hypothesis left to the lemma), with the existence of the forced integrals
made explicit (pathwise drift/driver, L^2 diffusion/jump integrands) and q only a Forcing.
