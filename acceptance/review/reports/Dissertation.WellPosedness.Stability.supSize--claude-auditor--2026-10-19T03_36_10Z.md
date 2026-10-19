### A:abstract, A:conclusion, A:cor:robust, A:lem:pert, A:rem:generalrank, A:rem:uniq-no-integ, A:sec3:HH-banach, A:sec4:horizon-not-contractive, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: Dissertation.WellPosedness.Stability.supSize
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash 8d946a220ee9b35c3ccfc7f258215a40 (pl-fp-v1:ab982025c40f9d7041f354c719dbf3d4dae6f03d190546e1f4cdcf702aed6101)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:36:10Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:18:00Z):
Reading of def:Dissertation.WellPosedness.Stability.supSize.

From the name and its users (Thm 3.1 stability, Thm 3.3, Lemma 4.3, Sec. 3 "S is Banach", Thm 3.5,
Cor 3.6): the squared S-norm of Sec. 3,
  ||Theta||_S^2 = E sup_{t<=T}|X_t|^2 + E sup_{t<=T}|Y_t|^2 + E int_0^T (|Z_t|_F^2 + ||U_t||^2_{L^2(nu)}) dt,
used for the left-hand side of (3.1) eq:stab / (4.14) eq:contpert (applied to the difference delta Theta) and for the
membership Theta in S (finiteness).

A faithful Lean definition must:
- take the sup over t in [0,T] (the closed interval including T and 0) of |X_t|^2 and |Y_t|^2
  pathwise, then the expectation; for cadlag processes the sup over all t equals the sup over a
  countable dense set, so measurability is not an issue; an essential sup in t would differ only
  for non-cadlag processes;
- the Euclidean norm on R^n, R^m, Frobenius norm on R^{m x d}, L^2(nu;R^m) norm on U;
- the dt-integral over [0,T] of the Z and U terms;
- values: in [0,oo] (ENNReal / lintegral) is exact; if real-valued, the junk value for
  non-integrable quantities (Bochner integral of a non-integrable function = 0) must be
  excluded by a separate finiteness hypothesis wherever it is used (otherwise an infinite norm
  reads as 0 and an estimate "supSize <= C * RHS" becomes vacuous on the left);
- the three terms summed with weight 1 each (no T factor etc.).
Comparison (verdict recorded 2026-10-19T03:34:53Z):
Comparison: def supSize P nu T X Y Z U (Stability/SupUpgrade.lean:56-64), in [0,oo]:
  int^- sup_{t in [0,T]} sum_i |X_i t|^2 dP + int^- sup_{t in [0,T]} sum_k |Y_k t|^2 dP
  + sum_k sum_j E int_[0,T] |Z_kj|^2 + sum_k E int_[0,T] int_E |U_k(e)|^2 nu(de) dt.
Reading: ||Theta||_S^2 = E sup|X|^2 + E sup|Y|^2 + E int(|Z|_F^2 + ||U||^2_{L^2(nu)}), sup over
the closed interval [0,T], Euclidean / Frobenius / L^2(nu;R^m) norms, weight 1 each, values in
[0,oo] preferably.
- esq x = sum_i |x_i|^2 (the squared Euclidean norm); the sum over k, j of the energies of Z_kj
  is E int |Z|_F^2; the sum over k of the marked energies of U_k is
  E int sum_k int |U_k(e)|^2 nu(de) dt = E int ||U_t||^2_{L^2(nu;R^m)} dt. Matches.
- ENNReal-valued: no junk-zero for infinite norms; finiteness is a separate statement where needed.
- The pathwise iSup over the uncountable set [0,T] is fed to a lower Lebesgue integral. For cadlag
  processes (every use: solutions and their differences) the sup is measurable. For non-measurable
  functions the lower integral could only make the quantity smaller. That does not matter for
  the paper's objects.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless:
1. Coordinates: the squared Euclidean norm is esq = sum of squared coordinates, the Frobenius norm
   squared is the sum over (k,j), and ||U||^2_{L^2(nu;R^m)} is the sum over k of the integrals of
   |U_k(e)|^2. These are exact identities.
2. Values in [0,oo] (lintegral), so there is no Bochner junk value. A real-valued version would
   read an infinite norm as 0; this one does not.
3. The sup over t in [0,T] is taken pathwise inside a lower Lebesgue integral. It is measurable
   for the right-continuous processes it is applied to, so it is E sup_{t<=T}|.|^2 exactly.
Disagreements with the author's review (shown 2026-10-19T03:36:01Z): none
