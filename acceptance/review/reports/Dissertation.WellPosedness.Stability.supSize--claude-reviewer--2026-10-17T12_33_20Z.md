### A:cor:robust, A:lem:pert, A:rem:generalrank, A:sec3:HH-banach, A:sec4:horizon-not-contractive, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: Dissertation.WellPosedness.Stability.supSize
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 8d946a220ee9b35c3ccfc7f258215a40 (pl-fp-v1:ab982025c40f9d7041f354c719dbf3d4dae6f03d190546e1f4cdcf702aed6101)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T12:33:20Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:32:57Z):
Reading: supSize = the H-norm squared / the left side of (3.1) and (4.13), the N of Step 5 of
Lemma 4.3:

  N = E sup_{0<=t<=T} |X_t|^2 + E sup_{0<=t<=T} |Y_t|^2 + E int_0^T (|Z_t|_F^2 + ||U_t||^2_{L^2(nu)}) dt,

applied to a tuple (typically a difference delta X, delta Y, delta Z, delta U). |.| is the
Euclidean norm of the whole vector, so the sup must be of the full squared norm sum_i X_{i,t}^2
(not the sum over coordinates of separate sups, which is a different, larger quantity — a
dimension-dependent change; the paper stresses its constants do not depend on n, m, d), over
t in [0,T] (all times, not a.e.); E as lower integral, value in [0, inf]. Z Frobenius = sum over
entries; ||U_t||^2 = int_E |U_t(e)|^2 nu(de) summed over coordinates. A faithful Lean definition
is this sum in ENNReal.
Comparison (verdict recorded 2026-10-17T12:33:10Z):
supSize P nu T X Y Z U = int^- sup_{t in [0,T]} esq(X_t) dP + int^- sup_{t in [0,T]} esq(Y_t) dP
  + sum_{k,j} energy(Z_{kj}) + sum_k markedEnergy(U_k).
- X, Y: the supremum over all t in [0,T] (Icc, every time) of the full squared Euclidean norm
  sum_i X_{i,t}^2 — not a sum of coordinate suprema. Matches E sup_{t<=T}|X_t|^2.
- Z: sum over entries of E int_0^T Z_{kj}^2 = E int_0^T |Z|_F^2 (additivity of lintegral for
  measurable integrands).
- U: sum over k of E int_0^T int_E U_k^2 nu = E int_0^T ||U_t||^2_{L^2(nu;R^m)}.
- ENNReal value: inf when a term is infinite, as the printed quantity.
Representation choices: coordinatewise split of the Z and U integrals into separate lower
integrals (equal for measurable processes); lower integral of the pathwise supremum (equal to
E sup for the measurable — e.g. cadlag — processes the paper considers). Faithful with
representation choices.
Witness: —
Verdict: faithful with representation choices — (1) The Z and U terms are sums over coordinates of separate lower integrals (energy,
markedEnergy) rather than one integral of |Z|_F^2 + ||U||^2: equal by additivity of the lower
integral for measurable integrands, which all processes of the paper are. (2) The suprema are of
the full squared Euclidean norm over every t in [0,T], under a lower integral in ENNReal: equal to
E sup_{t<=T}|X_t|^2 for the (cadlag, hence measurable-supremum) processes considered; the value
+inf is allowed, as in the printed quantity. (3) The arguments are the tuple components; callers
pass differences.
Disagreements with the author's review (shown 2026-10-17T12:33:10Z): none
