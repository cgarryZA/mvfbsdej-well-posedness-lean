### A:ass:mono, A:cor:robust, A:ex:brownian, A:ex:concrete, A:lem:cont, A:lem:pert, A:rem:diag-mono, A:rem:generalrank, A:rem:intrinsic, A:sec4:horizon-not-contractive, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: Dissertation.WellPosedness.Constants
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 523a9f9cc9be2abd0000000000000000 (pl-fp-v1:774cc4aab71fd127407611d8c74b17fb04b31edfcab7353ee9551228316b58af)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T12:28:18Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:27:58Z):
Unit: def Constants (a structure, used by Assumption 2.5 and 13 more claims).

Paper notion: the constants of the standing assumptions. Assumption 2.5 fixes the monotonicity
constants alpha, beta_1, beta_2 with the side conditions
   alpha, beta_1, beta_2 >= 0,  alpha + beta_1 > 0,  beta_1 + beta_2 > 0,
   beta_1 > 0 if m < n,   alpha > 0 and beta_2 > 0 if m > n,
where n is the forward and m the backward dimension. The other constants of the paper are the
Lipschitz constant L >= 0 (Assumption 2.3), the coupling matrix G in R^{m x n} of full rank
(Assumption 2.4) with ||G|| its operator norm and c_G = s_min(G)^{-2}; the theorems state that
C_stab etc. depend only on (T, L, ||G||, c_G, alpha, beta_1, beta_2, c_BDG).

A faithful Lean structure "Constants": if it bundles alpha, beta_1, beta_2 (and possibly L, G),
its invariants must be exactly the side conditions above, with the rank-case conditions tied to
the actual dimensions n, m of the system (not free parameters), m < n => beta_1 > 0 and
m > n => alpha > 0 and beta_2 > 0, and no extra conditions (e.g. not beta_1 > 0 always, not
strictness of all three). If it bundles L: L >= 0. If G: full rank (rank = min(m,n)) of an
m x n real matrix. If it is a bare record without the side conditions, then the statements must
impose them; then the record must at least have real-valued fields with the intended meaning.
Comparison (verdict recorded 2026-10-17T12:28:12Z):
Constants n m alpha beta1 beta2 : Prop (Assumptions.lean:119), with fields
  0 <= alpha, 0 <= beta1, 0 <= beta2, 0 < alpha + beta1, 0 < beta1 + beta2,
  m < n -> 0 < beta1,  n < m -> 0 < alpha /\ 0 < beta2.
Reading: exactly the side conditions of Assumption 2.5, with n the forward and m the backward
dimension (paper: "beta_1 > 0 if m < n and alpha, beta_2 > 0 if m > n"). Every condition is present,
none is added, the rank cases are tied to the dimension parameters n, m (the users, e.g.
Spec/Assumptions.lean:205, pass the system's n m in this order). The structure does not bundle L
or G, which the assumptions carry separately. A Prop with no junk values.
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-17T12:28:12Z): none
