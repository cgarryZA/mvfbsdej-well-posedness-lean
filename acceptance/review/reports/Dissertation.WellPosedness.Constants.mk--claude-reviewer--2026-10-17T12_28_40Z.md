### A:ass:mono, A:cor:robust, A:ex:brownian, A:ex:concrete, A:lem:cont, A:lem:pert, A:rem:diag-mono, A:rem:generalrank, A:rem:intrinsic, A:sec4:horizon-not-contractive, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: Dissertation.WellPosedness.Constants.mk
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 0851194a5962ef650000000000000000 (pl-fp-v1:a9341d7e170fc5a8f6a4d084abbe05b984b7db87667d6152700d69b8ac3d1450)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T12:28:40Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:28:27Z):
Unit: Constants.mk, the constructor of the structure Constants (the constant pattern of
Assumption 2.5). Its type must take exactly the side conditions of Assumption 2.5 as arguments
and produce Constants n m alpha beta1 beta2 (n forward, m backward dimension):
  alpha, beta1, beta2 >= 0; alpha + beta1 > 0; beta1 + beta2 > 0;
  m < n -> beta1 > 0;  m > n -> alpha > 0 and beta2 > 0.
No further premises, none missing.
Comparison (verdict recorded 2026-10-17T12:28:34Z):
Constants.mk takes exactly 0<=alpha, 0<=beta1, 0<=beta2, 0<alpha+beta1, 0<beta1+beta2,
(m<n -> 0<beta1), (n<m -> 0<alpha /\ 0<beta2) and returns Constants n m alpha beta1 beta2.
Item by item identical to the side conditions of Assumption 2.5 with n forward and m backward.
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-17T12:28:34Z): none
