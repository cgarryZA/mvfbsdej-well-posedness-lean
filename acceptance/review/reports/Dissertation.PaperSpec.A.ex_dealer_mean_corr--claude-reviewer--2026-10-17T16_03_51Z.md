### A:ex:dealer: Dissertation.PaperSpec.A.ex_dealer_mean_corr
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash ed839d34f480cba18bab6ae8a6c6a027 (pl-fp-v1:a742a2189589702624ce2a2ee2334910b9c01e24c8190c8165a988339c33c0bb)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T16:03:51Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T15:47:46Z):
Reading of spec ex_dealer_mean_corr: the crowding correction is no function of E[U], with the
correction L^2(nu) != 0.

Faithful corrected statement: for every sigma-finite nu on a countably generated (E,cE) whose
fibre L^2(nu;R) is nontrivial (exists a nonzero element; for sigma-finite nu equivalent to
nu != 0), the map (u, lambda) |-> A_lambda(u) on L^2(nu) x P_2(L^2(nu)) is not a function of
(u, mean(lambda)): there exist u, lambda_1, lambda_2 in P_2(L^2(nu)) with equal means and
A_{lambda_1}(u) != A_{lambda_2}(u) (or: no F with A_lambda(u) = F(u, m(lambda)) for all
u, lambda). A_lambda(u) = int gradV(u - v) lambda(dv), gradV(w) = w/sqrt(1+|w|^2).
It must not require more of nu than L^2(nu) != 0 (e.g. not finite nu, not a specific E, not
infinite activity), and must not weaken the conclusion to e.g. "A is not linear in the mean".
The laws must be in P_2 (probability measures with finite second moment); two-point laws
qualify. Representation choices allowed: the nontriviality as Nontrivial (Lp R 2 nu) or nu !=
0 with sigma-finiteness.
Comparison (verdict recorded 2026-10-17T16:01:28Z):
Comparison, ex_dealer_mean_corr (Sec5Dealer.lean:146-155).
Same as ex_dealer_mean with the extra hypothesis (exists u in L^2(nu;R^1), u != 0) - exactly
the correction "L^2(nu) != 0", nothing else (no finiteness of nu, no specific E). Conclusion the
non-existence of Phi with A_lambda(u) = Phi(mean lambda, u) over P2 laws - matches.
Witness ex_dealer_unit_hypotheses: the dealer mark measure (c = 1/2, r = 1) carries a unit
vector - an intended instance (the example's own marks).
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-17T16:01:35Z): none
