### A:ex:dealer: Dissertation.PaperSpec.A.ex_dealer_mean_corr
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba18bab6ae8a6c6a027 (pl-fp-v1:a742a2189589702624ce2a2ee2334910b9c01e24c8190c8165a988339c33c0bb)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:27:19Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:15:07Z):
Reading of spec:Dissertation.PaperSpec.A.ex_dealer_mean_corr (Example 5.5, clause "the crowding
correction is no function of E[U], with nu != 0 (so L2(nu) != 0)").

Paper (05-examples.tex:401-406): "Beyond the mean. The crowding correction is not a function of
E[U]: for a unit w in L2(nu), the two-point laws lambda_1 = (delta_{-w} + delta_w)/2 and
lambda_2 = (delta_{-2w} + delta_{2w})/2 share their mean, yet A_{lambda_1}(w) = w/sqrt5,
A_{lambda_2}(w) = (1/2)(3/sqrt10 - 1/sqrt2) w."  Here A_lambda(u) := int grad V(u - v) lambda(dv),
grad V(w) = w / sqrt(1 + ||w||^2), lambda in P2(L2(nu)); in the dealer example n = m = d = 1, so
L2(nu) = L2(nu; R) (or R^1).  The paper takes nu != 0 in Ex. 5.5 (05-examples.tex:22), which
makes unit vectors exist.

Faithful statement:
- Setting: a (sigma-finite) measure nu on the mark space with nu != 0 (equivalently, the fibre is
  nontrivial); the fibre L2(nu; R^m) with m = 1 (general m is broader and harmless).
- Conclusion: the map (lambda, u) |-> A_lambda(u) does not factor through (mean(lambda), u): there
  is no F with A_lambda(u) = F(mean lambda, u) for all lambda in P2(L2(nu)) and all u; equivalently
  there exist lambda_1, lambda_2 in P2(L2(nu)) with equal means (Bochner integral of the identity)
  and u with A_{lambda_1}(u) != A_{lambda_2}(u).  The mean must be the barycentre int v lambda(dv)
  (= E[U] for lambda = Law(U)).  Quantifying over a smaller class of laws than P2 for the
  non-factorisation is fine as long as the witnesses are in P2 (an existential); a "no F" version
  quantifying over all probability measures is also fine as the witness laws are two-point.
- The crowding correction must be the paper's A_lambda (integral of grad V(u - v) against lambda,
  grad V with the L2(nu) norm and the factor 1/sqrt(1 + ||w||^2)).
A version that only states different values at the printed laws without the equal-mean part
would be weaker; a version under no nontriviality hypothesis would be false (nu = 0).
Comparison (verdict recorded 2026-10-19T03:21:01Z):
Comparison for spec:Dissertation.PaperSpec.A.ex_dealer_mean_corr (Sec5Dealer.lean:166-175).

Lean: forall E nu [SigmaFinite nu] [CountablyGenerated E],
  (exists u : Lp (EuclideanSpace R (Fin 1)) 2 nu, u != 0) ->
  not exists Phi : L2 -> L2 -> L2, forall (Lam : P2 L2) (u : L2),
      ex55Crowd Lam.law u = Phi (int v dLam.law) u.
ex55Crowd (Sec5.lean:631-633): A_Lam(u) = int (sqrt(1 + ||u - v||^2))^{-1} . (u - v) dLam(v),
i.e. int gradV(u - v) Lam(dv) with gradV(w) = w/sqrt(1+||w||^2). Matches the paper's A_lambda.
(The integrand has norm <= 1 and is continuous in v; L2(nu) is separable under the instance
hypotheses, so it is Bochner integrable against any probability measure: no junk value.)

Against my reading:
- Setting: standing mark space (sigma-finite, countably generated), fibre L2(nu; R^1) (m = 1 of the
  dealer example). Matches.
- Nontriviality: the hypothesis is "L2(nu) has a nonzero element" instead of "nu != 0". Under
  sigma-finiteness nu != 0 implies it (rem_beta1_fibre), and conversely, so the hypothesis is the
  paper's (the clause name itself says "nu != 0 (so L2(nu) != 0)"). Satisfiable (witness
  ex_dealer_unit_hypotheses: a unit w for dealerMarks).
- Conclusion: no Phi with A_Lam(u) = Phi(mean Lam, u) for all Lam in P2(L2(nu)) and all u: the
  correction is not a function of the mean (together with u). The mean is the Bochner barycentre
  int v dLam (finite first moment for P2 laws, so genuine), = E[U] for Lam = Law(U). Matches.
- Quantifying over all P2 laws in the factorisation is right (the witnesses lambda_1, lambda_2 are
  two-point laws, in P2).
- It is the paper's claim at this revision ("The crowding correction is not a function of E[U]").
Representation choices: nontriviality stated on the fibre rather than on nu (equivalent for
sigma-finite nu); fibre valued in EuclideanSpace R (Fin 1) (= R).
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — (1) The hypothesis nu != 0 is stated as "L2(nu; R^1) has a nonzero element"; for sigma-finite nu
(assumed) the two are equivalent, so the proposition is the paper's. (2) The fibre is
Lp (EuclideanSpace R (Fin 1)) 2 nu, the U-channel of TupleH with m = 1, and the mean of a law is its
Bochner barycentre int v dLam, which is E[U] for Lam = Law(U).
Disagreements with the author's review (shown 2026-10-19T03:26:58Z): Minor, no effect on the verdict: the author calls the hypothesis "L2(nu) != {0}" broader than the
example's nu != 0. For sigma-finite nu (assumed) the two are equivalent (nu = 0 makes L2(nu) trivial,
and nu != 0 gives a nonzero element; both halves of rem_beta1_fibre), so the proposition is exactly
the printed claim, not broader. Otherwise none.
