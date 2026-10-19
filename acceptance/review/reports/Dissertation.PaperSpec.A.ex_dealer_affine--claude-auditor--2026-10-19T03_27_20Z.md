### A:ex:dealer: Dissertation.PaperSpec.A.ex_dealer_affine
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba14f86326a4c8f6eab (pl-fp-v1:aac77596119e4c6355cba08c23480d5cb8f5aecc2dce62b270324c151303fc6e)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:27:20Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:15:07Z):
Reading of spec:Dissertation.PaperSpec.A.ex_dealer_affine (Example 5.5, clause "the crowding
correction is affine in the population law: an expectation kernel of Example 5.3 with
K = L2(nu)").

Paper (05-examples.tex:408-412): "The correction is nonlinear in the valuation curves, but affine
in their population law: A_{s lambda_1 + (1-s) lambda_2} = s A_{lambda_1} + (1-s) A_{lambda_2} for
s in [0,1].  It is an expectation kernel in the sense of Example 5.3, with L2(nu) in the role of K".
Example 5.3 (05-examples.tex:211-221): phi(t, theta, mu) = int_H phibar(t, theta, theta') mu(dtheta')
with phibar measurable and Lipschitz in (theta, theta') uniformly in t; K a separable Hilbert space
(Remark 2.6) replacing R^k.

Faithful statement (two parts):
(a) Mixture identity: for all lambda_1, lambda_2 in P2(L2(nu)) and s in [0, 1],
    A_{s lambda_1 + (1-s) lambda_2} = s A_{lambda_1} + (1-s) A_{lambda_2} as functions of u (all u).
    (The mixture of two P2 laws is in P2.)  In the printed text lambda_1, lambda_2 are the two-point
    laws of the preceding sentence, but the claim "affine in their population law" is general;
    a general statement is the printed claim; one restricted to the two-point laws would be
    narrower.
(b) Expectation-kernel form: the crowding correction, as a function of (theta, mu) through
    u = pi_U(theta) and mu^U, is phi(theta, mu) = int_H phibar(theta, theta') mu(dtheta') with
    phibar(theta, theta') = grad V(pi_U theta - pi_U theta') valued in K = L2(nu), measurable and
    Lipschitz in (theta, theta') (constant <= 1 in each argument, since Lip(grad V) <= 1 and pi_U is
    1-Lipschitz); at the level of the fibre, A_lambda(u) = int k(u, v) lambda(dv) with k(u,v) =
    grad V(u - v) jointly Lipschitz.  Equivalently: there is a Lipschitz kernel with the
    representation identity for all mu in P2(H) (or lambda in P2(L2(nu))).
- A_lambda the paper's crowding correction; fibre L2(nu; R) (m = 1; general harmless).
A statement with only (a) would omit the "expectation kernel" part of the clause (narrower) unless
(b) is evidently definitional AND the Lipschitz property of the kernel is stated elsewhere; I will
judge part (b) by whether the Lean records the kernel's Lipschitz property.
Comparison (verdict recorded 2026-10-19T03:23:08Z):
Comparison for spec:Dissertation.PaperSpec.A.ex_dealer_affine (Sec5.lean:684-703).

Lean (three conjuncts, for every sigma-finite nu on a countably generated E):
(a) forall Lam1 Lam2 : P2 (L2(nu;R^1)), s in [0,1], u:
    ex55Crowd (ofReal s . Lam1.law + ofReal (1-s) . Lam2.law) u = s . A_{Lam1}(u) + (1-s) . A_{Lam2}(u);
(b) forall mu : P2 (TupleH nu 1 1 1), u: ex55Crowd mu.margU.law u
      = int_H (sqrt(1 + ||u - theta'.U||^2))^{-1} . (u - theta'.U) dmu(theta');
(c) forall theta1 theta1' theta2 theta2' in H:
    ||gradV(theta1.U - theta1'.U) - gradV(theta2.U - theta2'.U)||
      <= ||toL2 theta1 - toL2 theta2|| + ||toL2 theta1' - toL2 theta2'||.
margU (Law/TupleMarginal.lean:82) = pushforward of mu under the U-channel projection projUH, the
paper's mu^U. toL2 maps H to the l2-product TupleL2 (Hilbert norm |theta|_H of the paper).

Against my reading:
- (a) Mixture identity "affine in the population law", for all P2 laws (not only the two-point
  ones), all s in [0,1], all u. Matches.
- (b)+(c) Expectation kernel of Example 5.3 with K = L2(nu): the correction as a function of
  (theta, mu) is int_H phibar(theta, theta') mu(dtheta') with phibar(theta, theta') =
  gradV(u - theta'.U) (u = theta.U), and phibar is Lipschitz in (theta, theta') with constant 1 in
  each argument for the paper's Hilbert norm of H (c), hence continuous and Borel measurable, with no
  t-dependence (so "uniformly in t" holds trivially). Matches what Example 5.3 requires of the kernel
  (measurable, Lipschitz in (theta, theta') uniformly in t).
- Integrals are genuine: the integrand is bounded (norm <= 1) and continuous on a separable space.
- A = ex55Crowd, the paper's crowding correction. Fibre L2(nu; R^1), H = TupleH nu 1 1 1 (the
  dealer example's n = m = d = 1).
- No hypotheses beyond the standing setting; nothing to witness beyond existence of P2 laws.
- Claimed at this revision (05-examples.tex:408-412).
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-19T03:26:58Z): none
