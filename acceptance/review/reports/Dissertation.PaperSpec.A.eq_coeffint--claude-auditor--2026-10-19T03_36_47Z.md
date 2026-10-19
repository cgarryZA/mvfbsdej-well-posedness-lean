### A:eq:coeffint: Dissertation.PaperSpec.A.eq_coeffint
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba13c4b68e5e50bad34 (pl-fp-v1:b27c90ed9d6d2d473dda6751bc93f67cd4dcad569eb99f1b9bb3fb2d53b5dbe9)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:36:47Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:16:43Z):
# Reading: spec eq_coeffint ((4.2))

Paper: "By Assumptions 2.2-2.3, the coefficient processes (2.5) along any Theta in HH are
square-integrable: for psi in {b,sigma,h,f}, in the norms of Assumption 2.3,
  E int_0^T |psi(s,Theta_s,mu_s)|^2 ds <= C E int_0^T (|X_s|^2+|Y_s|^2+|Z_s|_F^2+||U_s||^2
                                                    + |psi(s,0,delta_0)|^2) ds,
by that Lipschitz bound together with the coupling estimate (2.8) at mu' = delta_0."
Convention of §4: C depends only on T, L, ||G||, c_G, alpha, beta1, beta2, c_BDG unless stated;
here the proof gives a C depending on L only.

A faithful formal statement must contain:
* Setting: standing basis, T > 0, dimensions, nu.
* Constant: C chosen BEFORE the coefficients and Theta, as a function of L (or of the
  conventional list T, L, ||G||, c_G, alpha, beta1, beta2), never depending on the coefficient
  functions, the tuple, nu, or the basis.
* Hypotheses: coefficients satisfying Assumption 2.3 (diagonal Lipschitz, constant L) (and
  Assumption 2.2 if one wants the RHS finite; the inequality itself needs only 2.3); Theta in HH
  (X,Y cadlag adapted, E sup|X|^2, E sup|Y|^2 < oo, Z in H^2_W, U in H^2_N); mu_s = Law(Theta_s)
  (the law flow; Borel representative agreeing a.e.).
* Conclusion: for each psi in {b, sigma, h, f} (all four), the inequality above, with norms |.|,
  |.|_F, ||.||_{L^2(nu)}, |.| respectively and the origin value psi(s,0,delta_0) at the Dirac mass
  at 0 in H. For h the evaluation at (Theta^-_s, mu^-_s) or at (Theta_s, mu_s) is the same inside
  the dt-integral.
* The inequality must be stated in a form junk values cannot trivialise: in [0,oo] (lintegral), or
  with Bochner integrals together with the integrability that makes them genuine (if the LHS's
  integrand were non-integrable, a Bochner integral would be 0 and the inequality vacuous).
  The paper also asserts square-integrability of the coefficient processes (finite LHS) under 2.2.
Comparison (verdict recorded 2026-10-19T03:26:37Z):
# Comparison: eq_coeffint ((4.2))

Lean (Sec4Coeff.lean): EXISTS K : R -> R such that for every filtered probability space, every
sigma-finite nu on a countably generated E, all n, m, d, T, L and coefficients C: if LipInterior
F P T L C (the interior bound of Assumption 2.3 with constant L, for a.e. t, over diagonal inputs,
with the Hilbert-norm W2) then for every Theta : R -> Omega -> H with Theta_t strongly
F_t-measurable and in L^2 for a.e. t in [0,T], for each psi in {b, sigma, h, f}:
  int_[0,T] int_Omega ||psi(t, Theta_t, lawP2 P Theta_t)||^2 dP dt
    <= ofReal (K L) * int_[0,T] int_Omega (|X|^2 + |Y|^2 + |Z|^2 + ||U||^2 + ||psi(t,0,delta_0)||^2),
all as lintegrals in [0, oo].

Against my reading:
* Constant chosen before everything, as a function of L alone: yes (exists K, then forall basis,
  dims, nu, T, L, C, Theta) — stronger than the §4 convention (which would allow T, ||G||, ...).
* Hypothesis: only the interior Lipschitz bound of Assumption 2.3 (which is what (4.2) uses);
  Assumption 2.2 and the terminal bound are not assumed (the inequality does not need them).
* Theta: any tuple process with Theta_t in L^2(Omega, F_t; H) for a.e. t — this contains every
  Theta in HH on the standing basis (X, Y adapted; Z predictable hence adapted; the L^2(nu) class
  of U_t strongly F_t-measurable; square integrable at a.e. t by Fubini).
* mu_s = lawP2 P Theta_s: the law at every time; it agrees with the Borel representative of
  Lemma A.1 for a.e. s, so the integrals are the same.
* Norms: Euclidean for b, f, X, Y; Euclidean on Fin n x Fin d (Frobenius) for sigma and Z;
  L^2(nu) for h and U; origin value psi(t, 0, delta_0) with delta_0 the Dirac at 0 of H: yes.
* All four psi: yes (conjunction). Junk-safety: lintegrals in [0, oo], so no Bochner junk can
  trivialise the inequality.
Differences: (1) arbitrary filtered probability space instead of the standing basis; (2) Theta
only required F_t-measurable and square integrable at a.e. t, instead of Theta in HH; (3) only the
interior Lipschitz bound assumed (not Assumptions 2.2-2.3 in full); (4) K depends on L only.
All generalise. The square-integrability statement accompanying (4.2) follows when the RHS is
finite (Theta in HH and Assumption 2.2).
Verdict: broader.
Witness: —
Verdict: broader — Broader than printed: the constant K(L) depends on L alone and is chosen first; the statement holds
on every filtered probability space, assumes only the interior Lipschitz bound of Assumption 2.3
(not Assumption 2.2 or the terminal bound), and applies to every tuple process Theta with Theta_t
strongly F_t-measurable and square integrable for a.e. t, not only Theta in HH; the inequality is
read in [0, oo]. Instantiation giving the printed (4.2): take the standing basis, coefficients
satisfying Assumptions 2.2-2.3 (so LipInterior holds), Theta = (X, Y, Z, U) in HH (then
Theta_t = tupleAt is F_t-measurable and in L^2 at a.e. t), C := K(L); since lawP2 P Theta_s equals
the Borel law flow mu_s for a.e. s, the four inequalities are (4.2) for psi = b, sigma, h, f, and
under Assumption 2.2 the right-hand sides are finite, giving the square integrability.
Disagreements with the author's review (shown 2026-10-19T03:36:39Z): Classification only. The reviewer records "faithful with representation choices"; I record
"broader": the constant K(L) depends on L alone, the statement holds on an arbitrary filtered
probability space, assumes only the interior Lipschitz bound of Assumption 2.3 (neither Assumption
2.2 nor the terminal bound), and applies to every tuple process that is F_t-measurable and square
integrable at a.e. t, not only to Theta in HH. The printed (4.2) is its instance at the standing
basis with Theta in HH (lawP2 P Theta_s equal to the Borel flow for a.e. s). No disagreement about
the mathematics.
