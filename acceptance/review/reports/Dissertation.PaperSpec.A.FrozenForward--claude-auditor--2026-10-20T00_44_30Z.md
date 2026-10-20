### A:eq:frozenbwd, A:eq:frozenfwd: Dissertation.PaperSpec.A.FrozenForward
Pins: manuscript A None; project 6d403c197bfb10fe8808933c6e525ee0ae544fb1; hash 2d8ed447ca12534ca192702cec9f9648 (pl-fp-v1:871288f90bc659ee9af03712f69b1ca1e4931b016e2b8685d76472dd49e1a0b0)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-20T00:44:30Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-20T00:30:26Z):
Reading of the notion behind FrozenForward: "Xbar solves the frozen forward dynamics (4.7)"
(eq:frozenfwd, manuscript/paper/sections/04-proof-wellposedness.tex, lines 265-275; the forced
system (4.1) eq:forced, lines 39-65, of which it is the forward line with the trial tuple
frozen in the coefficients).

Paper's notion: given the standing basis, coefficients b, sigma, h, lambda in [0,1], forcing
components q^b (progressive, L^2), q^sigma (progressive, L^2), q^h (P x E-measurable, L^2), an
initial datum xi_0 (F_0-measurable, L^2) and a trial Theta in S with Borel law flows mu^Theta,
mu^{Theta,-}, the process Xbar satisfies, for every t in [0,T], almost surely,
  Xbar_t = xi_0 + lambda int_0^t b(s, Theta_s, mu^Theta_s) ds
         + lambda int_0^t sigma(s, Theta_s, mu^Theta_s) dW_s
         + lambda int_0^t int_E h(s, Theta_s^-, e, mu^{Theta,-}_s) Ntilde(ds, de)
         + int_0^t q^b_s ds + int_0^t q^sigma_s dW_s + int_0^t int_E q^h_s(e) Ntilde(ds, de),
with Theta_s^- = (X_{s-}, Y_{s-}, Z_s, U_s), the dW-integrals Ito integrals, the Ntilde-integrals
compensated-Poisson L^2 integrals of the standing basis read through a P x E representative.
Since the right-hand side does not involve Xbar, "solving" means Xbar is a (cadlag adapted)
version of the right-hand side process. b, sigma at (Theta_s, mu^Theta_s) (not left limits); h at
the left-limit tuple and the law of the left-limit tuple; the law arguments are the laws under P
(Borel representatives, a.e. equal to Law(Theta_s), Law(Theta_s^-)); the factor lambda multiplies
the three coefficient terms only, not the forcing terms or xi_0.

What a faithful Lean definition must be: a predicate on (basis data, coefficients, lambda, q,
xi_0, Theta, Xbar) stating the displayed identity for each t in [0,T] a.s. (or a.s. for all t),
with the library's Lebesgue, Ito and compensated-Poisson integrals of exactly these integrands.
Possibly also Xbar cadlag adapted (may be part of the definition or of the statements using it).
Edge cases: Lean's integrals of non-integrable integrands are junk (0); the definition is
faithful where the statements using it guarantee integrability (they should, under Theta in S and
Assumptions 2.2-2.3), but a definition whose junk branch makes the identity hold or fail for a
reason the paper does not have would be a defect. The Lebesgue drift integral must be pathwise
(or a.s.) over [0,t]; the time variable restricted to [0,T].
Comparison (verdict recorded 2026-10-20T00:43:40Z):
Comparison of Dissertation.PaperSpec.A.FrozenForward (Dissertation/PaperSpec/A/Sec4Frozen.lean)
with "Xbar solves the frozen forward dynamics (4.7)"
(manuscript/paper/sections/04-proof-wellposedness.tex, lines 265-275; the forward line of the
forced system (4.1), lines 39-65, with the trial frozen in the coefficients). That passage defines
the notion.

FrozenForward D hG0 hind T lam C xi0 qb qsigma qh X Y Z U X' := there is gamma such that
(i) for a.e. s in [0,T], a.s., e -> (gamma_i s omega e)_i equals in L^2(nu) the value
h(s, tupleAt (leftLim X) (leftLim Y) Z U s omega, lawP2 P (that tuple)), and (ii) for every i,
LinearFSDEJ over the augmented filtration enlJoint with initial value xi0_i, drift
lam * driftProc_i + qb_i, diffusion lam * diffusionProc_i + qsigma_i, jump integrand
lam * (gamma_i cut to [0,T]) + qh_i, solution X'_i.

Item by item:
- b and sigma at (Theta_s, Law Theta_s) through driftProc/diffusionProc (cut to [0,T]): as printed.
- h at the left-limit tuple Theta^-_s = (X_{s-}, Y_{s-}, Z_s, U_s) and its law, read through a
  representative gamma: as printed ("read through such a representative", eq:fubiniiso). The
  representative is required to agree for a.e. s, a.s., in L^2(nu); with joint measurability
  (LinearFSDEJ) this fixes its dP x dt x nu class on [0,T], hence the compensated integral.
- lambda multiplies the three coefficient terms only; xi0 and the forcing enter unscaled; the
  linear combination of integrals is written as the integral of the combined integrand
  (linearity of the L^2 integrals): as printed.
- The identity holds for each t in [0,T] almost surely, with the Lebesgue, Ito and
  compensated-Poisson integrals of the library over the filtration of Section 2.
- X' adapted with every path right-continuous (LinearFSDEJ). The paper's Xbar is the cadlag
  version; a right-continuous adapted process satisfying the identity at each t a.s. is
  indistinguishable from it, and conversely the paper's Xbar (extended by constants off [0,T])
  satisfies FrozenForward. So the solution set is the paper's, up to indistinguishability.
- Built-in integrability: LinearFSDEJ requires the integrands jointly measurable, progressive
  (marked progressive), vanishing off [0,T], of finite energy, and xi0 square integrable. These are
  the conditions under which the printed integrals exist; under the hypotheses of Lemma 4.2 they
  hold (the existence clause of (4.7) is proved).

Representation choices (harmless): the jump integrand is required marked progressive and jointly
measurable rather than predictable (the library's compensated integral is defined for that class
and depends only on the L^2(dP dt nu) class, and such a class has a predictable version);
coordinatewise equations; "for each t a.s."; right-continuity in place of cadlag; the pointwise law
flow (lawP2, Dirac junk off L^2) in place of the Borel representative, differing on a Lebesgue-null
set of times; the left-limit process at s = 0 depends on values at negative times, a null time;
integrands extended by 0 off [0,T]. With lam = 0 the representative gamma still has to exist, which
it always does (pick representatives pointwise), so no spurious condition arises.
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless:
(1) h at the left-limit tuple enters through a representative gamma. gamma equals
h(s, Theta^-_s, ., mu^-_s) in L^2(nu) for a.e. s, a.s., and is jointly measurable and marked
progressive, where the paper asks for predictable. The library's compensated integral depends
only on the dP x dt x nu class, and that class has a predictable version.
(2) Each identity holds coordinatewise for each t in [0,T] a.s. The solution is adapted with
right-continuous paths, not cadlag. Every such solution is indistinguishable from the paper's
cadlag Xbar, and that Xbar extends to a FrozenForward solution.
(3) The law flow is the pointwise law lawP2 (Dirac junk off L^2) instead of the Borel
representative. The two differ on a Lebesgue-null set of times.
(4) Integrands are extended by 0 off [0,T]. The integrability and measurability conditions under
which the printed integrals exist are built in.
(5) The lambda-scaled coefficient integrals and the forcing integrals are combined into one
integral per kind, by linearity.
Disagreements with the author's review (shown 2026-10-20T00:43:45Z): No disagreement on the definition, which faithfully encodes "Xbar solves (4.7)". One clarification,
which belongs to the review of eq_frozenfwd rather than to this definition: LinearFSDEJ gives X'
adapted with right-continuous paths but not left limits. A FrozenForward solution is therefore not
by definition an element of S^2, and the existence clause of (4.7) inherits that gap. The
marked-progressive (rather than predictable) requirement on the jump representative is harmless,
as the review says: the compensated integral depends only on the dP x dt x nu class, which has a
predictable version.
