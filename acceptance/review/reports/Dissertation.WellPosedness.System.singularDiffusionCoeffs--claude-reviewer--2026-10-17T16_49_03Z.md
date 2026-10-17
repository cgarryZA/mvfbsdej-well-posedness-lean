### A:rem:uniq-no-integ: Dissertation.WellPosedness.System.singularDiffusionCoeffs
Pins: manuscript A None; project aaff2d964a19fbd6388335c908ac88573d3d4516; hash 9cbaca3d28850a5612dfa3a02c42b537 (pl-fp-v1:f917aed19be6f1abade4a97000b800c2b90fb13f6fe46f59b1bf176b5cc74656)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T16:49:03Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T16:41:44Z):
# Reading: def singularDiffusionCoeffs (used by the propositions of rem:uniq-no-integ)

The paper does not name such an object. Remark 3.4 asserts that existence requires Assumption 2.2
(origin integrability); the name says this definition is the counterexample coefficient system
behind that clause: a system whose DIFFUSION coefficient is singular in time, so that the origin
value sigma(., 0, delta_0) is not in L^2(0,T; R^{n x d}), while everything else of the setting is
admissible.

What the Lean definition must be, to mean the paper's notion "a coefficient system meeting the
standing hypotheses and Ass. 2.3-2.5 but not Ass. 2.2, with no solution":
- A coefficient system of the paper's type: deterministic b, sigma, h, f, g with signatures
  [0,T] x H x P_2(H) -> R^n, R^{n x d}, L^2(nu;R^n), R^m and g : R^n x P_2(R^n) -> R^m, jointly
  Borel, h Borel into L^2(nu;R^n) (2.3). Presumably at small dimensions (e.g. n = m = d = 1).
- Diffusion: sigma(t, theta, mu) = (base part Lipschitz in (theta, mu)) + s(t) e with a
  deterministic, Borel s : [0,T] -> R with integral_0^T s(t)^2 dt = infinity (e.g. s(t) = t^(-1/2)
  or 1/t). The t-only term cancels in every difference delta sigma, so Ass. 2.3 and 2.5 are
  unaffected. Preferably the singularity is such that integral_0^t s^2 = infinity for every t > 0
  (singular at 0), so the Ito integral does not exist even locally -- this is what makes "no
  solution" true under any reading of the paper's stochastic integral; a singularity at T also
  works (no limit at T).
- Remaining coefficients: a monotone base meeting Ass. 2.3-2.5 with admissible constants, e.g.
  Example 5.1(i)-type b = -beta_1 y, h = -beta_1 u, f = beta_2 x, g(x, rho) = x, G = 1; or
  b = 0, h = 0, f = x, g = x with alpha = beta_2 = 1, beta_1 = 0 (m = n).
- Edge cases: Lean's 1/0 = 0 or 0^(-1/2) = 0 at the single time t = 0 is harmless (Lebesgue-null);
  the coefficient must be genuinely non-square-integrable on [0,T] for the horizon T > 0 at hand
  (for EVERY T > 0 if T is a parameter); its measure argument and its values must be total
  functions with no junk that changes the meaning off a null time set; h's values must be in the
  Lean L^2(nu) type (e.g. 0 or -beta_1 u), with no a.e. issue.
- It is a definition, so faithfulness is: it is a well-typed coefficient system of the repository's
  coefficient-system structure, its diffusion origin value is not square-integrable, and its other
  components are the admissible monotone base intended.
Comparison (verdict recorded 2026-10-17T16:45:31Z):
# Comparison: def singularDiffusionCoeffs

Lean: singularDiffusionCoeffs : Coeffs nu 1 1 d := affineCoeffs 1 0 0 0 with
sigma t theta mu := toLp (p |-> if p.2 = 0 then (sqrt t)^{-1} else 0) + (0 - 1 * z).
Unfolding affineCoeffs (Example 5.1(i) family): b = -(1 * y), h = 0 - 1 * u (in Lp 2 nu),
f = 0 * x = 0, g(x, rho) = x.

Against my reading:
- Coefficient system of the paper's type: Coeffs has b : R -> H -> P2(H) -> R^n,
  sigma -> R^{n x d} (EuclideanSpace over Fin n x Fin d, Frobenius norm), h -> Lp(R^n) 2 nu (the
  L^2(nu) fibre), f -> R^m, g : R^n -> P2(R^n) -> R^m. n = m = 1, d free. Deterministic. Matches.
- Diffusion singular in time: entry (1,1) is t^{-1/2} for t > 0; int_0^T t^{-1} dt = inf for every
  T > 0, so sigma(., 0, delta_0) not in L^2(0,T), and int_0^t = inf for every t > 0 (singular at 0,
  so no Ito integral even locally). The t-only term cancels in every difference (Lean lemma
  diagDiff_singularDiffusionCoeffs), so Lipschitz/monotonicity are those of the affine base.
  Matches the intended "singular diffusion" counterexample.
- Base: beta1 = 1, beta2 = 0, sigma_c = 0, h_c = 0: b = -y, sigma part -z, h = -u, f = 0, g = x.
  This is an admissible monotone base for m = n = 1 (alpha = 1, beta1 = 1, beta2 = 0).
- Borel: (sqrt t)^{-1} is Borel, the rest continuous; proved (coeffBorelW2_singularDiffusionCoeffs).
- Edge cases: (sqrt t)^{-1} = 0 for t <= 0 (Real.sqrt of a nonpositive number is 0, 0^{-1} = 0);
  on [0, T] only t = 0 carries a junk value, a Lebesgue-null time -- harmless; times t < 0 are
  outside the horizon. At d = 0 there is no column, so the singular term disappears and the
  system is not singular; the definition is only used with 0 < d (the paper has d >= 1), so this
  is harmless. No a.e./representative issue: h = -u is an Lp element.

Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless:
1. The singular term is (Real.sqrt t)^{-1}, which Lean evaluates to 0 at t = 0 and for t < 0
   (sqrt of a nonpositive real is 0, 0^{-1} = 0). On [0, T] this changes a single, Lebesgue-null
   time; t < 0 is outside the horizon. The origin value is still not square integrable on (0, T),
   for every T > 0.
2. The definition is stated for every d, including d = 0, where Fin 1 x Fin 0 is empty and the
   singular term vanishes; the paper has d >= 1 and every proposition using it assumes 0 < d.
3. The base is the Example 5.1(i) family at beta1 = 1, beta2 = 0, sigma_c = 0, h_c = 0, so f = 0
   (written 0 * x); the singular term sits in entry (1,1) only. Any admissible monotone base would
   do; this one meets Ass. 2.3-2.5 with L = 1, G = 1, alpha = 1, beta1 = 1, beta2 = 0.
Disagreements with the author's review (shown 2026-10-17T16:48:54Z): none
