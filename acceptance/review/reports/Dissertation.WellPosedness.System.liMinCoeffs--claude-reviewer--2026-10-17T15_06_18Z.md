### A:sec:examples: Dissertation.WellPosedness.System.liMinCoeffs
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 0d9a685aa46f2a71719d94d7674f9ea4 (pl-fp-v1:317b4da127a5e5b3619de51505f75f9e69c80248c5dec8bae20d0a60b8d96707)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:06:18Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:33:35Z):
Reading for liMinCoeffs (paper §5 preamble: "The jump system of [LiMin, Example 3.2] is linear, hence
Lipschitz, and is shown there to admit no adapted solution on the horizon T = 3pi/4").
Li--Min Example 3.2 (arXiv 1812.10254 v1, Example 3.2), m = n = d = 1, t in [0, 3pi/4]:
 dx = E[y(t)] dt + dB_t + int_E k(t,e) Ntilde(dt,de),
 -dy = E[x(t)] dt - z dB - int_E k(t,e) Ntilde(dt,de),
 x(0) = 1, y(3pi/4) = -E[x(3pi/4)].
In the paper's coefficient format (b, sigma, h, f, g) on H = R x R x R^{1x1} x L^2(nu;R):
 b(t,theta,mu) = m_Y(mu) (Y-marginal mean), sigma(t,theta,mu) = 1 (the 1x1 matrix),
 h(t,theta,e,mu) = u(e) (the jump coefficient is the U-component itself), f(t,theta,mu) = m_X(mu)
 (X-marginal mean), g(x,rho) = -barycentre(rho) (= -int x rho(dx)); initial datum xi_0 = 1; T = 3pi/4.
(Li--Min's Levy measure is finite; the paper's setting admits any sigma-finite nu; the
non-existence argument via the mean ODE X' = Y, Y' = -X, X(0) = 1, Y(T) = -X(T) works for any nu.)
These are affine (linear), Lipschitz in (theta, W_2(mu,mu')), with square-integrable origin values
(sigma = 1 constant, others 0). A faithful Lean liMinCoeffs must be exactly these coefficients
(with the signs: +E[y] drift, +E[x] driver in -dy = f dt, i.e. Y_t = g + int_t^T f ds, terminal minus
the mean of X_T); any reformulation must keep the same system.
Comparison (verdict recorded 2026-10-17T15:05:29Z):
Comparison for liMinCoeffs (Remarks/LiMinSystem.lean:61), Coeffs nu 1 1 1:
b _ _ mu := (tupleMean mu).2.1, sigma := toLp (fun _ => 1), h _ theta _ := theta.2.2.2, f _ _ mu := (tupleMean mu).1,
g _ rho := -barycentre rho; tupleMean mu = int theta d(mu.law) (Bochner, MeanField.lean), barycentre reviewed.
Against my reading (Li--Min arXiv 1812.10254 Example 3.2, which I read in their source:
dx = E[y] dt + dB + int k Ntilde, -dy = E[x] dt - z dB - int k Ntilde, x(0) = 1, y(T) = -E[x(T)], m = n = d = 1;
in the paper's format b = m_Y(mu), sigma = 1, h(t,theta,e,mu) = u(e), f = m_X(mu), g(x,rho) = -frak b(rho)):
- b = Y-channel of the mean of mu = m_Y(mu): matches.
- sigma = the 1 x 1 matrix with entry 1: matches (dB coefficient 1).
- h = the U-component u in L^2(nu; R) (n = m = 1, so the types agree): matches (forward jump integrand = k = U).
- f = X-channel of the mean = m_X(mu): matches; with the paper's backward form Y_t = g + int_t^T f ds - ...,
  i.e. -dY = f dt - Z dW - U dNtilde, this is Li--Min's -dy = E[x] dt ... .
- g(x, rho) = -barycentre(rho) = -E[X_T] on diagonal laws: matches y(T) = -E[x(T)].
- Means are Bochner integrals over P_2 laws (integrable), so no junk values.
- The initial datum 1 and the horizon 3pi/4 are not part of the coefficients; they belong to the
  proposition. The mark space and sigma-finite nu are arbitrary (Li--Min take a finite Levy measure;
  the non-existence argument through the mean ODE does not use finiteness), as the paper's setting
  admits.
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-17T15:05:48Z): Not a disagreement with the coefficients, but with the review's status note: the author records that
the identification with the printed Example 3.2 of Li and Min "is not checked". I checked it against
the cited paper's arXiv source (arXiv 1812.10254v1, Example after Remark 3.2, "We take m = n = d = 1"):
dx = E[y(t)] dt + dB_t + int_E k(t,e) Ntilde(dt,de), -dy = E[x(t)] dt - z dB - int_E k Ntilde, x(0) = 1,
y(3pi/4) = -E[x(3pi/4)], t in [0, 3pi/4]. In the paper's format this is b = m_Y(mu), sigma = 1, h = u,
f = m_X(mu), g = -barycentre, exactly liMinCoeffs (initial value 1 and T = 3pi/4 left to the statement).
So the identification holds; Li--Min's Levy measure is finite, the definition allows any sigma-finite
nu, which the paper's setting admits and the non-existence argument (mean ODE X' = Y, Y' = -X, X(0) = 1,
Y(T) = -X(T)) does not need.
