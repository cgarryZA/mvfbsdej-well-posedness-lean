### A:abstract, A:ex:dealer, A:rem:regimes, A:sec5:overview: Dissertation.PaperSpec.A.ex55Crowd
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 8d3f49063f9d40bd91804eeb64810052 (pl-fp-v1:467e7411bbbd23eb5cf3ede2855146da942b82a9800e454e22284496fcd71d33)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:50:57Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T15:41:48Z):
Reading for def:Dissertation.PaperSpec.A.ex55Crowd (Example 5.5).

Paper notion: the crowding correction
  A_lambda(u) := int_{L^2(nu)} grad V(u - v) lambda(dv),  V(w) = sqrt(1 + ||w||^2) - 1,
  grad V(w) = w / sqrt(1 + ||w||^2),  lambda in P2(L^2(nu)),
in the dealer model with n = m = d = 1 (so L^2(nu) = L^2(nu;R)), entering
h = h_c - beta_1 u - eps * A_{mu^U}(u) with mu^U the U-marginal of the measure argument.
(The name "ex55Crowd" may denote A itself or the dealer coefficient system with the crowding term.)

Faithful Lean: a Bochner integral over lambda (or over mu pushed forward to its U-coordinate) of
v |-> (1 + ||u - v||^2)^{-1/2} (u - v) in L^2(nu;R). Edge cases: Lean's Bochner integral returns 0
if the integrand is not AE-strongly measurable or not integrable; the integrand is continuous and
bounded by 1, so integrability holds for a probability measure, but AE-strong measurability needs
separability / a second-countable or Borel structure on L^2(nu) (the paper gets separability from
E countably generated). If measurability fails in Lean, A would silently be 0 and the example would
degenerate to Ex 5.1(i) (eps-term vanishes) -- that would make the definition mean something else.
If the definition is the whole coefficient system: b = -beta1 y, sigma = sigma_c - beta1 z,
h = h_c - beta1 u - eps A_{mu^U}(u), f = beta2 x, g(x, rho) = x, with mu^U the U-marginal (pushforward
of mu by the projection onto the 4th coordinate).
Comparison (verdict recorded 2026-10-17T15:50:04Z):
Comparison for def:Dissertation.PaperSpec.A.ex55Crowd (PaperSpec/A/Sec5.lean:642-646):
ex55Crowd Lambda u = Bochner integral of v |-> (sqrt(1 + ||u - v||^2))^{-1} . (u - v) d Lambda,
for any real Hilbert space F with any measurable space and any measure Lambda.

This is A_Lambda(u) = int grad V(u - v) Lambda(dv) with grad V(w) = w / sqrt(1 + ||w||^2) -- the
operator itself (the coefficient system is the separate ex55Coeffs, h = h_c - beta1 u - eps
ex55Crowd mu.margU.law u). Edge cases from my reading: the Bochner integral is 0 when the integrand is
not integrable. In every use F = Lp (EuclideanSpace R (Fin 1)) 2 nu with its (scoped) Borel
sigma-algebra and sigma-finite nu on countably generated E, so L^2(nu) is separable; the integrand is
continuous, hence strongly measurable, and bounded by 1, hence integrable against the probability
measures Lambda.law (Lambda : P2 ...) or margU laws that are fed to it, and against the convex
combinations s Lambda1 + (1-s) Lambda2 of ex_dealer_affine. So in use the value is the genuine
integral; the junk value does not arise, and the degenerate "eps-term silently 0" scenario of my
reading does not occur (the separate claims ex_dealer_twopoint / ex_dealer_not_mean_corr even pin down
non-zero values). Generality over F and arbitrary Lambda is a harmless widening of the domain.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Choices: (1) defined for an arbitrary real Hilbert space F and an arbitrary measure Lambda (the paper:
F = L^2(nu), lambda in P2(L^2(nu))); every use instantiates F = L^2(nu;R^1) with the Borel
sigma-algebra and Lambda a probability law (a P2 law, the U-marginal margU of a law on H, or a convex
combination of two P2 laws); (2) Bochner integral with Mathlib's junk value 0 for non-integrable
integrands -- never reached in use, since the integrand is continuous and bounded by 1 on a
separable space (sigma-finite nu, countably generated E), hence integrable against any probability
measure.
Disagreements with the author's review (shown 2026-10-17T15:50:12Z): No disagreement with a stated position (the author's entry shown is only the section heading). For
the record: faithful with representation choices -- generic Hilbert space F and measure Lambda;
Bochner junk value never reached in use (continuous integrand bounded by 1 on the separable L^2(nu),
against probability laws).
