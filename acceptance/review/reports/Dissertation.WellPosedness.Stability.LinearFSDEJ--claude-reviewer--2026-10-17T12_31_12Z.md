### A:sec4:horizon-not-contractive: Dissertation.WellPosedness.Stability.LinearFSDEJ
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 61bb9f1d9c8aba870000000000000000 (pl-fp-v1:b515c3a31d7d6c9d201a61c5e87d42521d3db4eee7db121657e460813f7cf634)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T12:31:12Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:30:30Z):
Reading: LinearFSDEJ — the paper's forward equation with frozen (given) integrands, as in the
frozen forward dynamics (4.5) of Lemma 4.2 (and the forward difference equations (4.12)):

  X_t = xi + int_0^t beta_s ds + int_0^t Sigma_s dW_s + int_0^t int_E gamma_s(e) Ntilde(ds,de),

for t in [0,T], with beta (R^n-valued drift, here plausibly one coordinate) progressively
measurable with E int_0^T |beta|^2 < inf (the paper uses Cauchy–Schwarz on the drift), Sigma
progressively measurable R^{n x d} (or one row) with E int_0^T |Sigma|^2 < inf (Ito integral
against the d-dim W), gamma P (x) E-measurable (or progressive, read through a predictable
representative) with E int int |gamma|^2 nu ds < inf (compensated Poisson L^2 integral), xi an
F_0-measurable initial value (L^2 where needed). The equation is a.s. for every t (the paper's
solution sense: a.s. for every t, null set independent of t since both sides are cadlag); a
solution is adapted and cadlag, and is in S^2 by Doob/BDG. The filtration carries W (Brownian
for it) and N (Poisson for it). Since the right side involves no unknown, the equation simply
defines X as the sum (unique up to indistinguishability).

A faithful Lean structure must express: X adapted (cadlag), the integrands' measurability and
square-integrability so that the integrals are the L^2 ones, and the identity a.s. at every t of
[0,T] (or for all t on one null set), with the library's Ito and compensated Poisson integrals.
A coordinatewise (scalar) form with sum over the d Brownian coordinates is fine.
Comparison (verdict recorded 2026-10-17T12:31:06Z):
Comparison for LinearFSDEJ D F hW hN T xi0 b X sigma gamma (one scalar coordinate).

- identity: for each t in [0,T], a.s., X_t = xi0 + int_{[0,t]} b ds + sum_j int_0^t sigma^j dW^j
  (MultidimBrownianMotion.stochasticIntegral is the component sum of the 1-d L^2 Ito integrals)
  + int_0^t int_E gamma Ntilde (library cadlag L^2 compensated integral). Matches (4.5)/(4.12)
  in one coordinate; "a.s. at each t" is the paper's "a.s. for every t" (with right-continuous
  paths of X and cadlag integrals it upgrades to one null set).
- drift b: jointly measurable, progressive, finite energy E int_0^T b^2 < inf, vanishing off
  [0,T]; finite energy makes a.e. path integrable on [0,t], so the Bochner integral is the true
  one off a null set. Matches the paper's L^2 drift.
- sigma: jointly measurable, progressive, finite energy, vanishing off [0,T]: the L^2 Ito integrand.
- gamma: jointly measurable, marked progressive, finite marked energy, vanishing off [0,T]: the
  L^2 compensated Poisson integrand; paper reads it through a P (x) E representative — progressive
  versus predictable is immaterial for the L^2 integral.
- xi0 in L^2 (Ass. 2.2 for xi_0; the difference datum delta xi_0 in Lemma 4.3 is L^2 too).
  No F_0-measurability field, but X adapted with X_0 = xi0 a.s. gives it up to null sets.
- X adapted (all real t), every path right-continuous at every real t. Left limits are not
  demanded; they follow a.s. from the identity (the right side is cadlag a.s.). Values off [0,T]
  are unconstrained apart from adaptedness and right-continuity (e.g. 0 before 0, X_T after T),
  so every paper solution has such an extension.

Representation choices only; faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — (1) Scalar coordinate form (one coordinate of X, a row sigma in R^d, a scalar jump integrand):
the paper's vector equation is the conjunction over coordinates. (2) Integrands extended by 0
off [0,T] (fields *_vanish): only [0,T] enters. (3) gamma marked progressively measurable rather
than predictable: the L^2 compensated integral does not distinguish integrands equal
dP x dt x nu-a.e. (4) X right-continuous on every path at every real time and adapted at every
real time, with no left-limit field: left limits follow a.s. from the identity, and any paper
solution on [0,T] extends (0 before time 0, X_T after T). (5) identity a.s. at each t in [0,T],
the paper's "a.s. for every t". (6) xi0 in L^2, as in Assumption 2.2 and Lemma 4.3.
Disagreements with the author's review (shown 2026-10-17T12:31:06Z): No disagreement in substance. The author review shows only a marker (definitions.md:299) and no recorded reading; it should record the representation choices (scalar coordinate form, vanishing off [0,T], progressive gamma, right-continuity without left limits, values off [0,T]).
