### A:sec4:horizon-not-contractive: Dissertation.PaperSpec.A.BrownianFrozenStep
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 98bd6b9787534217c971d1dc13a30cc3 (pl-fp-v1:fe89adcadd9aa07bdfafda0dd6fc08aca936251cbc5fa8afc1fb7ceb7a96ec36)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T12:18:02Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:16:08Z):
# Reading: the frozen-coefficient step (Brownian case) (def:Dissertation.PaperSpec.A.BrownianFrozenStep)

Paper's notion. §4 intro (line 886): "shortening the horizon does not make the frozen-coefficient
map contractive, since the (z,u)-dependence of sigma, h and the full-tuple law coupling enter the
contraction constant with no T-factor." The frozen-coefficient map is Phi_lambda of the proof of
Lemma 4.2 (eq:frozenfwd, eq:frozenbwd): for a trial tuple Theta = (X,Y,Z,U) in S (the solution
space), with mu^Theta_t = Law(Theta_t), Phi(Theta) = Theta-bar where
  Xbar_t = xi_0 + lambda int_0^t b(s,Theta_s,mu_s) ds + lambda int_0^t sigma(s,Theta_s,mu_s) dW_s
           + lambda int int h(s,Theta_s^-,e,mu_s^-) N~(ds,de) + forcings,
  Ybar_t = lambda g(Xbar_T, Law Xbar_T) + q^g_T + int_t^T (lambda f(s,Theta_s,mu_s) + q^f_s) ds
           - int_t^T Zbar dW - int_t^T int Ubar dN~,
with (Zbar, Ubar) from the predictable representation of the martingale E[Xi | F_t].
"Brownian" step: the same with no jump channel (h = 0, U absent or zero), driven by W only, so
Theta = (X, Y, Z) and the backward component comes from Brownian martingale representation.
With lambda = 1 and zero forcing in the simplest reading (the §4 claim is about the frozen map
as such; scale lambda can be absorbed into the coefficients).

A faithful Lean definition (as a relation "Thetabar is the frozen step of Theta", or as the map):
- inputs: a trial (X, Y, Z) of the right integrability/adaptedness on [0,T], the coefficients
  (b, sigma, f, g) and initial datum xi_0, the horizon T, a Brownian motion W on a filtered
  probability space;
- Xbar given by the forward frozen dynamics with b, sigma evaluated at (Theta_s, Law Theta_s)
  of the TRIAL tuple (not of Thetabar), a.s. for every t ∈ [0,T];
- (Ybar, Zbar) solving the linear BSDE with terminal value g(Xbar_T, Law Xbar_T) (note: at the
  OUTPUT Xbar_T) and driver f evaluated along the trial, Zbar predictable/progressive square
  integrable, Ybar adapted (càdlàg/continuous);
- if laws enter, Law(Theta_s) must be the law of the trial tuple at time s.
For the claim, the definition should be general enough to contain an instance where sigma
depends on z (so that the frozen map's Lipschitz constant has no T-factor); if it is a
specialised linear Brownian example, it must still be a genuine instance of Phi as above.
Comparison (verdict recorded 2026-10-17T12:17:55Z):
# Comparison: BrownianFrozenStep

Lean (PaperSpec/A/Sec4Horizon.lean:47-59): over a Lévy driver D with d = 1 and mark space
`Unit` with ν = 0 (no jumps), the filtration `enlJoint 𝒢₀ D h𝒢₀` (usual augmentation of the
driver's filtration enlarged by an independent 𝒢₀ = §2's filtration), coefficients
`C : Coeffs 0 1 1 1` (n = m = d = 1), a trial (X, Y, Z, U) and an output (X', Y', Z', U'):
  (a) ∀ i, LinearFSDEJ … T 0 (driftProc P T C X Y Z U i) (X' i) (diffusionProc P T C X Y Z U i) 0
      i.e. X'_t = 0 + ∫_0^t b(s, Θ_s, Law Θ_s) ds + ∫_0^t σ(s, Θ_s, Law Θ_s) dW_s + 0, a.s. at each
      t ∈ [0,T], Θ the TRIAL tuple; integrands progressive, finite energy, vanishing off [0,T];
      X' adapted, right-continuous;
  (b) ∀ k, LinearBSDEJ … T (terminalVal P T C X' k) (driverProc P T C X Y Z U k) (Y' k) (Z' k) (U' k)
      i.e. Y'_t = g(X'_T, Law X'_T) + ∫_t^T f(s, Θ_s, Law Θ_s) ds − ∫_t^T Z' dW − ∫_t^T∫ U' dÑ,
      terminal value at the OUTPUT X'_T, driver along the trial; Z', U' progressive, finite
      energy; Y' adapted right-continuous; terminal value square integrable.

Item by item against the reading (Phi_lambda of the proof of Lemma 4.2, (4.10)-(4.11)):
- Coefficients b, σ, f evaluated at the trial tuple and its law Law(Θ_s) = lawP2 P (tupleAt …):
  yes (driftProc / diffusionProc / driverProc, Solves.lean:100-115). Law at every s; junk δ_0
  only at times where Θ_s ∉ L^2, a dt-null set for a trial in ℍ, invisible to the dt- and
  dW-integrals.
- g at the output X'_T with its law: yes (terminalVal P T C X' k).
- Backward via a linear BSDE with predictable-representation integrand: the paper constructs
  (Z̄, Ū) from E[Ξ|F_t]; here (Y', Z', U') is any solution of the linear BSDE in the
  progressive finite-energy class, which is the same (unique) object.
- Jumps: ν = 0 on a one-point mark space, so `C.h` takes values in the zero space
  L^2(0) = {0}, the jump integrand 0 is the only possibility, and the Poisson integrals vanish.
  This is the paper's setting with ν = 0 (σ-finite, countably generated E), i.e. no jumps:
  the "Brownian" case.
- Specialisation: λ = 1, zero forcing, ξ_0 = 0, n = m = d = 1. The paper's Φ_λ is general; the
  definition captures only this special case. Its sole use is an instance claim (§4 intro:
  shortening the horizon does not make the frozen map contractive), where a special case is
  exactly what is needed; λ = 1 is the target case, and ξ_0, q cancel in differences, so they do
  not affect contractivity.
- Equations a.s. at each t (not "a.s. for all t") and right-continuous paths (no left limits
  required): with right-continuous X', Y' and the L^2 stochastic integrals these are the
  paper's identities up to indistinguishability; harmless.
- Filtration: §2's (enlJoint), not a smaller one. Good.

Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices (each harmless for the definition's only use, the instance claim of the
§4 introduction):
1. Special case of the frozen map Φ_λ of Lemma 4.2: λ = 1, zero forcing, initial datum 0,
   n = m = d = 1, and no jumps (mark space a point, ν = 0, so h ∈ L^2(0) = {0} and the jump
   integrand 0 is forced). The claim is a counterexample to contractivity at the target λ = 1;
   ξ_0 and q cancel in differences of Φ, and ν = 0 is within the paper's σ-finite setting.
2. Stated as a relation between a trial and an output: the output solves the frozen linear
   forward equation (coefficients along the trial and its law) and the frozen linear BSDE
   (terminal value g at the output X'_T and its law, driver along the trial), each in the
   repository's class (progressive finite-energy integrands vanishing off [0,T], adapted
   right-continuous paths, equations a.s. at each t). The paper's output, built by
   predictable representation, is the unique such solution.
3. The trial's law is lawP2 of the trial tuple at every time (junk δ_0 only off L^2, a dt-null
   set of times for trials in ℍ, invisible to the dt and dW integrals).
Disagreements with the author's review (shown 2026-10-17T12:17:55Z): none
