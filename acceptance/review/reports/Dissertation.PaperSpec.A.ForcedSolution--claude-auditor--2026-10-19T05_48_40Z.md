### A:eq:forced, A:lem:cont, A:lem:small, A:sec4:WP-def: Dissertation.PaperSpec.A.ForcedSolution
Pins: manuscript A None; project 90f9502669c17b205fb9360fcfbae619d4e499e8; hash 6d8e8f373c5e26da320d4d9860023747 (pl-fp-v1:48a603d61ec17599f3078046a48dcff27e57ff01441c2f045551f6914e11ae98)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T05:48:40Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T05:36:17Z):
Reading of the paper's notion "solution of the lambda-scaled forced system (4.1)"
(04-proof-wellposedness.tex:37-68; used in WP(lambda), Lemmas 4.2, 4.3, 4.4).

Data: lambda in [0,1]; initial datum xi_0 (F_0-measurable); forcing q = (q^b, q^sigma, q^h, q^f,
q^g_T) with q^b in L2(Omega x [0,T]; R^n), q^sigma in L2(Omega x [0,T]; R^{n x d}), q^f in
L2(Omega x [0,T]; R^m) progressively measurable; q^h in L2(Omega x [0,T] x E; R^n) predictable
(P (x) calE-measurable, square-integrable for dP dt nu); q^g_T in L2(Omega, F_T; R^m).
Standing basis and coefficients as in sec. 2 (see the Solution reading).

The system (4.1): for every t in [0,T], a.s.,
 X_t = xi_0 + lambda int_0^t b(s,Theta_s,mu_s) ds + lambda int_0^t sigma(s,Theta_s,mu_s) dW_s
       + lambda int_0^t int_E h(s,Theta_s^-,e,mu_s^-) Ntilde(ds,de)
       + int_0^t q^b_s ds + int_0^t q^sigma_s dW_s + int_0^t int_E q^h_s(e) Ntilde(ds,de),
 Y_t = lambda g(X_T, Law(X_T)) + lambda int_t^T f(s,Theta_s,mu_s) ds + q^g_T + int_t^T q^f_s ds
       - int_t^T Z_s dW_s - int_t^T int_E U_s(e) Ntilde(ds,de),
with mu_s = Law(Theta_s), mu_s^- = Law(Theta_s^-), Theta_s^- = (X_{s-},Y_{s-},Z_s,U_s).
Note lambda multiplies all four coefficient terms AND the terminal function g; the forcing enters
unscaled; q^g_T is added at the terminal time; q^f is integrated over [t,T].

WP(lambda): for every such (admissible) forcing q, (4.1) has a unique solution in S (unique as
an element of S, i.e. up to indistinguishability of X, Y and a.e. equality of Z, U).
In Lemma 4.3 the paper also speaks of tuples that "solve (4.1)" in a weaker class (X, Y cadlag
adapted, E int (|X|^2+|Y|^2) < inf, X_T in L2, Z in H2_W, U in H2_N, difference in S), so the
phrase "solves (4.1)" is the two identities, with the class stated separately.

What a faithful Lean definition must be: parameterised by lambda, xi_0, the forcing q, the
coefficients and the tuple; the two identities above at every t (a.s.), with lambda on b, sigma,
h, f AND g; forcing terms unscaled, with the same signs/limits as printed; jump coefficient at
the predictable tuple (or a dt dP nu-a.e. equal predictable integrand); law under P. Class
membership either built in as S (matching WP(lambda)) or separate (matching Lemma 4.3); if S is
built in, uses of it for Lemma 4.3 would be narrower, but the definition itself is still the
paper's "solution in S of (4.1)". At lambda = 1 and q = 0 it must reduce to the Solution notion
of (1.1). Admissibility of q (progressive / predictable, square-integrable) must be required
where WP quantifies "every such forcing", either in the definition or in WP. Edge cases as for
Solution: junk integrals for non-admissible integrands (forcing or coefficient processes),
Euclidean norms, the augmented filtration.
Comparison (verdict recorded 2026-10-19T05:42:31Z):
Comparison: Dissertation.PaperSpec.A.ForcedSolution (PaperSpec/A/Setting.lean:102-110) against my
reading.

Lean: ForcedSolution D h𝒢₀ hind₀ T lam C ξ₀ qb qσ qh qf qg X Y Z U := WeakForcedSolution ... ∧
E sup |X|² < ∞ ∧ E sup |Y|² < ∞; WeakForcedSolution := (∃ γ, PaperWeakSolutionForcedInt D
(enlJoint 𝒢₀ D h𝒢₀) ... T lam C ξ₀ q X Y Z U γ) ∧ every path of X, Y with left limits on (0,T].
PaperWeakSolutionForcedInt: System/PaperWeakSolutionForcedInt.lean:68.

- Basis, filtration, class S: as for Solution (LevyDriver, 𝒢₀ independent, enlJoint usual
  augmentation; PaperWeakTuple + cadlag every path + S2 bounds): S.
- Forcing: field `forcing : Forcing ℱ P ν T q` (System/Coefficients.lean:196): q^b, q^σ, q^f
  jointly measurable, progressively measurable, vanishing off [0,T], finite energy; q^h jointly
  measurable in (ω,s,e), marked progressively measurable, vanishing off [0,T], finite marked
  energy; q^g_T strongly F_T-measurable and in L2. The paper's class has q^h predictable; WP
  quantifies over PredForcing (extends Forcing with q^h marked predictable), which is the paper's
  class. So ForcedSolution is defined for a slightly larger class of forcings, which contains the
  paper's; on the paper's forcings it is the paper's notion.
- Forward identity: a.s. for all t in [0,T],
  X_t = ξ₀ + int_[0,t] (lam b(s,Θ_s,μ_s) + q^b_s) ds + M_t + int_0^t int_E (lam γ + q^h) dNtilde,
  M a cadlag version of sum_j int (lam σ_{ij} + q^σ_{ij}) dW^j, γ a representative of
  h(s, Θ⁻_s, ., μ⁻_s) (jump_rep at the predictable tuple). Matches (4.1): lam on b, σ, h; forcing
  unscaled.
- Backward identity: a.s. for all t in [0,T],
  Y_t = lam g(X_T, Law X_T) + q^g_T + int_[t,T] (lam f + q^f) ds - (M'_T - M'_t)
        - (int_0^T int U dNtilde - int_0^t int U dNtilde).
  Matches (4.1): lam on g and f; q^g_T added; q^f over [t,T]; signs as printed.
- Integrals exist: forced drift/driver integrands progressive with a.s. integrable paths;
  forced diffusion/jump integrands progressive with finite energy; X_T in L2.
- lam is any real; the paper uses lam in [0,1]; the notion at lam in [0,1] is the paper's.
- At lam = 1, q = 0 it is the Solution notion (paperWeakSolutionForcedInt_one_zero_iff).
- WP (not this unit) quantifies over PredForcing and states uniqueness up to
  indistinguishability of X, Y and zero energy of the Z, U differences, i.e. in S as classes.

Representation choices (harmless):
 (1) all those of Solution (coordinate families and pointwise U; vanishing off [0,T]; actual law
     at every time; measurability of the coefficient processes as conditions; existential
     marked-progressive representative γ; identities a.s. for all t with cadlag versions of the
     Brownian integrals; every path cadlag; left limit at 0);
 (2) the admissibility of the forcing is a conjunct of the predicate, for the class Forcing
     (q^h marked progressive, not necessarily predictable): the paper only forms (4.1) for its
     admissible forcings, which lie in this class, and WP restricts to them (PredForcing);
 (3) each forced pair is integrated as one integrand (int (lam ψ + q^ψ) instead of
     lam int ψ + int q^ψ): equal by linearity, since q^ψ is admissible on its own, so the
     forced integrand is admissible exactly when lam ψ is;
 (4) lam ranges over all reals (only [0,1] is used).
The class S is built in, as in WP(lambda); Lemma 4.3's weaker class is the separate
WeakForcedSolution, so this is the paper's "solution in S of (4.1)".
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless: (1) all those of Solution: coordinate families with a pointwise U; vanishing off [0,T]; the actual law at every time; measurability of the coefficient processes as conditions; an existential marked progressive representative γ of h(s,Θ⁻_s,·,μ⁻_s); identities a.s. for all t with cadlag versions of the Brownian integrals; every path cadlag; (2) admissibility of the forcing is a conjunct of the predicate, in the class Forcing, where q^h only needs to be marked progressive rather than predictable; the paper's forcings lie in that class and WP(lambda) restricts to the paper's predictable class (PredForcing extends Forcing); (3) each forced pair is integrated as one integrand, ∫(λψ + q^ψ) rather than λ∫ψ + ∫q^ψ; by linearity these are equal, since q^ψ is admissible on its own; (4) λ ranges over all reals, and only [0,1] is used. λ multiplies b, σ, h, f and g, the forcing enters unscaled, q^g_T is added at T, and at λ = 1, q = 0 the notion is Solution.
Disagreements with the author's review (shown 2026-10-19T05:48:22Z): No disagreement in substance. The entry does not mention two representation choices that I would record. (a) Admissibility of the forcing is a conjunct of the predicate, in the class Forcing, where q^h only needs to be marked progressive rather than predictable. This is broader than the paper's predictable class, and WP(lambda) restricts to that class through PredForcing. (b) Each forced pair is integrated as one integrand, ∫(λψ + q^ψ), which by linearity equals the paper's λ∫ψ + ∫q^ψ. λ multiplies g as well as b, σ, h and f, as in (4.1). Verdict: faithful with representation choices.
