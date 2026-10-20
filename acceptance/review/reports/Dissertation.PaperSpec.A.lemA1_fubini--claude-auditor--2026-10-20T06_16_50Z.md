### A:lemA1:pettis: Dissertation.PaperSpec.A.lemA1_fubini
Pins: manuscript A None; project 6d403c197bfb10fe8808933c6e525ee0ae544fb1; hash ed839d34f480cba18bb7bf3a9a35bb91 (pl-fp-v1:21affc96cb4c8611e3f5aa34d8b24cb0fdaa743607613dd42246afce452628bc)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-20T06:16:50Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-20T06:10:05Z):
Reading of the clause (manuscript/paper/sections/09-appendix.tex, proof of Lemma A.1, Step 1: "The
Fubini isometry of [HNVW, Proposition 1.2.24], L^2([0,T] x Omega; H) = L^2(0,T; L^2(Omega; H)),
supplies a strongly measurable L^2(Omega;H)-valued representative of t -> Theta_t^-").

This is a cited fact, stated in the paper for the specific H of Section 2 on the standing
probability space. HNVW Prop. 1.2.24: for sigma-finite measure spaces (S, A, mu), (T, B, nu),
1 <= p < infinity and a Banach space X, the map f -> (s -> f(s, .)) is an isometric isomorphism
L^p(S x T; X) = L^p(S; L^p(T; X)).

What a faithful formal statement must contain.
Setting: T > 0; a probability space (Omega, F, P) (the full sigma-field F on Omega); H the paper's
Hilbert space R^n x R^m x R^{m x d} x L^2(nu; R^m), or more broadly any (separable) Hilbert or
Banach space (a broadening containing the paper's H as an instance is harmless; the instantiation
must then be the paper's H). Measure on [0,T] x Omega: Lebesgue restricted to [0,T] times P, on
B([0,T]) (x) F.
Conclusion: there exists a map Phi : L^2([0,T] x Omega; H) -> L^2([0,T]; L^2(Omega; H)) that is
(i) linear and isometric, and onto (an isometric isomorphism, "="); and
(ii) for every f in L^2([0,T] x Omega; H), for a.e. t in [0,T], the section omega -> f(t, omega)
    lies in L^2(Omega; H) and Phi(f)(t) is its class.
(ii) is the property used in the proof (it is what makes Phi(Theta^-) a representative of
t -> Theta^-_t). A statement giving only an abstract isometric isomorphism without (ii) would be
narrower than what the paper uses; a statement giving (ii) and isometry without surjectivity would
lose the "=" of the citation (the proof only needs the into-direction, but the paper asserts the
isomorphism). The clause name lists "Fubini isometry ... Phi(f)(t) = f(t, .) a.e. t", so the
isomorphism plus the section property is the target. Representatives: f is an a.e.-class; the
section property must be read for a representative of f (any two representatives give a.e.-equal
sections for a.e. t), so it must not depend on a particular junk representative in a way that
makes it false or vacuous.
No hypotheses beyond the setting.
Comparison (verdict recorded 2026-10-20T06:15:18Z):
Comparison of `Dissertation.PaperSpec.A.lemA1_fubini` (Dissertation/PaperSpec/A/AppASteps.lean) with my
locked reading of manuscript/paper/sections/09-appendix.tex, proof of Lemma A.1, Step 1 (the
Fubini isometry of HNVW Prop. 1.2.24).

Setting.
- Any probability space `(Ω, mΩ, P)` (the paper: the standing one, an instance). The σ-algebra on
  Ω is the full one, as in my reading. Broader, harmless.
- `ν` sigma-finite on a countably generated `E` (the standing hypothesis, needed to form H),
  `n m d : ℕ`, `T : ℝ` (any). Broader in the dimensions and T, harmless.
- H: `TupleL2 (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m ×
  Fin d)) (Lp (EuclideanSpace ℝ (Fin m)) 2 ν)`, the nested `WithLp 2` product: the paper's H with
  its Hilbert norm (Dissertation/WellPosedness/System/HilbertW2.lean, `TupleL2`, `norm_toL2_sq`).
  The statement is for the paper's H itself, not a general Banach space: exactly the printed
  instance.
- Spaces: `Lp H 2 ((volume.restrict (Icc 0 T)).prod P)` = L^2([0, T] × Ω; H) for
  Leb|[0,T] ⊗ P on Borel(ℝ) ⊗ mΩ; `Lp (Lp H 2 P) 2 (volume.restrict (Icc 0 T))` =
  L^2(0, T; L^2(Ω; H)) (closed versus open interval: a null difference).

Conclusion.
(i) `∃ Φ : … ≃ₗᵢ[ℝ] …`: a linear isometric equivalence, i.e. linear, isometric and onto. This is the
    "≅" of the citation, including surjectivity, as my reading required.
(ii) `∀ f, ∀ᵐ t ∂(Leb|[0,T]), (Φ f t : Ω → H) =ᵐ[P] fun ω => f (t, ω)`: for every f, for a.e. t, the
    section of (the canonical strongly measurable representative of) f at t is P-a.e. equal to
    the element Φ f t of L^2(Ω; H). This gives at once that the section lies in L^2(Ω; H) and that
    Φ(f)(t) is its class, for a.e. t. Since two representatives of f have P-a.e. equal sections
    for a.e. t (Fubini), the property does not depend on the representative, so it is neither
    vacuous nor an artefact of the junk choice of `↑f`. It pins Φ down uniquely as the section
    map, which is the map of HNVW 1.2.24 and the property the proof uses ("supplies a … representative
    of t ↦ Θ⁻_t").
No hypotheses beyond the setting; the quantifier order (Φ chosen after the data, before f) is
right.

Witness `Dissertation.Acceptance.A.lemA1_fubini_hypotheses`: the instance arguments are met at the
uniform law on Bool and ν = δ₀ on ℝ (nonzero). The only hypotheses are typeclass instances, met by
the paper's own setting; the proposition is not vacuous.

Comparison with my reading: every item matches; the only differences are the broadening to any
probability space, any T and any n, m, d (the paper's standing probability space, T > 0 and
n, m, d >= 1 are an instance).

Coverage (claim A:lemA1:pettis, acceptance/claims.json, clauses lemA1_L2, lemA1_fubini,
lemA1_pettis; scope_reviewed false). Its passage, as the scope note delimits it, is the sentence of
lines 43–51 with its input Θ⁻ ∈ L^2([0, T] × Ω; H) from lines 36–42. Its assertions: the input
(lemA1_L2), the Fubini isometry (this clause), the strongly measurable L^2(Ω; H)-valued
representative of t ↦ Θ⁻_t, separably valued off a null set by Pettis, with a Borel version a.e.
equal (lemA1_pettis). The clauses together state every assertion of the delimited passage, and no
clause states something it does not claim (the section property of this clause is the content of
HNVW 1.2.24 that "supplies a representative" relies on). Left out by the scope note: the
predictability of Θ⁻ and the earlier assertions of Step 1 (lines 25–36: left limits predictable
and a.e. equal to X, Y; H separable; the predictable L^2(ν)-valued representative of U), which no
other proof-step claim of the inventory states. Hypotheses: this clause has none beyond the
setting, as in the paper (a cited general fact); the other two carry exactly Lemma A.1's
hypotheses (X, Y càdlàg adapted, Z, U predictable, the integrability bound), those in force in
Step 1; no more, no fewer.
Witness: —
Verdict: broader — Broader only in the setting: any probability space (Ω, P) with its full σ-algebra, any T ∈ ℝ and any
n, m, d ∈ ℕ, for the paper's H (`TupleL2 …` with the Hilbert norm, ν sigma-finite on a countably
generated E). Instantiation giving the printed claim: the standing probability space
(Ω, F, P), T > 0, n, m, d >= 1. The conclusion is the printed one: a linear isometric equivalence
L^2([0, T] × Ω; H) ≃ L^2(0, T; L^2(Ω; H)) whose value at f is, for a.e. t, the class of the
section f(t, ·) (a representative-independent property).
Disagreements with the author's review (shown 2026-10-20T06:16:13Z): No substantive disagreement. One point on the verdict label: the author records `faithful` but also
says the proposition holds for every probability space and every T, with the printed claim as its
instance at the paper's (Ω, F, P) and horizon. That is the `broader` case of the protocol, with
that instantiation, and it is what I record. I agree with the reading of "≅" as a linear isometric
equivalence. I also agree that the a.e. section property identifies the map as the one of HNVW
1.2.24 and is independent of the representative of f.
