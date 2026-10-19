### A:rem:uniq-no-integ: Dissertation.PaperSpec.A.rem_uniq_singular
Pins: manuscript A None; project 90f9502669c17b205fb9360fcfbae619d4e499e8; hash ed839d34f480cba1ba6232c9763ebb54 (pl-fp-v1:06f71c096462fd68514de24682f31d6f20773bdbb1273329a526e9e9d3b72759)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T05:49:14Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T05:36:17Z):
Reading of the clause "the origin-value conditions are not necessary: the drift t^{-1/2} added
to one system of Example 5.1(i), with a solution in H" (Remark 3.4, 03-main-results.tex:180-194;
Example 5.1(i), 05-examples.tex:24-110; Assumption 2.2).

Remark 3.4: "the origin-value conditions are sufficient but not necessary. For instance, adding
the deterministic drift t^{-1/2} notin L2(0,T) to the b of a system satisfying Assumptions
2.2-2.5 violates Assumption 2.2 and leaves Assumptions 2.3-2.5 unchanged, yet the shift
X -> X - 2 sqrt t ... returns a system satisfying 2.2-2.5, so a solution still exists."
(The clause name says "a solution in H"; the paper's solution space is S (macro HH = \mathbb S),
and a "solution" is by definition in S; I read "in H" as "in S", i.e. a solution in the paper's
sense.)

This clause is the instance on one system of Example 5.1(i): n = m = d = 1, G = 1, nu
sigma-finite, xi_0 in L2(F_0), sigma_c in R, h_c in L2(nu), beta_1, beta_2 > 0, coefficients
b = -beta_1 y, sigma = sigma_c - beta_1 z, h = h_c - beta_1 u, f = beta_2 x, g(x,rho) = x.
Modified drift b'(t,theta,mu) = -beta_1 y + t^{-1/2} (value at t = 0 immaterial).

A faithful formal statement ("not necessary" = there is a system violating the origin-value
conditions which still has a solution) contains:
 (i) the modified system violates Assumption 2.2, specifically b'(.,0,delta_0) = t^{-1/2} is not
     in L2(0,T) (xi_0 in L2 kept, so it is the origin-value part that fails);
 (ii) the modified system has a solution Theta in S (paper's notion: cadlag adapted X,Y in S2,
     Z, U in H2_W, H2_N, identities of (1.1) a.s. for every t, with the ds-integrand
     s^{-1/2} - beta_1 Y_s pathwise integrable but NOT square-integrable in time);
 optionally (iii) Assumptions 2.3-2.5 hold for it (Remark: "leaves 2.3-2.5 unchanged").
Form: either universal over the Ex 5.1(i) data (T>0, any standing basis, beta_1, beta_2 > 0,
sigma_c, h_c, xi_0 in L2), or existential for one concrete system ("one system" in the clause
name); the existential form is acceptable only if the instance is a genuine standing-basis
instance (a real BM, a real Poisson random measure, the paper's filtration), not a degenerate
or junk one, and the conclusion (ii) is the paper's solution notion. Things to check in the Lean:
the solution notion must allow an L1-but-not-L2 drift (if the Lean Solution requires a
square-integrable drift process, then (ii) means something else or is false); (i) must be a
genuine failure of L2 membership (not produced by a junk value at t = 0); the coefficients must
be exactly those of 5.1(i) plus t^{-1/2}.
Comparison (verdict recorded 2026-10-19T05:46:02Z):
Comparison: Dissertation.PaperSpec.A.rem_uniq_singular (PaperSpec/A/Sec3Rem34.lean:56-76) against
my reading.

Lean: for every standing basis with 𝒢₀ = ⊥ (any E, σ-finite ν, countably generated E, any d,
LevyDriver D, ⊥ independent of it) and every T > 0, the coefficients singularCoeffs =
(affineCoeffs 1 0 0 0).addDrift singularDrift (Examples/SingularDrift.lean:83-90), i.e.
b = t^{-1/2} - y, σ = -z, h = -u, f = 0, g(x,ρ) = x (singularDrift t = (√t)⁻¹, which is 0 for
t ≤ 0), satisfy:
 JointBorel (2.3); Assumption23 with L = 1; G = 1 of full rank (Assumption 2.4); Assumption25
 with G = 1, α = 1, β₁ = 1, β₂ = 0; ¬ Assumption22 for every ξ₀; and ∃ X Y Z U with
 Solution D bot_le hind₀ T singularCoeffs 0 X Y Z U.
Assumption22/23/25 and JointBorel are the printed assumptions (Spec/Assumptions.lean): Assumption22
= ξ₀ ∈ L2(Ω, F_0) and the four origin values in L2 over (0,T) (volume.restrict (Ioo 0 T)).

Against my reading:
 (i) violation of Assumption 2.2: for every ξ₀ (in particular ξ₀ = 0, for which the initial-datum
     part holds), so it is the origin-value part that fails; b(t,0,δ₀) = t^{-1/2} on (0,T),
     not in L2(0,T). The junk value at t = 0 lies outside the Ioo 0 T over which L2 is taken, so
     the failure is genuine. Matches.
 (ii) a solution in S from ξ₀ = 0, in the reviewed Solution notion, whose drift integrand only
     needs integrable paths (PaperAdmissibleInt.b_int) -- so the L1-but-not-L2 drift
     s^{-1/2} - Y_s is admitted, as in the paper. Matches. (The explicit solution is
     X_t = 2√t - y_T t, Y ≡ y_T = 2√T/(1+T), Z = U = 0.)
 (iii) Assumptions 2.3-2.5 hold for the modified system: stated, with (2.3) too. Matches the
     optional part.
 The system: the affine family of Example 5.1(i) at β₁ = 1, β₂ = 0, σ_c = 0, h_c = 0, plus
 t^{-1/2}. Example 5.1(i) prints β₁, β₂ > 0, so with β₂ = 0 this is not literally a system of
 Example 5.1(i). The remark's own text, however, asks only for "a system satisfying Assumptions
 2.2-2.5", and this base system does satisfy them (n = m = 1, α = 1, β₁ = 1, β₂ = 0 are
 admissible constants, origin values 0, ξ₀ = 0). So it is an instance of the printed "for
 instance" claim. The clause name says "one system of Example 5.1(i)"; the paper's claim is
 still met.
 Form: universal over bases with 𝒢₀ = ⊥, for every d (d = 0 included, which is a harmless
 broadening) and every ν. An existential "not necessary" claim needs only one system on one
 basis. The witness rem_uniq_hypotheses (Acceptance/A/Sec3Rem34.lean:131) exhibits a probability
 space with a LevyDriver (d = 1, ν = δ₀) and ⊥ independent, so the statement is not about an
 empty class of bases.
 The coefficients are exactly the affine ones plus t^{-1/2}.

Representation choices: the instance is the β₂ = 0 member of the affine family of Example
5.1(i), not one with β₂ > 0, and is chosen to satisfy the remark's own hypothesis (Assumptions
2.2-2.5); the basis has trivial initial σ-field (𝒢₀ = ⊥) and any d; t^{-1/2} is coded as
(√t)⁻¹ with value 0 at t ≤ 0, a single null time.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices: (1) the system is the affine family of Example 5.1(i) at β₁ = 1, β₂ = 0, σ_c = 0, h_c = 0, with t^{-1/2} added to b. Example 5.1(i) prints β₂ > 0, so this is not literally one of its systems, as the clause name says. The remark's text only asks for "a system satisfying Assumptions 2.2-2.5", and this base system meets them with admissible constants α = 1, β₁ = 1, β₂ = 0 at n = m and zero origin values, so the statement is still an instance of the printed claim; (2) the statement holds on every basis with 𝒢₀ = ⊥ and any d, while a non-necessity claim needs only one system on one basis; the witness rem_uniq_hypotheses exhibits such a basis (d = 1, ν = δ₀); (3) t^{-1/2} is (√t)⁻¹, which is 0 for t ≤ 0. The L2 condition of Assumption 2.2 is taken over (0,T), so the failure of 2.2 is genuine and not a junk value. The solution exists in the reviewed Solution sense, which admits a drift integrable in time but not square-integrable.
Disagreements with the author's review (shown 2026-10-19T05:48:51Z): The recorded review says "broader", and it points to a report filed under rem_uniq_initial. I record "faithful with representation choices". This is a difference of label within the "matches" group. The Lean holds on every basis with 𝒢₀ = ⊥ and any d. The printed "for instance" needs only one system on one basis, so reading this as broader is also defensible. One point the recorded review may not flag: the instance is the affine family of Example 5.1(i) at β₂ = 0, while Example 5.1(i) prints β₁, β₂ > 0. So it is not literally "one system of Example 5.1(i)", as the clause name says. It is still a system satisfying Assumptions 2.2-2.5, which is all the remark's own text asks, so the printed claim is met.
