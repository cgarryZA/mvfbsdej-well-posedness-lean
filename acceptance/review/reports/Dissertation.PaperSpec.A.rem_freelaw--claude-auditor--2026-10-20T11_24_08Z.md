### A:rem:freelaw: Dissertation.PaperSpec.A.rem_freelaw
Pins: manuscript A None; project d3e594defeeeb94a6d05c33c666bcb870d584302; hash ed839d34f480cba105f02a9629cb6b98 (pl-fp-v1:37bf359e5fd4d04daf3d5ffb0ba9993b910a3dbe7b7fefc14cef695d3bba427e)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-20T11:24:08Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-20T11:09:24Z):
# Reading: rem_freelaw — Remark 5.6, clause "the coefficients depend on u pointwise whenever
# beta_1 > 0, with nu != 0"

Passage (05-examples.tex, Remark 5.6), with Remark 2.7 (beta_1 dichotomy) and Assumption 2.5.

What the passage asserts mathematically (beyond exposition about the proofs): coefficients that
read u ONLY THROUGH THE LAW (i.e. b, sigma, h, f do not depend on the u-coordinate of the point
theta = (x,y,z,u); they may depend on t, x, y, z and on mu, including the U-marginal of mu)
cannot satisfy the interior inequality (2.5) of Assumption 2.5 with beta_1 > 0 when nu != 0.
Equivalently: under (2.5) with beta_1 > 0 and nu != 0, some coefficient depends on u pointwise.
The argument: pick w in L^2(nu; R^m) with G^T w != 0 (exists when nu != 0 and G != 0, e.g. G
full rank), a symmetric sign xi independent of the other components (F_t-measurable, e.g. a
function of W_t for t > 0), tuples Theta, Theta' with U = xi w, U' = -xi w and equal other
components. Then Law(Theta) = Law(Theta'), so with u-free coefficients every delta-psi = 0
and the LHS of (2.5) is 0, while the RHS is -beta_1 E||G^T 2 xi w||^2 = -4 beta_1 ||G^T w||^2 < 0.
Since this works at every t in (0,T] (a set of positive measure), (2.5) "for a.e. t" fails.

Faithful formal statement must contain:
- setting: the standing filtered space (or one rich enough to carry an F_t-measurable symmetric
  sign independent of the other components at a non-null set of times), nu sigma-finite with
  nu != 0 (equivalently L^2(nu; R^m) != {0}); G in R^{m x n} (full rank, or at least such that
  some w has G^T w != 0);
- hypotheses: beta_1 > 0 (beta_2 arbitrary, >= 0 or real); coefficients b, sigma, h, f
  independent of the u-coordinate pointwise (they may depend on the law, including mu^U);
- conclusion: (2.5) fails, i.e. NOT [for a.e. t, for all diagonal inputs (Theta,mu),(Theta',mu')
  at t, the expected pairing <= -beta_1 E[...] - beta_2 E|G dX|^2]; or the contrapositive form
  (2.5) with beta_1 > 0 and nu != 0 implies some coefficient depends on u pointwise.
  A version exhibiting, at some t (in fact at every t>0), diagonal inputs with LHS = 0 and
  RHS = -4 beta_1 ||G^T w||^2 < 0 is also acceptable.
- the inequality must be the genuine (2.5) on diagonal inputs (mu = Law(Theta)), with the
  expectation of the pairing as in Assumption 2.5 (h-term integrated against nu), not a
  pointwise or free-measure surrogate; a version that weakens the hypothesis on the
  coefficients (e.g. only h u-free) would be a different (stronger) claim and must be checked
  for truth; a version that adds hypotheses (e.g. m = n only) would be narrower.
The other sentences ("the proofs consume the tuple law through a single mechanism", "nothing is
gained by restricting to the (X,Y,Z)-marginal law", the dealer-example remark) are exposition.
Comparison (verdict recorded 2026-10-20T11:23:00Z):
# Decision: spec:Dissertation.PaperSpec.A.rem_freelaw (Dissertation/PaperSpec/A/Sec5FreeLaw.lean)

Verdict: faithful with representation choices.

Numbering note on my locked reading: it wrote "(2.5)" for the interior inequality eq:mono, which
the paper numbers (2.7), and "Remark 2.7" for the beta_1 dichotomy, which is Remark 2.10. The
content referred to is unambiguous (Assumption 2.5's interior inequality; Remark rem:beta1-dich).

Comparison with the locked reading.
- Setting. Ω with a Lévy driver `D : LevyDriver P d ν` (Brownian motion W and Poisson random
  measure N with intensity dt ν(de)), an initial σ-field 𝒢₀ independent of the driver, and the
  filtration `enlJoint 𝒢₀ D h𝒢₀`, the usual augmentation of the filtration of W, N and 𝒢₀
  (Dissertation/WellPosedness/Enlarged/Filtration.lean): the paper's standing basis. ν σ-finite on
  a countably generated space; n, m, d >= 1; T > 0. All as in §2.
- Hypotheses. ν ≠ 0 (the passage's "ν ≠ 0"); G ∈ R^{m x n} with `G.rank = min m n` (Assumption
  2.4); `Assumption25 … G α β₁ β₂ C` (Dissertation/WellPosedness/Spec/Assumptions.lean: the
  terminal inequality, the interior inequality (2.7) for a.e. t over all pairs of diagonal inputs
  with the pairing required integrable, and the admissible constants); β₁ > 0. The passage's
  "whenever β₁ > 0" refers to the constant of Assumption 2.5, so the coefficients in question are
  those satisfying Assumption 2.5; the argument itself uses only the interior inequality, and
  requiring all of Assumption 2.5 is the context of the remark, not an added restriction on the
  printed claim (the remark is about the coefficients the theorems treat).
- Conclusion. For a.e. t ∈ [0, T] there are two diagonal inputs p, p' at t with the same law
  (p.2 = p'.2), the same X, Y, Z at every ω, and the jump coefficient h(t, ·, μ) differing at the
  two tuples with positive probability. Since the two tuples differ only in the u-channel and carry
  the same law, this says exactly that the coefficients depend on u pointwise and that this
  dependence is invisible to any law argument -- the positive form of "coefficients reading u only
  through the law make the left-hand side of (2.7) vanish, while its right-hand side is
  -4 β₁ ||Gᵀ w||^2 < 0". The proposition names h specifically; this is what the passage's
  construction yields, since with δX = δY = δZ = 0 only the jump term ∫⟨δh, Gᵀ δU⟩ dν of the
  pairing survives (the passage defers to Remark 2.10, "β₁ > 0 forces the jump coefficient h to be
  strictly U-dissipative"). So the h-specific form is the passage's content, slightly sharper
  than the words "the coefficients", and implies them.
- Diagonal inputs are `diagonalInputs` (strongly F_t-measurable, square integrable, with law
  `lawP2`), Definition 2.1. The expectation in (2.7) is the genuine one (integrability required),
  with the jump pairing ∫_E ⟨δh(e), Gᵀ δU(e)⟩ ν(de) (`pairing27`).
- Quantifier on t: "for a.e. t", which matches (2.7) being imposed for a.e. t; the construction
  of the passage (a symmetric F_t-measurable sign, e.g. a function of W_t, t > 0) works at every
  such t.
Representation choices: the positive (contrapositive) form exhibiting the same-law pair instead of
"u-free coefficients violate (2.7)"; the h-specific conclusion; the Lean encoding of the
standing basis. None changes the meaning.

Current text. Read at 1f67672 (Remark 5.6: "a dependence Remark 2.10 makes unavoidable whenever
β₁ > 0 and ν ≠ 0: for w ∈ L^2(ν) with Gᵀ w ≠ 0 and a symmetric sign ξ independent of the other
components, the tuples with U = ξ w and U' = -ξ w and equal other components have the same law
..."). I have not seen the earlier text, so I cannot say what changed; the proposition says what
the current passage says (same law, equal other components, pointwise u-dependence forced under
β₁ > 0 and ν ≠ 0). If the earlier text lacked the hypothesis ν ≠ 0 or the same-law construction,
the proposition's hypothesis ν ≠ 0 and its same-law conclusion now match the printed text.

Witness. `Dissertation.Acceptance.A.rem_affine_hypotheses` (Dissertation/Acceptance/A/
Sec2Remarks.lean): a Lévy driver with d = 1 and ν = δ_0 ≠ 0, 𝒢₀ = ⊥ (independent), T = 1,
G = 1 (full rank), the coefficients of Example 5.1(i) with β₁ = β₂ = 1 (σ_c = h_c = 0), which
satisfy Assumption 2.5 with α = 1, β₁ = 1 > 0. This is an instance the paper intends (Example
5.1(i) is the paper's model with β₁ > 0 and ν ≠ 0), with β₁ and ν nonzero; the zero baseline
noises σ_c, h_c are irrelevant to this clause.

Coverage (claim A:rem:freelaw: clauses eq_coupling "the W₂ term is dominated by (2.8)" and
rem_freelaw). The mathematical assertions of Remark 5.6 are: the W_2 term of Assumption 2.3 is
dominated by (2.8) (eq_coupling); the pointwise u-dependence forced by β₁ > 0 and ν ≠ 0, with the
same-law construction (rem_freelaw). "The proofs consume the tuple law through a single mechanism",
"nothing is gained by restricting to the (X, Y, Z)-marginal law" and the pointer to Example 5.5
are statements about the paper's proofs and exposition, not mathematical claims to prove
(Example 5.5's routing mechanism is covered under its own claim). The observation that the
right-hand side of (2.8) carries E||δU||^2 is a reading of (2.8). No clause states anything the
passage does not claim; the hypotheses (ν ≠ 0, β₁ > 0, the standing assumptions) are those in
force.
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless:
1. Positive form. Instead of "coefficients reading u only through the law violate (2.7) when
   β₁ > 0, ν ≠ 0", the proposition concludes, under Assumption 2.5 with β₁ > 0, ν ≠ 0 and G of
   full rank, that for a.e. t there are diagonal inputs with the same law and the same (X, Y, Z)
   at which h differs with positive probability. This is the contrapositive of the printed claim,
   made explicit by the printed same-law construction.
2. The conclusion names the jump coefficient h. With δX = δY = δZ = 0 only the jump term of the
   pairing survives, so the passage's construction forces exactly h to read u pointwise (as the
   cited Remark 2.10 states); the h-specific form implies "the coefficients depend on u pointwise".
3. The hypothesis is the whole of Assumption 2.5 (and Assumption 2.4's full rank), the context in
   which the remark speaks of β₁; the argument uses only the interior inequality (2.7).
4. The standing basis is the Lean Lévy driver with the augmented initially enlarged filtration.
Disagreements with the author's review (shown 2026-10-20T11:23:28Z): Disagreement in the verdict label only, against the current text. The earlier review records
"faithful"; I record "faithful with representation choices", because the proposition states the
printed claim in its positive (contrapositive) form -- under Assumption 2.5 with β₁ > 0, ν ≠ 0 and
G of full rank, for a.e. t there are diagonal inputs with the same law and the same (X, Y, Z) at
which the jump coefficient h differs with positive probability -- and names h specifically, which
is what the passage's construction (δX = δY = δZ = 0, so only the jump pairing survives, as the
cited Remark 2.10 says) yields, slightly sharper than the passage's words "the coefficients". It
also takes the whole of Assumption 2.5 as hypothesis, the context in which the remark speaks of
β₁, although the argument uses only the interior inequality (2.7). I agree it says what the current
Remark 5.6 says.
