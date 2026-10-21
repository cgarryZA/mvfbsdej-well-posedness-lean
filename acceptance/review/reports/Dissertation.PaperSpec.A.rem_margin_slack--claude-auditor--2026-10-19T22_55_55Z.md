### A:rem:margin: Dissertation.PaperSpec.A.rem_margin_slack
Pins: manuscript A None; project 6d403c197bfb10fe8808933c6e525ee0ae544fb1; hash ed839d34f480cba1fc10bfb5bc98adb1 (pl-fp-v1:2ae7bdd685c38a49e73f1989f4d1a6d33a33d95fc1e249656305066519b4a06f)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T22:55:55Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T22:46:30Z):
# Reading: spec rem_margin_slack (Remark 2.11, "recording weaker constants turns the difference into slack ...")

Paper passage (sec 2, Remark 2.11, rem:margin). Equation numbers: (2.7)=eq:mono, (2.12)=eq:monomargin,
(3.4)=eq:pertpair (Cor 3.6). The clause read here is the second half of the sentence "recording
weaker constants turns the difference into slack, which a perturbation raising the interior pairing
by at most the margin leaves intact", made precise as the clause name says:

Setting. Standing basis of section 2 (filtered probability space with usual conditions, horizon
T>0, dims n,m,d>=1, d-dim BM W, independent PRM N with intensity dt nu(de), nu sigma-finite on a
countably generated E; filtration = usual augmentation of sigma(W,N) v F_0). State space
H = R^n x R^m x R^{m x d} x L^2(nu;R^m). Coefficients (baseline) b0, sigma0, h0, f0 and
perturbations p_b, p_sigma, p_h, p_f: deterministic functions [0,T] x H x P_2(H) -> R^n,
R^{n x d}, L^2(nu;R^n), R^m (Borel). G in R^{m x n} (full rank is in force in section 2 but not
needed for this step). Diagonal inputs: pairs (Theta, Law(Theta)), Theta in L^2(Omega,F_t;H).

Hypotheses (a faithful statement must contain, or be broader than):
 (H1) baseline satisfies (2.12) with constants beta1, beta2 and margin c: for a.e. t in [0,T] and
      all diagonal pairs (Theta,mu),(Theta',mu') in D_t,
      E[<db0,G^T dY> + <dsigma0,G^T dZ>_F + <-df0,G dX> + int_E <dh0(e),G^T dU(e)> nu(de)]
        <= -beta1 E[|G^T dY|^2+|G^T dZ|_F^2+||G^T dU||^2] - beta2 E|G dX|^2
           - c E[|G^T dY|^2+|G^T dZ|_F^2+||G^T dU||^2+|G dX|^2].
 (H2) perturbation pairing bound (3.4) recorded in the weighted quantity: for a.e. t and all
      diagonal pairs, E[<dp_b,G^T dY> + <dp_sigma,G^T dZ>_F + <-dp_f,G dX> + int <dp_h,G^T dU> dnu]
        <= c_pert E[|G^T dY|^2+|G^T dZ|_F^2+||G^T dU||^2+|G dX|^2].
 (H3) 0 <= c_pert <= c ("raising the pairing by at most the margin"); c>0 in the definition of
      margin (c>=0 or arbitrary would be harmlessly broader). beta1, beta2: the reduced constants
      (any reals is broader, fine).
 (H4) Whatever makes the expectations meaningful and additive: in the paper the coefficients are
      Lipschitz along the diagonal (Assumption 2.5, and Cor 3.6 imposes it on the perturbations
      too), so every pairing is an expectation of a product of L^2 variables. A Lean statement
      must either carry such integrability (Lipschitz along the diagonal, or explicit
      integrability of the pairing integrands) or otherwise make the splitting
      E[A+B]=E[A]+E[B] valid; without it, Lean's Bochner junk value 0 for non-integrable
      integrands could make the formal statement false or about something else. Adding
      Lipschitz/integrability is in force in the paper's context and acceptable.

Conclusion: the perturbed coefficients (b0+p_b, sigma0+p_sigma, h0+p_h, f0+p_f) satisfy (2.7)
with beta1, beta2: for a.e. t and all diagonal pairs,
  E[<db,G^T dY> + <dsigma,G^T dZ>_F + <-df,G dX> + int <dh,G^T dU> dnu]
     <= -beta1 E[|G^T dY|^2+|G^T dZ|_F^2+||G^T dU||^2] - beta2 E|G dX|^2.
Differences dpsi = psi(t,Theta,mu) - psi(t,Theta',mu') along the diagonal pairs; the jump
coefficient differences are L^2(nu)-valued, the pairing int_E <dh(e), G^T dU(e)> nu(de) is the
L^2(nu;R^n) x L^2(nu;R^m) pairing <dh, G^T dU>_{L^2(nu)} (G^T acting pointwise).
A per-t version (hypotheses at t imply conclusion at t, for all t) is equivalent/broader and fine.
Hypotheses restricted to "for all t" instead of a.e. t would be narrower (but harmless if the
conclusion is also per t). Quantifier order: the constants beta1,beta2,c,c_pert are fixed before
t and the inputs.

Non-vacuity: hypotheses satisfiable e.g. by p = 0, c_pert = 0, and a baseline with margin (e.g.
b0 = -k G^T... dissipative linear coefficients as in Example 5.x(i)), any witness should exhibit a
genuine instance (nonzero coefficients) with c_pert in [0,c].
Coverage note (for later): the sentence also has a first half (reduction beta_i := barbeta_i - c
gives (2.12)) and a later m=n unweighted part (margin c/c_G in (2.13)); those should be other
clauses of the claim.
Comparison (verdict recorded 2026-10-19T22:49:46Z):
# Comparison: spec rem_margin_slack (Dissertation/PaperSpec/A/Sec3GeneralRank.lean:57-71)

Note on the revision: rv.py prints "revision f598204"; the brief, claims.json and the Lean
docstrings say 1f67672. I read the vendored manuscript/paper/ (the pinned source of claims.json).

Item by item against my locked reading:
* Setting. Ω, 𝒢₀ ≤ mΩ independent of the driver σ-algebra, E with countably generated σ-algebra,
  ν σ-finite, P probability, D : LevyDriver P d ν (d-dim BM W and PRM N with intensity
  Leb ⊗ ν, σ(W) ⫫ σ(N)); filtration enlJoint 𝒢₀ D h𝒢₀ = usual augmentation (right-continuous
  version, null sets) of t ↦ ℱ^{W,N}_t ⊔ 𝒢₀. This is the standing basis of §2. OK.
* Coefficients C, p : Coeffs ν n m d — deterministic b, σ, h, f (h valued in Lp 2 ν =
  L²(ν;ℝⁿ)) and g; C.perturb p = (b₀+p_b, σ₀+p_σ, h₀+p_h, f₀+p_f, g). OK (Borel measurability
  not required: broader, irrelevant to this algebraic step).
* (H1) Margin212 ... β₁ β₂ c C: for a.e. t ∈ [0,T], all p, p' ∈ diagonalInputs at t: the pairing
  pairing27 (= ⟨δb,GᵀδY⟩ + ⟨δσ,GᵀδZ⟩_F + ⟨−δf,GδX⟩ + ∫_E⟨δh(e),GᵀδU(e)⟩ν(de); GX/GZ/GU are
  x↦Gx, the Kronecker G⊗I_d on ℝ^{n×d} (column-wise G), and mark-wise G on L²(ν)) is integrable
  and its expectation is ≤ −β₁E[|GᵀδY|²+|GᵀδZ|²_F+‖GᵀδU‖²] − β₂E|GδX|² − cE[weighted sum].
  Matches (2.12). 0 < c: matches "margin c > 0".
* (H2) PairingBound34W ... cpert p: for a.e. t, all diagonal pairs, the perturbation pairing is
  integrable and E ≤ c_pert E[|GᵀδY|²+|GᵀδZ|²_F+‖GᵀδU‖²+|GδX|²]. Matches (3.4) recorded in the
  weighted quantity (as Remark 3.7 phrases it).
* (H3) 0 ≤ cpert ≤ c. Matches.
* (H4) integrability: carried inside Margin212 / PairingBound34W (Integrable of the pairing).
  This is what makes the splitting valid; it is the paper's tacit "the expectation exists",
  which under Assumption 2.3 (Lipschitz, in force throughout) holds automatically.
* Conclusion: ∀ᵐ t ∈ [0,T], Mono27At t G β₁ β₂ (C.perturb p): for all diagonal pairs at t, the
  perturbed pairing is integrable and E ≤ −β₁E[...] − β₂E|GδX|². Matches (2.7) for the perturbed
  coefficients with the recorded constants, a.e. t. The integrability is an extra (stronger)
  conclusion. Quantifier order: constants before t and inputs. OK.
* diagonalInputs: pairs (Θ, lawP2 P Θ) with Θ strongly ℱ_t-measurable and MemLp 2 — the
  representatives of L²(Ω,ℱ_t;H) with their law in P₂(H). OK.
* Edge cases: Bochner junk cannot bite — integrability is assumed for both brackets and the
  weighted quadratic integral is ≥ 0 whatever its value; ν-integral of the Lp-valued h is
  representative-independent; the max-norm on TupleH does not enter (only channel norms appear).
* Generality: arbitrary n, m, d (incl. 0), arbitrary T, arbitrary G (no full rank), arbitrary
  real β₁, β₂ — the printed claim (n,m,d ≥ 1, T > 0, G of Assumption 2.4, β_i = β̄_i − c > 0) is
  the instance. Unused standing hypotheses dropped.
* Witness rem_margin_slack_hypotheses: n = m = d = 1, ν = δ₀, G = 1, baseline affineCoeffs 2 2 0 0
  with (2.12) at β₁ = β₂ = c = 1, perturbation affineCoeffs (−1/2) 0 0 0 with weighted (3.4) at
  c_pert = 1 (from 1/2 by monotonicity), 0 ≤ 1 ≤ 1. A genuine nonzero instance of the
  Corollary 3.6 / Remark 3.7 type (finite ν though, so not infinite activity; not required). The
  hypotheses are met; not vacuous.
* Is it claimed by the paper at this revision? Yes: Remark 2.11, "recording weaker constants turns
  the difference into slack, which a perturbation raising the interior pairing by at most the
  margin leaves intact". Reading "raising by at most the margin" as the perturbation bracket being
  ≤ c_pert·(weighted quantity) with c_pert ≤ c is the natural one (Remark 3.7 uses the same
  weighted bookkeeping); with c_pert = c it is literally "at most the margin", and c_pert ≤ c is
  equivalent by monotonicity.

Verdict: faithful with representation choices.

## Coverage (claim A:rem:margin, after show)
Clauses: rem_margin_reduce (bound with β̄ᵢ is (2.12) with β̄ᵢ − c, margin c, 0 < c < min β̄ᵢ),
rem_margin_unweighted (m = n: weighted margin c gives margin c/c_G in (2.13)), rem_margin_smaller
(c/c_G < c when c_G > 1), rem_margin_slack (this unit). The passage's mathematical assertions are:
the definition of "with margin" (2.12) and of (2.13) (definitions, carried by Margin212 /
Margin213 in the closure), the reduction, the slack sentence, the m = n injectivity and the
channel-wise inequality c(weighted) ≥ (c/c_G)(unweighted) (a step of the unweighted clause), the
margin c/c_G in (2.13), and "smaller than c when c_G > 1". Every assertion is stated by some
clause; I see no clause stating something the passage does not claim. Hypotheses: the remark sits
in §2 under the standing setting only; this clause takes no Assumption 2.2–2.5 (none is used,
integrability being part of the bounds), so no hypothesis is added; the standing restrictions
n,m,d ≥ 1, T > 0, full-rank G are dropped (broader, harmless).
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless:
1. The expectations in (2.12), the weighted (3.4) and (2.7) are Bochner integrals with integrability
   of the pairing integrand built into Margin212, PairingBound34W and Mono27At. The paper's "E[...] ≤"
   presupposes the expectation exists (automatic under the Lipschitz Assumption 2.3 in force); the
   hypotheses thus match the paper's meaning and the conclusion is stronger (it also gives
   integrability). No junk value can enter.
2. Diagonal inputs are the strongly ℱ_t-measurable MemLp-2 maps Ω → H with their law lawP2 P Θ,
   i.e. representatives of L²(Ω,ℱ_t;H); the filtration is enlJoint (usual augmentation of
   σ(W,N) ⊔ 𝒢₀ with 𝒢₀ independent) — the standing basis.
3. Gᵀ acts on δZ through the Kronecker G⊗I_d (column-wise), on δU mark-wise in L²(ν); Frobenius
   norm via EuclideanSpace on Fin m × Fin d. Same objects as the paper.
4. Standing restrictions not needed by the step are dropped: n, m, d may be 0, T arbitrary, G need
   not be full rank, β₁, β₂ arbitrary reals, Coeffs need not be Borel. The printed claim is the
   instance n,m,d ≥ 1, T > 0, G full rank, β_i = β̄_i − c.
5. "A perturbation raising the interior pairing by at most the margin" is formalised as the
   perturbation bracket ≤ c_pert·(weighted quantity of (2.12)) with 0 ≤ c_pert ≤ c; c_pert = c is the
   literal reading and the c_pert ≤ c form is equivalent by monotonicity.
Disagreements with the author's review (shown 2026-10-19T22:55:46Z): Substantive disagreement: none. I agree with the author's correspondence (the slack clause read as
(2.12) with β₁, β₂, margin c > 0, plus the weighted (3.4) with 0 ≤ c_pert ≤ c, giving (2.7) with
β₁, β₂ for C.perturb p, a.e. t) and with the witness (a genuine nonzero instance).

Minor difference of verdict label: the author records "faithful"; I record "faithful with
representation choices", because (i) the integrability of the pairing integrands is part of the
hypotheses Margin212 / PairingBound34W (the paper's tacit "the expectation exists", automatic under
Assumption 2.3, which the sentence itself does not invoke), and (ii) the proposition drops the
standing restrictions n, m, d ≥ 1, T > 0 and full rank of G, so it is formally broader, the printed
claim being the instance. Both are harmless; neither changes the meaning.
Also noted: rv.py labels the paper revision f598204 while claims.json and the Lean say 1f67672.
