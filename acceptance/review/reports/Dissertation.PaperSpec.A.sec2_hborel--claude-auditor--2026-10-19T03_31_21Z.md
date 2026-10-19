### A:sec2:hborel-derivation: Dissertation.PaperSpec.A.sec2_hborel
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba1c7bf6ee7f1e38851 (pl-fp-v1:b1e4d726d3b3b991de9f5512ca4f3545c5196ffe05e90dd05535db981e2b5e9a)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:31:21Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:16:08Z):
Reading of spec sec2_hborel, clause "joint pointwise measurability of h gives (2.3)" (02:100-110).
Setting: nu sigma-finite on countably generated (E,calE), so L2(nu;R^n) separable; H separable Hilbert
(R^n x R^m x R^{m x d} x L2(nu;R^m)) with Borel sigma-algebra; P_2(H) with Borel sigma-algebra of W_2.
Claim: if h: [0,T] x H x E x P_2(H) -> R^n, (t,theta,e,mu) |-> h(t,theta,e,mu), is jointly measurable
(Borel([0,T]) ⊗ Borel(H) ⊗ calE ⊗ Borel(P_2(H))) and each section e |-> h(t,theta,e,mu) is in L2(nu;R^n)
(implicit in the signature h: ... -> L2(nu;R^n)), then (t,theta,mu) |-> [h(t,theta,.,mu)] in L2(nu;R^n) is
Borel measurable (equivalently strongly measurable, the target being separable).
Proof route: Tonelli gives weak measurability, Pettis upgrades. A faithful statement must quantify over all
such h (arbitrary dimension n or the needed n), allow arbitrary sigma-finite nu on a countably generated E,
take the Borel sigma-algebras on [0,T], H, P_2(H); the conclusion must be measurability into L2(nu;R^n)
(the Lp space, with its Borel sigma-algebra) of the map to the a.e.-class. Narrower if it adds hypotheses
(e.g. continuity, finite nu, boundedness); broader if the parameter space is an arbitrary measurable space
(instantiate with [0,T] x H x P_2(H)).
Comparison (verdict recorded 2026-10-19T03:29:17Z):
Comparison, sec2_hborel (Sec2Basics.lean:132-145) vs reading.
- Setting: ν σ-finite, E countably generated, any n,m,d,T; a coefficient record C whose h is valued in
  L²(ν;R^n) (so every section is in L²(ν), the implicit signature condition).
- Hypotheses: a function H : ([0,T] × H × P2(H)) × E → R^n, measurable for borel([0,T] × H × P2WH) ⊗ 𝓔
  (P2WH: W2 of the Hilbert norm), with H(p,·) a representative of h(p) for every p: this is "joint
  pointwise measurability of (t,θ,e,μ) ↦ h(t,θ,e,μ)" with the pointwise h given as a jointly measurable
  version of the L²-valued coefficient. The Borel σ-algebra of the product space is used (it equals the
  product of the Borel σ-algebras, all factors being second countable: H separable, P2(H) separable).
- Conclusion: p ↦ h(p) Borel measurable from borel([0,T] × H × P2WH) into borel(L²(ν;R^n)) -- exactly
  (2.3).
- Witness sec2_hborel_nonzero_hypotheses: a nonzero instance (affine h at ν = δ_0).
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices: (1) the jump coefficient is an L²(ν;R^n)-valued map C.h, and "the pointwise
h(t,θ,e,μ)" is a jointly measurable function H whose sections represent C.h(t,θ,μ) for every (t,θ,μ):
this encodes the paper's h whose e-sections lie in L²(ν); (2) the measurable structure on [0,T] × H ×
P2(H) is the Borel σ-algebra of the product topology (equal to the product of Borel σ-algebras for these
second-countable factors), P2(H) with the Hilbert-norm W2; (3) [0,T] as the subtype Set.Icc 0 T. Harmless.
Disagreements with the author's review (shown 2026-10-19T03:29:28Z): No disagreement on substance. Label only: the review records "faithful"; I record "faithful with
representation choices" (L²-valued coefficient with a jointly measurable pointwise version H whose sections
represent it; Borel σ-algebra of the product space [0,T] × H × P2WH). Same correspondence.
