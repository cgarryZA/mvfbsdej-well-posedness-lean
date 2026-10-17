### A:rem:generalrank: Dissertation.PaperSpec.A.PairingBound34W
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 2b1db421079e9e76f26e2afdddf6a5b4 (pl-fp-v1:683e0ac0a281424ee4e2bab8a001690f4a140d723462f6fc4a511f402726e476)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T12:23:19Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:22:51Z):
# Reading: (3.4) recorded in the weighted quantities (def:Dissertation.PaperSpec.A.PairingBound34W)

Paper: Corollary 3.6, (3.4) = eq:pertpair: for some c_pert ≥ 0, for a.e. t ∈ [0,T] and all
(Θ,μ), (Θ',μ') ∈ D_t,
  E[⟨δp_b, GᵀδY⟩ + ⟨δp_σ, GᵀδZ⟩_F + ⟨−δp_f, GδX⟩ + ∫_E ⟨δp_h(e), GᵀδU(e)⟩ ν(de)]
    ≤ c_pert E[|δX|² + |δY|² + |δZ|_F² + ‖δU‖²]   (unweighted, m = n).
Remark 3.7 (general rank): "(3.4) recorded in those [weighted] quantities", i.e. with the
right-hand side c_pert E[|GᵀδY|² + |GᵀδZ|_F² + ‖GᵀδU‖²_{L^2(ν)} + |GδX|²], the weighted
quantities of (2.12). δp_ψ = p_ψ(t,Θ,μ) − p_ψ(t,Θ',μ') for the perturbation coefficients
p = (p_b, p_σ, p_h, p_f) (same signatures as b, σ, h, f).

A faithful Lean definition: parameters (filtration, P, T, G, c_pert, the perturbation
coefficients); for a.e. t ∈ [0,T] and all pairs of D_t (F_t-measurable L^2 tuples with their
laws), the pairing of the perturbation differences (same pairing as (2.7), with p in place of
(b,σ,h,f)) has expectation at most c_pert times the expectation of the weighted sum (Gᵀ on Y, Z,
U; G on X). Integrability of the pairing may be required (as in the repository's convention),
harmless under the Lipschitz condition on p. c_pert ≥ 0 may be a separate hypothesis.
Comparison (verdict recorded 2026-10-17T12:23:08Z):
# Comparison: PairingBound34W

Lean (PaperSpec/A/Sec3GeneralRank.lean:36-51): for ℱ, P, T, G, c and a perturbation
`p : Coeffs ν n m d` (its b, σ, h, f fields are p_b, p_σ, p_h, p_f; its g field is unused):
∀ᵐ t ∂(Lebesgue on [0,T]), ∀ q, q' ∈ diagonalInputs … t,
  Integrable (pairing27 G p t …) ∧ E[pairing27 G p t …]
    ≤ c · E[|Gᵀ δY|² + |Gᵀ δZ|²_F + ‖Gᵀ δU‖²_{L^2(ν)} + |G δX|²].

- Left side: pairing27 with p in place of C: ⟨δp_b, GᵀδY⟩ + ⟨δp_σ, GᵀδZ⟩_F + ⟨−δp_f, GδX⟩ +
  ∫⟨δp_h(e), GᵀδU(e)⟩ν(de), δp_ψ = p_ψ(t,θ,μ) − p_ψ(t,θ',μ'). The pairing of (3.4). Good.
- Right side: c times the expectation of the four weighted quantities of (2.12) (Gᵀ on Y, Z,
  U; G on X). This is (3.4) "recorded in the weighted quantities" (Remark 3.7). Good.
- Quantifiers: a.e. t, then all pairs of D_t (as in Margin212). Good.
- Integrability conjunct: added, as in the repository's Ass. 2.5 convention; for perturbations
  satisfying the diagonal Lipschitz condition (hypothesis of Cor. 3.6/Rem. 3.7) the pairing is
  integrable for L^2 inputs. Harmless.
- c_pert ≥ 0: not part of the definition (belongs to the user). Fine.

Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices:
1. The perturbation (p_b, p_σ, p_h, p_f) is packaged as a `Coeffs` record whose terminal field is
   unused by the pairing; only the four interior fields enter.
2. The bound is accompanied by integrability of the pairing (the expectation exists), the
   repository's convention for Assumption 2.5; for perturbations satisfying the diagonal
   Lipschitz condition required by Cor. 3.6 / Remark 3.7 this holds for all L^2 diagonal inputs.
3. D_t represented by strongly F_t-measurable L^2 maps with their lawP2 laws (as in Margin212);
   the jump pairing through representatives of L^2(ν) elements (equal to the L^2 inner product).
Disagreements with the author's review (shown 2026-10-17T12:23:08Z): none
