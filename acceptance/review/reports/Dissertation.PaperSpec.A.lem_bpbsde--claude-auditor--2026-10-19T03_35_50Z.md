### A:lem:bpbsde: Dissertation.PaperSpec.A.lem_bpbsde
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba1202e3ec284da1f15 (pl-fp-v1:b9ef9bf6d8a83c03894450213b3ad879c95d5e54575291d921edba3be8b1d9d3)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:35:50Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:15:38Z):
Reading (locked before any Lean): spec lem_bpbsde, Lemma 4.1 (Brownian-Poisson L2 estimate),
clause "main".

Paper content. Let dY be cadlag adapted R^m-valued, dZ in H^2_W (predictable, E int |dZ|_F^2 <
inf), dU in H^2_N (predictable L2(nu)-valued, E int ||dU||^2 < inf), satisfying (4.2)
  dY_t = dxi + int_t^T phi_s ds - int_t^T dZ_s dW_s - int_t^T int_E dU_s(e) Ntilde(ds,de)
(a.s., for every t in [0,T]) with dxi in L2(F_T) and phi in L2(Omega x [0,T]) (implicitly
measurable/adapted so the dt-integral is meaningful). Then dY in S^2 (E sup|dY|^2 < inf) and there
is C_BP depending only on T and c_BDG with
  E sup_{t<=T}|dY_t|^2 + E int_0^T (|dZ_s|_F^2 + ||dU_s||^2) ds <= C_BP (E|dxi|^2 + E int |phi|^2).

A faithful formal statement must contain:
- Quantifier order: for all T > 0 there exists C_BP (function of T only, c_BDG universal) such
  that for all m, d, nu (arbitrary sigma-finite, infinite activity included), all bases, all
  dY, dZ, dU, phi, dxi with the hypotheses, the conclusion holds. C_BP must not depend on m, d,
  nu, the basis, or the processes.
- Hypotheses: dY cadlag adapted (paths cadlag), dZ predictable in H^2_W, dU predictable in H^2_N,
  dxi F_T-measurable square integrable, phi square integrable (progressively measurable or at
  least jointly measurable), and identity (4.2) a.s. for every t (genuine Ito / compensated
  Poisson integrals).
- Conclusion: both the membership dY in S^2 and the displayed inequality (if stated in real
  numbers, the finiteness of E sup|dY|^2 must be part of the conclusion or the inequality must be
  in [0, inf] so that the real-valued junk 0 of a non-integrable sup cannot make it trivially
  true).
- Narrowing watch: assuming dY already in S^2, finite nu, extra hypotheses on phi beyond L2 and
  measurability, or a constant depending on m, d, nu.
Comparison (verdict recorded 2026-10-19T03:26:16Z):
Comparison: spec lem_bpbsde (Sec4.lean:35-94) against my locked reading.

Quantifier order: exists CBP : R -> R before the basis, dims, nu and the processes; the constant is
CBP(T) (c_BDG universal, absorbed). It cannot depend on m, d, nu, the basis or the processes.
Matches "C_BP depending only on T and c_BDG".

Hypotheses: standing basis, m, d > 0, T > 0, arbitrary sigma-finite nu. dZ coordinatewise
predictable for the standing filtration, vanishing off [0,T] (normalisation), finite energy:
H^2_W. dU marked predictable (P x calE), vanishing off [0,T], finite marked energy: H^2_N. dxi
F_T-measurable and in L2. phi jointly measurable with finite energy on [0,T]: the printed
"phi in L2(Omega x [0,T])" (no adaptedness is printed, none is assumed; the dt-integral process is
adapted through the identity, so the lemma is true as stated). dY adapted on [0,T], every path
right-continuous on [0,T) with left limits on (0,T] (cadlag adapted). The identity (4.2) for
every k and every t in [0,T], almost surely, with the library Ito integral at t and T (pointwise
in time, as "a.s. for every t" requires) and the cadlag compensated Poisson integral increments.
No S^2 membership of dY assumed.

Conclusion: E sup_{[0,T]} |dY|^2 < inf (dY in S^2), and in [0, inf],
E sup |dY|^2 + sum_{k,j} E int dZ_kj^2 + sum_k E int int dU_k^2 dnu ds
<= CBP(T) (E|dxi|^2 + sum_k E int phi_k^2) — exactly the printed estimate with Frobenius/L2(nu)
norms in coordinates. Stated in extended reals with the membership separately, so no junk value can
trivialise it.

Witness lem_bpbsde_hypotheses (Witness.lean): the backward equation of the Thm 3.5 solution of
Example 5.1(i) meets the hypotheses. Not vacuous.

Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless:
1. Processes in coordinates; |dZ|_F^2 and ||dU||^2_{L2(nu)} are sums of coordinate energies.
2. dZ, dU normalised to vanish off [0,T] (every element of H^2_W, H^2_N has such a
   representative, the norms and integrals only see [0,T]); dU is a marked predictable function
   on Omega x R x E (the P x calE representative of (2.4)).
3. Cadlag adapted dY: adapted on [0,T], every path right-continuous on [0,T) with left limits on
   (0,T].
4. phi only jointly measurable and square integrable, as printed (L2(Omega x [0,T])).
5. The estimate is in [0, inf] (lintegrals) with S^2 membership as a separate conjunct; C_BP is a
   function of T alone, c_BDG being a universal constant.
Disagreements with the author's review (shown 2026-10-19T03:35:38Z): none
