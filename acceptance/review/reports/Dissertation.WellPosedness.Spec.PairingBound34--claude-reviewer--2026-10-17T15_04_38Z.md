### A:cor:robust: Dissertation.WellPosedness.Spec.PairingBound34
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 2b1db421079e9e767580b40b6b9fa24b (pl-fp-v1:66623bf41cb2c0125f636d80e162be349b2dc3e2fe4fbc5d09a996eb170c242f)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:04:38Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:37:23Z):
Unit: def Spec.PairingBound34 (the perturbation pairing bound (3.4), Corollary 3.6).
Paper: for some c_pert >= 0, for a.e. t in [0,T] and all (Theta,mu), (Theta',mu') in D_t,
  E[ <dp_b, G^T dY> + <dp_sigma, G^T dZ>_F + <-dp_f, G dX> + int_E <dp_h(e), G^T dU(e)> nu(de) ]
    <= c_pert E[ |dX|^2 + |dY|^2 + |dZ|_F^2 + ||dU||^2_{L^2(nu)} ],
with dp_psi = p_psi(t,Theta,mu) - p_psi(t,Theta',mu') (p = (p_b, p_sigma, p_h, p_f) a perturbation
system, same signatures as b, sigma, h, f), m = n so G is square.
Faithful Lean: a predicate over (F, P, T, G, c_pert, p) with exactly this inequality, for a.e. t
(chosen before the inputs) and all pairs of F_t-measurable square-integrable inputs with their own
laws; genuine expectations (Bochner junk-0 caveat if integrability fails); the bound unweighted
(plain norms), the pairing G-weighted as printed, minus sign on f. c_pert >= 0 may be a separate
hypothesis.
Comparison (verdict recorded 2026-10-17T15:04:13Z):
PairingBound34 F P T G c p (Spec/CorollaryHyps.lean:75): for a.e. t in [0,T], for all pairs of
diagonal inputs at t, the pairing pairing27 G p t ... of the perturbation differences is integrable
and E pairing27 <= c E(|dX|^2 + |dY|^2 + |dZ|_F^2 + ||dU||^2).
Matches (3.4): the G-weighted pairing <dp_b, G^T dY> + <dp_sigma, G^T dZ>_F + <-dp_f, G dX>
+ int <dp_h, G^T dU> dnu (pairing27 with the perturbation as coefficient system), the unweighted
right side, a.e. t before inputs, diagonal inputs with their laws. c_pert >= 0 is not in the
predicate (a hypothesis of the corollary), and m = n is the statement's.
Representation choice: existence of the expectation of the pairing required (automatic when p
satisfies the diagonal Lipschitz condition and (2.3), which Cor 3.6 assumes); strongly measurable
representatives.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — The expectation of the pairing is required to exist (Integrable); under the corollary's hypotheses
on p (diagonal Lipschitz, measurability) it is automatic, and it is the natural reading of E[...].
Inputs are strongly measurable representatives (harmless). c_pert >= 0 and m = n are left to the
statement.
Disagreements with the author's review (shown 2026-10-17T15:04:22Z): No disagreement on substance. The author's review is an empty marker with no recorded
comparison; the representation choices listed in my detail are not recorded there.
