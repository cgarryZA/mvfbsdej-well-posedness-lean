### A:cor:robust, A:eq:coefmeas, A:eq:forced, A:eq:mvfbsdej, A:ex:brownian, A:ex:concrete, A:intro:mvfbsdej, A:lem:bpbsde, A:lem:cont, A:lem:lawflow, A:lem:pert, A:lem:small, A:rem:cwp-class, A:rem:generalrank, A:sec2:coefmeas, A:sec2:prp, A:sec3:HH-banach, A:sec3:one-null-set, A:sec4:WP-def, A:sec4:horizon-not-contractive, A:sec:examples, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: LevyStochCalc.Brownian.Ito.energy
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash d863e7f664002259c7c4c422b7f327c7 (pl-fp-v1:b4385e42d1ab284bc2c5d392aaa46f608382ce6121f4958d55dc1d98bbeee468)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:02:25Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:34:24Z):
Reading for def:LevyStochCalc.Brownian.Ito.energy (written before seeing any Lean).

Paper notion. The norm of the Ito isometry / H^2_W: E int_0^T |Z_t|^2 dt (for Z in R^{m x d},
|Z_t|_F^2); for real integrands E int_0^T Z_t^2 dt. It is used for H^2_W membership
(E int_0^T |Z|^2 dt < infinity), the HH norm, and the isometry E|int_0^T Z dW|^2 = E int_0^T |Z|^2 dt.

A faithful Lean definition must:
- be the double integral over Omega (w.r.t. P) and over the time interval [0,T] (Lebesgue) of
  |Z_t(omega)|^2 (squared, not |Z|), possibly as a lintegral in R>=0-infinity (then "< infinity"
  is the integrability condition) or as a Bochner integral in R (then junk 0 for non-integrable Z
  must be guarded by an integrability hypothesis);
- integrate over [0,T] (the horizon) or [0,t] as parametrised — not over all of R_+ unless the
  integrand is cut off at T;
- be with respect to the product measure dt x dP (equivalently iterated, by Tonelli).
Comparison (verdict recorded 2026-10-17T15:01:15Z):
Comparison for Ito.energy.
Lean: energy P T H = ∫⁻ ω, ∫⁻ s in Icc 0 T, ‖H ω s‖₊² ∂volume ∂P (ℝ≥0∞).
- E ∫_0^T |H_s|² ds, as an iterated lower integral of the squared norm over [0,T] (Lebesgue) and Ω
  (P). This is the norm of the isometry / H²_W. By Tonelli it equals the dt⊗dP integral for
  measurable H. It is squared, not |H|, and over [0,T], not ℝ_+. Matches.
- In ℝ≥0∞, so "< ⊤" is the integrability condition and there is no junk.
- Real-valued integrands. The paper's |Z|_F² for matrix Z is the sum of these over entries,
  assembled elsewhere.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices. (1) The value is an iterated ℝ≥0∞-valued lower integral, first over
[0,T] in time and then over Ω. For measurable integrands this equals the dt⊗dP integral by
Tonelli, and it needs no integrability side condition. (2) Integrands are real-valued
(H : Ω → ℝ → ℝ), so the paper's E∫_0^T|Z_t|_F² dt for Z ∈ ℝ^{m×d} is the sum of the energies of
the entries.
Disagreements with the author's review (shown 2026-10-17T15:01:52Z): No disagreement on the substance. The author's entry (acceptance/review/definitions.md) records only the review marker, or a section heading, and no comparison with the paper. It does not state the points I relied on: the value is the iterated ℝ≥0∞ lower integral E∫_0^T|H|², equal to the dt⊗dP integral for measurable H, for real-valued integrands.
