### A:rem:uniq-no-integ: Dissertation.WellPosedness.System.singularDrift
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 52bed42bcf81ba997be36c4ad7c8d90e (pl-fp-v1:dbfae93e0a36a23f8e461a320ff2f33adf6b5b22dc32cb961c91fb149a7e2987)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:50:57Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T15:41:48Z):
Reading for def:Dissertation.WellPosedness.System.singularDrift (Remark 3.4).

Paper notion: Remark 3.4 says uniqueness (Thm 3.3) needs only Assumptions 2.4-2.6 (Lipschitz,
G, monotonicity), not origin integrability (Assumption 2.3), while existence requires 2.3. The paper
gives no explicit example; the formalisation presumably uses a "singular drift", a deterministic
drift whose origin value b(., 0, delta_0) is NOT in L^2(0,T;R^n) (e.g. an additive time-singular term
like t^{-1/2} or 1/t, or a term not square-integrable near 0), to witness that Thm 3.3's hypotheses
can hold while Assumption 2.3 fails (and possibly that existence fails).

Faithful Lean: a drift b(t, theta, mu) that is (i) deterministic and Borel, (ii) satisfies the
diagonal Lipschitz bound and the monotonicity (differences only; an additive theta-independent
singular term cancels in delta b), and (iii) has |b(., 0, delta_0)| not square integrable on
[0,T]. If it is used to show existence FAILS, it must make every candidate solution impossible
(e.g. a term not integrable near 0 so int_0^t b ds diverges, or a term in L^1 but not L^2 whose
effect makes X not in S^2 -- note: an L^1 \ L^2 deterministic drift alone still gives a cadlag
X with E sup |X|^2 < infinity, so it would not obstruct existence). Junk values: Lean's 1/t at t=0 is
0 and the Bochner/Lebesgue integral of a non-integrable function is 0, which could make a
"singular" drift behave as an integrable one in the Lean equation -- must be checked.
Comparison (verdict recorded 2026-10-17T15:50:04Z):
Comparison for def:Dissertation.WellPosedness.System.singularDrift (Examples/SingularDrift.lean:82-84):
singularDrift t = toLp (fun _ => (Real.sqrt t)^{-1}) in R^1, i.e. t^{-1/2} for t > 0 and 0 for t <= 0
(Real.sqrt t = 0 for t <= 0, 0^{-1} = 0).

The paper's Remark 3.4 gives no explicit example; this is the witness drift used in
rem_uniq_singular: singularCoeffs = (affineCoeffs 1 0 0 0).addDrift singularDrift, b = t^{-1/2} - y.
Against my reading: deterministic, Borel (measurable), theta- and mu-independent so it cancels in
every difference (DiagonalLipschitz.addDrift, DiagonalMonotone.addDrift), and its origin value
t^{-1/2} is not in L^2(0,T) (int_0^T 1/t dt = infinity), so Assumption 2.2 fails, as intended. The
junk value at t = 0 (and t < 0) is on a Lebesgue-null subset of [0,T] / off the horizon, so it
changes neither the L^2 failure nor any integral. It is in L^1(0,T), so the drift integral exists
pathwise and the rem_uniq_singular claim exhibits a solution (my reading noted that an L^1 \ L^2 drift
does not obstruct existence: consistent with how it is used -- to show a solution exists without
2.2, not that existence fails). Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-17T15:50:12Z): none
