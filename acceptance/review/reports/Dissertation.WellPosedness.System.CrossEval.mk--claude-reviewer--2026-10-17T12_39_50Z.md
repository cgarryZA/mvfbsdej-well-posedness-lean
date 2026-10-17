### A:eq:coefmeas, A:sec2:coefmeas: Dissertation.WellPosedness.System.CrossEval.mk
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 73ff8f763f31638d0000000000000000 (pl-fp-v1:a9e38a11a2ebb4e99a381bf0a736a29d629d986554a47da74887044bbfdbbc02)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T12:39:50Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:35:39Z):
Reading: CrossEval.mk is the constructor of the measurability record of (2.5) for coefficient
evaluations along a tuple (progressive measurability of the b, sigma, f evaluations, predictable
/ P (x) E-measurable representative of the h evaluation). It must take exactly the fields of the
structure and nothing else; faithful iff the structure is.
Comparison (verdict recorded 2026-10-17T12:38:31Z):
CrossEval.mk takes exactly the nine fields of CrossEval (jump_rep, b_meas, b_prog, sigma_meas, sigma_prog, h_meas, h_prog, f_meas, f_prog) and returns CrossEval F P T C X Y Z U gamma; no further hypothesis. Its meaning is the structure's: faithful with representation choices, with the same caveat (the jump channel is a marked progressive representative at the non-left-limit tuple; predictability of the jump evaluation of (2.5) is the separate proposition eq_coefmeas_jump).
Witness: —
Verdict: faithful with representation choices — (1) Coordinate processes cut to [0,T] (driftProc etc.), evaluated with the exact law lawP2 at each
time instead of the Borel representative of Lemma A.1 (equal at a.e. s). (2) The jump channel is
recorded as a given representative gamma, jointly measurable and marked progressively measurable,
of h(s, Theta_s, ., mu_s), at the non-left-limit tuple: for cadlag X, Y this agrees with
h(s, Theta_s^-, ., mu_s^-) dt x dP-a.e., and progressive integrands suffice for the L^2 Poisson
integral. CAVEAT: CrossEval does not by itself express (2.5)'s "predictable" for the jump
evaluation at the predictable tuple; that clause is the separate proposition
PaperSpec.A.eq_coefmeas_jump. A proposition that used CrossEval alone in place of (2.5)'s h-clause
would be weaker than the printed claim; the current split (eq_coefmeas + eq_coefmeas_jump) covers
both lines.
Disagreements with the author's review (shown 2026-10-17T12:39:35Z): none (same caveat as recorded for CrossEval: the jump channel is a progressive representative at the non-left-limit tuple).
