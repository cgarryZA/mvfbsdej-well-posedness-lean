### A:cor:robust, A:eq:forced, A:eq:mvfbsdej, A:ex:concrete, A:intro:mvfbsdej, A:lem:cont, A:lem:lawflow, A:lem:pert, A:lem:small, A:rem:cwp-class, A:rem:generalrank, A:sec3:one-null-set, A:sec4:WP-def, A:sec:examples, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: Dissertation.WellPosedness.System.leftLimProc
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 9171262935c3b1fde4f555261cd0b9ba (pl-fp-v1:1ced7da3bb4fe58d54863ca0fec5bfa9cab6026e5d201d8f57d2308534ad8454)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:06:18Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:33:35Z):
Reading for leftLimProc (paper: X_{t-} in Theta^-_t = (X_{t-}, Y_{t-}, Z_t, U_t)).
X_{t-} := lim_{s -> t, s < t} X_s, the left limit of the cadlag path, for t in (0,T]; at t = 0 the
convention X_{0-} = X_0 (the process starts at 0). Faithful Lean: for each omega, the left limit of
s |-> X_s(omega) at t (e.g. Function.leftLim / limUnder (nhdsWithin t (Iio t))), componentwise. Edge
cases: (i) at t = 0 a Lean left limit over R reads values at negative times (junk w.r.t. the paper)
-- harmless because the jump integrand at the single time 0 is irrelevant (Lebesgue/dt nu-null, N has
no atom at a fixed time a.s.); (ii) for non-cadlag paths the limit may not exist (junk), harmless on
cadlag paths; (iii) the resulting process must be predictable when X is cadlag adapted.
Comparison (verdict recorded 2026-10-17T15:05:07Z):
Comparison for leftLimProc (System/LawFlow.lean:79): leftLimProc X i s omega := Function.leftLim (fun r =>
X i r omega) s. Mathlib's leftLim f a is limUnder (nhds within (-inf, a)) f when a left limit exists (and a
is not left-isolated), and f a otherwise.
Against my reading (X_{t-} = lim_{s up t} X_s for t in (0,T], X_{0-} := X_0, componentwise, predictable for
cadlag adapted X):
- For t in (0,T] and a path with a left limit at t: exactly the left limit. Matches.
- Paths without a left limit (a null set of omega under the a.s.-left-limit hypotheses): the value
  X_t (Mathlib's convention). Junk on a null set, irrelevant.
- t = 0: X is a process on R; leftLim at 0 reads X on negative times, which nothing constrains (or X_0
  if no left limit). The paper's X_{0-} convention is X_0. This differs only at the single time 0,
  which is Lebesgue-null and is never charged by dt nu, so every use (jump_rep for a.e. s, the
  Poisson integrand, the law flow mu^- for a.e. s) is unaffected.
- Measurability: the file proves joint measurability of the left-limit process for jointly
  measurable X with left limits everywhere (measurable_uncurry_leftLimProc); predictability is
  handled where it is used.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices (harmless):
1. At time 0 the left limit is taken over R (reads X at negative times, or X_0 if no limit exists)
   instead of the convention X_{0-} = X_0: a single, Lebesgue-null time, never seen by dt-a.e. or
   dt nu-integrated statements.
2. Where a path has no left limit (a null set of omega for the a.s.-cadlag processes it is applied to)
   the value is X_t, Mathlib's junk convention: irrelevant up to null sets.
3. Defined for any family of real processes, componentwise.
Disagreements with the author's review (shown 2026-10-17T15:05:48Z): none (the author's excerpt shown for this unit is a marker and at most a section heading, with no
item-level reading to compare against; my comparison file records the representation choices in
detail).
