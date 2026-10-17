### A:ass:integ, A:cor:robust, A:ex:brownian, A:ex:concrete, A:lem:cont, A:lem:small, A:rem:cwp-class, A:rem:generalrank, A:sec4:horizon-not-contractive, A:sec:examples, A:thm3.1:companion, A:thm:cwp, A:thm:stab: Dissertation.WellPosedness.Spec.OriginValues.mk
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 4f791247b92d220e0000000000000000 (pl-fp-v1:9a8212fff7a9c2af048de8a71085a15d6970406e705c0b81535e530ac9f9585b)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:04:37Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:37:23Z):
Unit: OriginValues.mk, the constructor of OriginValues. Its type must take exactly the four
memberships b(.,0,delta_0) in L^2(0,T;R^n), sigma(.,0,delta_0) in L^2(0,T;R^{n x d}),
h(.,0,.,delta_0) in L^2(0,T;L^2(nu;R^n)), f(.,0,delta_0) in L^2(0,T;R^m) (with 0 the origin of H and
delta_0 the Dirac mass there, L^2 on [0,T] with Lebesgue measure) and return OriginValues T C.
Comparison (verdict recorded 2026-10-17T15:04:13Z):
OriginValues.mk takes the four MemLp facts (b, sigma, h, f at theta = 0 and P2.dirac 0 = the Dirac
mass at the origin of H, square integrable on Ioo 0 T for Lebesgue measure) and returns
OriginValues T C. Exactly my reading, with the Ioo-for-[0,T] choice (null difference).
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — L^2(0,T) is taken over Ioo 0 T rather than [0,T]: the two differ by a Lebesgue-null set, so the
memberships are the same. h's origin value is in the Bochner space of L^2(nu;R^n)-valued maps, the
paper's L^2(0,T; L^2(nu;R^n)).
Disagreements with the author's review (shown 2026-10-17T15:04:22Z): No disagreement on substance. The author's review is an empty marker with no recorded
comparison; the representation choices listed in my detail are not recorded there.
