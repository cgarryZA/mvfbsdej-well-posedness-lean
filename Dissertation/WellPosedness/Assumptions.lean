/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Mathlib

/-!
# The paper's structural assumptions as predicates

Assumptions 2.2–2.5 of the paper are conditions on the coefficient functions, on a coupling
operator `G`, and on the pairing of coefficient differences with channel differences along a
diagonal pair. Written out they are, for `δΘ = (δX, δY, δZ, δU)` and the coefficient
differences `(δb, δσ, δh, δf)` at that pair,

* **2.2** `ξ₀ ∈ L²` and the origin values `b(·, 0, δ₀), σ(·, 0, δ₀), h(·, 0, ·, δ₀), f(·, 0, δ₀)`
  square-integrable in time over `[0, T]`;
* **2.3** `|δb| + |δσ| + |δh| + |δf| ≤ L(|δX| + |δY| + |δZ| + |δU| + W₂(µ, µ'))` and
  `|δg_T| ≤ L(|X_T − X'_T| + W₂(ρ, ρ'))`;
* **2.4** `|x|² ≤ c_G |G x|²` (forward branch) and `|y|² ≤ c_G |Gᵀ y|²` (backward branch);
* **2.5, terminal** `α 𝔼|G δX_T|² ≤ 𝔼⟨δg_T, G δX_T⟩`;
* **2.5, interior** `𝔼[⟨δb, GᵀδY⟩ + ⟨δσ, GᵀδZ⟩ + ⟨−δf, GδX⟩ + ∫⟨δh, GᵀδU⟩ dν]`
  `≤ −β₁ 𝔼[|GᵀδY|² + |GᵀδZ|² + |GᵀδU|²] − β₂ 𝔼|GδX|²`,

with `α, β₁, β₂ ≥ 0`, `α + β₁ > 0`, `β₁ + β₂ > 0`, and `β₁ > 0` when `m < n`, `α, β₂ > 0` when
`m > n`.

Expectations are absorbed into the inner products — `𝔼⟨·,·⟩` is `⟪·,·⟫` on `L²`, `𝔼|·|²` is
`‖·‖²`. The rectangular case `m ≠ n` is carried by giving each channel its own pair of spaces:
the forward operator `G : HX →L HY` pairs `δf` with `δX` and `δg_T` with `δX_T`, and its adjoint
pairs `δb` with `δY`; the `Z` and `U` channels get their own `GZ` and `GU`, which in the concrete
model are `G` acting on matrix- and `L²(ν)`-valued arguments. The square case `n = m` is the
instance in which all six spaces and all three operators coincide (`SquareCoupling`).

Assumption 2.3 is stated over an abstract law distance rather than `W₂` itself, so this file stays
Mathlib-only; its instance at `W₂` on `P₂(H)` is `Dissertation.Law.LipschitzCoefficientsP2`.

## Main definitions

* `ChannelDiff` — the eight differences at a diagonal pair.
* `interiorPairing`, `dissipation` — the two sides of the interior inequality of Assumption 2.5.
* `GCoerciveForward`, `GCoerciveBackward` — Assumption 2.4.
* `Constants` — the admissible constant pattern, including the two rank cases.
* `OriginIntegrable` — the origin-value clause of Assumption 2.2.
* `LipschitzCoefficients`, `LipschitzTerminal` — Assumption 2.3.
-/

namespace Dissertation.WellPosedness

open scoped InnerProductSpace
open MeasureTheory

variable {HX HY HZX HZY HUX HUY : Type*}
  [NormedAddCommGroup HX] [InnerProductSpace ℝ HX] [CompleteSpace HX]
  [NormedAddCommGroup HY] [InnerProductSpace ℝ HY] [CompleteSpace HY]
  [NormedAddCommGroup HZX] [InnerProductSpace ℝ HZX] [CompleteSpace HZX]
  [NormedAddCommGroup HZY] [InnerProductSpace ℝ HZY] [CompleteSpace HZY]
  [NormedAddCommGroup HUX] [InnerProductSpace ℝ HUX] [CompleteSpace HUX]
  [NormedAddCommGroup HUY] [InnerProductSpace ℝ HUY] [CompleteSpace HUY]

/-! ## Assumption 2.5 -/

/-- The channel differences of a diagonal pair — the tuple difference `δΘ = (δX, δY, δZ, δU)`
together with the coefficient differences `(δb, δσ, δh, δf)` evaluated along it. The forward
channels `δX, δb` and the backward channels `δY, δf` are paired by `G`; the `Z` and `U` channels
by `GZ` and `GU`. -/
structure ChannelDiff (HX HY HZX HZY HUX HUY : Type*)
    [NormedAddCommGroup HX] [InnerProductSpace ℝ HX]
    [NormedAddCommGroup HY] [InnerProductSpace ℝ HY]
    [NormedAddCommGroup HZX] [InnerProductSpace ℝ HZX]
    [NormedAddCommGroup HZY] [InnerProductSpace ℝ HZY]
    [NormedAddCommGroup HUX] [InnerProductSpace ℝ HUX]
    [NormedAddCommGroup HUY] [InnerProductSpace ℝ HUY] where
  /-- The forward-state difference. -/
  δX : HX
  /-- The backward-value difference. -/
  δY : HY
  /-- The Brownian-integrand difference. -/
  δZ : HZY
  /-- The jump-integrand difference. -/
  δU : HUY
  /-- The drift difference. -/
  δb : HX
  /-- The diffusion difference. -/
  δσ : HZX
  /-- The jump-coefficient difference. -/
  δh : HUX
  /-- The backward-driver difference. -/
  δf : HY

variable (G : HX →L[ℝ] HY) (GZ : HZX →L[ℝ] HZY) (GU : HUX →L[ℝ] HUY)

/-- The left-hand side of the interior inequality (2.7). -/
noncomputable def interiorPairing (c : ChannelDiff HX HY HZX HZY HUX HUY) : ℝ :=
  inner ℝ c.δb (ContinuousLinearMap.adjoint G c.δY)
    + inner ℝ c.δσ (ContinuousLinearMap.adjoint GZ c.δZ)
    + inner ℝ (-c.δf) (G c.δX)
    + inner ℝ c.δh (ContinuousLinearMap.adjoint GU c.δU)

/-- The right-hand side of the interior inequality (2.7): the dissipation the pairing must
not exceed. -/
noncomputable def dissipation (β₁ β₂ : ℝ) (c : ChannelDiff HX HY HZX HZY HUX HUY) : ℝ :=
  -β₁ * (‖ContinuousLinearMap.adjoint G c.δY‖ ^ 2
      + ‖ContinuousLinearMap.adjoint GZ c.δZ‖ ^ 2
      + ‖ContinuousLinearMap.adjoint GU c.δU‖ ^ 2)
    - β₂ * ‖G c.δX‖ ^ 2

/-! ## Assumption 2.4 -/

/-- **Assumption 2.4, forward branch**: `G` is coercive with constant `c_G` (`m ≥ n`). -/
def GCoerciveForward (cG : ℝ) : Prop := ∀ x : HX, ‖x‖ ^ 2 ≤ cG * ‖G x‖ ^ 2

/-- **Assumption 2.4, backward branch**: `Gᵀ` is coercive with constant `c_G` (`n ≥ m`). -/
def GCoerciveBackward (cG : ℝ) : Prop :=
  ∀ y : HY, ‖y‖ ^ 2 ≤ cG * ‖ContinuousLinearMap.adjoint G y‖ ^ 2

/-! ## The admissible constants of Assumption 2.5 -/

/-- **The admissible constant pattern of Assumption 2.5** at forward dimension `n` and backward
dimension `m`: nonnegative, not both of `α, β₁` zero, not both of `β₁, β₂` zero, with `β₁ > 0`
forced when `m < n` and `α, β₂ > 0` forced when `m > n`. -/
structure Constants (n m : ℕ) (α β₁ β₂ : ℝ) : Prop where
  /-- `α ≥ 0`. -/
  α_nonneg : 0 ≤ α
  /-- `β₁ ≥ 0`. -/
  β₁_nonneg : 0 ≤ β₁
  /-- `β₂ ≥ 0`. -/
  β₂_nonneg : 0 ≤ β₂
  /-- The terminal and backward coercivities do not both vanish. -/
  terminal_or_backward : 0 < α + β₁
  /-- The backward and forward coercivities do not both vanish. -/
  backward_or_forward : 0 < β₁ + β₂
  /-- With fewer backward than forward coordinates, `Gᵀ` is injective and `β₁` must be positive. -/
  rank_lt : m < n → 0 < β₁
  /-- With more backward than forward coordinates, `G` is injective and `α, β₂` must be
  positive. -/
  rank_gt : n < m → 0 < α ∧ 0 < β₂

namespace Constants

variable {n m : ℕ} {α β₁ β₂ : ℝ}

/-- In the square case the two rank clauses are vacuous, so the admissible patterns are exactly
the nonnegative constants with `α + β₁ > 0` and `β₁ + β₂ > 0`. -/
theorem square (hα : 0 ≤ α) (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂) (h1 : 0 < α + β₁)
    (h2 : 0 < β₁ + β₂) : Constants n n α β₁ β₂ where
  α_nonneg := hα
  β₁_nonneg := hβ₁
  β₂_nonneg := hβ₂
  terminal_or_backward := h1
  backward_or_forward := h2
  rank_lt h := absurd h (lt_irrefl n)
  rank_gt h := absurd h (lt_irrefl n)

/-- **The rank dichotomy.** Either `β₁ > 0`, or `β₁ = 0` and then both `α` and `β₂` are
positive. -/
theorem dichotomy (h : Constants n m α β₁ β₂) :
    0 < β₁ ∨ (β₁ = 0 ∧ 0 < α ∧ 0 < β₂) := by
  rcases h.β₁_nonneg.lt_or_eq with hb | hb
  · exact Or.inl hb
  · refine Or.inr ⟨hb.symm, ?_, ?_⟩
    · have := h.terminal_or_backward; linarith [hb.symm ▸ (le_refl β₁)]
    · have := h.backward_or_forward; linarith

end Constants

/-! ## Assumption 2.2 -/

/-- **Assumption 2.2, origin values**: the coefficients evaluated at the origin of the tuple and
the Dirac mass there are square-integrable in time over `[0, T]`. -/
structure OriginIntegrable (T : ℝ) (b : ℝ → HX) (σ : ℝ → HZX) (h : ℝ → HUX) (f : ℝ → HY) :
    Prop where
  /-- `b(·, 0, δ₀) ∈ L²(0, T)`. -/
  b_memLp : MemLp b 2 (volume.restrict (Set.Icc 0 T))
  /-- `σ(·, 0, δ₀) ∈ L²(0, T)`. -/
  σ_memLp : MemLp σ 2 (volume.restrict (Set.Icc 0 T))
  /-- `h(·, 0, ·, δ₀) ∈ L²(0, T; L²(ν))`. -/
  h_memLp : MemLp h 2 (volume.restrict (Set.Icc 0 T))
  /-- `f(·, 0, δ₀) ∈ L²(0, T)`. -/
  f_memLp : MemLp f 2 (volume.restrict (Set.Icc 0 T))

omit [InnerProductSpace ℝ HX] [CompleteSpace HX] [InnerProductSpace ℝ HY] [CompleteSpace HY]
  [InnerProductSpace ℝ HZX] [CompleteSpace HZX] [InnerProductSpace ℝ HUX] [CompleteSpace HUX] in
/-- Constant origin values — the affine base of Example 5.1(i), whose origin values are the
constants `σ_c` and `h_c` — are square-integrable over a finite horizon. -/
theorem originIntegrable_const (T : ℝ) (b₀ : HX) (σ₀ : HZX) (h₀ : HUX) (f₀ : HY) :
    OriginIntegrable T (fun _ => b₀) (fun _ => σ₀) (fun _ => h₀) (fun _ => f₀) where
  b_memLp := memLp_const _
  σ_memLp := memLp_const _
  h_memLp := memLp_const _
  f_memLp := memLp_const _

/-! ## Assumption 2.3 -/

/-- The tuple space `H = ℝⁿ × ℝᵐ × ℝ^{m×d} × L²(ν; ℝᵐ)` of the paper, as the product of the four
channel spaces. -/
abbrev Tuple (HX HY HZY HUY : Type*) [NormedAddCommGroup HX] [InnerProductSpace ℝ HX]
    [NormedAddCommGroup HY] [InnerProductSpace ℝ HY]
    [NormedAddCommGroup HZY] [InnerProductSpace ℝ HZY]
    [NormedAddCommGroup HUY] [InnerProductSpace ℝ HUY] : Type _ := HX × HY × HZY × HUY

/-- The sum of the four channel norms, the paper's `|δX| + |δY| + |δZ|_F + ‖δU‖_{L²(ν)}`. -/
noncomputable def tupleNorm (θ : Tuple HX HY HZY HUY) : ℝ :=
  ‖θ.1‖ + ‖θ.2.1‖ + ‖θ.2.2.1‖ + ‖θ.2.2.2‖

/-- **Assumption 2.3, interior**: the four coefficient functions are jointly Lipschitz in the
tuple and in the law, with one constant `L`. The law argument ranges over an abstract type `Λ`
with a distance `dΛ`; its instance at `W₂` on `P₂(H)` is
`Dissertation.Law.LipschitzCoefficientsP2`. -/
def LipschitzCoefficients (L : ℝ) {Λ : Type*} (dΛ : Λ → Λ → ℝ)
    (b : ℝ → Tuple HX HY HZY HUY → Λ → HX) (σ : ℝ → Tuple HX HY HZY HUY → Λ → HZX)
    (h : ℝ → Tuple HX HY HZY HUY → Λ → HUX) (f : ℝ → Tuple HX HY HZY HUY → Λ → HY) : Prop :=
  ∀ (t : ℝ) (θ θ' : Tuple HX HY HZY HUY) (lam lam' : Λ),
    ‖b t θ lam - b t θ' lam'‖ + ‖σ t θ lam - σ t θ' lam'‖ + ‖h t θ lam - h t θ' lam'‖
        + ‖f t θ lam - f t θ' lam'‖
      ≤ L * (tupleNorm (θ - θ') + dΛ lam lam')

/-- **Assumption 2.3, terminal** (2.6): the terminal map is Lipschitz in the state and in the
terminal law. -/
def LipschitzTerminal (L : ℝ) {Ρ : Type*} (dΡ : Ρ → Ρ → ℝ) (g : HX → Ρ → HY) : Prop :=
  ∀ (x x' : HX) (ρ ρ' : Ρ), ‖g x ρ - g x' ρ'‖ ≤ L * (‖x - x'‖ + dΡ ρ ρ')

end Dissertation.WellPosedness
