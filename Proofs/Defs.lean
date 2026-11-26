import Mathlib

namespace Solon

/-- A colouring `c` of finite sets of points is kept by the action of `G` when moving a set by any element of `G`
keeps its colour. -/
def Invariant (G : Type*) {X C : Type*} [Group G] [MulAction G X] [DecidableEq X] (c : Finset X → C) : Prop :=
  ∀ (g : G) (A : Finset X), c (A.image (g • ·)) = c A

/-- No `k` points have all their `t`-subsets in colour `i`. -/
def NoMono {X C : Type*} (c : Finset X → C) (t k : ℕ) (i : C) : Prop :=
  ∀ K : Finset X, K.card = k → ∃ A ∈ K.powersetCard t, c A ≠ i

end Solon

-- Used only in the statement of `stepping_up_four_to_five_additive_palette`.
def additiveFiveThreshold {C : Type*} [DecidableEq C]
    (a b : C) (s : C → ℕ) (i : C) : ℕ :=
  if i = a ∨ i = b then s i + 2 else s i + 1

-- Used only in the statement of `parity_stepping_up_from_five`.
def earlyParitySize (k n d : ℕ) : ℕ :=
  max (n + d) (2 * k + 1)

-- Used only in the statement of `stepping_up_one_fallback_all_palettes`.
def oneFallbackStepSize {C : Type*} [DecidableEq C]
    (a : C) (s : C → ℕ) (i : C) : ℕ :=
  if i = a then 2 ^ (s i - 1) + 1 else s i + 1
