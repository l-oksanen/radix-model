import Mathlib

namespace RadixModel

/-- A rounding function is valid if it satisfies two properties. -/
class ValidRnd (rnd : ℝ → ℤ) : Prop where
  id (x : ℤ): rnd x = x
  monotone (x y : ℝ) (h : x ≤ y) : rnd x ≤ rnd y

lemma rnd_eq_floor_or_ceil (rnd : ℝ → ℤ) (x : ℝ) [h : ValidRnd rnd]
  : rnd x = ⌊x⌋ ∨ rnd x = ⌈x⌉
:= by
  cases h
  have := Int.floor_le x
  have := Int.le_ceil x
  have := Int.ceil_le_floor_add_one x
  grind


/-! ### Rounding strategies -/

/-- Round to floor. -/
noncomputable abbrev rndFloor (x : ℝ) : ℤ := ⌊x⌋

instance validRndFloor : ValidRnd rndFloor where
  id (x : ℤ) := by simp
  monotone (x y : ℝ) (h : x ≤ y) := Int.floor_le_floor h


/-- Round to ceil. -/
noncomputable abbrev rndCeil (x : ℝ) : ℤ := ⌈x⌉

instance validRndCeil : ValidRnd rndCeil where
  id (x : ℤ) := by simp
  monotone (x y : ℝ) (h : x ≤ y) := Int.ceil_le_ceil h


/-- Round to nearest, tie to even. -/
noncomputable def rndNearest (x : ℝ) :=
  let f := ⌊x⌋
  if x - f < 1/2 then f
  else if x - f > 1/2 then f + 1
  else if Even f then f else f + 1

instance validRndNearest : ValidRnd rndNearest where
  id (x : ℤ) := by simp [rndNearest]
  monotone (x y : ℝ) (h : x ≤ y) := by
    have (x : ℝ) := calc
      (⌊x⌋ : ℝ)
      _ = x - (x - ⌊x⌋) := by grind
      _ = x - Int.fract x := rfl
    have := Int.floor_le_floor h
    simp [rndNearest]
    split_ifs <;> grind


/-! ### Error bounds -/

/-- Nearest even rounding error is one half. -/
lemma nearest_dist_le_half (x : ℝ) : |rndNearest x - x| ≤ 2⁻¹
:= by
  have := Int.fract_lt_one x
  have := Int.fract_nonneg x
  simp [rndNearest]
  have : Int.fract x = x - ⌊x⌋ := rfl
  simp only [this] at *
  split_ifs <;> grind
