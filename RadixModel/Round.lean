import Mathlib

namespace RadixModel

/-- A rounding function is valid if it satisfies two properties. -/
class ValidRounding (rnd : ℝ → ℤ) : Prop where
  id (x : ℤ): rnd x = x
  monotone {x y : ℝ} (h : x ≤ y) : rnd x ≤ rnd y

/-- A valid rounding function yields floor or ceil. -/
lemma rnd_eq_floor_or_ceil (rnd : ℝ → ℤ) (x : ℝ) [h : ValidRounding rnd]
  : rnd x = ⌊x⌋ ∨ rnd x = ⌈x⌉
:= by
  cases h
  have := Int.floor_le x
  have := Int.le_ceil x
  have := Int.ceil_le_floor_add_one x
  grind

@[simp]
lemma rnd_zero (rnd : ℝ → ℤ) [hrnd : ValidRounding rnd]
  : rnd 0 = 0
:= by
  obtain h | h := rnd_eq_floor_or_ceil rnd 0
  all_goals simp [h]


/-! ### Rounding strategies -/

/-- Round to floor. -/
noncomputable abbrev rndFloor (x : ℝ) : ℤ := ⌊x⌋

instance validRndFloor : ValidRounding rndFloor where
  id := by simp
  monotone := Int.floor_le_floor


/-- Round to ceil. -/
noncomputable abbrev rndCeil (x : ℝ) : ℤ := ⌈x⌉

instance validRndCeil : ValidRounding rndCeil where
  id := by simp
  monotone := Int.ceil_le_ceil


/-- Round by truncation toward zero. -/
noncomputable def rndTruncate (x : ℝ) : ℤ :=
  if x < 0 then ⌈x⌉ else ⌊x⌋

instance validRndTruncate : ValidRounding rndTruncate where
  id := by simp [rndTruncate]
  monotone := by
    intro x y h
    have (x : ℝ) (hx : (0 : ℤ) ≤ x) : 0 ≤ ⌊x⌋ := Int.le_floor.mpr hx
    have (x : ℝ) (hx : x ≤ (0 : ℤ)) : ⌈x⌉ ≤ 0 := Int.ceil_le.mpr hx
    have := Int.floor_le_floor h
    have := Int.ceil_le_ceil h
    simp [rndTruncate]
    grind


/-- Round to nearest, tie to even. -/
noncomputable def rndNearest (x : ℝ) :=
  let f := ⌊x⌋
  if x - f < 1/2 then f
  else if x - f > 1/2 then f + 1
  else if Even f then f else f + 1

instance validRndNearest : ValidRounding rndNearest where
  id := by simp [rndNearest]
  monotone {x y : ℝ} (h : x ≤ y) := by
    have (x : ℝ) : Int.fract x = x - ⌊x⌋ := rfl
    have := Int.floor_le_floor h
    simp [rndNearest]
    grind


/-! ### Symmetry of rounding by truncation -/

lemma odd_rndTruncate : Function.Odd rndTruncate
:= by
  simp [Function.Odd, rndTruncate]
  intro x
  split_ifs <;> try grind [Int.ceil_neg, Int.floor_neg]
  have : x = 0 := by grind
  simp [this]


/-! ### Error bounds -/

/-- Nearest even rounding error is one half. -/
lemma nearest_dist_le_half (x : ℝ) : |rndNearest x - x| ≤ 2⁻¹
:= by
  have : Int.fract x = x - ⌊x⌋ := rfl
  have := Int.fract_lt_one x
  have := Int.fract_nonneg x
  simp [rndNearest]
  grind
