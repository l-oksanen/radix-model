import Mathlib
import RadixModel.Radix

namespace RadixModel


/-! ### Radix representations -/

/-- A radix representation with value `coefficient * β ^ exponent`. -/
structure RadixRep (β : Radix) where
  coefficient : ℤ
  exponent : ℤ

namespace RadixRep

/-- The value of a radix representation -/
noncomputable def value {β : Radix} (x : RadixRep β) : ℝ :=
  x.coefficient * β ^ x.exponent

/-- The magnitude of `x` in radix `β` as characterized by
`magnitude_iff` and `magnitude_zero` -/
noncomputable def magnitude (β : Radix) (x : ℝ) : ℤ :=
  Int.log β |x| + 1

/--
The magnitude of nonzero `x` is the integer `k` satisfying
`β ^ (k - 1) ≤ |x| < β ^ k`.
-/
lemma magnitude_iff (β : Radix) (k : ℤ) {x : ℝ}
  (hx : x ≠ 0)
  : magnitude β x = k ↔ β ^ (k - 1) ≤ |x| ∧ |x| < β ^ k
:= by
  simp [magnitude]
  grind [Int.zpow_le_iff_le_log, Int.lt_zpow_iff_log_lt]

/--
The magnitude of zero is one.
-/
lemma magnitude_zero {β : Radix}
  : magnitude β 0 = 1
:= by
  simp [magnitude]


/--
Select the exponent for `x` by applying `esel` to the magnitude of `x`
in radix `β`.
-/
noncomputable def selectExp (β : Radix) (esel : ℤ → ℤ)
  (x : ℝ) : ℤ
:=
  esel (magnitude β x)

/--
The unrounded coefficient of `x` in radix `β`.

The exponent is selected using `esel`.
-/
noncomputable def rawCoeff (β : Radix) (esel : ℤ → ℤ)
  (x : ℝ) : ℝ
:=
  let e := selectExp β esel x
  x * β ^ (-e)

/--
Construct the rounded representation of `x` in radix `β`.

The exponent is selected using `esel`, and the coefficient is rounded
using `rnd`.
-/
noncomputable def mkRounded {β : Radix} (esel : ℤ → ℤ) (rnd : ℝ → ℤ)
  (x : ℝ) : RadixRep β
where
  coefficient := rnd (rawCoeff β esel x)
  exponent := selectExp β esel x

end RadixRep
open RadixRep


/--
Round `x` in radix `β`.

The exponent is selected using `esel`, and the coefficient is rounded
using `rnd`.
-/
noncomputable def round (β : Radix) (esel : ℤ → ℤ) (rnd : ℝ → ℤ)
  (x : ℝ) : ℝ
:=
  (mkRounded (β := β) esel rnd x).value


/-! ### Representable reals -/

/--
A real number `x` is representable in radix `β` for exponent selection
`esel` if floor rounding preserves it.
-/
def Representable (β : Radix) (esel : ℤ → ℤ) (x : ℝ) : Prop :=
  round β esel rndFloor x = x

/--
The subtype of reals representable in radix `β` for exponent selection
`esel`.
-/
abbrev RepresentableReal (β : Radix) (esel : ℤ → ℤ) :=
  {x : ℝ // Representable β esel x}

/--
A radix power `β ^ e` is representable if the exponent selected at
magnitude `e + 1` is at most `e`.
-/
lemma representable_radix_pow {β : Radix} {esel : ℤ → ℤ} {e : ℤ}
  (h : esel (e + 1) ≤ e)
  : Representable β esel ((β : ℝ) ^ e)
:= by
  have : selectExp β esel (β ^ e) = esel (e + 1) := by
    simp [selectExp]
    have := magnitude_iff β (e + 1) (by grind : (β : ℝ) ^ e ≠ 0)
    grind
  simp [Representable, round, mkRounded, value, rawCoeff]
  grind

/--
The value of a radix representation is representable if the exponent
selected for that value is no larger than the representation's
exponent,  or if the coefficient is zero.
-/
lemma RadixRep.value_representable {β : Radix} {esel : ℤ → ℤ}
  {x : RadixRep β}
  (h : selectExp β esel x.value ≤ x.exponent ∨ x.coefficient = 0)
  : Representable β esel x.value
:= by
  simp [Representable, round, mkRounded, value, rawCoeff]
  obtain h | h := h
  · simp [value] at h
    grind
  · simp [h]


/-! ### Rounding produces representable values -/

/--
A valid exponent selection satisfies a growth bound for large values
and stays constant for small values.
-/
class ValidEsel (esel : ℤ → ℤ) : Prop where
  large_bound (k : ℤ) (h : esel k < k) : esel (k + 1) ≤ k
  small_stable (k : ℤ) (h : k ≤ esel k) :
    esel (esel k + 1) ≤ esel k
    ∧ ∀ l : ℤ, l ≤ esel k → esel l = esel k


lemma round_pos_large {β : Radix} {esel : ℤ → ℤ} (rnd : ℝ → ℤ)
  [hexp : ValidEsel esel] [hrnd : ValidRnd rnd]
  {x : ℝ} {k : ℤ}
  (hxl : β ^ (k - 1) ≤ x) (hxu : x < β ^ k)
  (hk : esel k < k)
  : let y := round β esel rnd x
  β ^ (k - 1) ≤ y ∧ y ≤ β ^ k
:= by
  set e := selectExp β esel x with he
  have : e < k := by
    simp [he, selectExp]
    cases hexp
    have := magnitude_iff β k (by grind : x ≠ 0)
    grind

  set b := (β : ℝ) with hb
  set c := rawCoeff β esel x with hc

  have : b ^ (k - 1 - e) ≤ c := by
    simp only [hc, rawCoeff]
    calc
      b ^ (k - 1 - e)
      _ = b ^ (k - 1) * b ^ (-e) := by grind
      _ ≤ x * b ^ (-e) := by grind
  have := Int.floor_le_floor this
  have : ⌊b ^ (k - 1 - e)⌋ ≤ (⌊c⌋ : ℝ) := by exact_mod_cast this

  have : c ≤ b ^ (k - e) := by
    simp only [hc, rawCoeff]
    calc
      x * b ^ (-e)
      _ ≤ b ^ k * b ^ (-e) := by grind
      _ = b ^ (k - e) := by grind
  have := Int.ceil_le_ceil this
  have : ⌈c⌉ ≤ (⌈b ^ (k - e)⌉ : ℝ) := by exact_mod_cast this

  have := Int.floor_le_ceil c
  have : ⌊c⌋ ≤ (⌈c⌉ : ℝ) := by exact_mod_cast this

  have := rnd_eq_floor_or_ceil rnd c

  have := calc
    b ^ (k - 1)
    _ = b ^ (k - 1) * (b ^ e)⁻¹ * b ^ e := by grind
    _ = b ^ (k - 1 - e) * b ^ e := by grind
    _ ≤ (rnd c) * b ^ e := by grind

  have := calc
    (rnd c) * b ^ e
    _ ≤ b ^ (k - e) * b ^ e := by grind
    _ = b ^ k * (b ^ e)⁻¹ * b ^ e := by grind
    _ = b ^ k := by grind

  simp [round, mkRounded, value]
  grind

lemma round_pos_small {β : Radix} {esel : ℤ → ℤ} (rnd : ℝ → ℤ)
  [hexp : ValidEsel esel] [hrnd : ValidRnd rnd]
  {x : ℝ} {k : ℤ}
  (hl : β ^ (k - 1) ≤ x) (hu : x < β ^ k)
  (hk : k ≤ esel k)
  : let y := round β esel rnd x
  y = 0 ∨ y = β ^ (esel k)
:= by
  set e := selectExp β esel x with he
  have : e = esel k := by
    simp [he, selectExp]
    cases hexp
    have := magnitude_iff β k (by grind : x ≠ 0)
    grind

  set b := (β : ℝ) with hb
  have := calc
      x * (b ^ e)⁻¹
      _ = x * (b ^ (- esel k)) := by grind
      _ ≤ x * b ^ (-k) := by grind
      _ < b ^ k * b ^ (-k) := by grind
      _ = b ^ k * (b ^ k)⁻¹ := by grind
      _ = 1 := by grind

  set c := rawCoeff β esel x with hc
  have : ⌊c⌋ = 0 := by
    simp [hc, rawCoeff, Int.floor_eq_iff]
    grind
  have : ⌈c⌉ = 1 := by
    simp [hc, rawCoeff, Int.ceil_eq_iff]
    grind
  have := rnd_eq_floor_or_ceil rnd c

  simp [round, mkRounded, value]
  have : rnd c = 0 ∨ rnd c = 1 := by grind
  obtain _ | h := this
  · grind
  · right
    calc
      (rnd c) * b ^ e
      _ = 1 * b ^ e := by simp [h]
      _ = b ^ (esel k) := by grind

lemma representable_round_pos {β : Radix} {esel : ℤ → ℤ} (rnd : ℝ → ℤ)
  [hexp : ValidEsel esel] [hrnd : ValidRnd rnd]
  {x : ℝ}
  (hx : 0 < x)
  : Representable β esel (round β esel rnd x)
:= by
  set y := round β esel rnd x with hy
  set k := magnitude β x with hk
  have := magnitude_iff β k (by grind : x ≠ 0)
  by_cases esel k ≥ k
  · have : y = 0 ∨ y = β ^ (esel k) := by
      apply round_pos_small <;> grind
    obtain h | h := this
    · simp [h, Representable, round, mkRounded, value, rawCoeff]
    · simp [h]
      cases hexp
      apply representable_radix_pow
      grind
  · by_cases h : y = β ^ k
    · simp [h]
      cases hexp
      apply representable_radix_pow
      grind
    · have : magnitude β y = k := by
        have : β ^ (k - 1) ≤ y ∧ y ≤ β ^ k := by
          apply round_pos_large <;> grind
        have := magnitude_iff β k (by grind : y ≠ 0)
        grind
      cases hexp
      apply (mkRounded esel rnd x).value_representable
      simp [hy, round, mkRounded, value, selectExp] at this ⊢
      grind
