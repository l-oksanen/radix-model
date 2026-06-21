import Mathlib
import RadixModel.Round

namespace RadixModel

/-- A radix is a natural number greater than one. -/
abbrev Radix := {b : ℕ // b > 1}

namespace Radix


/-! ### Basic properties -/

lemma ge_two (β : Radix) : (β : ℝ) ≥ 2
:= by
  have : (β : ℕ) ≥ 2 := by grind
  exact_mod_cast this

grind_pattern ge_two => (β : ℝ)


@[grind =]
lemma pow_inv (β : Radix) (n : ℤ)
  : ((β : ℝ) ^ n)⁻¹ = (β : ℝ) ^ (-n)
:= by
  group

@[grind =]
lemma pow_add (β : Radix) (n m : ℤ)
  : (β : ℝ) ^ (n + m) = (β : ℝ) ^ n * (β : ℝ) ^ m
:= by
  grind [zpow_add₀]


/-! ### Inequalities -/

lemma pow_pos (β : Radix) (n : ℤ) : 0 < (β : ℝ) ^ n
:= by
  grind [zpow_pos]

grind_pattern pow_pos => (β : ℝ) ^ n


@[grind ←]
lemma mul_pow_pos (β : Radix) (n : ℤ) {x : ℝ}
  (hx : 0 < x)
  : 0 < x * (β : ℝ) ^ n
:= by
  have : 0 < (β : ℝ) ^ n := by grind
  nlinarith

@[grind ←]
lemma mul_pow_nonneg (β : Radix) (n : ℤ) {x : ℝ}
  (hx : 0 ≤ x)
  : 0 ≤ x * (β : ℝ) ^ n
:= by
  have : 0 < (β : ℝ) ^ n := by grind
  nlinarith

@[grind ←]
lemma pow_monotone (β : Radix) {n m : ℤ}
  (hnm : n ≤ m)
  : (β : ℝ) ^ n ≤ (β : ℝ) ^ m
:= by
  grind [zpow_le_zpow_iff_right₀]

@[grind ←]
lemma mul_pow_monotone (β : Radix) {n m : ℤ} {x : ℝ}
  (hnm : n ≤ m) (hx : 0 ≤ x)
  : x * (β : ℝ) ^ n ≤ x * (β : ℝ) ^ m
:= by
  have : (β : ℝ) ^ n ≤ (β : ℝ) ^ m := by grind
  nlinarith

@[grind ←]
lemma pow_strictMono (β : Radix) {n m : ℤ}
  (hnm : n < m)
  : (β : ℝ) ^ n < (β : ℝ) ^ m
:= by
  grind [zpow_lt_zpow_iff_right₀]

@[grind ←]
lemma mul_pow_strictMono (β : Radix) {n m : ℤ} {x : ℝ}
  (hnm : n < m) (hx : 0 < x)
  : x * (β : ℝ) ^ n < x * (β : ℝ) ^ m
:= by
  have : (β : ℝ) ^ n < (β : ℝ) ^ m := by grind
  nlinarith

@[grind ←]
lemma mul_pow_le (β : Radix) (n : ℤ) {x y : ℝ}
  (hxy : x ≤ y)
  : x * (β : ℝ) ^ n ≤ y * (β : ℝ) ^ n
:= by
  have : 0 < (β : ℝ) ^ n := by grind
  nlinarith

@[grind ←]
lemma mul_pow_lt (β : Radix) (n : ℤ) {x y : ℝ}
  (hxy : x < y)
  : x * (β : ℝ) ^ n < y * (β : ℝ) ^ n
:= by
  have : 0 < (β : ℝ) ^ n := by grind
  nlinarith


/-! ### Rounding -/

lemma rnd_mul_pow (β : Radix) (rnd : ℝ → ℤ)
  [hrnd : ValidRounding rnd]
  (c : ℤ) {n : ℤ}
  (hn : 0 ≤ n)
  : rnd (c * (β : ℝ) ^ n) = c * (β : ℝ) ^ n
:= by
  set m := n.toNat with hm
  have : (β : ℝ) ^ n = β ^ m := by
    have : m = n := Int.toNat_of_nonneg (by grind)
    simp [←this]
  simp [this]
  obtain ⟨h, _⟩ := hrnd
  exact_mod_cast h (c * β ^ m)

@[grind =]
lemma floor_mul_pow (β : Radix) {n : ℤ} (c : ℤ)
  (hn : 0 ≤ n)
  : ⌊c * (β : ℝ) ^ n⌋ = c * (β : ℝ) ^ n
:= by
  exact rnd_mul_pow β rndFloor c hn

@[grind =]
lemma floor_pow (β : Radix) {n : ℤ}
  (hn : 0 ≤ n)
  : ⌊(β : ℝ) ^ n⌋ = (β : ℝ) ^ n
:= by
  simpa using floor_mul_pow β 1 hn

@[grind =]
lemma ceil_mul_pow (β : Radix) {n : ℤ} (c : ℤ)
  (hn : 0 ≤ n)
  : ⌈c * (β : ℝ) ^ n⌉ = c * (β : ℝ) ^ n
:= by
  exact rnd_mul_pow β rndCeil c hn

@[grind =]
lemma ceil_pow (β : Radix) {n : ℤ}
  (hn : 0 ≤ n)
  : ⌈(β : ℝ) ^ n⌉ = (β : ℝ) ^ n
:= by
  simpa using ceil_mul_pow β 1 hn


lemma rnd_mul_pow_conj_small (β : Radix) (rnd : ℝ → ℤ)
  [hrnd : ValidRounding rnd]
  (c : ℤ) {n e : ℤ}
  (hn : e ≤ n)
  : rnd (c * (β : ℝ) ^ n * ((β : ℝ) ^ e)⁻¹) * (β : ℝ) ^ e
    = c * (β : ℝ) ^ n
:= by
  set b := (β : ℝ) with hb
  calc
    rnd (c * b ^ n * (b ^ e)⁻¹) * b ^ e
    _ = rnd (c * b ^ (n - e)) * b ^ e := by grind
    _ = c * b ^ (n - e) * b ^ e := by
      simp [hb, rnd_mul_pow β rnd c (by grind : 0 ≤ n - e)]
    _ = c * b ^ n * (b ^ e)⁻¹ * b ^ e := by grind
    _ = c * b ^ n := by grind

@[grind =]
lemma floor_mul_pow_conj_small (β : Radix) (c : ℤ) {n e : ℤ}
  (hn : e ≤ n)
  : ⌊c * (β : ℝ) ^ n * ((β : ℝ) ^ e)⁻¹⌋ * (β : ℝ) ^ e
    = c * (β : ℝ) ^ n
:= by
  exact rnd_mul_pow_conj_small β rndFloor c hn

@[grind =]
lemma floor_pow_conj_small (β : Radix) {n e : ℤ}
  (hn : e ≤ n)
  : ⌊(β : ℝ) ^ n * ((β : ℝ) ^ e)⁻¹⌋ * (β : ℝ) ^ e = (β : ℝ) ^ n
:= by
  simpa using floor_mul_pow_conj_small β 1 hn

@[grind =]
lemma ceil_mul_pow_conj_small (β : Radix) {n e : ℤ}
  (c : ℤ)
  (hn : e ≤ n)
  : ⌈c * (β : ℝ) ^ n * ((β : ℝ) ^ e)⁻¹⌉ * (β : ℝ) ^ e
    = c * (β : ℝ) ^ n
:= by
  exact rnd_mul_pow_conj_small β rndCeil c hn

@[grind =]
lemma ceil_pow_conj_small (β : Radix) {n e : ℤ}
  (hn : e ≤ n)
  : ⌈(β : ℝ) ^ n * ((β : ℝ) ^ e)⁻¹⌉ * (β : ℝ) ^ e
    = (β : ℝ) ^ n
:= by
  simpa using ceil_mul_pow_conj_small β 1 hn
