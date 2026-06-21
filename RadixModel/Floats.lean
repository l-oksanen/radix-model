import Mathlib
import RadixModel.Core

namespace RadixModel

/-- Exponent function matching to the finite fragment of IEEE-754. -/
def eselFlt (emin prec e : ℤ) := max (e - prec) emin

instance validEselFlt (emin prec : ℤ)
  (h : 0 < prec)
  : ValidEsel (eselFlt emin prec)
where
  large_bound := by
    intros
    simp [eselFlt] at *
    grind
  small_stable := by
    intros
    simp [eselFlt] at *
    grind
