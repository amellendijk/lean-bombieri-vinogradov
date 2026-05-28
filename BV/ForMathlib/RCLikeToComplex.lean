module

public import Mathlib

variable {𝕜 : Type*} [RCLike 𝕜]

@[expose]
public section

open RCLike in
def Complex.ofRCLike : 𝕜 →+* ℂ where
  toFun x := RCLike.re x + Complex.I * RCLike.im x
  map_one' := by simp
  map_mul' := by
    intro x y
    simp
    ring_nf
    simp only [I_sq, mul_neg, mul_one]
    ring
  map_zero' := by simp
  map_add' := by simp; grind

end
