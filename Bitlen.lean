import Mathlib.Data.Nat.Size

/-!
# Bit length by binary search

Given `n` and `maxBits` with `n < 2 ^ maxBits`, `bitLen` finds the number of significant bits
of `n` by binary search on `maxBits`, halving it at each step.

`bitLen_eq_size` proves that this computes the bit length as defined by
[`Nat.size`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Bits.html#Nat.size),
mathlib's length of the binary representation: `n < 2 ^ maxBits ⇒ bitLen n maxBits = n.size`.
Note that the bound is a hypothesis of the theorem rather than of the definition, so `bitLen`
returns a junk value when it fails to hold.

The algorithm is described at <https://www.jonaslindstrom.dk/?p=997>.
-/

/-- The number of bits in `n`, assuming `n < 2 ^ maxBits`; see `bitLen_eq_size`. -/
def bitLen (n maxBits : ℕ) : ℕ :=
  let k := maxBits / 2
  if maxBits ≤ 1 then n
  else if n >>> k = 0 then bitLen n k
  else k + bitLen (n >>> k) (maxBits - k)
termination_by maxBits
decreasing_by all_goals omega

namespace Nat

/-- `n >>> k < 2 ^ j ⇔ n < 2 ^ (j + k)` -/
theorem shiftRight_lt_two_pow_iff (n k j : ℕ) : n >>> k < 2 ^ j ↔ n < 2 ^ (j + k) := by
  rw [shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), Nat.pow_add]

/-- `n >>> k = 0 ⇔ n < 2 ^ k` -/
theorem shiftRight_eq_zero_iff {n k : ℕ} : n >>> k = 0 ↔ n < 2 ^ k := by
  rw [← Nat.lt_one_iff, ← Nat.pow_zero 2, shiftRight_lt_two_pow_iff, Nat.zero_add]

/-- `(n >>> k).size = n.size - k` -/
theorem size_shiftRight (n k : ℕ) : (n >>> k).size = n.size - k := by
  have key (j : ℕ) : (n >>> k).size ≤ j ↔ n.size ≤ j + k := by
    rw [size_le, size_le, shiftRight_lt_two_pow_iff]
  have h₁ := (key (n.size - k)).mpr (by omega)
  have h₂ := (key (n >>> k).size).mp (Nat.le_refl _)
  omega

end Nat

/-- `n < 2 ^ maxBits ⇒ bitLen n maxBits = n.size` -/
theorem bitLen_eq_size (n maxBits : ℕ) (h : n < 2 ^ maxBits) : bitLen n maxBits = n.size := by
  induction n, maxBits using bitLen.induct with
  | case1 n maxBits hm =>
      rw [bitLen, if_pos hm]
      have h2 : n < 2 ^ 1 := Nat.size_le.mp (Nat.le_trans (Nat.size_le.mpr h) hm)
      rw [Nat.pow_one] at h2
      obtain rfl | rfl := Nat.le_one_iff_eq_zero_or_eq_one.mp (show n ≤ 1 by omega) <;> simp
  | case2 n maxBits k hm hz ih =>
      rw [bitLen, if_neg hm, if_pos hz]
      exact ih (Nat.shiftRight_eq_zero_iff.mp hz)
  | case3 n maxBits k hm hz ih =>
      have hlt : n >>> (maxBits / 2) < 2 ^ (maxBits - maxBits / 2) :=
        Nat.size_le.mp (by have := Nat.size_le.mpr h; rw [Nat.size_shiftRight]; omega)
      have hpos : 0 < (n >>> (maxBits / 2)).size := Nat.size_pos.mpr (Nat.pos_of_ne_zero hz)
      rw [Nat.size_shiftRight] at hpos
      rw [bitLen, if_neg hm, if_neg hz, ih hlt, Nat.size_shiftRight]
      omega
