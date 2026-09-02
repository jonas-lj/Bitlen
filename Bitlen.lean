import Mathlib.Data.Nat.Size

/-!
# Bit length by binary search

`bitLen` computes `Nat.size`.
-/

namespace Nat

/-- `n >>> k < 2 ^ j ↔ n < 2 ^ (j + k)` -/
theorem shiftRight_lt_two_pow_iff (n k j : Nat) : n >>> k < 2 ^ j ↔ n < 2 ^ (j + k) := by
  rw [shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), Nat.pow_add]

/-- `n >>> k = 0 ↔ n < 2 ^ k` -/
theorem shiftRight_eq_zero_iff {n k : Nat} : n >>> k = 0 ↔ n < 2 ^ k := by
  rw [← Nat.lt_one_iff, ← Nat.pow_zero 2, shiftRight_lt_two_pow_iff, Nat.zero_add]

/-- `(n >>> k).size = n.size - k` -/
theorem size_shiftRight (n k : Nat) : (n >>> k).size = n.size - k := by
  have key (j : Nat) : (n >>> k).size ≤ j ↔ n.size ≤ j + k := by
    rw [size_le, size_le, shiftRight_lt_two_pow_iff]
  have h₁ := (key (n.size - k)).mpr (by omega)
  have h₂ := (key (n >>> k).size).mp (Nat.le_refl _)
  omega

end Nat

/-- `n < 2 ^ maxBits ⇒ 2 ≤ n ⇒ 2 ≤ maxBits` -/
private theorem two_le_maxBits {n maxBits : Nat} (h : n < 2 ^ maxBits) (hn : 2 ≤ n) :
    2 ≤ maxBits :=
  Nat.lt_of_lt_of_le (Nat.lt_size.mpr (by rw [Nat.pow_one]; omega)) (Nat.size_le.mpr h)

/-- `n < 2 ^ maxBits ⇒ n >>> m < 2 ^ (maxBits - m)` -/
private theorem shift_lt {n maxBits : Nat} (h : n < 2 ^ maxBits) (m : Nat) :
    n >>> m < 2 ^ (maxBits - m) :=
  Nat.size_le.mp <| by
    have := Nat.size_le.mpr h
    rw [Nat.size_shiftRight]; omega

/-- The number of bits in `n`, computed by binary search over `h : n < 2 ^ maxBits`. -/
def bitLen (n maxBits : Nat) (h : n < 2 ^ maxBits) : Nat :=
  match n, h with
  | 0, _ => 0
  | 1, _ => 1
  | n + 2, h =>
      if hp : (n + 2) >>> (maxBits / 2) > 0 then
        maxBits / 2 + bitLen ((n + 2) >>> (maxBits / 2)) (maxBits - maxBits / 2)
          (shift_lt h (maxBits / 2))
      else
        bitLen (n + 2) (maxBits / 2) (Nat.shiftRight_eq_zero_iff.mp (Nat.eq_zero_of_not_pos hp))
termination_by maxBits
decreasing_by all_goals (have := two_le_maxBits h (by omega); omega)

/-- `bitLen n maxBits h = n.size` -/
theorem bitLen_eq_size (n maxBits : Nat) (h : n < 2 ^ maxBits) : bitLen n maxBits h = n.size := by
  induction n, maxBits, h using bitLen.induct with
  | case1 => simp [bitLen]
  | case2 => simp [bitLen]
  | case3 maxBits n h hp _ ih =>
      have hpos := Nat.size_pos.mpr hp
      rw [Nat.size_shiftRight] at hpos
      rw [bitLen, dif_pos hp, ih, Nat.size_shiftRight]
      have : Nat.size (Nat.succ (Nat.succ n)) = (n + 2).size := rfl
      omega
  | case4 maxBits n h hp _ ih =>
      rw [bitLen, dif_neg hp, ih]
