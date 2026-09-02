import Mathlib.Data.Nat.Size

/-!
# Bit length by binary search

`bitLen` computes `Nat.size`.
-/

namespace Nat

/-- Shifting right by `k` drops the bottom `k` bits, hence `k` from the bit length. -/
theorem size_shiftRight (n k : Nat) : (n >>> k).size = n.size - k := by
  have key (j : Nat) : (n >>> k).size ≤ j ↔ n.size ≤ j + k := by
    rw [size_le, size_le, shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _),
      Nat.pow_add]
  have h₁ := (key (n.size - k)).mpr (by omega)
  have h₂ := (key (n >>> k).size).mp (Nat.le_refl _)
  omega

end Nat

/-- Any `n` above 1 bounded by `2 ^ maxBits` forces `maxBits` to be at least 2. -/
theorem two_le_maxBits {n maxBits : Nat} (h : n < 2 ^ maxBits) (hn : ¬ n ≤ 1) :
    2 ≤ maxBits :=
  Nat.lt_of_lt_of_le (Nat.lt_size.mpr (by rw [Nat.pow_one]; omega)) (Nat.size_le.mpr h)

/-- Shifting right by `m` shrinks the bound on `n` by `m` bits. -/
theorem shift_lt {n maxBits : Nat} (h : n < 2 ^ maxBits) (m : Nat) :
    n >>> m < 2 ^ (maxBits - m) :=
  Nat.size_le.mp <| by
    have := Nat.size_le.mpr h
    rw [Nat.size_shiftRight]; omega

/-- A right shift by `m` vanishing means `n` fits in `m` bits. -/
theorem lt_of_shift_eq_zero {n m : Nat} (hp : ¬ (n >>> m > 0)) : n < 2 ^ m :=
  Nat.size_le.mp <| by
    have := Nat.size_shiftRight n m
    rw [Nat.le_zero.mp (Nat.not_lt.mp hp), Nat.size_zero] at this
    omega

/-- The number of bits in `n`, given a bound `n < 2 ^ maxBits`. -/
def bitLen (n maxBits : Nat) (h : n < 2 ^ maxBits) : Nat :=
  if _hn : n ≤ 1 then n
  else
    if hp : n >>> (maxBits / 2) > 0 then
      maxBits / 2 + bitLen (n >>> (maxBits / 2)) (maxBits - maxBits / 2) (shift_lt h (maxBits / 2))
    else
      bitLen n (maxBits / 2) (lt_of_shift_eq_zero hp)
termination_by maxBits
decreasing_by all_goals (have := two_le_maxBits h _hn; omega)

/-- `bitLen` computes the bit length, i.e. it agrees with `Nat.size`. -/
theorem bitLen_eq_size (n maxBits : Nat) (h : n < 2 ^ maxBits) : bitLen n maxBits h = n.size := by
  induction n, maxBits, h using bitLen.induct with
  | case1 n maxBits h hn =>
      rw [bitLen, dif_pos hn]
      rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl <;> simp
  | case2 n maxBits h hn hp ih =>
      have := Nat.size_pos.mpr hp
      rw [Nat.size_shiftRight] at this
      rw [bitLen, dif_neg hn, dif_pos hp, ih, Nat.size_shiftRight]
      omega
  | case3 n maxBits h hn hp ih =>
      rw [bitLen, dif_neg hn, dif_neg hp, ih]

/-- The result `r` of `bitLen` brackets `n`, with `2 ^ (r - 1) ≤ n < 2 ^ r`. -/
theorem bitLen_spec (n maxBits : Nat) (h : n < 2 ^ maxBits) :
    n < 2 ^ bitLen n maxBits h ∧ (bitLen n maxBits h ≠ 0 → 2 ^ (bitLen n maxBits h - 1) ≤ n) := by
  rw [bitLen_eq_size]
  exact ⟨Nat.lt_size_self n, fun hr => Nat.lt_size.mp (by omega)⟩

/-- `bitLen n maxBits h` is the least `r` with `n < 2 ^ r`. -/
theorem bitLen_isLeast (n maxBits : Nat) (h : n < 2 ^ maxBits) :
    n < 2 ^ bitLen n maxBits h ∧ ∀ k, n < 2 ^ k → bitLen n maxBits h ≤ k := by
  rw [bitLen_eq_size]
  exact ⟨Nat.lt_size_self n, fun _ hk => Nat.size_le.mpr hk⟩
