/-!
# Bit length by binary search
-/

/-- Any `n` above 1 bounded by `2 ^ maxBits` forces `maxBits` to be at least 2. -/
theorem two_le_maxBits {n maxBits : Nat} (h : n < 2 ^ maxBits) (hn : ¬ n ≤ 1) :
    2 ≤ maxBits := by
  have h2 : (2:Nat) ^ 1 < 2 ^ maxBits := by rw [Nat.pow_one]; omega
  exact (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp h2

/-- Shifting right by `m` shrinks the bound on `n` by `m` bits. -/
theorem shift_lt {n maxBits : Nat} (h : n < 2 ^ maxBits) (m : Nat) (hm : m ≤ maxBits) :
    n >>> m < 2 ^ (maxBits - m) := by
  rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
  rwa [Nat.sub_add_cancel hm]

/-- A right shift by `m` vanishing means `n` fits in `m` bits. -/
theorem lt_of_shift_eq_zero {n m : Nat} (hp : ¬ (n >>> m > 0)) : n < 2 ^ m := by
  rw [Nat.shiftRight_eq_div_pow] at hp
  exact Nat.lt_of_div_eq_zero (Nat.two_pow_pos _) (Nat.le_zero.mp (Nat.not_lt.mp hp))

/-- The number of bits in `n`, given a bound `n < 2 ^ maxBits`. -/
def bitLen (n maxBits : Nat) (h : n < 2 ^ maxBits) : Nat :=
  if hn : n ≤ 1 then n
  else
    if hp : n >>> (maxBits / 2) > 0 then
      maxBits / 2 + bitLen (n >>> (maxBits / 2)) (maxBits - maxBits / 2)
        (shift_lt h (maxBits / 2) (by omega))
    else
      bitLen n (maxBits / 2) (lt_of_shift_eq_zero hp)
termination_by maxBits
decreasing_by all_goals (have := two_le_maxBits h hn; omega)

/-- Bit-count bounds for `x` transfer from bounds for `x >>> m`, shifted by `m`. -/
theorem step (x m r : Nat) (hx : 0 < x >>> m)
    (h1 : x >>> m < 2 ^ r) (h2 : r ≠ 0 → 2 ^ (r - 1) ≤ x >>> m) :
    x < 2 ^ (m + r) ∧ (m + r ≠ 0 → 2 ^ (m + r - 1) ≤ x) := by
  rw [Nat.shiftRight_eq_div_pow] at hx h1 h2
  have hr0 : r ≠ 0 := by
    intro hz; subst hz; rw [Nat.pow_zero] at h1; omega
  refine ⟨?_, fun _ => ?_⟩
  · have := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos m)).mp h1
    rw [Nat.pow_add, Nat.mul_comm]; exact this
  · have := (Nat.le_div_iff_mul_le (Nat.two_pow_pos m)).mp (h2 hr0)
    rw [← Nat.pow_add] at this
    have heq : r - 1 + m = m + r - 1 := by omega
    rwa [heq] at this

/-- The result `r` of `bitLen` brackets `n`, with `2 ^ (r - 1) ≤ n < 2 ^ r`. -/
theorem bitLen_spec (n maxBits : Nat) (h : n < 2 ^ maxBits) :
    n < 2 ^ bitLen n maxBits h ∧ (bitLen n maxBits h ≠ 0 → 2 ^ (bitLen n maxBits h - 1) ≤ n) := by
  induction n, maxBits, h using bitLen.induct with
  | case1 n maxBits h hn =>
      rw [bitLen, dif_pos hn]
      have : n = 0 ∨ n = 1 := by omega
      cases this with
      | inl h0 => subst h0; simp
      | inr h1 => subst h1; simp
  | case2 n maxBits h hn hp ih =>
      rw [bitLen, dif_neg hn, dif_pos hp]
      exact step n _ _ hp ih.1 ih.2
  | case3 n maxBits h hn hp ih =>
      rw [bitLen, dif_neg hn, dif_neg hp]
      exact ih

/-- `bitLen n maxBits h` is the least `r` with `n < 2 ^ r`. -/
theorem bitLen_isLeast (n maxBits : Nat) (h : n < 2 ^ maxBits) :
    n < 2 ^ bitLen n maxBits h ∧ ∀ k, n < 2 ^ k → bitLen n maxBits h ≤ k := by
  have hs := bitLen_spec n maxBits h
  refine ⟨hs.1, fun k hk => ?_⟩
  cases Nat.eq_zero_or_pos (bitLen n maxBits h) with
  | inl hz => omega
  | inr hpos =>
      have h1 : (2:Nat) ^ (bitLen n maxBits h - 1) < 2 ^ k :=
        Nat.lt_of_le_of_lt (hs.2 (by omega)) hk
      have := (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp h1
      omega
