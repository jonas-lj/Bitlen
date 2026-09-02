# bitlen

A Lean 4 formalisation of the bitlength-from-binary-search algorithm presented
[here](https://www.jonaslindstrom.dk/?p=997).

Given `n` and `maxBits` with `n < 2 ^ maxBits`, `bitLen` finds the number of significant bits of
`n` by binary search on `maxBits`, halving it at each step.

## Main results

* `bitLen` — the algorithm.
* `bitLen_eq_size` — it computes the bit length as defined by
  [`Nat.size`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Bits.html#Nat.size):

  ```lean
  theorem bitLen_eq_size (n maxBits : ℕ) (h : n < 2 ^ maxBits) : bitLen n maxBits = n.size
  ```
