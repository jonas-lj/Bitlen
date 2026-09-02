# bitlen

A Lean 4 proof of correctness for the bitlength-from-binary-search algorithm presented
[here](https://www.jonaslindstrom.dk/?p=997).

Given `n` and `maxBits` with `n < 2 ^ maxBits`, `bitLen` finds the number of significant bits of
`n` by binary search on `maxBits`, halving it at each step. The theorem `bitLen_eq_size` proves
that this computes the bit length as defined by
[`Nat.size`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Bits.html#Nat.size),
mathlib's length of the binary representation:

```lean
theorem bitLen_eq_size (n maxBits : ℕ) (h : n < 2 ^ maxBits) : bitLen n maxBits = n.size
```

Everything lives in [`Bitlen.lean`](Bitlen.lean).

## Building

There is nothing to run: this is a library, not a program. Checking the proofs *is* the build, so
if `lake build` succeeds then the theorems hold.

You need [elan](https://github.com/leanprover/elan), the Lean toolchain manager. On macOS:

```bash
brew install elan-init
```

Otherwise:

```bash
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
```

elan reads [`lean-toolchain`](lean-toolchain) and fetches the matching Lean version
automatically, so you do not need to install Lean yourself.

This project depends on [mathlib](https://github.com/leanprover-community/mathlib4). Download its
prebuilt binaries before the first build — this takes a few GB, but compiling mathlib from source
instead would take hours:

```bash
lake exe cache get
```

Then:

```bash
lake build
```

Success looks like `Build completed successfully`, and means every proof in the file type-checks.
A failure is reported as an error at a specific line.

## Trying it out

`bitLen` is computable, so you can evaluate it. Create a scratch file with:

```lean
import Bitlen

#eval bitLen 100 10  -- 7, since 100 = 0b1100100
#eval Nat.size 100   -- 7
```

and run it with:

```bash
lake env lean Scratch.lean
```

For an interactive setup — hovering over terms, seeing proof states as you move through a proof —
install [VS Code](https://code.visualstudio.com) and its
[Lean 4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4), then open
this folder. That is the usual way to read and edit Lean.
