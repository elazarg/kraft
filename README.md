# Kraft's Inequality in Lean 4

A formalization of Kraft's inequality and related results from information theory in Lean 4 with Mathlib.

## Overview

Kraft's inequality is a fundamental result in coding theory that characterizes when a set of codeword lengths can form a prefix-free (instantaneous) code. This project formalizes:

- **Kraft's inequality**: For any prefix-free code over an alphabet of size D, the sum of D^(-length) over all codewords is at most 1
- **The converse**: Any sequence of lengths satisfying this constraint admits a prefix-free code
- **Kraft-McMillan inequality**: The same bound holds for the broader class of uniquely decodable codes
- **Prefix-free implies uniquely decodable**: Every prefix-free code is uniquely decodable

All results are generalized to arbitrary finite alphabets (not just binary).

## Main Results

| Theorem | Statement |
|---------|-----------|
| `kraft_inequality` | For finite prefix-free S: `sum_{w in S} D^(-|w|) <= 1` |
| `kraft_inequality_infinite` | Extension to infinite prefix-free codes (as a tsum) |
| `kraft_mcmillan_inequality` | Same bound for uniquely decodable codes |
| `Kraft.Converse.exists_code` | Converse: lengths with `sum D^(-l_i) <= 1` admit a prefix-free code |
| `PrefixFree.uniquelyDecodable` | Prefix-free codes are uniquely decodable |

## Project Structure

```
Kraft/
  Basic.lean              -- Core definitions: PrefixFree, UniquelyDecodable
  ConcatFn.lean           -- Concatenation function for code construction
  Converse.lean           -- Converse of Kraft's inequality (main construction)
  Digits.lean             -- Number-to-digit representation (arbitrary base)
  ExtShift.lean           -- Helper for extending finite sequences to infinite
  Helpers.lean            -- Utility lemmas
  InequalityInfinite.lean -- Extension to infinite codes via tsum
  KraftOrder.lean         -- Ordering machinery for infinite index sets
  McMillan.lean           -- Kraft-McMillan inequality and finite Kraft inequality
  UniquelyDecodable.lean  -- Prefix-free implies uniquely decodable
```

### File Descriptions

- **Basic.lean**: Defines `PrefixFree` (no codeword is a prefix of another) and `UniquelyDecodable` (distinct concatenations yield distinct strings)

- **ConcatFn.lean**: Defines the concatenation function mapping tuples of codewords to their concatenation, used in the McMillan proof

- **Converse.lean**: Constructs a prefix-free code for any length sequence satisfying the inequality, via D-adic interval allocation; handles both finite and infinite index sets

- **Digits.lean**: Provides `natToDigitsBE` and related functions for converting numbers to fixed-width digit representations in arbitrary bases

- **ExtShift.lean**: Utility for extending finite length sequences (over `Fin k`) to infinite sequences over `ℕ`, preserving monotonicity

- **Helpers.lean**: Utility lemmas for working with finite sets, sums, and real arithmetic

- **InequalityInfinite.lean**: Extends to infinite codes by showing any finite subset satisfies the bound, establishing summability

- **KraftOrder.lean**: Two components: (1) `kraft_numerator`, which computes interval start positions for the canonical code construction, and (2) `KraftOrder`/`kraftRank`, which orders indices to make length functions monotone for infinite index sets

- **McMillan.lean**: Proves Kraft's inequality and the Kraft-McMillan inequality using the exponential growth of C^r where C is the Kraft sum

- **UniquelyDecodable.lean**: Shows prefix-free codes are uniquely decodable by induction on the decoded string length

### Example

- **Example.lean**: Demonstrates the library's usefulness with a source coding application. Defines Shannon-Fano lengths and proves `exists_prefix_code_near_entropy`: for any probability distribution, there exists a prefix-free code with expected length less than entropy + 1.

## Building

```bash
lake build
```

## Requirements

- **Lean**: 4.26.0
- **Mathlib**: v4.26.0

See `lean-toolchain` and `lake-manifest.json` for exact versions.

## Acknowledgments

Significant portions of this formalization were developed by AI systems:

- **Aristotle** (Harmonic)
- **ChatGPT 5.2**
- **Gemini 3**

## References

See `kraft.tex` for the mathematical exposition of the theorems formalized here.

### Background Reading

- Cover & Thomas, *Elements of Information Theory*, Chapter 5
- Kraft, L.G. (1949), *A device for quantizing, grouping, and coding amplitude-modulated pulses*

## License

MIT License - see LICENSE file.
