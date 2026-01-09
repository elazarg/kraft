# Kraft's Inequality in Lean 4

A formalization of Kraft's inequality and related results from information theory in Lean 4 with Mathlib.

## Overview

Kraft's inequality is a fundamental result in coding theory that characterizes when a set of codeword lengths can form a prefix-free (instantaneous) code. This project formalizes:

- **Kraft's inequality**: For any prefix-free code over a binary alphabet, the sum of 2^(-length) over all codewords is at most 1
- **The converse**: Any sequence of lengths satisfying this constraint admits a prefix-free code
- **Kraft-McMillan inequality**: The same bound holds for the broader class of uniquely decodable codes
- **Prefix-free implies uniquely decodable**: Every prefix-free code is uniquely decodable

## Main Results

| Theorem | Statement |
|---------|-----------|
| `kraft_inequality` | For finite prefix-free S: `sum_{w in S} 2^(-|w|) <= 1` |
| `kraft_inequality_infinite` | Extension to infinite prefix-free codes (as a tsum) |
| `kraft_mcmillan_inequality` | Same bound for uniquely decodable codes |
| `kraft_inequality_tight` | Converse: lengths with `sum 2^(-l_i) <= 1` admit a prefix-free code |
| `kraft_inequality_tight_infinite` | Infinite version of the converse |
| `prefix_free_is_uniquely_decodable` | Prefix-free codes are uniquely decodable |

## Project Structure

```
Kraft/
  Basic.lean              -- Core definitions: PrefixFree, UniquelyDecodable
  InequalityFinite.lean   -- Kraft's inequality for finite codes
  InequalityInfinite.lean -- Extension to infinite codes via tsum
  McMillan.lean           -- Kraft-McMillan inequality for uniquely decodable codes
  TightFinite.lean        -- Converse of Kraft's inequality (finite case)
  TightInfinite.lean      -- Converse of Kraft's inequality (infinite case)
  UniquelyDecodable.lean  -- Prefix-free implies uniquely decodable
```

### File Descriptions

- **Basic.lean**: Defines `PrefixFree` (no codeword is a prefix of another) and `UniquelyDecodable` (distinct concatenations yield distinct strings)

- **InequalityFinite.lean**: Proves Kraft's inequality using a cylinder counting argument: extensions of codewords to a fixed length are disjoint

- **InequalityInfinite.lean**: Extends to infinite codes by showing any finite subset satisfies the bound, establishing summability

- **McMillan.lean**: Proves the inequality for uniquely decodable codes using the exponential growth of C^r where C is the Kraft sum

- **TightFinite.lean**: Constructs a prefix-free code for any length sequence satisfying the inequality, via recursive binary tree allocation

- **TightInfinite.lean**: Extends the construction to infinite index sets using an ordering by length and injectivity arguments

- **UniquelyDecodable.lean**: Shows prefix-free codes are uniquely decodable by induction on the decoded string length

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
