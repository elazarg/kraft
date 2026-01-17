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
| `kraft_inequality` | For finite prefix-free S: `sum_{w in S} D^(-\|w\|) <= 1` |
| `kraft_inequality_infinite` | Extension to infinite prefix-free codes (as a tsum) |
| `kraft_mcmillan_inequality` | Same bound for uniquely decodable codes |
| `Kraft.Converse.exists_code` | Converse: lengths with `sum D^(-l_i) <= 1` admit a prefix-free code |
| `PrefixFree.uniquelyDecodable` | Prefix-free codes are uniquely decodable |

## Project Structure

```
Kraft.lean                          -- Root import file

InformationTheory/
  Coding/
    PrefixFree.lean                 -- Definition of prefix-free codes
    UniquelyDecodable.lean          -- Definition of uniquely decodable codes
    Kraft.lean                      -- Kraft's inequality (main theorem)
    KraftConverse.lean              -- Converse of Kraft's inequality
    KraftMcMillan.lean              -- Kraft-McMillan inequality
    Example.lean                    -- Shannon-Fano coding application

    ConstructionHelpers/
      Codeword.lean                 -- Fixed-width digit codeword construction
      Construction.lean             -- Core prefix-free code construction algorithm
      ExtShift.lean                 -- Extension of finite sequences to infinite
      Helpers.lean                  -- Utility lemmas for lists and arithmetic
      Sum.lean                      -- Helper lemmas for Kraft sums
```

### File Descriptions

- **PrefixFree.lean**: Defines `PrefixFree` (no codeword is a prefix of another) and proves prefix-free codes are uniquely decodable

- **UniquelyDecodable.lean**: Defines `UniquelyDecodable` (distinct concatenations yield distinct strings) and `concatFn` for codeword concatenation

- **Kraft.lean**: Proves Kraft's inequality for finite prefix-free codes, deriving it from the Kraft-McMillan inequality

- **KraftConverse.lean**: Constructs a prefix-free code for any length sequence satisfying the Kraft condition, via D-adic interval allocation; handles both finite (`Fin k`) and infinite (`ℕ`) index sets

- **KraftMcMillan.lean**: Proves the Kraft-McMillan inequality for uniquely decodable codes using the exponential growth of C^r where C is the Kraft sum

- **Example.lean**: Demonstrates the library with a source coding application. Defines Shannon-Fano lengths and proves `exists_prefix_code_near_entropy`: for any probability distribution, there exists a prefix-free code with expected length less than entropy + 1

### Construction Helpers

- **Codeword.lean**: Provides `kraftCodeword` and related functions for converting numbers to fixed-width digit representations in arbitrary bases

- **Construction.lean**: Core algorithmic engine for the converse proof. Defines `kraftNumerator` which computes interval start positions for the canonical code construction

- **ExtShift.lean**: Utility for extending finite length sequences (over `Fin k`) to infinite sequences over `ℕ`, preserving monotonicity

- **Helpers.lean**: Utility lemmas for working with lists, prefixes, and injective mappings

- **Sum.lean**: Helper lemmas for Kraft sum bounds, including that proper prefix sums are strictly less than 1

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

Apache 2.0 License - see LICENSE file.
