# OEIS A172572 Supercongruence — Lean 4 formalization

A complete, machine-checked Lean 4 / Mathlib proof of **Peter Bala's Conjecture 1**
on [OEIS A172572](https://oeis.org/A172572) (October 2024), and of the full
`m`-parameter family behind it.

The formalization has **no `sorry`**, no custom `axiom`, and no `native_decide`.
All main theorems depend only on the standard axioms `propext`,
`Classical.choice`, and `Quot.sound`.

## Result

For every prime `p` and every `m ≥ 1`, let `aArray m p` be the number of
`(m*p) × (2*m)` 0-1 matrices with row sums `2` and column sums `p`. Then

```text
aArray m p ≡ (2*m)! / 2^m  (mod p^2).
```

Specializing `m = 3` gives

```text
aArray 3 p ≡ 90  (mod p^2),
```

which is exactly Bala's conjecture on OEIS A172572.

In Lean:

```lean
theorem aArray_prime_mod_sq (m p : ℕ) (hp : p.Prime) :
    aArray m p ≡ (2 * m)! / 2 ^ m [MOD p ^ 2]

theorem oeis_A172572_conj1 (p : ℕ) (hp : p.Prime) :
    aArray 3 p ≡ 90 [MOD p ^ 2]
```

## Proof outline

1. **Babbage's congruence** — `C(j*p, p) ≡ j (mod p^2)` for every prime `p`.
2. **Fiber decomposition** — group the matrices by their edge-multiplicity
   vector `k`; the count becomes a sum of multinomial coefficients over
   `p`-regular multigraphs on `2m` vertices.
3. **Graph gap lemma** — a `p`-regular multigraph on `2m` vertices cannot have
   exactly `m - 1` edges of multiplicity `p`, so every non-perfect-matching
   contributes a factor `p^2`.
4. **`p`-adic valuation** — the surviving terms are exactly the perfect
   matchings, each contributing `(m*p)! / (p!)^m`.
5. **Product evaluation** — `∏_{j=1}^m C(j*p, p) ≡ m! (mod p^2)`, and
   `(2m-1)!! * m! = (2m)! / 2^m`.

## Build

Requires Lean `v4.37.0-rc1`. Mathlib is pinned in `lake-manifest.json`.

```bash
lake exe cache get
lake build
```

Check the axioms:

```bash
lake env lean Axioms.lean
```

## Files

| File | Contents |
| --- | --- |
| `OEIS_A172572_Supercongruence.lean` | Full proof (namespace `OEIS_A172572`) |
| `Axioms.lean` | `#print axioms` for the two main theorems |
| `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` | Reproducible build configuration |

## References

- OEIS A172572, *Number of 3n X 6 0..1 arrays with row sums 2 and column sums n*,
  Peter Bala's conjecture (Oct 28, 2024).
- The Babbage congruence and the multinomial/perfect-matching count are
  classical; the file gives a self-contained proof of the stated family.
