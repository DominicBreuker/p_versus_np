# Approach: Diagonalization for the Time Hierarchy Theorem

**Priority:** 70

**Status:** Active — monotonicity proven; diagonalization blocked on diagonal language construction

---

## Problem Statement

Formally prove the **Deterministic Time Hierarchy Theorem** in Lean4:

> For time-constructible functions f, g with f(n) log f(n) = o(g(n)),
> we have DTIME(f(n)) ⊊ DTIME(g(n)).

This is a proven theorem in complexity theory. Unlike P vs NP, it has a complete classical proof
via diagonalization. Formalizing it in Lean4 gives:
- A concrete, achievable milestone (a real theorem, not an open problem).
- A formal framework for complexity classes that could later be extended to P vs NP.
- A demonstration that diagonalization arguments can be mechanized.

**Why this helps P vs NP:**
The THT establishes that the complexity class hierarchy is non-trivial (P ⊊ EXPTIME, etc.).
The same framework — diagonalization over a universal machine — underlies many complexity results.
A formal Lean4 THT proof would be a landmark formalization achievement in itself.

---

## Approach

Use an abstract model of computation to keep the formalization tractable:

1. **Abstract machine model**: A *decider* is a function `List Bool → Bool`.
2. **DTIME class**: `inDTIME f L = ∃ M, decides M L ∧ ∀ w, timeOf M w ≤ f w.length`.
3. **Universal simulation**: Axiomatized with quadratic overhead.
4. **Diagonalization**: Construct D that differs from every M_i on some input.

> `Proof.lean` uses `f(n) * (f(n) + 1) < g(n)` (quadratic gap) to match the quadratic simulation axiom.

---

## Tasks

- [x] Task 1: Define abstract machine model (`Decider`, `decides`, `timeOf`)
- [x] Task 2: Define `inDTIME f`
- [x] Task 3: Prove `inDTIME_mono` (monotonicity — no sorry)
- [x] Task 4: Prove `inDTIME_congr` (bound equality → class equality — no sorry)
- [x] Task 5: Define `encode : Nat → List Bool → List Bool` concretely (uses `PVsNpLib.unaryPair`)
- [x] Task 6: Prove `encode_length` and `index_lt_encode_length`
- [ ] Task 7: Construct the diagonal language D — see proof strategy below
- [ ] Task 8: Prove D ∈ DTIME(g) using the universal simulation axiom
- [ ] Task 9: Prove D ∉ DTIME(f) by contradiction (diagonalization)
- [ ] Task 10: Conclude `DTIME_strictSubset f g` (complete `time_hierarchy_theorem`)
- [ ] Task 11 (bonus): Instantiate for f = id, g = n³, giving DTIME(n) ⊊ DTIME(n³)

---

## Immediate Next Steps

### Task 7 — Diagonal Language D

Define D as the language that universal *rejects* within the g-step budget:

```lean
noncomputable def diagLang (g : Nat → Nat) : Lang :=
  fun w => universal w = false ∧ timeOf universal w ≤ g w.length
```

Here `w` encodes both an index `i` and a sub-word `v` via `encode i v`.
The idea: D contains `w` iff the universal simulator *rejects* `w` within `g(|w|)` steps.

### Task 8 — D ∈ DTIME(g)

Use the `universal` decider directly:
- `universal` decides `diagLang g` by definition (it accepts iff D(w) = true).
- The time bound comes from the `universal_simulation` axiom: `timeOf universal (encode i v) ≤ f v.length * (f v.length + 1) < g (encode i v).length`.
- Use `encode_length` to convert the length bound.

```lean
-- D ∈ DTIME(g) by taking M = universal:
-- decides universal (diagLang g) is by definition
-- timeOf universal w ≤ g w.length: need to relate universal's run time to g
-- Use universal_simulation: for the right i, timeOf universal (encode i v) ≤ f |v| * (f |v| + 1) < g |encode i v|
```

### Task 9 — D ∉ DTIME(f) (the diagonal contradiction)

Assume for contradiction that some M decides D in time f.
By `universal_simulation`, there exists index j such that `universal (encode j v) = M v` for all v.
Take v = encode j v itself (or any fixed v):
- If `M (encode j v) = true`, then D contains `encode j v`, so `universal (encode j v) = false`. But `M v = universal (encode j v) = false`. Contradiction.
- If `M (encode j v) = false`, symmetric contradiction.

```lean
-- formal sketch:
obtain ⟨j, hj_sim, hj_time⟩ := universal_simulation M f hM
-- hj_sim : ∀ v, universal (encode j v) = M v ∧ timeOf universal (encode j v) ≤ ...
-- Let v₀ be any word; consider w₀ = encode j v₀
-- Case split on M w₀
```

---

## Hints

- `encode` is already defined using `PVsNpLib.unaryPair`; do not redefine it.
- `universal` is noncomputable with `sorry`; this is fine — the axiom bridges the gap.
- For `decides universal (diagLang g)`: show `∀ w, universal w = true ↔ diagLang g w`
  by unfolding `diagLang` and using the definition of `universal`.
- The `Bool.eq_false_iff_ne_true` and `Bool.not_eq_true` lemmas are useful.
- For diagonalization, `Bool.dichotomy` (every Bool is true or false) drives the case split.
