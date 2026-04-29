# Approach: Diagonalization for the Time Hierarchy Theorem

**Priority:** 70

**Status:** Active — monotonicity proven; diagonalization blocked on encoding and universal simulator

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
- [ ] Task 5: Define `encode : Nat → List Bool → List Bool` concretely (remove sorry)
- [ ] Task 6: Define `universal : Decider` concretely (remove sorry)
- [ ] Task 7: Construct the diagonalizing language D
- [ ] Task 8: Prove D ∈ DTIME(g) using the universal simulation axiom
- [ ] Task 9: Prove D ∉ DTIME(f) by contradiction (diagonalization)
- [ ] Task 10: Conclude `DTIME_strictSubset f g` (complete `time_hierarchy_theorem`)
- [ ] Task 11 (bonus): Instantiate for f = id, g = n³, giving DTIME(n) ⊊ DTIME(n³)

---

## Immediate Next Steps

### Task 5 — Concrete `encode`

Replace the `sorry` in `encode` with a concrete pairing:

```lean
def encode (i : Nat) (w : List Bool) : List Bool :=
  List.replicate i false ++ [true] ++ w
```

This represents index `i` as a run of `i` false-bits followed by a `true` separator, then the
word `w`. No sorry needed for the definition itself.

### Task 6 — Universal simulator (axiom is fine for now)

The `universal` decider can remain a `noncomputable def` with `sorry` for now, since it is backed
by the `universal_simulation` axiom. Focus on the diagonalization proof structure instead.

### Task 7–9 — Diagonalization sketch

Define D using the universal simulator:

```lean
noncomputable def diagLang (f : Nat → Nat) : Lang :=
  fun w => universal w = false ∧ timeOf universal w ≤ f w.length
```

Or more precisely, using the Gödel-numbering interpretation:
```lean
-- D w = "the i-th machine does NOT accept w in f(|w|) steps"
-- where i is encoded in w itself (first few bits as unary)
```

The key steps:
1. Show `diagLang g` ∈ `inDTIME g`: universal runs within the g-step budget.
2. Show `diagLang g` ∉ `inDTIME f`: if some M_j decided D within f steps, then on the
   encoded input `encode j v`, M_j and universal disagree — contradiction.

---

## Hints

- For the diagonalization, use `universal_simulation` to get the index `i` such that
  `universal (encode i v) = M v` for all v.
- Use `Set.ssubset_iff_subset_ne` for strict inclusion.
- For `IsLittleO`, use Mathlib's `Asymptotics.IsLittleO` or define a concrete version.
- See Sipser *Introduction to the Theory of Computation* §9.1 for the classical proof.
