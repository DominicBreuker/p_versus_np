# Idea: Time Hierarchy Theorem

**Priority:** High

**Status:** Active — new idea; formalization of a concrete, provable complexity separation

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

1. **Abstract machine model**: Rather than full Turing machines, use an abstract notion:
   - A *decider* is a function `ℕ → List Bool → Bool` (computes a yes/no answer).
   - A *timed decider* carries a step-count bound: `∀ w, steps(M, w) ≤ f(w.length)`.
2. **DTIME class**: `DTIME f = {L | ∃ M, decides M L ∧ ∀ w, timeOf M w ≤ f w.length}`.
3. **Universal simulation**: State (as axiom or prove for a concrete model) that a universal
   machine can simulate any f(n)-time machine in O(f(n) log f(n)) steps.
4. **Diagonalization**: Construct a language D that differs from every machine M_i on some input
   while running in g(n) time; conclude D ∈ DTIME(g) \ DTIME(f).

---

## Tasks

- [ ] Task 1: Define the abstract machine model (`Decider`, `decides`, `timeOf`)
- [ ] Task 2: Define `DTIME f` as a set of languages
- [ ] Task 3: Define `IsTimeConstructible f` and `IsLittleO f g`
- [ ] Task 4: State the universal simulation axiom (or prove for a concrete model)
- [ ] Task 5: Construct the diagonalizing language D
- [ ] Task 6: Prove D ∈ DTIME(g) using the time budget
- [ ] Task 7: Prove D ∉ DTIME(f) by diagonalization
- [ ] Task 8: Conclude DTIME(f) ⊊ DTIME(g) (strict inclusion)
- [ ] Task 9 (bonus): Instantiate for f = n, g = n², giving DTIME(n) ⊊ DTIME(n²)

---

## Immediate Next Steps

### Step 1 — Core definitions (start here)

```lean
namespace PVsNp.TimeHierarchy

-- A language on binary words (represented as List Bool)
abbrev Lang := List Bool → Prop

-- An abstract decider: maps input to Bool
abbrev Decider := List Bool → Bool

-- A decider M decides language L
def decides (M : Decider) (L : Lang) : Prop :=
  ∀ w, M w = true ↔ L w

-- Abstract step count (axiomatized for now)
noncomputable def timeOf (M : Decider) (w : List Bool) : Nat := sorry

-- DTIME(f): languages decidable within f(n) steps
def inDTIME (f : Nat → Nat) (L : Lang) : Prop :=
  ∃ M : Decider, decides M L ∧ ∀ w, timeOf M w ≤ f w.length
```

### Step 2 — Provable subset relation

Before tackling strict inclusion, prove the easy direction:
```lean
theorem inDTIME_mono {f g : Nat → Nat} (h : ∀ n, f n ≤ g n) (L : Lang)
    (hL : inDTIME f L) : inDTIME g L
```
This is straightforward from the definitions (already in `Proof.lean`).

### Step 3 — Diagonalization sketch

The diagonal language is:
```
D = {⟨i, w⟩ | M_i does NOT accept w within f(|w|) log f(|w|) steps}
```
where `⟨i, w⟩` is an encoding of index i and word w.
Key invariant: deciding D takes at most g(n) steps (simulate for f(n) log f(n) steps + overhead).

---

## Hints

- Lean4's `Finset` and `Set` are in Mathlib; use `Set.ssubset_iff_subset_ne` for strict inclusion.
- For little-o: use Mathlib's `Asymptotics.IsLittleO` or define a simpler version.
- Abstract over the exact machine model using axioms if needed — the diagonalization argument
  is model-independent given the simulation axiom.
- A simpler target: just prove DTIME(f) ⊆ DTIME(g) whenever f ≤ g pointwise (no diagonalization needed).
- See Sipser *Introduction to the Theory of Computation* Ch. 9 for the classical proof.
