# Idea: Circuit Complexity Lower Bounds

**Priority:** High

**Status:** Active — stalled at initial stub; concrete first steps needed

---

## Problem Statement

Prove that Boolean circuit complexity lower bounds for NP problems are sufficient to separate P from NP.
Specifically, formalize the argument that if any NP-complete problem (e.g., SAT) requires superpolynomial
circuit complexity, then P ≠ NP.

**Approach:**
1. Define Boolean circuits and circuit complexity formally in Lean4.
2. Define the complexity classes P and NP in terms of circuit families.
3. Prove (or assume as axiom) that SAT is NP-complete.
4. Develop lower bound lemmas showing exponential circuit complexity for some NP instance.
5. Conclude P ≠ NP.

---

## Tasks

- [ ] Task 1: Formalize Boolean circuit definitions (gates, wires, circuit size) — **stub exists**
- [ ] Task 2: Fix `evalCircuit` — remove the `sorry` by iterating nodes in array order
- [ ] Task 3: Define `IsPolynomial` predicate and clean up `inP`
- [ ] Task 4: Fix `inNP` witness encoding (use `Fin (n + n) → Bool` for combined input/witness)
- [ ] Task 5: State Cook–Levin theorem (SAT is NP-complete) — axiomatize if necessary
- [ ] Task 6: Prove a superpolynomial lower bound for some explicit Boolean function
- [ ] Task 7: Connect lower bound to P ≠ NP separation

---

## Immediate Next Steps (unblock the researchers)

### Fix `evalCircuit` (Task 2)
The nodes array is assumed to be in topological order (children have smaller indices than parents).
Evaluate by folding left over the node array:
```lean
def evalCircuit {n : ℕ} (c : BoolCircuit n) (inp : Fin n → Bool) : Bool :=
  let vals := c.nodes.foldl (fun acc node => acc.push (evalNode inp acc node)) #[]
  vals.getD c.output false
```
Then prove a small sanity lemma: a circuit with a single `Const true` node evaluates to `true`.

### Define `IsPolynomial` (Task 3)
```lean
def IsPolynomial (p : ℕ → ℕ) : Prop :=
  ∃ k c : ℕ, ∀ n, p n ≤ c * n ^ k + c
```
Replace the `sorry` in `inP` with `IsPolynomial p`.

### Fix `inNP` witness encoding (Task 4)
Use a combined bitstring of length `2 * n` (first `n` bits = input, second `n` bits = witness):
```lean
def inNP (L : Language) : Prop :=
  ∃ (V : Language), inP V ∧
  ∀ n inp, L n inp ↔ ∃ w : Fin n → Bool,
    V (2 * n) (fun i =>
      if h : i.val < n then inp ⟨i.val, h⟩
      else w ⟨i.val - n, by omega⟩)
```

---

## Hints

- Keep nodes in topological order (children before parents); this avoids circular dependencies.
- The Shannon counting argument gives an *existence* proof that most Boolean functions need exponential
  circuits — try formalizing this first as it avoids explicit NP-completeness.
- For the lower bound, start with a specific function like PARITY (linear lower bound for monotone circuits).
- The `lib/utils.lean` file contains shared definitions; move reusable pieces there.

---

## Library Code

Reusable definitions should live in `lib/utils.lean`. Factor out:
- `BoolCircuit` type definition (once stable)
- `IsPolynomial` predicate
- Any combinatorics lemmas used repeatedly
