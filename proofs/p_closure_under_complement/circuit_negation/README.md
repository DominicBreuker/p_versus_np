# Approach: Circuit Negation

**Priority:** 50

**Status:** New — proof stub created; goal is a sorry-free proof

---

## Problem Statement

Prove that if `L ∈ P` (decided by a polynomial circuit family) then the complement
language `¬L` is also in `P`.

```lean
theorem p_closed_under_complement {L : Language} (hL : inP L) : inP (complement L)
```

This uses the same circuit model as `circuit-lower-bounds`.

---

## Why This Matters

- Unconditionally provable — no open-problem axioms.
- Demonstrates that the circuit model is expressive enough to prove structural facts about P.
- A stepping stone toward proving that P is a complexity class closed under basic operations.

---

## Proof Strategy

**Key idea:** Given a circuit `c` for `L` at size n, build `negateCircuit c` by pushing a
`Gate.Not` node whose single child is `c.output`.

**Step 1 — Define `negateCircuit`:**
```lean
def negateCircuit {n : Nat} (c : BoolCircuit n) : BoolCircuit n :=
  let notNode : CircuitNode := { gate := Gate.Not, children := [c.output] }
  { nodes := c.nodes.push notNode, output := c.nodes.size }
```

**Step 2 — Prove `negateCircuit_size`:**
```lean
theorem negateCircuit_size {n : Nat} (c : BoolCircuit n) :
    circuitSize (negateCircuit c) = circuitSize c + 1 := by
  simp [negateCircuit, circuitSize, Array.size_push]
```

**Step 3 — Prove `negateCircuit_eval`:**
```lean
theorem negateCircuit_eval {n : Nat} (c : BoolCircuit n) (inp : Fin n → Bool) :
    evalCircuit (negateCircuit c) inp = !(evalCircuit c inp)
```

Proof sketch:
1. Use `Array.foldl_push` to split the foldl on `c.nodes.push notNode`:
   the result is `vals.push (evalNode inp vals notNode)` where `vals` is the foldl on `c.nodes`.
2. `evalNode inp vals notNode`: gate is `Gate.Not`, children is `[c.output]`,
   so result is `!(vals.getD c.output false)`.
3. `vals.getD c.output false = evalCircuit c inp` because `vals` is built from `c.nodes`
   and `evalCircuit c inp = (c.nodes.foldl ...).getD c.output false`.
4. The output index `c.nodes.size` into `vals.push x` gives `x` by `Array.getD_push_eq`.

Key Lean4/Mathlib lemmas to look up:
```lean
Array.foldl_push   -- (a.push x).foldl f i = f (a.foldl f i) x
Array.size_push    -- (a.push x).size = a.size + 1
Array.getD_push_eq -- (a.push x).getD a.size d = x  (check exact name)
```

**Step 4 — Prove `poly_succ`:**
```lean
theorem poly_succ {p : Nat → Nat} (hp : IsPolynomial p) : IsPolynomial (fun n => p n + 1)
```
Use the same k and c+1 from the original polynomial, then `omega`.

**Step 5 — Assemble `p_closed_under_complement`:**
```lean
theorem p_closed_under_complement {L : Language} (hL : inP L) : inP (complement L) := by
  obtain ⟨p, hp_poly, h_circuits⟩ := hL
  refine ⟨fun n => p n + 1, poly_succ hp_poly, fun n => ?_⟩
  obtain ⟨c, h_size, h_eval⟩ := h_circuits n
  exact ⟨negateCircuit c, by rw [negateCircuit_size]; omega,
         fun inp => by simp [complement, negateCircuit_eval, h_eval]⟩
```

---

## Tasks

- [ ] Task 1: Copy circuit definitions into this file (or figure out cross-namespace import)
- [ ] Task 2: Define `complement : Language → Language`
- [ ] Task 3: Define `negateCircuit`
- [ ] Task 4: Prove `negateCircuit_size` (should be `decide` or `simp`)
- [ ] Task 5: Prove `negateCircuit_eval` (main work; see proof sketch above)
- [ ] Task 6: Prove `poly_succ`
- [ ] Task 7: Prove `p_closed_under_complement`

---

## Hints

- The circuit definitions are duplicated locally in each proof file; copy them from
  `p_subset_np/circuit-lifting/Proof.lean` (already a self-contained copy).
- `evalNode` for `Gate.Not` returns `!(vals.getD c false)` — check the children list.
- Do not use sorry as a shortcut for `Array.getD_push_eq`; search Mathlib for the exact lemma.
- The `complement` predicate is `fun n inp => ¬ L n inp`.
