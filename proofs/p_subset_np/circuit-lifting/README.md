# Approach: Circuit Lifting for P ⊆ NP

**Priority:** 85

**Status:** Active — `liftCircuit` and `poly_half` proven; two key `sorry` placeholders remain in `liftCircuit_eval` and `verifier_iff`

---

## Problem Statement

Formally prove **P ⊆ NP** in the circuit complexity model already established in
`proofs/p_versus_np/circuit-lower-bounds/Proof.lean`.

Concretely: prove the Lean4 theorem

```lean
theorem p_subset_np {L : Language} (hL : inP L) : inNP L
```

using the definitions of `inP`, `inNP`, `BoolCircuit`, and `evalCircuit` already in place.

This is a foundational result — every polynomial-time problem is trivially verifiable
(use the same circuit as the verifier; the witness is irrelevant).

---

## Why This Matters

- It is **provable with no sorry** (no open-problem axioms required).
- It complements the conditional `p_neq_np` proof in circuit-lower-bounds:
  together they give P ⊆ NP (this idea) and P ≠ NP (circuit-lower-bounds, conditional).
- A sorry-free P ⊆ NP is the first *genuine* theorem in this formalization.

---

## Current State of `Proof.lean`

| Lemma/Theorem | Status |
|---|---|
| `liftCircuit` | ✓ defined |
| `liftCircuit_size` | ✓ proven |
| `poly_half` | ✓ proven (sorry-free) |
| `liftCircuit_eval` | ✗ sorry |
| `verifier_iff` | ✗ sorry |
| `p_subset_np` | ✗ sorry (P-membership branch) |

---

## Tasks

- [x] Task 1: Copy/re-export definitions (Language, inP, inNP, BoolCircuit, evalCircuit)
- [x] Task 2: Define `liftCircuit`
- [x] Task 3 (partial): `liftCircuit_size` proven; `liftCircuit_eval` still has sorry
- [x] Task 4: `poly_half` proven sorry-free
- [ ] Task 5: Prove `liftCircuit_eval` — see proof strategy below
- [ ] Task 6: Prove `verifier_iff` — see proof strategy below
- [ ] Task 7: Complete `p_subset_np` using Tasks 5 and 6

---

## Immediate Next Steps

### Task 5 — Prove `liftCircuit_eval`

**Key insight:** `evalNode inp vals node` for a `Gate.Var i` node with `i < n` in a
`BoolCircuit n` and in the lifted `BoolCircuit (2*n)` both reduce to `inp ⟨i, _⟩`.
The proof h differs in type, but `Fin.ext` collapses the difference.

**Step 1 — node-level helper:**
```lean
lemma evalNode_lift_eq {n : Nat} (vals : Array Bool) (node : CircuitNode)
    (inp : Fin (2 * n) → Bool) :
    evalNode inp vals node =
    evalNode (fun i => inp ⟨i.val, by have := i.isLt; omega⟩) vals node := by
  simp only [evalNode]
  split
  · rfl  -- Const: no input access
  · rename_i i
    simp only
    split_ifs with h1 h2
    · congr 1; ext; rfl   -- same Nat value, Fin.ext
    · -- h2 : i < 2*n but not i < n, impossible since h1 : i < n
      exact absurd h1 (by omega)
    · -- h1 : ¬ i < n, h2 : i < 2*n — but inner function also needs i < n
      simp
    · rfl
  · rfl  -- Not: reads vals, not inp
  · rfl  -- And: reads vals
  · rfl  -- Or: reads vals
```

**Step 2 — accumulate over the array:**
Prove by induction on `c.nodes` that the entire `foldl` accumulation is equal.
The key Lean4/Mathlib lemma:
```lean
Array.foldl_congr : (∀ i, f acc a[i] = g acc a[i]) → a.foldl f init = a.foldl g init
-- (exact name may vary; look for Array.foldl with pointwise congruence)
```

Alternatively, prove by induction using `Array.foldl_push` (unfolding one element at a time):
```lean
lemma foldl_eq_of_eval_eq {n : Nat} (nodes : Array CircuitNode)
    (inp : Fin (2 * n) → Bool) :
    nodes.foldl (fun acc nd => acc.push (evalNode inp acc nd)) #[] =
    nodes.foldl (fun acc nd => acc.push
      (evalNode (fun i => inp ⟨i.val, by have := i.isLt; omega⟩) acc nd)) #[] := by
  induction nodes using Array.induction_on with
  | empty => simp
  | push a x ih => simp [Array.foldl_push, ih, evalNode_lift_eq]
```

Then `liftCircuit_eval` follows from `foldl_eq_of_eval_eq` and `Array.getD_congr`.

### Task 6 — Prove `verifier_iff`

**Key insight:** `(2 * n) / 2 = n` (Lean4: `Nat.mul_div_cancel_left n 2` or `omega`).
Once that is established, the `Fin ((2*n)/2)` type becomes `Fin n`, and the combined
input's first-n slice is exactly `inp`.

```lean
theorem verifier_iff (L : Language) (n : Nat) (inp : Fin n → Bool) (w : Fin n → Bool) :
    L ((2 * n) / 2) (...) ↔ L n inp := by
  -- Step 1: show (2 * n) / 2 = n
  have hn2 : 2 * n / 2 = n := Nat.mul_div_cancel_left n (by norm_num)
  -- Step 2: rewrite L's first argument
  rw [hn2]
  -- Step 3: show the Fin-indexed function is propositionally equal to inp
  -- For i : Fin n, combined ⟨i.val, _⟩ = if i.val < n then inp ⟨i.val, _⟩ else ...
  --                                      = inp ⟨i.val, i.isLt⟩  (since i.val < n always)
  --                                      = inp i  (by Fin.ext)
  congr 1
  funext i
  simp [i.isLt]
  congr 1; ext; rfl
```

---

## Hints

- `BoolCircuit n` has `n` as a phantom type; `liftCircuit` is essentially a type coercion.
- The bound `p(m/2)` is polynomial in `m`; `poly_half` is already proven.
- Lean4's `omega` handles `i < n → i < 2 * n` and `2 * n / 2 = n`.
- The witness `w` in the NP existential can be *anything* — use `fun _ => false` as a dummy.
- For array induction, look for `Array.induction_on` or `Array.rec`.
