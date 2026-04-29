# Idea: P ⊆ NP (Formal Proof)

**Priority:** Medium

**Status:** New — provable without open-problem axioms; foundational building block

---

## Problem Statement

Formally prove **P ⊆ NP** in the circuit complexity model already established in
`candidates/circuit-lower-bounds/Proof.lean`.

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

## Definitions (imported from circuit-lower-bounds)

```lean
def Language := ∀ (n : Nat), (Fin n → Bool) → Prop

def IsPolynomial (p : Nat → Nat) : Prop := ∃ k c : Nat, ∀ n, p n ≤ c * n ^ k + c

def inP (L : Language) : Prop :=
  ∃ (p : Nat → Nat) (_is_polynomial : IsPolynomial p),
  ∀ n, ∃ (c : BoolCircuit n), circuitSize c ≤ p n ∧
        ∀ inp, (evalCircuit c inp = true ↔ L n inp)

def inNP (L : Language) : Prop :=
  ∃ (V : Language), inP V ∧
  ∀ n inp, (L n inp ↔ ∃ w : Fin n → Bool,
    V (2 * n) (fun i =>
      if h : i.val < n then inp ⟨i.val, h⟩
      else w ⟨i.val - n, by omega⟩))
```

---

## Proof Strategy

**Key idea:** Given `L ∈ P` (circuit family `{c_n}` of size ≤ p(n)), define the verifier
`V` at size `2*n` by *lifting* the circuit `c_n` to `2*n` inputs and ignoring the second half.

**Concretely:**

1. **Define `V : Language`:**
   ```
   V (2*n) combined_inp = L n (fun i => combined_inp ⟨i.val, ...⟩)
   ```
   i.e., V extracts the first n bits and runs L on them.

2. **`V ∈ P`:** The circuit family for `V` at size `2*n` is `liftCircuit c_n`, where
   `liftCircuit` keeps the same gate array but treats it as a `2*n`-input circuit.
   Since `Gate.Var i` nodes with `i < n` still read the correct input bit, and
   `circuitSize (liftCircuit c_n) = circuitSize c_n ≤ p n ≤ q(2n)` for `q(m) = p(m/2) + 1`.

3. **L n inp ↔ ∃ w, V (2*n) (combined):** Since `V (2*n) combined = L n (first_n combined)`,
   and `first_n (inp ++ w) = inp`, this reduces to `L n inp ↔ L n inp`. Trivially true.

---

## Tasks

- [ ] Task 1: Copy/re-export the `Language`, `inP`, `inNP`, `BoolCircuit`, `evalCircuit`
              definitions into this file (or import from circuit-lower-bounds namespace)
- [ ] Task 2: Define `liftCircuit {n : Nat} (c : BoolCircuit n) : BoolCircuit (2 * n)`
- [ ] Task 3: Prove `liftCircuit_eval`: `evalCircuit (liftCircuit c) inp = evalCircuit c (fun i => inp ⟨i.val, ...⟩)`
- [ ] Task 4: Define the verifier `V : Language` using `liftCircuit`
- [ ] Task 5: Prove `V ∈ inP` — use `liftCircuit c_n` with a suitable polynomial bound
- [ ] Task 6: Prove the witness direction: `∀ n inp, L n inp ↔ ∃ w, V (2*n) (combined inp w)`
- [ ] Task 7: Combine Tasks 5–6 into `p_subset_np`

---

## Immediate Next Steps

### Task 2 — `liftCircuit`

```lean
def liftCircuit {n : Nat} (c : BoolCircuit n) : BoolCircuit (2 * n) :=
  { nodes := c.nodes, output := c.output }
```

Note: `BoolCircuit n` stores `n` only as a phantom type parameter; the gate array itself
is just `Array CircuitNode`. Lifting is therefore trivial — no rewriting of the nodes needed.

### Task 3 — `liftCircuit_eval`

The key observation: `evalNode inp vals node` for a `Gate.Var i` node checks `i < n` via
a decidable proposition. When we lift to `2*n` inputs, the same `Gate.Var i` with `i < n`
will use `inp ⟨i, h⟩` where `h : i < 2*n`. We just need to relate the two input functions.

```lean
theorem liftCircuit_eval {n : Nat} (c : BoolCircuit n) (inp : Fin (2 * n) → Bool) :
    evalCircuit (liftCircuit c) inp =
    evalCircuit c (fun i => inp ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_mul_of_pos_left n (by norm_num))⟩) := by
  simp [liftCircuit, evalCircuit]
  congr 1
  -- Prove the node arrays are identical and evaluations agree
  ...
```

### Task 7 — `p_subset_np`

```lean
theorem p_subset_np {L : Language} (hL : inP L) : inNP L := by
  obtain ⟨p, hp_poly, h_circuits⟩ := hL
  -- Define V: V m inp = L (m / 2) (fun i => inp ⟨i.val, ...⟩)
  -- V is in P: use liftCircuit with bound q(m) = p(m/2) + 1 (polynomial in m)
  -- Witness direction: take any w; V (2*n) (inp ++ w) = L n inp by liftCircuit_eval
  sorry
```

---

## Hints

- `BoolCircuit n` has `n` as a phantom type; `liftCircuit` is essentially a type coercion.
- The bound `p(m/2)` is polynomial in `m` — need to show `∃ k c, p(m/2) ≤ c * m^k + c`.
  Use `k` and `c` from the polynomial bound of `p`, with `m/2 ≤ m`.
- Lean4's `omega` handles `i < n → i < 2 * n` and similar linear arithmetic automatically.
- The witness `w` in the NP existential can be *anything* — use `fun _ => false` as a dummy.
