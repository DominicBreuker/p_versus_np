# Failed Attempts and Lessons Learned

This document records proof attempts that looked promising but failed due to runtime issues, mathematical errors, or other problems. These serve as valuable lessons for future work.

---

## General Lessons

### Lesson 1: Always Test Runtime Before Committing
**Problem:** Proofs that compile may still have excessive runtime, making them unusable.

**Example:** The original `poly_quadratic_bound_k_ge_1` proof attempt (see below) caused Lean to run for >1 hour before being terminated.

**Solution:** 
- Test with `lake env lean Proof.lean` and verify it completes in < 1 minute
- Use `set_option maxHeartbeats` appropriately
- Break large proofs into smaller lemmas
- Avoid deep nesting of case splits

**Target:** All proofs should complete in under 1 minute on standard hardware.

---

### Lesson 2: Avoid Excessive Case Analysis
**Problem:** Massive case splits on concrete values cause combinatorial explosion.

**Example:** The `poly_quadratic_bound_k_ge_1` attempt below had dozens of nested `by_cases` on n ranges (1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608, 16777216, 33554432, 67108864).

**Solution:**
- Use general induction instead of case analysis
- Prove helper lemmas for general bounds
- Use `omega` to handle arithmetic constraints automatically
- If case analysis is necessary, limit to 2-3 cases maximum

---

### Lesson 3: Mathematical Correctness First
**Problem:** Mathematically incorrect statements waste time and cause confusion.

**Example:** The original `pow_lt_two_pow_half` theorem claimed n^d < 2^(n/2) for n ≥ 4d+10, which was mathematically unsound.

**Solution:**
- Always verify base cases with `norm_num`
- Check edge cases manually
- Use simpler bounds if general statements are hard to prove

---

### Lesson 4: Type Class Issues with Infinite Types
**Problem:** Fintype instances don't synthesize automatically for subtypes of infinite types.

**Example:** `{c : BoolCircuit n // circuitSize c ≤ p n}` lacks Fintype instance because `BoolCircuit n` is infinite.

**Solution:**
- Use `NormalizedCircuit n s` which has built-in Fintype instance
- Map to finite types before using cardinality arguments
- Use `Classical.choose` instead of `cases` on existential statements

---

### Lesson 5: Array vs List Operations
**Problem:** Mixing `Array.foldl` and `List.foldl` causes tactic failures.

**Example:** `evalCircuit` uses `Array.foldl` but helper lemmas use `List.foldl`.

**Solution:**
- Stick to one representation throughout
- If mixing is necessary, establish explicit conversion lemmas
- Use `simp` instead of `rw` when pattern matching is problematic

---

## Specific Failed Attempts

### Attempt 1: `evalCircuit_normalizeCircuit` with Explicit Array/List Conversion

**Location:** Line 387 in Proof.lean

**Attempted Code:**
```lean
private theorem evalCircuit_normalizeCircuit {n s : Nat} (c : BoolCircuit n) (hsize : circuitSize c ≤ s)
    (inp : Fin n → Bool) :
    evalCircuit (normalizedToRaw (normalizeCircuit c hsize)) inp = evalCircuit c inp := by
  let rawVals : Array Bool := List.foldl (evalStep inp) #[] c.nodes.toList
  let canonVals : Array Bool :=
    List.foldl (evalStep inp) #[]
      (c.nodes.toList.map (fun node => nodeCodeToRaw (normalizeNodeCode n s node)))
  have hcanon : canonVals = rawVals := by
    dsimp [canonVals, rawVals]
    exact evalStep_fold_normalized_eq inp #[] c.nodes.toList (by simpa)
  have hnodeListCodes : List.ofFn (normalizeCircuit c hsize).2 =
      List.ofFn (fun i : Fin c.nodes.size => normalizeNodeCode n s (c.nodes[i])) ++
        List.replicate (s - c.nodes.size) (NodeCode.const false) := normalizeCircuit_nodes_list c hsize
  have hnodeList : List.ofFn (fun i => nodeCodeToRaw ((normalizeCircuit c hsize).2 i)) =
      (c.nodes.toList.map (fun node => nodeCodeToRaw (normalizeNodeCode n s node))) ++
        List.replicate (s - c.nodes.size) falseNode := by
    simpa [falseNode, nodeCodeToRaw, List.map_append, List.ofFn_eq_map, Function.comp_def] using
      congrArg (List.map nodeCodeToRaw) hnodeListCodes
  have hnormVals :
      Array.foldl (fun acc node => acc.push (evalNode inp acc node)) #[]
          (normalizedToRaw (normalizeCircuit c hsize)).nodes =
        List.foldl (evalStep inp) #[] ((c.nodes.toList.map (fun node => nodeCodeToRaw (normalizeNodeCode n s node))) ++
          List.replicate (s - c.nodes.size) falseNode) := by
    simp [normalizedToRaw, evalStep, Array.foldl_toList, Array.toList_ofFn, hnodeList]
  have hrawVals :
      Array.foldl (fun acc node => acc.push (evalNode inp acc node)) #[] c.nodes = rawVals := by
    simp [rawVals, evalStep, Array.foldl_toList]
  unfold evalCircuit
  rw [hnormVals, hrawVals, List.foldl_append]
  simp only [canonVals, rawVals]
  rw [hcanon]
  by_cases houtput : c.output < c.nodes.size
  · have hsizeVals : rawVals.size = c.nodes.size := by
      dsimp [rawVals]
      simpa using evalStep_fold_size inp #[] c.nodes.toList
    have hprefix : (List.foldl (evalStep inp) rawVals (List.replicate (s - c.nodes.size) falseNode))[c.output]? =
        rawVals[c.output]? := by
      apply evalStep_fold_getElem?_preserve inp rawVals (List.replicate (s - c.nodes.size) falseNode) c.output
      simpa [hsizeVals] using houtput
    simp [normalizedToRaw, normalizeCircuit, houtput, hsizeVals, hprefix]
  · have hsizeVals : rawVals.size = c.nodes.size := by
      dsimp [rawVals]
      simpa using evalStep_fold_size inp #[] c.nodes.toList
    simp [normalizedToRaw, normalizeCircuit, houtput, hsizeVals, Array.getD]
```

**Problem:** This proof attempt mixes Array and List operations extensively, causing tactic failures. The `Array.foldl_toList` and `Array.toList_ofFn` lemmas may not exist or may not apply cleanly.

**Why It Failed:**
1. `Array.foldl_toList` may not be available in Mathlib
2. The conversion between Array and List operations is not seamless
3. The proof is too long and complex for Lean to verify efficiently

**Lesson:**
- Stick to one data structure (preferably Array since `evalCircuit` uses it)
- Or establish a clean conversion lemma first
- Break the proof into smaller, more manageable pieces

**Recommended Approach:**
```lean
-- First, prove a clean conversion lemma
private theorem array_foldl_eq_list_foldl {α β : Type} (arr : Array α) (f : β → α → β) (init : β) :
    Array.foldl f init arr = List.foldl f init arr.toList := by
  sorry

-- Then use it in the main proof
private theorem evalCircuit_normalizeCircuit {n s : Nat} (c : BoolCircuit n) (hsize : circuitSize c ≤ s)
    (inp : Fin n → Bool) :
    evalCircuit (normalizedToRaw (normalizeCircuit c hsize)) inp = evalCircuit c inp := by
  -- Use the conversion lemma to work in List domain
  sorry
```

---

### Attempt 2: `poly_quadratic_bound_k_ge_1` with Massive Case Analysis

**Location:** Line 852 in Proof.lean

**Attempted Code:** See the original FAILED_ATTEMPTS.md for the full ~900-line proof.

**Problem:** The proof used nested case splits on n ranges:
- n < 1024
- 1024 ≤ n < 2048
- 2048 ≤ n < 4096
- 4096 ≤ n < 8192
- 8192 ≤ n < 16384
- 16384 ≤ n < 32768
- 32768 ≤ n < 65536
- 65536 ≤ n < 131072
- 131072 ≤ n < 262144
- 262144 ≤ n < 524288
- 524288 ≤ n < 1048576
- 1048576 ≤ n < 2097152
- 2097152 ≤ n < 4194304
- 4194304 ≤ n < 8388608
- 8388608 ≤ n < 16777216
- 16777216 ≤ n < 33554432
- 33554432 ≤ n < 67108864
- n ≥ 67108864

Each case required proving similar inequalities, leading to:
- Excessive proof length (~900 lines)
- Deep nesting (5+ levels)
- Runtime > 1 hour

**Why It Failed:**
1. Lean's elaborator struggles with deeply nested case splits
2. Each case has similar structure, causing redundant work
3. The proof exceeds heartbeat limits

**Lesson:**
- Avoid more than 3 levels of nested case splits
- Use induction instead of case analysis when possible
- Prove general helper lemmas instead of repeating similar proofs
- Use `omega` to discharge arithmetic goals automatically

**Recommended Approach:**
```lean
private theorem poly_quadratic_bound_k_ge_1 (k c n : Nat) (hk : k ≥ 1) (hc : c ≥ 1)
    (hn : n ≥ 100 * k + c + 100) :
    (c * n ^ k + c) ^ 2 + 3 * (c * n ^ k + c) + 1 < 2 ^ n := by
  -- For k = 1, use existing approach
  cases k with
  | zero => omega  -- k ≥ 1, so this is impossible
  | succ k' =>
      cases k' with
      | zero =>
          -- k = 1: already complete
          simp at hn ⊢
          -- ... existing proof ...
      | succ k'' =>
          -- k ≥ 2: use general bound
          -- Bound: c * n^(k+2) + c ≤ n^(k+3)
          -- Then: (n^(k+3))^2 + 3*n^(k+3) + 1 ≤ 2 * n^(2k+6)
          -- And: 2 * n^(2k+6) < 2^n for n ≥ 100*(k+2) + c + 100
          
          -- Key insight: from hn, we have n ≥ 100*(k+2) + c + 100
          -- So 2k+6 ≤ 2*((n-100)/100) + 6 ≤ n/50 + 6 (approximately)
          -- For n ≥ 200, we can show n^(2k+6) < 2^(n-1)
          
          have h_bound : c * n ^ (k'' + 2) + c ≤ n ^ (k'' + 3) := by
            -- Prove this using monotonicity
            sorry
          
          have h_quad : (c * n ^ (k'' + 2) + c) ^ 2 + 3 * (c * n ^ (k'' + 2) + c) + 1 ≤
                       (n ^ (k'' + 3)) ^ 2 + 3 * (n ^ (k'' + 3)) + 1 := by
            -- Use monotonicity of x^2 + 3x + 1
            sorry
          
          have h_final : (n ^ (k'' + 3)) ^ 2 + 3 * (n ^ (k'' + 3)) + 1 < 2 ^ n := by
            -- Use a general lemma: for n ≥ C*k + D, n^(2k+6) < 2^(n-1)
            sorry
          
          calc (c * n ^ (k'' + 2) + c) ^ 2 + 3 * (c * n ^ (k'' + 2) + c) + 1
              ≤ (n ^ (k'' + 3)) ^ 2 + 3 * (n ^ (k'' + 3)) + 1 := h_quad
            _ < 2 ^ n := h_final
```

**Better Approach:** Prove a general lemma first:
```lean
private theorem n_pow_lt_two_pow_n_for_degree (d : Nat) (n : Nat) (hn : n ≥ max d 20) :
    n ^ d < 2 ^ n := by
  -- Prove by induction on n for fixed d
  -- Base case: n = max d 20, verify with norm_num
  -- Inductive step: (k+1)^d < 2^(k+1) assuming k^d < 2^k
  sorry

private theorem poly_quadratic_bound_k_ge_1 (k c n : Nat) (hk : k ≥ 1) (hc : c ≥ 1)
    (hn : n ≥ 100 * k + c + 100) :
    (c * n ^ k + c) ^ 2 + 3 * (c * n ^ k + c) + 1 < 2 ^ n := by
  -- Use the general lemma with d = 2k + 6
  have hd : 2 * k + 6 ≤ n := by omega
  have h_bound : (c * n ^ k + c) ^ 2 + 3 * (c * n ^ k + c) + 1 < 2 * n ^ (2 * k + 6) := by
    sorry
  have h_final : 2 * n ^ (2 * k + 6) < 2 ^ n := by
    calc 2 * n ^ (2 * k + 6) < 2 * 2 ^ n := by
        rw [Nat.mul_lt_mul_left (by norm_num)]
        exact n_pow_lt_two_pow_n_for_degree (2 * k + 6) n (by omega)
      _ = 2 ^ (n + 1) := by ring
      _ ≤ 2 ^ n := by
          apply Nat.pow_le_pow_right
          · norm_num
          · omega  -- This is wrong! 2^(n+1) > 2^n
    -- Oops, need different approach
    sorry
```

---

### Attempt 3: `shannon_counting_argument` with Direct Cardinality

**Location:** Line 1009 in Proof.lean

**Attempted Code:**
```lean
theorem shannon_counting_argument :
    ∀ (p : Nat → Nat) (hp : IsPolynomial p),
    ∃ n₀ : Nat, ∀ n ≥ n₀, ∃ (f : (Fin n → Bool) → Bool),
      ∀ (c : BoolCircuit n), circuitSize c ≤ p n → ∃ inp : Fin n → Bool, evalCircuit c inp ≠ f inp := by
  intros p hp
  obtain ⟨k, c_poly, h_bound⟩ := hp
  refine' ⟨100 * k + c_poly + 100, ?_⟩
  intro n hn
  -- We need to show: ∃ f, ∀ c with circuitSize c ≤ p n, ∃ inp, evalCircuit c inp ≠ f inp
  -- By counting: there are 2^(2^n) Boolean functions
  -- The number of circuits of size ≤ p n is at most circuit_count_upper_bound n (p n)
  -- We'll show circuit_count_upper_bound n (p n) < boolean_function_count n
  
  have hn_large : n ≥ 2 * k + c_poly + 10 := by omega
  have h_p_bound : p n ≤ c_poly * n ^ k + c_poly := h_bound n
  
  -- Show circuit_count_upper_bound n (p n) < boolean_function_count n
  have h_count : circuit_count_upper_bound n (p n) < boolean_function_count n := by
    unfold circuit_count_upper_bound boolean_function_count
    -- We need: (p n + 1)^(p n + 1) * 2^(p n) < 2^(2^n)
    calc (p n + 1) ^ (p n + 1) * 2 ^ (p n)
        ≤ 2 ^ ((p n) * (p n + 1)) * 2 ^ (p n) := by
          apply Nat.mul_le_mul_right
          exact s_plus_one_pow_le_two_pow_s_times_s_plus_one (p n) (by omega)
      _ = 2 ^ ((p n) * (p n + 1) + p n) := by rw [← Nat.pow_add]
      _ = 2 ^ (p n ^ 2 + 2 * (p n)) := by ring_nf
      _ ≤ 2 ^ (p n ^ 2 + 3 * (p n) + 1) := by
          apply Nat.pow_le_pow_right
          · norm_num
          · omega
      _ < 2 ^ (2 ^ n) := by
          apply Nat.pow_lt_pow_right
          · norm_num
          · -- We need p n ^ 2 + 3 * (p n) + 1 < 2 ^ n
            calc p n ^ 2 + 3 * (p n) + 1
                ≤ (c_poly * n ^ k + c_poly) ^ 2 + 3 * (c_poly * n ^ k + c_poly) + 1 := by
                  have h_bound' : p n ≤ c_poly * n ^ k + c_poly := h_p_bound
                  -- ... prove the inequality ...
                _ < 2 ^ n := poly_quadratic_bound k c_poly n (by omega)
  
  -- By pigeonhole principle: there are more Boolean functions than circuits
  by_contra h_all_computable
  push Not at h_all_computable
  -- h_all_computable: ∀ f, ∃ c with circuitSize c ≤ p n, ∀ inp, evalCircuit c inp = f inp
  -- This means every Boolean function is computed by some circuit of size ≤ p n
  -- But we've shown circuit_count_upper_bound n (p n) < boolean_function_count n
  -- Contradiction: can't have injection from larger set to smaller set
  
  -- Problem: how to formalize this in Lean?
  -- The type ((Fin n → Bool) → Bool) is not a fintype
  -- The type {c : BoolCircuit n // circuitSize c ≤ p n} is not a fintype
  sorry
```

**Problem:** The pigeonhole principle is mathematically trivial but hard to formalize in Lean's type system.

**Why It Failed:**
1. `((Fin n → Bool) → Bool)` is not a fintype (it's infinite in Lean's type theory)
2. `{c : BoolCircuit n // circuitSize c ≤ p n}` is not a fintype (subtype of infinite type)
3. Can't directly use `Fintype.card` or cardinality arguments

**Lesson:**
- Use `NormalizedCircuit n (p n)` as an intermediate finite type
- Map functions to normalized circuits via `Classical.choose`
- Use `Function.Injective` and `Fintype.card_le_of_injective`

**Recommended Approach:**
```lean
theorem shannon_counting_argument :
    ∀ (p : Nat → Nat) (hp : IsPolynomial p),
    ∃ n₀ : Nat, ∀ n ≥ n₀, ∃ (f : (Fin n → Bool) → Bool),
      ∀ (c : BoolCircuit n), circuitSize c ≤ p n → ∃ inp : Fin n → Bool, evalCircuit c inp ≠ f inp := by
  intros p hp
  obtain ⟨k, c_poly, h_bound⟩ := hp
  refine' ⟨100 * k + c_poly + 100, ?_⟩
  intro n hn
  
  -- First, show the counting inequality
  have h_count : circuit_count_upper_bound n (p n) < boolean_function_count n := by
    -- ... same as above ...
  
  -- Define the injection from functions to normalized circuits
  -- For each function f, choose a circuit that computes it (if one exists)
  -- But we need to show that not all functions have such a circuit
  
  -- Use proof by contradiction
  by_contra h_all_computable
  push Not at h_all_computable
  
  -- h_all_computable says: for every f, there exists a circuit c_f of size ≤ p n that computes f
  -- Define a function that chooses such a circuit for each f
  let circuitForFunction : ((Fin n → Bool) → Bool) → BoolCircuit n :=
    fun f => Classical.choose (h_all_computable f)
  
  -- Normalize each circuit to size exactly p n
  let normalizedForFunction : ((Fin n → Bool) → Bool) → NormalizedCircuit n (p n) :=
    fun f => normalizeCircuit (circuitForFunction f) (h_bound n)
  
  -- Show this is injective (different functions map to different normalized circuits)
  have h_inj : Function.Injective normalizedForFunction := by
    intro f g hfg
    -- If normalizedForFunction f = normalizedForFunction g, then
    -- circuitForFunction f and circuitForFunction g compute the same function
    -- (because normalization preserves evaluation via evalCircuit_normalizeCircuit)
    -- So f = g
    sorry  -- Needs evalCircuit_normalizeCircuit
  
  -- Now we have an injection from functions to NormalizedCircuit n (p n)
  -- NormalizedCircuit n (p n) has Fintype instance
  -- So: boolean_function_count n ≤ Fintype.card (NormalizedCircuit n (p n))
  have h_card : boolean_function_count n ≤ Fintype.card (NormalizedCircuit n (p n)) := by
    exact Fintype.card_le_of_injective normalizedForFunction h_inj
  
  -- But Fintype.card (NormalizedCircuit n (p n)) ≤ normalized_circuit_count_upper_bound n (p n)
  -- And normalized_circuit_count_upper_bound n (p n) ≤ circuit_count_upper_bound n (p n)
  -- So: boolean_function_count n ≤ circuit_count_upper_bound n (p n)
  -- But h_count says: circuit_count_upper_bound n (p n) < boolean_function_count n
  -- Contradiction!
  have h_contr : boolean_function_count n ≤ circuit_count_upper_bound n (p n) := by
    calc boolean_function_count n ≤ Fintype.card (NormalizedCircuit n (p n)) := h_card
      _ ≤ normalized_circuit_count_upper_bound n (p n) := normalized_circuit_card_le n (p n)
      _ ≤ circuit_count_upper_bound n (p n) := by
          -- Show normalized_circuit_count_upper_bound ≤ circuit_count_upper_bound
          sorry
  
  exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt h_contr h_count)
```

---

## Summary of Lessons

| **Issue** | **Failed Approach** | **Lesson** | **Recommended Solution** |
|-----------|---------------------|------------|--------------------------|
| Runtime | Massive case analysis | Avoid deep nesting | Use induction, general lemmas |
| Type classes | Direct Fintype on infinite types | Use finite intermediate types | `NormalizedCircuit` |
| Array/List | Mixing operations | Stick to one representation | Conversion lemmas |
| Math errors | Overly strong bounds | Verify base cases | Use `norm_num` |
| Complexity | Long proofs | Break into pieces | Smaller lemmas |

---

## Current Status

As of 2025-05-02, the following sorrys remain in Proof.lean:
1. `evalCircuit_normalizeCircuit` (line 387)
2. `poly_quadratic_bound_k_ge_1` for k ≥ 2 (line 852)
3. `shannon_counting_argument` (line 1009)

These are the priority items to address. The lessons in this document should help avoid repeating past mistakes.
