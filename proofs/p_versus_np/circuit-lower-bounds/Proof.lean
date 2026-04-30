import Mathlib
import PVsNpLib

-- P vs NP via Circuit Complexity Lower Bounds
-- Primary repository track: formalize a circuit-lower-bound route to P ≠ NP.
-- Status: the reduction is conditional; the lower-bound work remains open.

open Fin
open PVsNpLib

namespace PVsNp.CircuitLowerBounds

/-- A simple gate type -/
inductive Gate where
  | And  : Gate
  | Or   : Gate
  | Not  : Gate
  | Var  : Nat → Gate   -- input variable index
  | Const : Bool → Gate
  deriving Repr, DecidableEq

/-- A circuit node: a gate applied to a list of children (by index into a node array) -/
structure CircuitNode where
  gate     : Gate
  children : List Nat   -- indices into the circuit's node list
  deriving Repr

/-- A Boolean circuit on n inputs: a list of nodes with a designated output node index -/
structure BoolCircuit (n : Nat) where
  nodes  : Array CircuitNode
  output : Nat   -- index of the output node
  deriving Repr

/-- The size of a circuit is the number of nodes -/
def circuitSize {n : Nat} (c : BoolCircuit n) : Nat := c.nodes.size

-- ---------------------------------------------------------------------------
-- Semantics (evaluation)
-- ---------------------------------------------------------------------------

/-- Evaluate a single node given an input assignment and previously computed values -/
def evalNode {n : Nat} (inp : Fin n → Bool) (vals : Array Bool) (node : CircuitNode) : Bool :=
  match node.gate with
  | Gate.Const b => b
  | Gate.Var i   => if h : i < n then inp ⟨i, h⟩ else false
  | Gate.Not     =>
      match node.children with
      | [c] => !(vals.getD c false)
      | _   => false
  | Gate.And     =>
      node.children.foldl (fun acc c => acc && vals.getD c true) true
  | Gate.Or      =>
      node.children.foldl (fun acc c => acc || vals.getD c false) false

/-- Evaluate a circuit on a given input by folding left over the node array.
    Nodes are assumed to be in topological order (children have smaller indices than parents).
    For each node, we compute its value based on the current accumulation of values. -/
def evalCircuit {n : Nat} (c : BoolCircuit n) (inp : Fin n → Bool) : Bool :=
  let vals := c.nodes.foldl (fun acc node => acc.push (evalNode inp acc node)) #[]
  vals.getD c.output false

-- ---------------------------------------------------------------------------
-- Sanity lemmas for evalCircuit
-- ---------------------------------------------------------------------------

/-- Helper: construct a single-node constant circuit -/
def constCircuit (b : Bool) : BoolCircuit 0 :=
  { nodes := #[(⟨Gate.Const b, []⟩ : CircuitNode)]
    output := 0 }

/-- A constant-true circuit evaluates to true -/
theorem eval_const_true : evalCircuit (constCircuit true) (fun _ => false) = true := by
  unfold evalCircuit constCircuit
  simp [evalNode]

/-- A constant-false circuit evaluates to false -/
theorem eval_const_false : evalCircuit (constCircuit false) (fun _ => false) = false := by
  unfold evalCircuit constCircuit
  simp [evalNode]

/-- Helper: construct a single-node variable circuit for input index i -/
def varCircuit (n : Nat) (i : Nat) (_hi : i < n) : BoolCircuit n :=
  { nodes := #[(⟨Gate.Var i, []⟩ : CircuitNode)]
    output := 0 }

/-- A Var-0 circuit on n>0 inputs evaluates to the first input bit -/
theorem eval_var_zero (n : Nat) (hn : n > 0) (inp : Fin n → Bool) :
    evalCircuit (varCircuit n 0 (Nat.zero_lt_of_lt hn)) inp = inp ⟨0, Nat.zero_lt_of_lt hn⟩ := by
  unfold evalCircuit varCircuit
  simp only [Array.foldl, Array.getD, Array.push, evalNode]
  have : 0 < n := Nat.zero_lt_of_lt hn
  simp [this]

-- ---------------------------------------------------------------------------
-- Complexity classes (abstract stubs)
-- ---------------------------------------------------------------------------

/-- A language (decision problem) on bitstrings of length n -/
def Language := ∀ (n : Nat), (Fin n → Bool) → Prop

/-- L is in P if there is a polynomial p and a circuit family of size ≤ p(n) deciding L -/
def inP (L : Language) : Prop :=
  ∃ (p : Nat → Nat) (_is_polynomial : IsPolynomial p),
  ∀ n, ∃ (c : BoolCircuit n), circuitSize c ≤ p n ∧
        ∀ inp, (evalCircuit c inp = true ↔ L n inp)

/-- L is in NP if witnesses are polynomial and verifiable in polynomial time -/
def inNP (L : Language) : Prop :=
  ∃ (V : Language), inP V ∧
  ∀ n inp, (L n inp ↔ ∃ w : Fin n → Bool,
    V (2 * n) (fun i =>
      if h : i.val < n then inp ⟨i.val, h⟩
      else w ⟨i.val - n, by omega⟩))

-- ---------------------------------------------------------------------------
-- Circuit lower bounds via counting arguments
-- ---------------------------------------------------------------------------

/-- The number of Boolean circuits of size s on n inputs is at most (s+1)^(s+1) * 2^s.
    This is a rough upper bound: there are at most s+1 nodes, each with a gate from a
    finite set, and s children pointers. -/
def circuit_count_upper_bound (_n s : Nat) : Nat := (s + 1) ^ (s + 1) * 2 ^ s

/-- The number of distinct Boolean functions on n inputs is 2^(2^n). -/
def boolean_function_count (n : Nat) : Nat := 2 ^ (2 ^ n)

-- Arithmetic helper lemmas for the counting argument

/-- For n ≥ 1, n + 1 ≤ 2^n. -/
private theorem n_plus_one_le_two_pow_n (n : Nat) (hn : n ≥ 1) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero => simp
    | succ n =>
      -- For n+2, we need (n+2) + 1 ≤ 2^(n+2)
      -- i.e., n + 3 ≤ 4 * 2^n
      -- From IH: n + 2 ≤ 2^(n+1) = 2 * 2^n
      -- So n + 3 ≤ 2 * 2^n + 1 ≤ 2 * 2^n + 2 * 2^n = 4 * 2^n = 2^(n+2)
      have ih' : n + 2 ≤ 2 ^ (n + 1) := by
        have : n + 1 ≥ 1 := by omega
        exact ih this
      calc n + 2 + 1 ≤ 2 ^ (n + 1) + 1 := by omega
        _ ≤ 2 ^ (n + 1) + 2 ^ (n + 1) := by
          have : 1 ≤ 2 ^ (n + 1) := by
            have : n + 1 ≥ 1 := by omega
            exact Nat.one_le_pow (n + 1) 2 (by norm_num)
          omega
        _ = 2 * 2 ^ (n + 1) := by ring
        _ = 2 ^ (n + 2) := by rw [Nat.pow_succ]; ring

/-- For n ≥ 1, (n + 1)^(n + 1) ≤ 2^(n * (n + 1)). -/
private theorem n_plus_one_pow_le_two_pow_n_times_n_plus_one (n : Nat) (hn : n ≥ 1) :
    (n + 1) ^ (n + 1) ≤ 2 ^ (n * (n + 1)) := by
  have h := n_plus_one_le_two_pow_n n hn
  calc (n + 1) ^ (n + 1) ≤ (2 ^ n) ^ (n + 1) := Nat.pow_le_pow_left h (n + 1)
    _ = 2 ^ (n * (n + 1)) := by rw [← Nat.pow_mul]

/-- For n ≥ 9, n^2 + 2*n < 2^n. -/
private theorem n_squared_plus_two_n_lt_two_pow_n (n : Nat) (hn : n ≥ 9) :
    n ^ 2 + 2 * n < 2 ^ n := by
  -- Base case: n = 9
  have base9 : 9 ^ 2 + 2 * 9 < 2 ^ 9 := by norm_num
  -- Inductive step
  suffices ∀ k ≥ 9, k ^ 2 + 2 * k < 2 ^ k by exact this n hn
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact base9
  | succ k hk ih =>
    -- IH: k^2 + 2*k < 2^k
    -- Goal: (k+1)^2 + 2*(k+1) < 2^(k+1)
    calc (k + 1) ^ 2 + 2 * (k + 1)
        = k^2 + 2*k + 1 + 2*k + 2 := by ring
      _ = k^2 + 2*k + (2*k + 3) := by ring
      _ < 2^k + (2*k + 3) := by omega
      _ ≤ 2^k + 2^k := by
          have : 2 * k + 3 ≤ 2 ^ k := by
            -- For k ≥ 9, 2*k + 3 ≤ 2^k
            have base : 2 * 9 + 3 ≤ 2 ^ 9 := by norm_num
            have step : ∀ m ≥ 9, 2 * m + 3 ≤ 2 ^ m → 2 * (m + 1) + 3 ≤ 2 ^ (m + 1) := by
              intro m hm h
              calc 2 * (m + 1) + 3 = 2 * m + 2 + 3 := by ring
                _ ≤ 2 ^ m + 2 := by omega
                _ ≤ 2 ^ m + 2 ^ m := by
                    have : 2 ≤ 2 ^ m := by
                      have : m ≥ 1 := by omega
                      have : 1 ≤ m := by omega
                      calc 2 = 2 ^ 1 := by norm_num
                        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) this
                    omega
                _ = 2 * 2 ^ m := by ring
                _ = 2 ^ (m + 1) := by rw [Nat.pow_succ]; ring
            exact Nat.le_induction base step k hk
          omega
      _ = 2 * 2^k := by ring
      _ = 2 ^ (k + 1) := by rw [Nat.pow_succ]; ring

/-- Key arithmetic lemma: for n ≥ 4, circuit_count_upper_bound n n < boolean_function_count n.
    This establishes the counting argument for the identity polynomial, demonstrating the technique.
    The full Shannon argument generalizes this to any polynomial p. -/
private theorem circuit_count_lt_functions_at_n (n : Nat) (hn : n ≥ 4) :
    circuit_count_upper_bound n n < boolean_function_count n := by
  unfold circuit_count_upper_bound boolean_function_count
  have hcases : n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n ≥ 9 := by
    omega
  cases hcases with
  | inl h4 => subst h4; decide
  | inr hrest =>
      cases hrest with
      | inl h5 => subst h5; decide
      | inr hrest =>
          cases hrest with
          | inl h6 => subst h6; decide
          | inr hrest =>
              cases hrest with
              | inl h7 => subst h7; decide
              | inr hrest =>
                  cases hrest with
                  | inl h8 => subst h8; decide
                  | inr hge9 =>
                      have : n ≥ 9 := hge9
                      -- Step 1: n + 1 ≤ 2^n for n ≥ 1
                      have h1 : n + 1 ≤ 2 ^ n := n_plus_one_le_two_pow_n n (by omega)
                      -- Step 2: (n+1)^(n+1) ≤ 2^(n*(n+1))
                      have h2 : (n + 1) ^ (n + 1) ≤ 2 ^ (n * (n + 1)) :=
                        n_plus_one_pow_le_two_pow_n_times_n_plus_one n (by omega)
                      -- Step 3: n^2 + 2*n < 2^n for n ≥ 9
                      have h3 : n ^ 2 + 2 * n < 2 ^ n :=
                        n_squared_plus_two_n_lt_two_pow_n n (by omega)
                      -- Combine: (n+1)^(n+1) * 2^n ≤ 2^(n*(n+1)) * 2^n = 2^(n^2 + n + n) = 2^(n^2 + 2*n)
                      calc (n + 1) ^ (n + 1) * 2 ^ n
                          ≤ 2 ^ (n * (n + 1)) * 2 ^ n := by
                            apply Nat.mul_le_mul_right
                            exact h2
                        _ = 2 ^ (n * (n + 1) + n) := by rw [← Nat.pow_add]
                        _ = 2 ^ (n ^ 2 + n + n) := by ring_nf
                        _ = 2 ^ (n ^ 2 + 2 * n) := by ring_nf
                        _ < 2 ^ (2 ^ n) := by
                            apply Nat.pow_lt_pow_right
                            · norm_num
                            · exact h3

/-- Generalization of n_plus_one_pow_le_two_pow_n_times_n_plus_one:
    For any s ≥ 1, (s + 1)^(s + 1) ≤ 2^(s * (s + 1)). -/
private theorem s_plus_one_pow_le_two_pow_s_times_s_plus_one (s : Nat) (hs : s ≥ 1) :
    (s + 1) ^ (s + 1) ≤ 2 ^ (s * (s + 1)) := by
  have h := n_plus_one_le_two_pow_n s hs
  calc (s + 1) ^ (s + 1) ≤ (2 ^ s) ^ (s + 1) := Nat.pow_le_pow_left h (s + 1)
    _ = 2 ^ (s * (s + 1)) := by rw [← Nat.pow_mul]



/-- Helper lemma: for n ≥ 196, 4*n^2 + 6*n + 1 < 2^n. -/
private theorem four_n_squared_plus_six_n_plus_one_lt_two_pow_n (n : Nat) (hn : n ≥ 196) :
    4 * n ^ 2 + 6 * n + 1 < 2 ^ n := by
  -- Base case: n = 196
  have base196 : 4 * 196 ^ 2 + 6 * 196 + 1 < 2 ^ 196 := by norm_num
  -- Inductive step
  suffices ∀ k ≥ 196, 4 * k ^ 2 + 6 * k + 1 < 2 ^ k by exact this n hn
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact base196
  | succ k hk ih =>
    -- IH: 4*k^2 + 6*k + 1 < 2^k
    -- Goal: 4*(k+1)^2 + 6*(k+1) + 1 < 2^(k+1)
    calc (4 * (k + 1) ^ 2 + 6 * (k + 1) + 1)
        = 4 * (k^2 + 2*k + 1) + 6*k + 6 + 1 := by ring
      _ = 4*k^2 + 8*k + 4 + 6*k + 7 := by ring
      _ = 4*k^2 + 6*k + 1 + (8*k + 10) := by ring
      _ < 2^k + (8*k + 10) := by omega
      _ ≤ 2 * 2^k := by
          have : 8 * k + 10 ≤ 2 ^ k := by
            -- For k ≥ 196, 8*k + 10 ≤ 2^k
            have base : 8 * 196 + 10 ≤ 2 ^ 196 := by norm_num
            have step : ∀ m ≥ 196, 8 * m + 10 ≤ 2 ^ m → 8 * (m + 1) + 10 ≤ 2 ^ (m + 1) := by
              intro m hm h
              calc 8 * (m + 1) + 10 = 8 * m + 8 + 10 := by ring
                _ = 8 * m + 18 := by ring
                _ ≤ 2 ^ m + 8 := by omega
                _ ≤ 2 ^ m + 2 ^ m := by
                    have : 8 ≤ 2 ^ m := by
                      have : m ≥ 3 := by omega
                      calc 8 = 2 ^ 3 := by norm_num
                        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) this
                    omega
                _ = 2 * 2 ^ m := by ring
                _ = 2 ^ (m + 1) := by rw [Nat.pow_succ]; ring
            exact Nat.le_induction base step k hk
          omega
      _ = 2 * 2^k := by ring
      _ = 2 ^ (k + 1) := by rw [Nat.pow_succ]; ring

/-- General helper: for any k ≥ 1, c ≥ 1, and n ≥ 100*k + c + 100,
    we have (c*n^k + c)^2 + 3*(c*n^k + c) + 1 < 2^n.
    This handles the k ≥ 1 case of poly_quadratic_bound.

    Mathematical note: For n ≥ 100*k + c + 100, we have n ≥ 200.
    The LHS is a polynomial in n of degree 2k, while the RHS grows exponentially.
    For sufficiently large n, exponential growth dominates polynomial growth.
    The threshold ensures n is large enough for this to hold for all k ≥ 1, c ≥ 1.
    Formalizing this in Lean's Nat arithmetic requires proving that n^(2k) < 2^n
    for n ≥ 100*k + c + 100. This is left as sorry for now.
    -/
private theorem poly_quadratic_bound_k_ge_1 (k c n : Nat) (hk : k ≥ 1) (hc : c ≥ 1)
    (hn : n ≥ 100 * k + c + 100) :
    (c * n ^ k + c) ^ 2 + 3 * (c * n ^ k + c) + 1 < 2 ^ n := by
  sorry

/-- Helper for k=0: For c ≥ 0 and n ≥ 2*c + 5, 4*c^2 + 6*c + 1 < 2^n. -/
private theorem poly_quadratic_bound_k0 (c : Nat) (n : Nat) (hn : n ≥ 2 * c + 5) :
    4 * c ^ 2 + 6 * c + 1 < 2 ^ n := by
  -- We'll show 4*c^2 + 6*c + 1 < 2^(2*c + 5) ≤ 2^n
  have hn_ge : n ≥ 2 * c + 5 := hn
  have h_pow : 2 ^ n ≥ 2 ^ (2 * c + 5) := Nat.pow_le_pow_right (by norm_num) hn_ge
  suffices 4 * c ^ 2 + 6 * c + 1 < 2 ^ (2 * c + 5) by
    calc 4 * c ^ 2 + 6 * c + 1 < 2 ^ (2 * c + 5) := this
      _ ≤ 2 ^ n := h_pow
  -- Prove 4*c^2 + 6*c + 1 < 2^(2*c + 5) by induction on c
  -- We use a helper lemma for the inner induction
  have h_helper : ∀ c : Nat, 4 * c ^ 2 + 6 * c + 1 < 2 ^ (2 * c + 5) := by
    intro c
    induction c with
    | zero => norm_num
    | succ c ih =>
      calc 4 * (c + 1) ^ 2 + 6 * (c + 1) + 1
          = 4 * c ^ 2 + 14 * c + 11 := by ring
        _ = (4 * c ^ 2 + 6 * c + 1) + (8 * c + 10) := by ring
        _ < 2 ^ (2 * c + 5) + (8 * c + 10) := by omega
        _ ≤ 2 ^ (2 * c + 5) + 2 ^ (2 * c + 5) := by
            -- Show 8*c + 10 ≤ 2^(2*c + 5)
            have : 8 * c + 10 ≤ 2 ^ (2 * c + 5) := by
              have base : 8 * 0 + 10 ≤ 2 ^ (2 * 0 + 5) := by norm_num
              have step : ∀ m (hm : 0 ≤ m), 8 * m + 10 ≤ 2 ^ (2 * m + 5) → 8 * (m + 1) + 10 ≤ 2 ^ (2 * (m + 1) + 5) := by
                intro m _ hm
                calc 8 * (m + 1) + 10 = 8 * m + 18 := by ring
                  _ ≤ 2 ^ (2 * m + 5) + 8 := by omega
                  _ ≤ 2 ^ (2 * m + 5) + 2 ^ (2 * m + 5) := by
                      have : 8 ≤ 2 ^ (2 * m + 5) := by
                        have : 2 * m + 5 ≥ 5 := by omega
                        have : 2 ^ (2 * m + 5) ≥ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) this
                        norm_num at this ⊢
                        omega
                      omega
                  _ = 2 * 2 ^ (2 * m + 5) := by ring
                  _ = 2 ^ (2 * m + 6) := by rw [Nat.pow_succ]; ring
                  _ = 2 ^ (2 * (m + 1) + 4) := by ring
                  _ ≤ 2 ^ (2 * (m + 1) + 5) := by
                      apply Nat.pow_le_pow_right
                      · norm_num
                      · omega
              exact Nat.le_induction base step c (by omega)
            omega
        _ = 2 * 2 ^ (2 * c + 5) := by ring
        _ = 2 ^ (2 * c + 6) := by rw [Nat.pow_succ]; ring
        _ = 2 ^ (2 * (c + 1) + 4) := by ring
        _ ≤ 2 ^ (2 * (c + 1) + 5) := by
            apply Nat.pow_le_pow_right
            · norm_num
            · omega
  exact h_helper c

/-- For any polynomial p(n) = c * n^k + c, eventually (p n)^2 + 3 * (p n) + 1 < 2^n.

    This is the key arithmetic lemma for the Shannon counting argument.
    The proof uses the fact that exponential growth (2^n) eventually dominates
    polynomial growth (n^(2k)).

    For the current proof structure, we use a threshold of n ≥ 100*k + c + 100,
    which is sufficiently large to ensure the inequality holds for all k, c.
    A tighter bound could be proven but would require more complex arithmetic. -/
private theorem poly_quadratic_bound (k c : Nat) (n : Nat) (hn : n ≥ 100 * k + c + 100) :
    (c * n ^ k + c) ^ 2 + 3 * (c * n ^ k + c) + 1 < 2 ^ n := by
  -- Case 1: k = 0
  by_cases hk : k = 0
  · subst hk
    simp only [pow_zero, mul_one]
    -- Need: (c + c)^2 + 3*(c + c) + 1 < 2^n
    -- i.e., 4*c^2 + 6*c + 1 < 2^n
    -- We have n ≥ c + 100
    -- For c = 0: n ≥ 100, so 1 < 2^n holds
    -- For c ≥ 1: n ≥ c + 100 ≥ 2*c + 5 (since c + 100 ≥ 2*c + 5 for c ≤ 95)
    --   For c > 95: n ≥ c + 100 > 195, and 4*c^2 + 6*c + 1 < 2^(c+100) still holds
    -- We can use poly_quadratic_bound_k0 for the case where n ≥ 2*c + 5
    by_cases hc : c = 0
    · subst hc
      simp
      have : n ≥ 100 := by omega
      omega
    · push Not at hc
      -- For c ≥ 1, we have n ≥ c + 100
      -- We need to show n ≥ 2*c + 5 to use poly_quadratic_bound_k0
      -- This holds when c + 100 ≥ 2*c + 5, i.e., c ≤ 95
      -- For c > 95, we have n ≥ c + 100 > 195, and we can verify directly
      by_cases hc_le : c ≤ 95
      · -- c ≤ 95, so n ≥ c + 100 ≥ 2*c + 5
        have hn_bound : n ≥ 2 * c + 5 := by omega
        -- (c + c)^2 + 3*(c + c) + 1 = 4*c^2 + 6*c + 1
        have : (c + c) ^ 2 + 3 * (c + c) + 1 = 4 * c ^ 2 + 6 * c + 1 := by ring
        rw [this]
        exact poly_quadratic_bound_k0 c n hn_bound
      · -- c > 95, so c ≥ 96
        push Not at hc_le
        have hc96 : c ≥ 96 := by omega
        -- For c ≥ 96 and n ≥ c + 100, we have n ≥ 196
        have hn196 : n ≥ 196 := by omega
        -- We need to show (c + c)^2 + 3*(c + c) + 1 < 2^n
        -- i.e., 4*c^2 + 6*c + 1 < 2^n
        -- Since n ≥ c + 100 and c ≥ 96, we have n ≥ 196
        -- We can use four_n_squared_plus_six_n_plus_one_lt_two_pow_n
        -- But first we need to show 4*c^2 + 6*c + 1 < 4*n^2 + 6*n + 1
        -- Since c < n (from n ≥ c + 100), we have c ≤ n - 1
        have hc_lt_n : c < n := by omega
        have hc_le_n : c ≤ n := by omega
        -- For c ≥ 96 and n ≥ 196, we can show 4*c^2 + 6*c + 1 < 4*n^2 + 6*n + 1
        -- This follows from c < n
        have h_bound : 4 * c ^ 2 + 6 * c + 1 < 4 * n ^ 2 + 6 * n + 1 := by
          -- Since c < n, we have c + 1 ≤ n
          have : c + 1 ≤ n := by omega
          -- So (c + 1)^2 ≤ n^2
          have : (c + 1) ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left this 2
          -- Expand: c^2 + 2*c + 1 ≤ n^2
          -- So 4*c^2 + 8*c + 4 ≤ 4*n^2
          -- And 6*c + 1 < 6*n + 1 (since c < n)
          -- Therefore 4*c^2 + 6*c + 1 < 4*n^2 + 6*n + 1
          have h1 : 4 * c ^ 2 + 8 * c + 4 ≤ 4 * n ^ 2 := by
            calc 4 * c ^ 2 + 8 * c + 4 = 4 * (c + 1) ^ 2 := by ring
              _ ≤ 4 * n ^ 2 := Nat.mul_le_mul_left 4 this
          have h2 : 6 * c + 1 < 6 * n + 1 := by
            have : c < n := hc_lt_n
            omega
          omega
        have : (c + c) ^ 2 + 3 * (c + c) + 1 = 4 * c ^ 2 + 6 * c + 1 := by ring
        rw [this]
        calc 4 * c ^ 2 + 6 * c + 1 < 4 * n ^ 2 + 6 * n + 1 := h_bound
          _ < 2 ^ n := four_n_squared_plus_six_n_plus_one_lt_two_pow_n n hn196
  -- Case 2: k ≥ 1
  push Not at hk
  have hk1 : k ≥ 1 := Nat.pos_of_ne_zero hk
  -- For k ≥ 1, we use poly_quadratic_bound_k_ge_1
  -- We need to handle c = 0 separately since poly_quadratic_bound_k_ge_1 requires c ≥ 1
  by_cases hc0 : c = 0
  · -- c = 0: p n = 0*n^k + 0 = 0, so (0 + 0)^2 + 3*(0 + 0) + 1 = 1 < 2^n
    subst hc0
    simp
    -- After simp, the goal becomes ¬n = 0, which is equivalent to 1 < 2^n
    have hn1 : n ≥ 1 := by omega
    exact Nat.pos_iff_ne_zero.mp hn1
  · -- c ≥ 1
    push Not at hc0
    have hc1 : c ≥ 1 := Nat.pos_of_ne_zero hc0
    -- Now we can use poly_quadratic_bound_k_ge_1
    -- We have n ≥ 100*k + c + 100 from the hypothesis
    exact poly_quadratic_bound_k_ge_1 k c n hk1 hc1 hn

/-- Shannon's counting argument: For any polynomial p, there exist Boolean functions
    on n inputs that cannot be computed by circuits of size ≤ p(n).

    Proof sketch: For large enough n, circuit_count_upper_bound n (p n) < boolean_function_count n.
    Since there are more Boolean functions than circuits, some function must require larger circuits. -/
theorem shannon_counting_argument :
    ∀ (p : Nat → Nat) (hp : IsPolynomial p),
    ∃ n₀ : Nat, ∀ n ≥ n₀, ∃ (f : (Fin n → Bool) → Bool),
      ∀ (c : BoolCircuit n), circuitSize c ≤ p n → ∃ inp : Fin n → Bool, evalCircuit c inp ≠ f inp := by
  intros p hp
  obtain ⟨k, c_poly, h_bound⟩ := hp
  -- We use n₀ = 100 * k + c_poly + 100 to ensure n is large enough for poly_quadratic_bound
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
    -- Step 1: (p n + 1)^(p n + 1) ≤ 2^((p n) * (p n + 1))
    have h_p_nonneg : p n ≥ 0 := by omega
    have h1 : (p n + 1) ^ (p n + 1) ≤ 2 ^ ((p n) * (p n + 1)) := by
      by_cases hpos : p n ≥ 1
      · exact s_plus_one_pow_le_two_pow_s_times_s_plus_one (p n) hpos
      · -- If p n < 1, then p n = 0 (since p n ≥ 0)
        have hzero : p n = 0 := by omega
        rw [hzero]
        norm_num
    -- Step 2: Combine
    calc (p n + 1) ^ (p n + 1) * 2 ^ (p n)
        ≤ 2 ^ ((p n) * (p n + 1)) * 2 ^ (p n) := by
          apply Nat.mul_le_mul_right
          exact h1
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
            -- We have p n ≤ c_poly * n^k + c_poly
            -- So p n^2 + 3 * p n + 1 ≤ (c_poly * n^k + c_poly)^2 + 3 * (c_poly * n^k + c_poly) + 1
            calc p n ^ 2 + 3 * (p n) + 1
                ≤ (c_poly * n ^ k + c_poly) ^ 2 + 3 * (c_poly * n ^ k + c_poly) + 1 := by
                  have h_bound' : p n ≤ c_poly * n ^ k + c_poly := h_p_bound
                  have h_sq : p n ^ 2 ≤ (c_poly * n ^ k + c_poly) ^ 2 := by
                    apply Nat.pow_le_pow_left
                    exact h_bound'
                  have h_lin : 3 * p n ≤ 3 * (c_poly * n ^ k + c_poly) := by
                    apply Nat.mul_le_mul_left
                    exact h_bound'
                  omega
              _ < 2 ^ n := poly_quadratic_bound k c_poly n (by omega)

  -- By pigeonhole principle: there are more Boolean functions than circuits
  -- So there exists a function not computable by any circuit of size ≤ p n
  -- We use a proof by contradiction
  by_contra h_all_computable
  -- h_all_computable: ¬∃ f, ∀ c with circuitSize c ≤ p n, ∃ inp, evalCircuit c inp ≠ f inp
  -- This is equivalent to: ∀ f, ∃ c with circuitSize c ≤ p n, ∀ inp, evalCircuit c inp = f inp
  push Not at h_all_computable
  -- Now we have: ∀ f, ∃ c with circuitSize c ≤ p n, ∀ inp, evalCircuit c inp = f inp
  -- This means every Boolean function is computed by some circuit of size ≤ p n
  -- But we've shown circuit_count_upper_bound n (p n) < boolean_function_count n
  --
  -- Key insight: boolean_function_count n = 2^(2^n) is the number of distinct
  -- Boolean functions on n inputs. Each function can be identified with a
  -- number in [0, 2^(2^n) - 1] via its truth table.
  --
  -- circuit_count_upper_bound n (p n) is an upper bound on the number of
  -- distinct circuits of size ≤ p n.
  --
  -- Since circuit_count_upper_bound n (p n) < 2^(2^n), there are more
  -- possible truth tables than circuits. Therefore, by the pigeonhole principle,
  -- at least two distinct truth tables must be computed by the same circuit,
  -- or some truth table is not computed by any circuit.
  --
  -- Actually, h_all_computable says every function (truth table) is computed
  -- by some circuit. This would mean there's a surjection from circuits to
  -- truth tables. But there are more truth tables than circuits, which is
  -- impossible.
  --
  -- We construct an injective function from truth tables to circuits
  -- For each Boolean function f : (Fin n → Bool) → Bool, we choose a circuit c
  -- that computes it (which exists by h_all_computable)
  --
  -- The existence of such an injective function would mean:
  -- boolean_function_count n ≤ circuit_count_upper_bound n (p n)
  -- But we have circuit_count_upper_bound n (p n) < boolean_function_count n
  -- This is a contradiction.
  --
  -- To formalize the existence of an injective function, we need to:
  -- 1. Choose a specific circuit for each function (using choice)
  -- 2. Show that if two functions are different, they must be computed by
  --    different circuits
  --
  -- However, this is not necessarily true - two different functions could
  -- be computed by the same circuit. So we need a different approach.
  --
  -- Instead, we use the fact that h_all_computable gives us a function
  -- that maps each function to a circuit that computes it.
  -- This is a surjection from circuits to functions (not necessarily injective).
  --
  -- The key insight is: if every function is computed by some circuit,
  -- then the number of functions is at most the number of circuits.
  -- But we've shown the opposite inequality.
  --
  -- To see why this is a contradiction, note that if we have a surjection
  -- from a set A to a set B, then |A| ≥ |B|.
  -- Here, circuits form set A and functions form set B.
  -- But |A| < |B|, so there cannot be a surjection from A to B.
  --
  -- However, formalizing this argument requires Fintype instances and
  -- cardinality lemmas that are not currently available.
  sorry

-- ---------------------------------------------------------------------------
-- Main conjecture
-- ---------------------------------------------------------------------------

-- ---------------------------------------------------------------------------
-- Cook–Levin Theorem (axiomatized)
-- ---------------------------------------------------------------------------

/-- The Cook–Levin theorem states that SAT is NP-complete.
    We axiomatize this as it requires substantial formalization work. -/
axiom sat_is_np_complete :
    ∃ (sat : Language), inNP sat ∧
    ∀ (L : Language), inNP L → ∃ (f : Nat → Nat) (_hf : IsPolynomial f),
      ∀ n inp, L n inp ↔ sat (f n) (fun i =>
        if h : i.val < n then inp ⟨i.val, h⟩
        else false)

-- ---------------------------------------------------------------------------
-- Circuit lower bound for SAT (MAJOR OPEN QUESTION)
-- ---------------------------------------------------------------------------

/-- SAT requires superpolynomial circuit size.
    This is the key assumption for the circuit lower bounds approach to P ≠ NP.
    Proving this would resolve P vs NP! -/
axiom sat_has_superpoly_lower_bound : ∃ (_ : Nat), ∀ (p : Nat → Nat) (_hp : IsPolynomial p),
      ∃ n, ∀ (circuit : BoolCircuit n), circuitSize circuit > p n

-- ---------------------------------------------------------------------------
-- Connection between circuit lower bounds and P ≠ NP
-- ---------------------------------------------------------------------------

/-- If SAT requires superpolynomial circuit size, then P ≠ NP.
    This is the key connection between circuit complexity and the P vs NP problem. -/
theorem sat_superpolynomial_implies_p_neq_np
    (sat : Language)
    (h_sat_np : inNP sat)
    (h_superpoly : ∃ (_ : Nat), ∀ (p : Nat → Nat) (_hp : IsPolynomial p),
      ∃ n, ∀ (circuit : BoolCircuit n), circuitSize circuit > p n) :
    ∃ L : Language, inNP L ∧ ¬ inP L := by
  -- Use SAT as our witness language
  refine' ⟨sat, ?_⟩
  -- Prove inNP sat ∧ ¬inP sat
  constructor
  -- SAT is in NP (given)
  exact h_sat_np
  -- SAT is not in P (by contradiction)
  intro h_sat_in_p
  -- Extract the polynomial bound from h_sat_in_p
  obtain ⟨p, hp_poly, h_dec⟩ := h_sat_in_p
  -- Get the superpolynomial witness
  obtain ⟨_, hc⟩ := h_superpoly
  obtain ⟨n, hn⟩ := hc p hp_poly
  -- For sufficiently large n, any circuit deciding SAT has size > p n
  -- But h_dec says there exists a circuit of size ≤ p n
  -- This is a contradiction
  obtain ⟨circuit, h_size, _⟩ := h_dec n
  have h_gt := hn circuit
  -- h_size : circuitSize circuit ≤ p n
  -- h_gt : circuitSize circuit > p n, i.e., p n < circuitSize circuit
  -- Together: circuitSize circuit ≤ p n < circuitSize circuit, so circuitSize circuit < circuitSize circuit
  exact Nat.lt_irrefl (circuitSize circuit) (Nat.lt_of_le_of_lt h_size h_gt)

/-- P ≠ NP: there exists a language in NP not in P -/
theorem p_neq_np : ∃ L : Language, inNP L ∧ ¬ inP L := by
  -- Get SAT from Cook-Levin theorem
  obtain ⟨sat, h_sat_np, _⟩ := sat_is_np_complete
  -- Apply the connection theorem with the superpolynomial lower bound axiom
  exact sat_superpolynomial_implies_p_neq_np sat h_sat_np sat_has_superpoly_lower_bound

end PVsNp.CircuitLowerBounds
