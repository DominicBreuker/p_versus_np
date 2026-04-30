import Mathlib
import PVsNpLib

-- P ⊆ NP — supporting formalization in the circuit complexity model used by the
-- main P vs NP track.
-- Goal: Every language in P is also in NP.
-- Status: Stub — the remaining work is ordinary Lean proof engineering.
--
-- The proof strategy is:
--   1. Given L ∈ P (polynomial circuit family {c_n}), define the verifier V at size 2*n
--      as liftCircuit(c_n) — same gate array, but typed for 2*n inputs.
--   2. V ∈ P: liftCircuit preserves circuit size; the polynomial bound is q(m) = p(m/2) + 1.
--   3. Witness direction: V(2*n)(inp ++ w) = L(n)(inp) for any w, because V ignores the
--      second half of its input. The witness w can be anything (e.g., all false).

-- ---------------------------------------------------------------------------
-- Re-use definitions from the shared library and the local circuit model
-- ---------------------------------------------------------------------------

open PVsNpLib

namespace PVsNp.PSubsetNP

-- ---------------------------------------------------------------------------
-- Circuit definitions (copied from circuit-lower-bounds for self-containment)
-- ---------------------------------------------------------------------------

inductive Gate where
  | And   : Gate
  | Or    : Gate
  | Not   : Gate
  | Var   : Nat → Gate
  | Const : Bool → Gate
  deriving Repr, DecidableEq

structure CircuitNode where
  gate     : Gate
  children : List Nat
  deriving Repr

instance : Inhabited CircuitNode := ⟨{ gate := Gate.Const false, children := [] }⟩

structure BoolCircuit (n : Nat) where
  nodes  : Array CircuitNode
  output : Nat
  deriving Repr

def circuitSize {n : Nat} (c : BoolCircuit n) : Nat := c.nodes.size

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

def evalCircuit {n : Nat} (c : BoolCircuit n) (inp : Fin n → Bool) : Bool :=
  let vals := c.nodes.foldl (fun acc node => acc.push (evalNode inp acc node)) #[]
  vals.getD c.output false

def Language := ∀ (n : Nat), (Fin n → Bool) → Prop

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

-- ---------------------------------------------------------------------------
-- Circuit lifting: BoolCircuit n → BoolCircuit (2 * n)
-- ---------------------------------------------------------------------------

/-- Lift a circuit for n inputs to a circuit for 2*n inputs.
    The gate array is unchanged; Var nodes with index < n still read the correct
    input (the first n bits of the combined 2*n input). -/
def liftCircuit {n : Nat} (c : BoolCircuit n) : BoolCircuit (2 * n) :=
  { nodes := c.nodes, output := c.output }

/-- Lifting preserves circuit size -/
theorem liftCircuit_size {n : Nat} (c : BoolCircuit n) :
    circuitSize (liftCircuit c) = circuitSize c := by
  simp [liftCircuit, circuitSize]

/-- General circuit lifting: BoolCircuit n → BoolCircuit m for n ≤ m.
    The gate array is unchanged; Var nodes with index < n still read the correct
    input (the first n bits of the m-bit input). -/
def liftCircuitTo {n m : Nat} (_h : n ≤ m) (c : BoolCircuit n) : BoolCircuit m :=
  { nodes := c.nodes, output := c.output }

/-- General lifting preserves circuit size -/
theorem liftCircuitTo_size {n m : Nat} (h : n ≤ m) (c : BoolCircuit n) :
    circuitSize (liftCircuitTo h c) = circuitSize c := by
  simp [liftCircuitTo, circuitSize]

/-- Well-formedness predicate: all Var nodes in a circuit have indices < n. -/
def IsWellFormed {n : Nat} (c : BoolCircuit n) : Prop :=
  ∀ i < c.nodes.size, ∀ j, c.nodes[i]!.gate = Gate.Var j → j < n

/-- Lifting preserves evaluation when restricted to the first n inputs.
    Proof sketch: evalNode and evalCircuit only consult inp at Var-gate positions i < n;
    lifting keeps those same positions so the values agree.

    TODO: Complete the Array.foldl congruence proof.
    The key lemma needed is: if f and g agree on all elements of arr, then
    arr.foldl (fun acc x => acc.push (f acc x)) #[] = arr.foldl (fun acc x => acc.push (g acc x)) #[]
    This is non-trivial because Array.foldl is defined via foldlM. -/
theorem liftCircuit_eval {n : Nat} (c : BoolCircuit n) (inp : Fin (2 * n) → Bool)
    (h_wf : IsWellFormed c) :
    evalCircuit (liftCircuit c) inp =
    evalCircuit c (fun i => inp ⟨i.val, by have := i.isLt; omega⟩) := by
  simp only [liftCircuit, evalCircuit]
  -- Prove that for each node in c.nodes, evalNode gives the same result for both inputs
  have h_nodes : ∀ i < c.nodes.size, ∀ acc : Array Bool,
      evalNode inp acc c.nodes[i]! = evalNode (fun (i : Fin n) => inp ⟨i.val, by have := i.isLt; omega⟩) acc c.nodes[i]! := by
    intro i hi acc
    unfold evalNode
    match h_gate : c.nodes[i]!.gate with
    | Gate.And => rfl
    | Gate.Or => rfl
    | Gate.Not => rfl
    | Gate.Const b => rfl
    | Gate.Var idx =>
      by_cases hi_idx : idx < n
      · -- idx < n: both sides read from inp at index idx
        have h : idx < 2 * n := by omega
        simp only [h, hi_idx]
      · -- idx >= n: By well-formedness, this case doesn't occur
        exfalso
        have : idx < n := h_wf i hi idx h_gate
        omega
  -- TODO: Prove the foldl equality using h_nodes
  -- The two foldl expressions differ only in the inp function passed to evalNode
  -- Since h_nodes shows they give the same result for all nodes in c.nodes,
  -- the foldl results should be equal.
  -- This requires a lemma about Array.foldl congruence for functions that agree on the array elements.
  sorry

-- ---------------------------------------------------------------------------
-- Polynomial bound for the lifted family
-- ---------------------------------------------------------------------------

/-- If p is polynomial then so is the function m ↦ p (m / 2) + 1.
    This gives the polynomial bound for the verifier circuit family at size 2*n.
    Proof: p(m/2) ≤ c*(m/2)^k + c ≤ c*m^k + c < (c+1)*m^k + (c+1). -/
theorem poly_half {p : Nat → Nat} (hp : IsPolynomial p) : IsPolynomial (fun m => p (m / 2) + 1) := by
  obtain ⟨k, c, hpc⟩ := hp
  refine ⟨k, c + 1, fun m => ?_⟩
  show p (m / 2) + 1 ≤ (c + 1) * m ^ k + (c + 1)
  have h_half : m / 2 ≤ m := Nat.div_le_self m 2
  have hpow : (m / 2) ^ k ≤ m ^ k := Nat.pow_le_pow_left h_half k
  have h1 : p (m / 2) ≤ c * m ^ k + c :=
    Nat.le_trans (hpc (m / 2))
      (Nat.add_le_add_right (Nat.mul_le_mul_left c hpow) c)
  -- (c + 1) * m^k + (c + 1) = c * m^k + m^k + c + 1 ≥ c * m^k + c + 1 ≥ p(m/2) + 1
  have h2 : c * m ^ k + c + 1 ≤ (c + 1) * m ^ k + (c + 1) := by
    have hexp : 0 ≤ m ^ k := Nat.zero_le _
    have : (c + 1) * m ^ k = c * m ^ k + m ^ k := by
      rw [Nat.add_mul, Nat.one_mul]
    omega
  omega

-- ---------------------------------------------------------------------------
-- Key lemma: V (2*n) (combined inp w) ↔ L n inp
-- ---------------------------------------------------------------------------

/-- The verifier at size 2*n, applied to the combined input, evaluates L on inp.
    Proof idea: 2*n/2 = n and the combined function equals inp after transport.

    TODO: Complete the dependent-type bookkeeping proof.
    The mathematical content is trivial: (2*n)/2 = n and the functions are pointwise equal.
    The challenge is proving this in Lean's dependent type system.

    Key insight: for i : Fin ((2*n)/2), we have i.val < n, so the combined function
    (fun j => if h : j.val < n then inp ⟨j.val, h⟩ else w ⟨j.val - n, _⟩) ⟨i.val, _⟩ = inp ⟨i.val, _⟩
    And inp ⟨i.val, _⟩ = inp (Fin.cast h_div i) where h_div : (2*n)/2 = n.
    So the combined function = inp ∘ Fin.cast h_div.
    Then we need: L ((2*n)/2) (inp ∘ Fin.cast h_div) ↔ L n inp.
    This requires Eq.rec to transport L along h_div. -/
theorem verifier_iff (L : Language) (n : Nat) (inp : Fin n → Bool) (w : Fin n → Bool) :
    L ((2 * n) / 2)
      (fun (i : Fin ((2 * n) / 2)) =>
        (fun j : Fin (2 * n) =>
          if h : j.val < n then inp ⟨j.val, h⟩ else w ⟨j.val - n, by omega⟩)
        ⟨i.val, by omega⟩)
    ↔ L n inp := by
  have h_div : (2 * n) / 2 = n := by omega
  -- For i : Fin ((2*n)/2), i.val < n, so the combined function at i = inp at i
  have h_func_eq : (fun (i : Fin ((2 * n) / 2)) =>
        (fun j : Fin (2 * n) =>
          if h : j.val < n then inp ⟨j.val, h⟩ else w ⟨j.val - n, by omega⟩)
        ⟨i.val, by omega⟩) = inp ∘ (fun i : Fin ((2 * n) / 2) => (⟨i.val, by omega⟩ : Fin n)) := by
    funext i
    have h_i_lt : i.val < n := by omega
    simp only [Function.comp_apply]
    show (if h : i.val < n then inp ⟨i.val, h⟩ else w ⟨i.val - n, by omega⟩) = inp ⟨i.val, by omega⟩
    rw [dif_pos h_i_lt]
  rw [h_func_eq]
  -- Now: L ((2*n)/2) (inp ∘ (fun i => (⟨i.val, by omega⟩ : Fin n))) ↔ L n inp
  -- We convert the goal using the fact that (2*n)/2 = n and the functions are compatible
  -- This requires dependent type transport, which is complex
  sorry

-- ---------------------------------------------------------------------------
-- Main theorem
-- ---------------------------------------------------------------------------

/-- P ⊆ NP: every language decidable in polynomial time is also in NP.
    Proof: given a polynomial circuit family {c_n} for L, define the verifier V at
    size 2*n as the lifted circuit liftCircuit c_n.  The witness is ignored entirely.

    TODO: Complete the proof by:
    1. Proving well-formedness for circuits from inP
    2. Handling odd sizes using liftCircuitTo
    3. Using verifier_iff for the witness direction -/
theorem p_subset_np {L : Language} (hL : inP L) : inNP L := by
  obtain ⟨p, hp_poly, h_circuits⟩ := hL
  -- The verifier V: V(m)(inp) = L(m/2)(inp restricted to first m/2 bits)
  refine ⟨fun m inp => L (m / 2) (fun i => inp ⟨i.val, by have := i.isLt; omega⟩),
          ⟨fun m => p (m / 2) + 1, poly_half hp_poly, fun m => ?_⟩,
          fun n inp => ?_⟩
  · -- V ∈ P: at size m, use liftCircuit or liftCircuitTo
    by_cases h_even : m % 2 = 0
    · -- m is even: m = 2k for some k
      have : ∃ k, m = 2 * k := by
        use m / 2
        omega
      obtain ⟨k, hk⟩ := this
      subst hk
      obtain ⟨c, hc_size, hc_correct⟩ := h_circuits k
      use liftCircuit c
      constructor
      · -- circuitSize (liftCircuit c) ≤ p (m / 2) + 1
        have h_div : (2 * k) / 2 = k := by omega
        have h_size : circuitSize (liftCircuit c) = circuitSize c := liftCircuit_size c
        rw [h_size]
        have : (fun m => p (m / 2) + 1) (2 * k) = p k + 1 := by
          simp [h_div]
        rw [this]
        omega
      · -- evalCircuit (liftCircuit c) inp = true ↔ V (2 * k) inp
        intro inp
        have h_div : (2 * k) / 2 = k := by omega
        -- TODO: Need well-formedness for c
        have h_wf : IsWellFormed c := by
          sorry
        have h_eval := liftCircuit_eval c inp h_wf
        rw [h_eval]
        -- TODO: Use verifier_iff or similar to relate L ((2*k)/2) f' and L k f
        sorry
    · -- m is odd: m = 2k + 1 for some k
      have : ∃ k, m = 2 * k + 1 := by
        use m / 2
        omega
      obtain ⟨k, hk⟩ := this
      subst hk
      -- For odd m, use liftCircuitTo to lift circuit for size k to size 2k+1
      obtain ⟨c, hc_size, hc_correct⟩ := h_circuits k
      have h_le : k ≤ 2 * k + 1 := by omega
      use liftCircuitTo h_le c
      constructor
      · -- circuitSize (liftCircuitTo h_le c) ≤ p (m / 2) + 1
        have h_size : circuitSize (liftCircuitTo h_le c) = circuitSize c := liftCircuitTo_size h_le c
        rw [h_size]
        have h_div : (2 * k + 1) / 2 = k := by omega
        have : (fun m => p (m / 2) + 1) (2 * k + 1) = p k + 1 := by
          simp [h_div]
        rw [this]
        omega
      · -- evalCircuit (liftCircuitTo h_le c) inp = true ↔ V (2*k+1) inp
        intro inp
        -- TODO: Need a version of liftCircuit_eval for liftCircuitTo
        sorry
  · -- Witness direction: use verifier_iff
    constructor
    · -- L n inp → ∃ w, V (2*n) (combined inp w)
      intro hL_n
      exact ⟨fun _ => false, (verifier_iff L n inp (fun _ => false)).mpr hL_n⟩
    · -- ∃ w, V (2*n) (combined inp w) → L n inp
      intro ⟨w, hV⟩
      exact (verifier_iff L n inp w).mp hV

end PVsNp.PSubsetNP
-- Test
