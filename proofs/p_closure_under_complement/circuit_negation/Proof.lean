-- P is Closed Under Complement — circuit negation approach
-- Goal: if L ∈ P then complement(L) ∈ P.
-- Strategy: add a NOT gate at the output of every circuit in the P-family.
-- Status: stub — poly_succ proven; negateCircuit_eval has sorry pending Array lemma work.

namespace PVsNpLib

/- A function is polynomial if it is bounded by c * n^k + c for some constants -/
def IsPolynomial (p : Nat -> Nat) : Prop := ∃ k c : Nat, ∀ n, p n ≤ c * n ^ k + c

end PVsNpLib

open PVsNpLib

namespace PVsNp.PClosedUnderComplement

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

-- ---------------------------------------------------------------------------
-- Complement language
-- ---------------------------------------------------------------------------

/-- The complement of a language: inputs not in L -/
def complement (L : Language) : Language := fun n inp => ¬ L n inp

-- ---------------------------------------------------------------------------
-- Circuit negation: add a NOT gate at the output
-- ---------------------------------------------------------------------------

/-- Wrap a circuit with a NOT gate at the output.
    The NOT node has child = c.output; the new output index = c.nodes.size. -/
def negateCircuit {n : Nat} (c : BoolCircuit n) : BoolCircuit n :=
  let notNode : CircuitNode := { gate := Gate.Not, children := [c.output] }
  { nodes := c.nodes.push notNode, output := c.nodes.size }

/-- Negation increases size by exactly 1 -/
theorem negateCircuit_size {n : Nat} (c : BoolCircuit n) :
    circuitSize (negateCircuit c) = circuitSize c + 1 := by
  simp [negateCircuit, circuitSize]

/-- Negation flips the output bit.
    Proof plan:
    1. Let vals := c.nodes.foldl (fun acc nd => acc.push (evalNode inp acc nd)) #[].
       Note vals.size = c.nodes.size by Array.foldl_size (or induction).
    2. By Array.foldl_push:
       (c.nodes.push notNode).foldl ... #[] = vals.push (evalNode inp vals notNode).
    3. evalNode inp vals notNode  -- Gate.Not, children = [c.output]
       = !(vals.getD c.output false) = !(evalCircuit c inp).
    4. (vals.push x).getD vals.size false = x  (use Array.size_push and Array.getD).
    Key Lean4 array lemmas to look up:
    - Array.foldl_push
    - Array.size_foldl (or induction to show vals.size = c.nodes.size)
    - Array.getD_push_eq or Array.get_push_eq -/
theorem negateCircuit_eval {n : Nat} (c : BoolCircuit n) (inp : Fin n → Bool) :
    evalCircuit (negateCircuit c) inp = !(evalCircuit c inp) := by
  sorry

-- ---------------------------------------------------------------------------
-- Polynomial bound: size + 1 is polynomial if size was polynomial
-- ---------------------------------------------------------------------------

/-- size + 1 is polynomial if size was polynomial -/
theorem poly_succ {p : Nat → Nat} (hp : IsPolynomial p) : IsPolynomial (fun n => p n + 1) := by
  obtain ⟨k, c, hpc⟩ := hp
  exact ⟨k, c + 1, fun n => by have := hpc n; omega⟩

-- ---------------------------------------------------------------------------
-- Main theorem
-- ---------------------------------------------------------------------------

/-- P is closed under complement: if L ∈ P then complement(L) ∈ P -/
theorem p_closed_under_complement {L : Language} (hL : inP L) : inP (complement L) := by
  obtain ⟨p, hp_poly, h_circuits⟩ := hL
  refine ⟨fun n => p n + 1, poly_succ hp_poly, fun n => ?_⟩
  obtain ⟨c, h_size, h_eval⟩ := h_circuits n
  refine ⟨negateCircuit c, ?_, ?_⟩
  · rw [negateCircuit_size]; omega
  · intro inp
    rw [negateCircuit_eval]
    simp only [complement]
    constructor
    · intro h hL_n
      -- !(evalCircuit c inp) = true → evalCircuit c inp = false
      -- but h_eval says evalCircuit c inp = true when L n inp holds
      have hct := (h_eval inp).mpr hL_n
      simp [hct] at h
    · intro hcompl
      -- ¬ L n inp → evalCircuit c inp = false → !(false) = true
      cases heq : evalCircuit c inp with
      | true =>
          exact absurd ((h_eval inp).mp heq) hcompl
      | false =>
          simp

end PVsNp.PClosedUnderComplement
