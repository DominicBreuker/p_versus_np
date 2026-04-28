-- P vs NP via Circuit Complexity Lower Bounds
-- Idea: If NP-complete problems require superpolynomial circuits, then P ≠ NP.
-- Status: Fixed evalCircuit, added IsPolynomial, fixed inNP witness encoding.

-- Import shared library definitions
import PVsNp.Lib.Utils

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

/-- A circuit with a single Const true node evaluates to true. -/
lemma evalCircuit_const_true :
    let c : BoolCircuit 0 := {
      nodes := #[{ gate := Gate.Const true, children := [] }]
      output := 0
    }
    evalCircuit c (fun i => false) = true := by
  simp [evalCircuit, evalNode]
  rfl

/-- A circuit with a single Const false node evaluates to false. -/
lemma evalCircuit_const_false :
    let c : BoolCircuit 0 := {
      nodes := #[{ gate := Gate.Const false, children := [] }]
      output := 0
    }
    evalCircuit c (fun i => false) = false := by
  simp [evalCircuit, evalNode]
  rfl

/-- A circuit with a single Var node (input 0) evaluates to the input value.
    Requires n > 0. -/
lemma evalCircuit_var_zero {n : Nat} (hn : n > 0) (inp : Fin n → Bool) :
    let c : BoolCircuit n := {
      nodes := #[{ gate := Gate.Var 0, children := [] }]
      output := 0
    }
    evalCircuit c inp = inp ⟨0, hn⟩ := by
  simp [evalCircuit, evalNode, hn]

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
-- Main conjecture
-- ---------------------------------------------------------------------------

/-- P ≠ NP: there exists a language in NP not in P -/
theorem p_neq_np : ∃ L : Language, inNP L ∧ ¬ inP L := by
  sorry

end PVsNp.CircuitLowerBounds
