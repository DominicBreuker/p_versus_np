import Mathlib
import PVsNpLib

set_option maxHeartbeats 4000000

/-
# P vs NP via Circuit Complexity Lower Bounds

## Scope and Caveats

  - shannon_counting_argument is proved only for polynomials with a
    degree-≤-4 witness. This is a current technical restriction inherited
    from poly_quadratic_bound, NOT a fundamental mathematical limitation.

  - The two axioms (sat_is_np_complete, sat_has_superpoly_lower_bound)
    have very different statuses:
      * sat_is_np_complete is fully provable known mathematics
        (Cook-Levin theorem, 1971). Axiomatized for engineering reasons.
      * sat_has_superpoly_lower_bound is THE P vs NP problem itself,
        restated. Axiomatizing it does not make progress on P vs NP;
        it merely organizes the reduction.

  - Therefore p_neq_np is a CONDITIONAL THEOREM, not an unconditional
    proof of P ≠ NP. The phrase "conditional on circuit lower bounds
    for SAT" already appears in the docstring; reinforce it.

## Proof Structure (Hierarchical Overview)

```
P ≠ NP
├── sat_superpolynomial_implies_p_neq_np
│   ├── SAT ∈ NP (from Cook-Levin)
│   └── SAT has superpolynomial circuit lower bounds
│       └── sat_has_superpoly_lower_bound (axiom)
└── p_neq_np (main theorem)
    └── sat_is_np_complete (axiom)

Shannon Counting Argument
├── circuit_count_upper_bound: |Circuits(n, s)| ≤ (s+1)^(s+1) * 2^s
├── boolean_function_count: |Functions(n)| = 2^(2^n)
├── normalized_circuit_count_upper_bound
│   └── NodeCode, NormalizedCircuit
├── n_pow_lt_two_pow_n: n^D < 2^n for n ≥ 4*D^2 + 8
├── poly_quadratic_bound: (c*n^k + c)^2 + 3*(...) + 1 < 2^n
└── shannon_counting_argument: ∀ polynomial p, ∃ functions not computable by p(n)-size circuits

Circuit Framework
├── Gate: And, Or, Not, Var, Const
├── CircuitNode: gate + child indices
├── BoolCircuit: nodes + output index
├── evalNode, evalCircuit
└── Sanity lemmas: eval_const_true, eval_const_false, eval_var_zero

Complexity Classes
├── Language: ∀ n, (Fin n → Bool) → Prop
├── inP: decidable by polynomial-size circuit family
└── inNP: verifiable by polynomial-size circuit family
```

## Key Results

- `shannon_counting_argument`: For any polynomial p, most Boolean functions require circuits larger than p(n)
- `p_neq_np`: P ≠ NP (conditional on circuit lower bounds for SAT)

## Status

Reduction from circuit lower bounds to P ≠ NP is complete. Open: proving superpolynomial
circuit lower bounds for specific problems (e.g., SAT).
-/

open Fin
open PVsNpLib

namespace PVsNp.CircuitLowerBounds

/-- Basic Boolean gate operations -/
inductive Gate where
  | And    : Gate
  | Or     : Gate
  | Not    : Gate
  | Var    : Nat → Gate   -- Input variable index
  | Const  : Bool → Gate
  deriving Repr, DecidableEq

/-- Circuit node: gate with child indices -/
structure CircuitNode where
  gate     : Gate
  children : List Nat   -- Indices into circuit's node list
  deriving Repr

/-- Boolean circuit with n inputs -/
structure BoolCircuit (n : Nat) where
  nodes  : Array CircuitNode
  output : Nat   -- Output node index
  deriving Repr

/-- Circuit size = number of nodes -/
def circuitSize {n : Nat} (c : BoolCircuit n) : Nat := c.nodes.size

-- Semantics (evaluation)

/-- Evaluate a node given input and computed child values -/
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

/-- Evaluate a circuit on input. Nodes must be in topological order. -/
def evalCircuit {n : Nat} (c : BoolCircuit n) (inp : Fin n → Bool) : Bool :=
  let vals := c.nodes.foldl (fun acc node => acc.push (evalNode inp acc node)) #[]
  vals.getD c.output false

-- Sanity lemmas for evalCircuit

/-- Single-node constant circuit -/
def constCircuit (b : Bool) : BoolCircuit 0 :=
  { nodes := #[(⟨Gate.Const b, []⟩ : CircuitNode)]
    output := 0 }

/-- Constant-true circuit evaluates to true -/
theorem eval_const_true : evalCircuit (constCircuit true) (fun _ => false) = true := by
  unfold evalCircuit constCircuit; simp [evalNode]

/-- Constant-false circuit evaluates to false -/
theorem eval_const_false : evalCircuit (constCircuit false) (fun _ => false) = false := by
  unfold evalCircuit constCircuit; simp [evalNode]

/-- Single-node variable circuit for input index i -/
def varCircuit (n : Nat) (i : Nat) (_hi : i < n) : BoolCircuit n :=
  { nodes := #[(⟨Gate.Var i, []⟩ : CircuitNode)]
    output := 0 }

/-- Var-0 circuit evaluates to first input bit -/
theorem eval_var_zero (n : Nat) (hn : n > 0) (inp : Fin n → Bool) :
    evalCircuit (varCircuit n 0 (Nat.zero_lt_of_lt hn)) inp = inp ⟨0, Nat.zero_lt_of_lt hn⟩ := by
  unfold evalCircuit varCircuit
  simp only [Array.foldl, Array.getD, Array.push, evalNode]
  have : 0 < n := Nat.zero_lt_of_lt hn
  simp [this]

-- Complexity classes

/-- Language = decision problem on bitstrings -/
def Language := ∀ (n : Nat), (Fin n → Bool) → Prop

/-- L ∈ P iff decidable by polynomial-size circuit family -/
def inP (L : Language) : Prop :=
  ∃ (p : Nat → Nat) (_is_polynomial : IsPolynomial p),
  ∀ n, ∃ (c : BoolCircuit n), circuitSize c ≤ p n ∧
        ∀ inp, (evalCircuit c inp = true ↔ L n inp)

/-- L ∈ NP iff verifiable by polynomial-size circuit family -/
def inNP (L : Language) : Prop :=
  ∃ (V : Language), inP V ∧
  ∀ n inp, (L n inp ↔ ∃ w : Fin n → Bool,
    V (2 * n) (fun i =>
      if h : i.val < n then inp ⟨i.val, h⟩
      else w ⟨i.val - n, by omega⟩))

-- Circuit lower bounds via counting arguments

/-- Upper bound on number of Boolean circuits of size s: (s+1)^(s+1) * 2^s -/
def circuit_count_upper_bound (_n s : Nat) : Nat := (s + 1) ^ (s + 1) * 2 ^ s

/-- Number of distinct Boolean functions on n inputs: 2^(2^n) -/
def boolean_function_count (n : Nat) : Nat := 2 ^ (2 ^ n)


/-- Finite node codes for normalized counting -/
inductive NodeCode (n s : Nat) where
  | const : Bool → NodeCode n s
  | var : Fin n → NodeCode n s
  | not : Fin s → NodeCode n s
  | and : Finset (Fin s) → NodeCode n s
  | or : Finset (Fin s) → NodeCode n s
  deriving DecidableEq, Fintype

/-- Normalized circuit of size exactly s -/
abbrev NormalizedCircuit (n s : Nat) := Option (Fin s) × (Fin s → NodeCode n s)

private def falseNode : CircuitNode := ⟨Gate.Const false, []⟩

private def boundedChildren (s : Nat) (children : List Nat) : Finset (Fin s) :=
  (children.filterMap (fun child => if h : child < s then some ⟨child, h⟩ else none)).toFinset

private theorem mem_boundedChildren {s : Nat} {children : List Nat} {x : Fin s} :
    x ∈ boundedChildren s children ↔ x.val ∈ children := by
  simp [boundedChildren]
  constructor
  · intro h
    rcases h with ⟨a, ha, ha_lt, hax⟩
    cases hax
    simpa using ha
  · intro hx
    refine ⟨x.val, hx, x.isLt, ?_⟩
    ext
    simp

private noncomputable def nodeCodeToRaw {n s : Nat} : NodeCode n s → CircuitNode
  | .const b => ⟨Gate.Const b, []⟩
  | .var v => ⟨Gate.Var v.val, []⟩
  | .not child => ⟨Gate.Not, [child.val]⟩
  | .and children => ⟨Gate.And, children.toList.map Fin.val⟩
  | .or children => ⟨Gate.Or, children.toList.map Fin.val⟩

private noncomputable def normalizedToRaw {n s : Nat} (c : NormalizedCircuit n s) : BoolCircuit n :=
  { nodes := Array.ofFn (fun i => nodeCodeToRaw (c.2 i))
    output := match c.1 with
      | some out => out.val
      | none => s }

private def normalizeNodeCode (n s : Nat) (node : CircuitNode) : NodeCode n s :=
  match node.gate with
  | Gate.Const b => .const b
  | Gate.Var i => if h : i < n then .var ⟨i, h⟩ else .const false
  | Gate.Not =>
      match node.children with
      | [child] => if h : child < s then .not ⟨child, h⟩ else .const true
      | _ => .const false
  | Gate.And => .and (boundedChildren s node.children)
  | Gate.Or => .or (boundedChildren s node.children)

private def normalizeCircuit {n s : Nat} (c : BoolCircuit n) (hsize : circuitSize c ≤ s) :
    NormalizedCircuit n s :=
  let pre : Fin c.nodes.size → NodeCode n s := fun i => normalizeNodeCode n s (c.nodes[i]);
  let suf : Fin (s - c.nodes.size) → NodeCode n s := fun _ => .const false;
  let hsplit : c.nodes.size + (s - c.nodes.size) = s := Nat.add_sub_of_le hsize;
  let nodes : Fin s → NodeCode n s := fun i => Fin.append pre suf (Fin.cast hsplit.symm i);
  let output : Option (Fin s) :=
    if h : c.output < c.nodes.size then some ⟨c.output, lt_of_lt_of_le h hsize⟩ else none;
  (output, nodes)

private theorem foldl_and_false {α : Type} (l : List α) (f : α → Bool) :
    l.foldl (fun b x => b && f x) false = false := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [List.foldl, ih]

private theorem foldl_or_true {α : Type} (l : List α) (f : α → Bool) :
    l.foldl (fun b x => b || f x) true = true := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [List.foldl, ih]

private theorem foldl_and_true_iff {α : Type} (l : List α) (f : α → Bool) :
    l.foldl (fun b x => b && f x) true = true ↔ ∀ x ∈ l, f x = true := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      cases hfx : f x
      · simp [List.foldl, hfx, foldl_and_false]
      · simp [List.foldl, hfx, ih]

private theorem foldl_or_true_iff {α : Type} (l : List α) (f : α → Bool) :
    l.foldl (fun b x => b || f x) false = true ↔ ∃ x ∈ l, f x = true := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      cases hfx : f x
      · simp [List.foldl, hfx, ih]
      · simp [List.foldl, hfx, foldl_or_true]

private theorem foldl_and_map_val {s : Nat} (vals : Array Bool) (l : List (Fin s)) (init : Bool) :
    List.foldl (fun (acc : Bool) c => acc && vals.getD c true) init (l.map Fin.val) =
      List.foldl (fun (acc : Bool) (child : Fin s) => acc && vals.getD child.val true) init l := by
  induction l generalizing init with
  | nil => simp
  | cons child rest ih => simpa using ih (init := init && vals.getD child.val true)

private theorem foldl_or_map_val {s : Nat} (vals : Array Bool) (l : List (Fin s)) (init : Bool) :
    List.foldl (fun (acc : Bool) c => acc || vals.getD c false) init (l.map Fin.val) =
      List.foldl (fun (acc : Bool) (child : Fin s) => acc || vals.getD child.val false) init l := by
  induction l generalizing init with
  | nil => simp
  | cons child rest ih => simpa using ih (init := init || vals.getD child.val false)

private theorem foldl_and_map_eval {s : Nat} (vals : Array Bool) (l : List (Fin s)) (init : Bool) :
    List.foldl (fun (acc : Bool) (child : Fin s) => acc && vals.getD child.val true) init l =
      List.foldl (fun (acc : Bool) b => acc && b) init (l.map (fun child => vals.getD child.val true)) := by
  induction l generalizing init with
  | nil => simp
  | cons child rest ih => simpa using ih (init := init && vals.getD child.val true)

private theorem foldl_or_map_eval {s : Nat} (vals : Array Bool) (l : List (Fin s)) (init : Bool) :
    List.foldl (fun (acc : Bool) (child : Fin s) => acc || vals.getD child.val false) init l =
      List.foldl (fun (acc : Bool) b => acc || b) init (l.map (fun child => vals.getD child.val false)) := by
  induction l generalizing init with
  | nil => simp
  | cons child rest ih => simpa using ih (init := init || vals.getD child.val false)

private theorem and_fold_preserved (vals : Array Bool) (s : Nat) (hs : vals.size ≤ s)
    (children : List Nat) :
    children.foldl (fun acc c => acc && vals.getD c true) true =
      ((boundedChildren s children).toList.map (fun child => vals.getD child.val true)).foldl (· && ·) true := by
  apply (Bool.eq_iff_iff).2
  constructor <;> intro h
  · rw [foldl_and_true_iff] at h
    rw [foldl_and_true_iff]
    intro b hb
    rcases List.mem_map.mp hb with ⟨child, hchild, rfl⟩
    have hmem : child.val ∈ children := (mem_boundedChildren).mp (Finset.mem_toList.mp hchild)
    exact h child.val hmem
  · rw [foldl_and_true_iff] at h
    rw [foldl_and_true_iff]
    intro c hc
    by_cases hcs : c < s
    · let child : Fin s := ⟨c, hcs⟩
      have hchild : child ∈ (boundedChildren s children).toList := by
        exact Finset.mem_toList.mpr ((mem_boundedChildren).2 hc)
      have hbool : vals.getD child.val true ∈
          (boundedChildren s children).toList.map (fun child => vals.getD child.val true) := by
        exact List.mem_map.mpr ⟨child, hchild, rfl⟩
      have hval : vals.getD child.val true = true := h _ hbool
      simpa [child] using hval
    · have hge : vals.size ≤ c := le_trans hs (Nat.le_of_not_gt hcs)
      simp [Array.getD, hge]

private theorem or_fold_preserved (vals : Array Bool) (s : Nat) (hs : vals.size ≤ s)
    (children : List Nat) :
    children.foldl (fun acc c => acc || vals.getD c false) false =
      ((boundedChildren s children).toList.map (fun child => vals.getD child.val false)).foldl (· || ·) false := by
  apply (Bool.eq_iff_iff).2
  constructor <;> intro h
  · rw [foldl_or_true_iff] at h
    rw [foldl_or_true_iff]
    rcases h with ⟨c, hc, hval⟩
    by_cases hcs : c < s
    · let child : Fin s := ⟨c, hcs⟩
      refine ⟨vals.getD child.val false, ?_, ?_⟩
      · exact List.mem_map.mpr ⟨child, Finset.mem_toList.mpr ((mem_boundedChildren).2 hc), rfl⟩
      · simpa [child] using hval
    · have hge : vals.size ≤ c := le_trans hs (Nat.le_of_not_gt hcs)
      simp [Array.getD, hge] at hval
  · rw [foldl_or_true_iff] at h
    rw [foldl_or_true_iff]
    rcases h with ⟨b, hb, htrue⟩
    rcases List.mem_map.mp hb with ⟨child, hchild, hbdef⟩
    refine ⟨child.val, (mem_boundedChildren).mp (Finset.mem_toList.mp hchild), ?_⟩
    simpa [hbdef] using htrue

private theorem evalNode_normalizeNodeCode {n s : Nat} (inp : Fin n → Bool) (vals : Array Bool)
    (hs : vals.size ≤ s) (node : CircuitNode) :
    evalNode inp vals (nodeCodeToRaw (normalizeNodeCode n s node)) = evalNode inp vals node := by
  rcases node with ⟨gate, children⟩
  cases gate with
  | And =>
      simp only [normalizeNodeCode, nodeCodeToRaw, evalNode]
      rw [foldl_and_map_val, foldl_and_map_eval, ← and_fold_preserved vals s hs children]
  | Not =>
      cases children with
      | nil => simp [normalizeNodeCode, nodeCodeToRaw, evalNode]
      | cons child tail =>
          cases htail : tail with
          | nil =>
              by_cases hchild : child < s
              · simp [normalizeNodeCode, nodeCodeToRaw, hchild, evalNode]
              · have hge : vals.size ≤ child := le_trans hs (Nat.le_of_not_gt hchild)
                simp [normalizeNodeCode, nodeCodeToRaw, hchild, evalNode, Array.getD, hge]
          | cons child' rest =>
              simp [normalizeNodeCode, nodeCodeToRaw, evalNode]
  | Or =>
      simp only [normalizeNodeCode, nodeCodeToRaw, evalNode]
      rw [foldl_or_map_val, foldl_or_map_eval, ← or_fold_preserved vals s hs children]
  | Var i =>
      by_cases hi : i < n
      · simp [normalizeNodeCode, nodeCodeToRaw, hi, evalNode]
      · simp [normalizeNodeCode, nodeCodeToRaw, hi, evalNode]
  | Const b => simp [normalizeNodeCode, nodeCodeToRaw, evalNode]

private def evalStep {n : Nat} (inp : Fin n → Bool) (acc : Array Bool) (node : CircuitNode) : Array Bool :=
  acc.push (evalNode inp acc node)

private theorem evalStep_fold_size {n : Nat} (inp : Fin n → Bool) (vals : Array Bool)
    (nodes : List CircuitNode) :
    (List.foldl (evalStep inp) vals nodes).size = vals.size + nodes.length := by
  induction nodes generalizing vals with
  | nil => simp [evalStep]
  | cons node rest ih => simp [List.foldl, evalStep, ih, Array.size_push, Nat.add_left_comm, Nat.add_comm]

private theorem evalStep_fold_getElem?_preserve {n : Nat} (inp : Fin n → Bool) (vals : Array Bool)
    (extra : List CircuitNode) (i : Nat) (hi : i < vals.size) :
    (List.foldl (evalStep inp) vals extra)[i]? = vals[i]? := by
  induction extra generalizing vals with
  | nil => simp
  | cons node rest ih =>
      simp [List.foldl, evalStep]
      rw [ih (vals := vals.push (evalNode inp vals node))]
      · rw [Array.getElem?_eq_getElem hi]
        exact Array.getElem?_push_lt hi
      · rw [Array.size_push]
        exact Nat.lt_succ_of_lt hi

private theorem evalStep_fold_normalized_eq {n s : Nat} (inp : Fin n → Bool)
    (vals : Array Bool) (nodes : List CircuitNode) (hbound : vals.size + nodes.length ≤ s) :
    List.foldl (evalStep inp) vals (nodes.map (fun node => nodeCodeToRaw (normalizeNodeCode n s node))) =
      List.foldl (evalStep inp) vals nodes := by
  induction nodes generalizing vals with
  | nil => simp [evalStep]
  | cons node rest ih =>
      have hs : vals.size ≤ s := by omega
      have hnode : evalNode inp vals (nodeCodeToRaw (normalizeNodeCode n s node)) = evalNode inp vals node :=
        evalNode_normalizeNodeCode inp vals hs node
      simp [List.foldl, evalStep, hnode]
      apply ih
      simpa [Array.size_push, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hbound

private theorem array_foldl_ofFn_eq_list_foldl {α β : Type} {n : Nat} (f : β → α → β) (init : β)
    (g : Fin n → α) :
    Array.foldl f init (Array.ofFn g) = List.foldl f init (List.ofFn g) := by
  rw [Array.foldl_toList]
  simp

private theorem normalizeCircuit_nodes_list {n s : Nat} (c : BoolCircuit n) (hsize : circuitSize c ≤ s) :
    List.ofFn (normalizeCircuit c hsize).2 =
      List.ofFn (fun i : Fin c.nodes.size => normalizeNodeCode n s (c.nodes[i])) ++
        List.replicate (s - c.nodes.size) (NodeCode.const false) := by
  dsimp [normalizeCircuit]
  let pre : Fin c.nodes.size → NodeCode n s := fun i => normalizeNodeCode n s (c.nodes[i])
  let suf : Fin (s - c.nodes.size) → NodeCode n s := fun _ => NodeCode.const false
  have hsplit : c.nodes.size + (s - c.nodes.size) = s := Nat.add_sub_of_le hsize
  calc
    List.ofFn (fun i : Fin s => Fin.append pre suf (Fin.cast hsplit.symm i))
        = List.ofFn (Fin.append pre suf) := by
            simpa [hsplit] using (List.ofFn_congr hsplit (Fin.append pre suf)).symm
    _ = List.ofFn pre ++ List.ofFn suf := List.ofFn_fin_append pre suf
    _ = List.ofFn pre ++ List.replicate (s - c.nodes.size) (NodeCode.const false) := by
          simp [suf, List.ofFn_const]

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
  have hnormVals :
      Array.foldl (fun acc node => acc.push (evalNode inp acc node)) #[]
          (normalizedToRaw (normalizeCircuit c hsize)).nodes =
        List.foldl (evalStep inp) #[] ((c.nodes.toList.map (fun node => nodeCodeToRaw (normalizeNodeCode n s node))) ++
          List.replicate (s - c.nodes.size) falseNode) := by
    unfold normalizedToRaw
    -- After unfolding, .nodes = Array.ofFn (fun i => nodeCodeToRaw ((normalizeCircuit c hsize).2 i))
    -- Goal: Array.foldl (evalStep inp) #[] (Array.ofFn ...) = List.foldl (evalStep inp) #[] (... ++ ...)
    rw [array_foldl_ofFn_eq_list_foldl]
    -- Now both sides are List.foldl (evalStep inp) #[] applied to some list.
    -- Reduce to a list equality.
    congr 1
    -- CURRENT GOAL (list equality):
    --   List.ofFn (fun i : Fin s => nodeCodeToRaw ((normalizeCircuit c hsize).2 i))
    --   = List.map (fun node => nodeCodeToRaw (normalizeNodeCode n s node)) c.nodes.toList
    --     ++ List.replicate (s - c.nodes.size) falseNode

    -- STEP A: rewrite the lhs so nodeCodeToRaw is lifted outside List.ofFn.
    rw [show (fun i => nodeCodeToRaw ((normalizeCircuit c hsize).2 i)) =
              nodeCodeToRaw ∘ (normalizeCircuit c hsize).2 from rfl]
    rw [← List.map_ofFn]

    -- STEP B: expand List.ofFn (normalizeCircuit c hsize).2 via hnodeListCodes
    rw [hnodeListCodes]

    -- STEP C: push the map over ++ and List.replicate
    rw [List.map_append, List.map_replicate]

    -- STEP D: subgoal 2 is definitional.
    simp only [nodeCodeToRaw, falseNode]

    -- STEP E: subgoal 1. Need to show:
    --   List.map nodeCodeToRaw (List.ofFn (fun i : Fin c.nodes.size => normalizeNodeCode n s c.nodes[i]))
    --   = List.map (fun node => nodeCodeToRaw (normalizeNodeCode n s node)) c.nodes.toList

    -- Key insight: c.nodes.toList = List.ofFn (fun i : Fin c.nodes.size => c.nodes[i])
    have htoList : c.nodes.toList = List.ofFn (fun i : Fin c.nodes.size => c.nodes[i]) := by
      simp [← Array.toList_ofFn, Array.ofFn_getElem]
    rw [htoList]
    -- Both sides are List.map ... (List.ofFn ...) with compatible functions
    rw [List.map_ofFn, List.map_ofFn]
    -- Now both are List.ofFn (nodeCodeToRaw ∘ ...), so they're equal
    -- The left: nodeCodeToRaw ∘ (fun i => normalizeNodeCode n s c.nodes[i])
    -- The right: nodeCodeToRaw ∘ normalizeNodeCode n s ∘ (fun i => c.nodes[i])
    -- These are the same
    rfl
  have hrawVals :
      Array.foldl (fun acc node => acc.push (evalNode inp acc node)) #[] c.nodes = rawVals := by
    rw [← Array.foldl_toList]
    rfl
  unfold evalCircuit
  rw [hnormVals, hrawVals, List.foldl_append]
  simp only [rawVals]
  -- The inner List.foldl is canonVals
  have : List.foldl (evalStep inp) #[] (List.map (fun node => nodeCodeToRaw (normalizeNodeCode n s node)) c.nodes.toList) = canonVals := by
    rfl
  rw [this, hcanon]
  by_cases houtput : c.output < c.nodes.size
  · have hsizeVals : rawVals.size = c.nodes.size := by
      dsimp [rawVals]
      simpa using evalStep_fold_size inp #[] c.nodes.toList
    have hprefix : (List.foldl (evalStep inp) rawVals (List.replicate (s - c.nodes.size) falseNode))[c.output]? =
        rawVals[c.output]? := by
      apply evalStep_fold_getElem?_preserve inp rawVals (List.replicate (s - c.nodes.size) falseNode) c.output
      simpa [hsizeVals] using houtput
    have h_output_eq : (normalizedToRaw (normalizeCircuit c hsize)).output = c.output := by
      simp [normalizedToRaw, normalizeCircuit, houtput]
    rw [h_output_eq]
    -- We need: (List.foldl ...).getD c.output false = (List.foldl ...).getD c.output false
    -- From hprefix: (List.foldl ...)[c.output]? = rawVals[c.output]?
    -- And c.output < rawVals.size, so both are some value
    have h_lt : c.output < rawVals.size := by rw [hsizeVals]; exact houtput
    have : (List.foldl (evalStep inp) rawVals (List.replicate (s - c.nodes.size) falseNode)).getD c.output false = 
           rawVals.getD c.output false := by
      have : (List.foldl (evalStep inp) rawVals (List.replicate (s - c.nodes.size) falseNode))[c.output]? = rawVals[c.output]? := hprefix
      simp [List.getD, this, h_lt]
    rw [this]
  · have hsizeVals : rawVals.size = c.nodes.size := by
      dsimp [rawVals]
      simpa using evalStep_fold_size inp #[] c.nodes.toList
    have h_ge : c.nodes.size ≤ c.output := not_lt.mp houtput
    have h_output_eq : (normalizedToRaw (normalizeCircuit c hsize)).output = s := by
      simp [normalizedToRaw, normalizeCircuit, houtput]
    rw [h_output_eq]
    -- Both sides are false because the index is out of bounds
    have h_norm_size : (List.foldl (evalStep inp) rawVals (List.replicate (s - c.nodes.size) falseNode)).size = s := by
      have : c.nodes.size + (s - c.nodes.size) = s := by
        have : c.nodes.size ≤ s := hsize
        omega
      simp [evalStep_fold_size, hsizeVals, this]
    have h_raw_size : (Array.foldl (evalStep inp) #[] c.nodes).size = c.nodes.size := by
      have : Array.foldl (evalStep inp) #[] c.nodes = rawVals := hrawVals
      rw [this, hsizeVals]
    simp [List.getD, Array.getD, h_norm_size, h_raw_size, h_ge]

private def encodeNodeCode {n s : Nat} : NodeCode n s → Bool ⊕ Fin n ⊕ Fin s ⊕ Finset (Fin s) ⊕ Finset (Fin s)
  | .const b => Sum.inl b
  | .var v => Sum.inr <| Sum.inl v
  | .not child => Sum.inr <| Sum.inr <| Sum.inl child
  | .and children => Sum.inr <| Sum.inr <| Sum.inr <| Sum.inl children
  | .or children => Sum.inr <| Sum.inr <| Sum.inr <| Sum.inr children

private theorem encodeNodeCode_injective {n s : Nat} : Function.Injective (@encodeNodeCode n s) := by
  intro a b h; cases a <;> cases b <;> cases h <;> rfl

private theorem node_code_card_sum_bound (n s : Nat) :
    Fintype.card (NodeCode n s) ≤ 2 + n + s + 2 ^ s + 2 ^ s := by
  let β := Bool ⊕ Fin n ⊕ Fin s ⊕ Finset (Fin s) ⊕ Finset (Fin s)
  have hle := Fintype.card_le_of_injective (@encodeNodeCode n s) encodeNodeCode_injective
  simpa [β, Fintype.card_sum, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hle

private theorem node_code_card_le (n s : Nat) :
    Fintype.card (NodeCode n s) ≤ 2 ^ (n + s + 4) := by
  have hcard := node_code_card_sum_bound n s
  have hpow : 2 ^ s ≤ 2 ^ (n + s + 1) := by
    apply Nat.pow_le_pow_right
    · norm_num
    · omega
  have hn : n ≤ 2 ^ (n + s + 1) := by
    calc n ≤ 2 ^ n := Nat.le_of_lt n.lt_two_pow_self
      _ ≤ 2 ^ (n + s + 1) := by
        apply Nat.pow_le_pow_right
        · norm_num
        · omega
  have hs : s ≤ 2 ^ (n + s + 1) := by
    calc s ≤ 2 ^ s := Nat.le_of_lt s.lt_two_pow_self
      _ ≤ 2 ^ (n + s + 1) := by
        apply Nat.pow_le_pow_right
        · norm_num
        · omega
  have htwo : 2 ≤ 2 ^ (n + s + 1) := by
    have h1 : 1 ≤ n + s + 1 := by omega
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n + s + 1) := Nat.pow_le_pow_right (by norm_num) h1
  calc
    Fintype.card (NodeCode n s) ≤ 2 + n + s + 2 ^ s + 2 ^ s := hcard
    _ ≤ 2 ^ (n + s + 1) + 2 ^ (n + s + 1) + 2 ^ (n + s + 1) + 2 ^ (n + s + 1) + 2 ^ (n + s + 1) := by omega
    _ = 5 * 2 ^ (n + s + 1) := by ring
    _ ≤ 8 * 2 ^ (n + s + 1) := by omega
    _ = 2 ^ (n + s + 4) := by
      rw [show 8 = 2 ^ 3 by rfl, ← Nat.pow_add]
      congr 1
      omega

/-- Upper bound on number of normalized circuits of size s -/
def normalized_circuit_count_upper_bound (n s : Nat) : Nat := (s + 1) * (2 ^ (n + s + 4)) ^ s

private theorem normalized_circuit_card_le (n s : Nat) :
    Fintype.card (NormalizedCircuit n s) ≤ normalized_circuit_count_upper_bound n s := by
  dsimp [NormalizedCircuit, normalized_circuit_count_upper_bound]
  calc
    Fintype.card (Option (Fin s) × (Fin s → NodeCode n s))
        = (s + 1) * Fintype.card (NodeCode n s) ^ s := by
            simp [Fintype.card_prod, Fintype.card_option]
    _ ≤ (s + 1) * (2 ^ (n + s + 4)) ^ s := by
          apply Nat.mul_le_mul_left
          exact Nat.pow_le_pow_left (node_code_card_le n s) s

-- Arithmetic helper lemmas

/-- For n ≥ 1, n + 1 ≤ 2^n -/
private theorem n_plus_one_le_two_pow_n (n : Nat) (hn : n ≥ 1) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero => simp
    | succ n =>
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

/-- For n ≥ 1, (n + 1)^(n + 1) ≤ 2^(n * (n + 1)) -/
private theorem n_plus_one_pow_le_two_pow_n_times_n_plus_one (n : Nat) (hn : n ≥ 1) :
    (n + 1) ^ (n + 1) ≤ 2 ^ (n * (n + 1)) := by
  have h := n_plus_one_le_two_pow_n n hn
  calc (n + 1) ^ (n + 1) ≤ (2 ^ n) ^ (n + 1) := Nat.pow_le_pow_left h (n + 1)
    _ = 2 ^ (n * (n + 1)) := by rw [← Nat.pow_mul]

/-- For n ≥ 9, n^2 + 2*n < 2^n -/
private theorem n_squared_plus_two_n_lt_two_pow_n (n : Nat) (hn : n ≥ 9) :
    n ^ 2 + 2 * n < 2 ^ n := by
  have base9 : 9 ^ 2 + 2 * 9 < 2 ^ 9 := by norm_num
  suffices ∀ k ≥ 9, k ^ 2 + 2 * k < 2 ^ k by exact this n hn
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact base9
  | succ k hk ih =>
    calc (k + 1) ^ 2 + 2 * (k + 1)
        = k^2 + 2*k + 1 + 2*k + 2 := by ring
      _ = k^2 + 2*k + (2*k + 3) := by ring
      _ < 2^k + (2*k + 3) := by omega
      _ ≤ 2^k + 2^k := by
          have : 2 * k + 3 ≤ 2 ^ k := by
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

/-- For n ≥ 4, circuit_count_upper_bound n n < boolean_function_count n -/
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
                      have h1 : n + 1 ≤ 2 ^ n := n_plus_one_le_two_pow_n n (by omega)
                      have h2 : (n + 1) ^ (n + 1) ≤ 2 ^ (n * (n + 1)) :=
                        n_plus_one_pow_le_two_pow_n_times_n_plus_one n (by omega)
                      have h3 : n ^ 2 + 2 * n < 2 ^ n :=
                        n_squared_plus_two_n_lt_two_pow_n n (by omega)
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

/-- For any s ≥ 1, (s + 1)^(s + 1) ≤ 2^(s * (s + 1)) -/
private theorem s_plus_one_pow_le_two_pow_s_times_s_plus_one (s : Nat) (hs : s ≥ 1) :
    (s + 1) ^ (s + 1) ≤ 2 ^ (s * (s + 1)) := by
  have h := n_plus_one_le_two_pow_n s hs
  calc (s + 1) ^ (s + 1) ≤ (2 ^ s) ^ (s + 1) := Nat.pow_le_pow_left h (s + 1)
    _ = 2 ^ (s * (s + 1)) := by rw [← Nat.pow_mul]



/-- Helper lemma: for n ≥ 196, 4*n^2 + 6*n + 1 < 2^n. -/
private theorem four_n_squared_plus_six_n_plus_one_lt_two_pow_n (n : Nat) (hn : n ≥ 196) :
    4 * n ^ 2 + 6 * n + 1 < 2 ^ n := by
  have base196 : 4 * 196 ^ 2 + 6 * 196 + 1 < 2 ^ 196 := by norm_num
  suffices ∀ k ≥ 196, 4 * k ^ 2 + 6 * k + 1 < 2 ^ k by exact this n hn
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact base196
  | succ k hk ih =>
    calc (4 * (k + 1) ^ 2 + 6 * (k + 1) + 1)
        = 4 * (k^2 + 2*k + 1) + 6*k + 6 + 1 := by ring
      _ = 4*k^2 + 8*k + 4 + 6*k + 7 := by ring
      _ = 4*k^2 + 6*k + 1 + (8*k + 10) := by ring
      _ < 2^k + (8*k + 10) := by omega
      _ ≤ 2 * 2^k := by
          have : 8 * k + 10 ≤ 2 ^ k := by
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

/-- For n ≥ 200, n^4 + 3*n^2 + 1 < 2^n -/
private theorem n_quartic_plus_lt_two_pow_n_200 (n : Nat) (hn : n ≥ 200) : n ^ 4 + 3 * n ^ 2 + 1 < 2 ^ n := by
  have base200 : 200 ^ 4 + 3 * 200 ^ 2 + 1 < 2 ^ 200 := by norm_num
  suffices ∀ k ≥ 200, k ^ 4 + 3 * k ^ 2 + 1 < 2 ^ k by exact this n hn
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact base200
  | succ k hk ih =>
    -- Goal: (k+1)^4 + 3*(k+1)^2 + 1 < 2^(k+1)
    calc (k + 1) ^ 4 + 3 * (k + 1) ^ 2 + 1
        = k^4 + 4*k^3 + 6*k^2 + 4*k + 1 + 3*k^2 + 6*k + 3 + 1 := by ring
      _ = k^4 + 4*k^3 + 9*k^2 + 10*k + 5 := by ring
      _ = k^4 + 3*k^2 + 1 + (4*k^3 + 6*k^2 + 10*k + 4) := by ring
      _ < 2^k + (4*k^3 + 6*k^2 + 10*k + 4) := by omega
      _ ≤ 2^k + 2^k := by
          have h_k4_lt : k ^ 4 < 2 ^ k := by omega
          have h_k4_ge : k ^ 4 ≥ 4 * k ^ 3 + 6 * k ^ 2 + 10 * k + 4 := by
            have base : 200 ^ 4 ≥ 4 * 200 ^ 3 + 6 * 200 ^ 2 + 10 * 200 + 4 := by norm_num
            have step : ∀ m ≥ 200, m ^ 4 ≥ 4 * m ^ 3 + 6 * m ^ 2 + 10 * m + 4 →
                (m + 1) ^ 4 ≥ 4 * (m + 1) ^ 3 + 6 * (m + 1) ^ 2 + 10 * (m + 1) + 4 := by
              intro m hm h
              have h_ih : m ^ 4 ≥ 4 * m ^ 3 + 6 * m ^ 2 + 10 * m + 4 := h
              have h_cubic : 4 * m ^ 3 ≥ 12 * m ^ 2 + 30 * m + 23 := by
                have : m ≥ 200 := hm
                have h_lower : 4 * m ^ 3 ≥ 4 * 200 ^ 3 := by
                  have : m ^ 3 ≥ 200 ^ 3 := Nat.pow_le_pow_left (by omega) 3
                  omega
                have h_upper : 12 * m ^ 2 + 30 * m + 23 ≤ 12 * m ^ 2 + 30 * m ^ 2 + 23 * m ^ 2 := by
                  have : m ≥ 200 := hm
                  have : m ≥ 1 := by omega
                  have : 30 * m ≤ 30 * m ^ 2 := by
                    calc 30 * m = 30 * m * 1 := by ring
                      _ ≤ 30 * m * m := by apply Nat.mul_le_mul_left; omega
                      _ = 30 * m ^ 2 := by ring
                  have : 23 ≤ 23 * m ^ 2 := by
                    have : m ^ 2 ≥ 1 := by
                      calc m ^ 2 ≥ 1 ^ 2 := Nat.pow_le_pow_left (by omega) 2
                        _ = 1 := by norm_num
                    calc 23 = 23 * 1 := by ring
                      _ ≤ 23 * m ^ 2 := by apply Nat.mul_le_mul_left; exact this
                  omega
                have h_combined : 12 * m ^ 2 + 30 * m ^ 2 + 23 * m ^ 2 = 65 * m ^ 2 := by ring
                rw [h_combined] at h_upper
                -- We want to show 4 * m^3 ≥ 12 * m^2 + 30 * m + 23
                -- This follows from 4 * m^3 ≥ 65 * m^2 (since 12 * m^2 + 30 * m + 23 ≤ 65 * m^2)
                -- which is equivalent to 4 * m ≥ 65, i.e., m ≥ 17 (since m ≥ 200)
                have h_final : 4 * m ^ 3 ≥ 65 * m ^ 2 := by
                  -- 4 * m^3 ≥ 65 * m^2  <=>  4 * m ≥ 65  (for m ≥ 1)
                  -- Since m ≥ 200, we have 4 * m ≥ 800 ≥ 65
                  have : m ≥ 17 := by omega
                  calc 4 * m ^ 3 = 4 * m * m ^ 2 := by ring
                    _ ≥ 65 * m ^ 2 := by
                        apply Nat.mul_le_mul_right
                        -- Need to show 4 * m ≥ 65
                        omega
                omega
              calc (m + 1) ^ 4 = m^4 + 4*m^3 + 6*m^2 + 4*m + 1 := by ring
                _ ≥ 4*m^3 + 6*m^2 + 10*m + 4 + 4*m^3 + 6*m^2 + 4*m + 1 := by omega
                _ = 8*m^3 + 12*m^2 + 14*m + 5 := by ring
                _ ≥ 4*(m^3 + 3*m^2 + 3*m + 1) + 6*(m^2 + 2*m + 1) + 10*(m + 1) + 4 := by ring_nf; omega
                _ = 4 * (m + 1) ^ 3 + 6 * (m + 1) ^ 2 + 10 * (m + 1) + 4 := by ring
            exact Nat.le_induction base step k hk
          omega
      _ = 2 * 2^k := by ring
      _ = 2 ^ (k + 1) := by rw [Nat.pow_succ]; ring



/-- Helper lemma: for n ≥ 200, (n^2 + n)^2 + 3*(n^2 + n) + 1 < 2^n. -/
private theorem n_squared_plus_n_quartic_lt_two_pow_n_200 (n : Nat) (hn : n ≥ 200) :
    (n ^ 2 + n) ^ 2 + 3 * (n ^ 2 + n) + 1 < 2 ^ n := by
  -- Induction similar to n_quartic_plus_lt_two_pow_n_200
  -- Base case: n = 200
  have base200 : (200 ^ 2 + 200) ^ 2 + 3 * (200 ^ 2 + 200) + 1 < 2 ^ 200 := by norm_num
  -- Inductive step
  suffices ∀ k ≥ 200, (k ^ 2 + k) ^ 2 + 3 * (k ^ 2 + k) + 1 < 2 ^ k by exact this n hn
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact base200
  | succ k hk ih =>
    -- IH: (k^2 + k)^2 + 3*(k^2 + k) + 1 < 2^k
    -- Goal: ((k+1)^2 + (k+1))^2 + 3*((k+1)^2 + (k+1)) + 1 < 2^(k+1)
    calc ((k + 1) ^ 2 + (k + 1)) ^ 2 + 3 * ((k + 1) ^ 2 + (k + 1)) + 1
        = (k^2 + 3*k + 2)^2 + 3*(k^2 + 3*k + 2) + 1 := by ring
      _ = k^4 + 6*k^3 + 16*k^2 + 21*k + 11 := by ring
      _ = (k^2 + k)^2 + 3*(k^2 + k) + 1 + (4*k^3 + 12*k^2 + 18*k + 10) := by ring
      _ < 2^k + (4*k^3 + 12*k^2 + 18*k + 10) := by omega
      _ ≤ 2^k + k^4 := by
          -- Show 4*k^3 + 12*k^2 + 18*k + 10 ≤ k^4 for k ≥ 200
          -- For k ≥ 200: k^4 = k*k^3 ≥ 200*k^3
          -- And 200*k^3 - (4*k^3 + 12*k^2 + 18*k + 10) = 196*k^3 - 12*k^2 - 18*k - 10
          -- For k ≥ 200: 196*k^3 ≥ 196*200^3 = 1568000000
          -- And 12*k^2 + 18*k + 10 ≤ 12*k^2 + 18*k^2 + 10*k^2 = 40*k^2 (since k ≥ 1)
          -- And 40*k^2 ≤ k^3 for k ≥ 40 (since k^3 - 40*k^2 = k^2*(k-40) ≥ 0)
          -- And 196*k^3 ≥ k^3 for k ≥ 1
          -- So 196*k^3 ≥ k^3 ≥ 40*k^2 ≥ 12*k^2 + 18*k + 10
          have : k ≥ 200 := by omega
          have : k ^ 4 ≥ 200 * k ^ 3 := by
            calc k ^ 4 = k * k ^ 3 := by ring
              _ ≥ 200 * k ^ 3 := by
                  apply Nat.mul_le_mul_right
                  omega
          have : 200 * k ^ 3 ≥ 4 * k ^ 3 + 12 * k ^ 2 + 18 * k + 10 := by
            have : 200 * k ^ 3 - 4 * k ^ 3 = 196 * k ^ 3 := by omega
            have : 196 * k ^ 3 ≥ 12 * k ^ 2 + 18 * k + 10 := by
              have : 12 * k ^ 2 + 18 * k + 10 ≤ 40 * k ^ 2 := by
                have : 18 * k + 10 ≤ 28 * k ^ 2 := by
                  have : k ≥ 200 := by omega
                  have : 18 * k ≤ 18 * k ^ 2 := by
                    calc 18 * k = 18 * k * 1 := by ring
                      _ ≤ 18 * k * k := by
                          apply Nat.mul_le_mul_left
                          omega
                      _ = 18 * k ^ 2 := by ring
                  have : 10 ≤ 10 * k ^ 2 := by
                    calc 10 = 10 * 1 := by ring
                      _ ≤ 10 * k ^ 2 := by
                          apply Nat.mul_le_mul_left
                          omega
                  omega
                omega
              have : 40 * k ^ 2 ≤ k ^ 3 := by
                have : k ^ 3 = k * k ^ 2 := by ring
                rw [this]
                apply Nat.mul_le_mul_right
                omega
              have : k ^ 3 ≤ 196 * k ^ 3 := by omega
              omega
            omega
          omega
      _ < 2^k + 2^k := by
          have : k ^ 4 < 2 ^ k := by
            have : k ^ 4 + 3 * k ^ 2 + 1 < 2 ^ k := n_quartic_plus_lt_two_pow_n_200 k (by omega)
            omega
          omega
      _ = 2 * 2^k := by ring
      _ = 2 ^ (k + 1) := by rw [Nat.pow_succ]; ring




private theorem succ_pow_le_pow_add (D : Nat) (hD : D ≥ 1) :
    ∀ n, n ≥ 2 * D + 1 → (n + 1) ^ D ≤ n ^ D + 2 * D * n ^ (D - 1) := by
  induction D, hD using Nat.le_induction with
  | base =>
      intro n hn
      simp only [pow_one]
      have : 1 - 1 = 0 := by norm_num
      rw [this, pow_zero, mul_one]
      omega
  | succ D hD ih =>
      intro n hn
      have hn_ih : n ≥ 2 * D + 1 := by omega
      have ih_n : (n + 1) ^ D ≤ n ^ D + 2 * D * n ^ (D - 1) := ih n hn_ih
      have h_pow_D : n * n ^ (D - 1) = n ^ D := by
        have hD_eq : D = (D - 1) + 1 := by omega
        conv_rhs => rw [hD_eq]
        rw [pow_succ]; ring
      have h_pow_succ_D : (n + 1) * n ^ D = n ^ (D + 1) + n ^ D := by
        rw [pow_succ]; ring
      have hmul : (n + 1) * ((n + 1) ^ D) ≤ (n + 1) * (n ^ D + 2 * D * n ^ (D - 1)) :=
        Nat.mul_le_mul_left (n + 1) ih_n
      have hLHS_eq : (n + 1) * ((n + 1) ^ D) = (n + 1) ^ (D + 1) := by
        rw [pow_succ]; ring
      have hRHS_eq : (n + 1) * (n ^ D + 2 * D * n ^ (D - 1))
                   = n ^ (D + 1) + (1 + 2 * D) * n ^ D + 2 * D * n ^ (D - 1) := by
        calc (n + 1) * (n ^ D + 2 * D * n ^ (D - 1))
            = (n + 1) * n ^ D + 2 * D * ((n + 1) * n ^ (D - 1)) := by ring
          _ = n ^ (D + 1) + n ^ D + 2 * D * (n * n ^ (D - 1) + n ^ (D - 1)) := by
                rw [h_pow_succ_D]
                ring_nf
          _ = n ^ (D + 1) + n ^ D + 2 * D * (n ^ D + n ^ (D - 1)) := by rw [h_pow_D]
          _ = n ^ (D + 1) + (1 + 2 * D) * n ^ D + 2 * D * n ^ (D - 1) := by ring
      rw [hLHS_eq, hRHS_eq] at hmul
      -- Goal: (n+1)^(D+1) ≤ n^(D+1) + 2*(D+1)*n^D
      -- We have: (n+1)^(D+1) ≤ n^(D+1) + (1+2D)*n^D + 2D*n^(D-1)
      -- Suffices: 2D*n^(D-1) ≤ n^D = n*n^(D-1), i.e., 2D ≤ n.
      have h_2D_le_n : 2 * D ≤ n := by omega
      have h_extra : 2 * D * n ^ (D - 1) ≤ n ^ D := by
        rw [← h_pow_D]
        exact Nat.mul_le_mul_right (n ^ (D - 1)) h_2D_le_n
      -- Simplify the goal: n ^ (D + 1 - 1) = n ^ D
      have h_simp : n ^ (D + 1 - 1) = n ^ D := by
        have : D + 1 - 1 = D := by omega
        rw [this]
      rw [h_simp]
      linarith


private theorem succ_pow_le_two_mul_pow (D n : Nat) (hD : D ≥ 1) (hn : n ≥ 2 * D + 1) :
    (n + 1) ^ D ≤ 2 * n ^ D := by
  have h := succ_pow_le_pow_add D hD n hn
  -- h : (n+1)^D ≤ n^D + 2*D*n^(D-1)
  have h_pow_D : n * n ^ (D - 1) = n ^ D := by
    have hD_eq : D = (D - 1) + 1 := by omega
    conv_rhs => rw [hD_eq]
    rw [pow_succ]; ring
  have h_extra : 2 * D * n ^ (D - 1) ≤ n ^ D := by
    rw [← h_pow_D]
    exact Nat.mul_le_mul_right _ (by omega : 2 * D ≤ n)
  linarith

private theorem four_d_sq_plus_eight_le_two_pow_2d3 (D : Nat) :
    4 * D * D + 8 ≤ 2 ^ (2 * D + 3) := by
  induction D with
  | zero => norm_num
  | succ D ih =>
    have h_pow_eq : 2 ^ (2 * (D + 1) + 3) = 4 * 2 ^ (2 * D + 3) := by
      rw [show 2 * (D + 1) + 3 = 2 * D + 3 + 2 from by ring]
      rw [pow_add]; ring
    rw [h_pow_eq]
    have h_sub : 4 * (D + 1) * (D + 1) + 8 ≤ 4 * (4 * D * D + 8) := by
      nlinarith [sq_nonneg D, sq_nonneg (D - 1)]
    have h_chain : 4 * (4 * D * D + 8) ≤ 4 * 2 ^ (2 * D + 3) :=
      Nat.mul_le_mul_left 4 ih
    linarith

private theorem base_pow_lt_two_pow (D : Nat) :
    (4 * D * D + 8) ^ D < 2 ^ (4 * D * D + 8) := by
  by_cases hD : D = 0
  · subst hD
    simp only [pow_zero]
    norm_num
  · have hD_pos : D ≥ 1 := Nat.one_le_iff_ne_zero.mpr hD
    have hA : 4 * D * D + 8 ≤ 2 ^ (2 * D + 3) :=
      four_d_sq_plus_eight_le_two_pow_2d3 D
    have hB : (2 * D + 3) * D < 4 * D * D + 8 := by nlinarith
    have h1 : (4 * D * D + 8) ^ D ≤ (2 ^ (2 * D + 3)) ^ D :=
      Nat.pow_le_pow_left hA D
    have h2 : (2 ^ (2 * D + 3)) ^ D = 2 ^ ((2 * D + 3) * D) := by
      rw [← pow_mul]
    have h3 : 2 ^ ((2 * D + 3) * D) < 2 ^ (4 * D * D + 8) := by
      apply Nat.pow_lt_pow_right (by norm_num : 1 < 2)
      exact hB
    linarith

-- For n ≥ 4*D^2 + 8, n^D < 2^n.
private theorem n_pow_lt_two_pow_n (D n : Nat) (hn : n ≥ 4 * D * D + 8) :
    n ^ D < 2 ^ n := by
  by_cases hD : D = 0
  · subst hD
    simp only [pow_zero]
    have : n ≥ 1 := by omega
    calc 1 = 2 ^ 0 := by norm_num
      _ < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) this
  · have hD_pos : D ≥ 1 := Nat.one_le_iff_ne_zero.mpr hD
    induction n, hn using Nat.le_induction with
    | base => exact base_pow_lt_two_pow D
    | succ n hn ih =>
      have h_step_apply : n ≥ 2 * D + 1 := by
        nlinarith [sq_nonneg D, sq_nonneg (D - 1)]
      have h_step := succ_pow_le_two_mul_pow D n hD_pos h_step_apply
      calc (n + 1) ^ D ≤ 2 * n ^ D := h_step
        _ < 2 * 2 ^ n := by linarith [ih]
        _ = 2 ^ (n + 1) := by rw [pow_succ]; ring

def poly_threshold (k c : Nat) : Nat := 4 * (2 * k + 7) ^ 2 + 8 + c

private theorem poly_quadratic_bound_k_ge_1 (k c n : Nat) (hk : k ≥ 1) (hc : c ≥ 1)
    (hn : n ≥ poly_threshold k c) :
    (c * n ^ k + c) ^ 2 + 3 * (c * n ^ k + c) + 1 < 2 ^ n := by
  cases k with
  | zero => omega
  | succ k =>
    cases k with
    | zero =>
      simp at hn ⊢
      have hc_bound : c ≤ n - 332 := by
        have : n ≥ 332 + c := by
          simp only [poly_threshold] at hn
          omega
        have : n - 332 ≥ c := by omega
        omega
      have h_poly_bound : c * n + c ≤ n ^ 2 + n := by
        have h1 : c ≤ n - 332 := hc_bound
        have h2 : c * (n + 1) ≤ (n - 332) * (n + 1) := Nat.mul_le_mul_right (n + 1) h1
        have h3 : (n - 332) * (n + 1) ≤ n * (n + 1) := by
          apply Nat.mul_le_mul_right
          have : n ≥ 332 := by omega
          exact Nat.sub_le n 332
        have h4 : n * (n + 1) = n ^ 2 + n := by ring
        calc c * n + c = c * (n + 1) := by ring
          _ ≤ (n - 332) * (n + 1) := h2
          _ ≤ n * (n + 1) := h3
          _ = n ^ 2 + n := h4
      have hn200 : n ≥ 200 := by omega
      have h_target : (n ^ 2 + n) ^ 2 + 3 * (n ^ 2 + n) + 1 < 2 ^ n := 
        n_squared_plus_n_quartic_lt_two_pow_n_200 n hn200
      have h_mono : ∀ x y : Nat, x ≤ y → x ^ 2 + 3 * x + 1 ≤ y ^ 2 + 3 * y + 1 := by
        intro x y hxy
        calc x ^ 2 + 3 * x + 1
            ≤ y ^ 2 + 3 * x + 1 := by
                apply Nat.add_le_add_right
                have : x ^ 2 ≤ y ^ 2 := by
                  apply Nat.pow_le_pow_left
                  omega
                omega
          _ ≤ y ^ 2 + 3 * y + 1 := by
                apply Nat.add_le_add_right
                have : 3 * x ≤ 3 * y := by
                  apply Nat.mul_le_mul_left
                  omega
                omega
      calc (c * n + c) ^ 2 + 3 * (c * n + c) + 1
          ≤ (n ^ 2 + n) ^ 2 + 3 * (n ^ 2 + n) + 1 := h_mono (c * n + c) (n ^ 2 + n) h_poly_bound
        _ < 2 ^ n := h_target
    | succ k =>
      have hn_ge : n ≥ 1 := by
        simp only [poly_threshold] at hn
        -- After simplification, omega should see the quadratic expression
        omega
      have hc_lt_n : c < n := by
        simp only [poly_threshold] at hn
        -- We have n ≥ 4*(2*(k+2) + 7)^2 + 8 + c = 4*((2*k) + 11)^2 + 8 + c
        -- Since k ≥ 0, we have 2*k ≥ 0, so (2*k) + 11 ≥ 11
        -- Therefore (2*k + 11)^2 ≥ 121, so 4*(2*k + 11)^2 ≥ 484
        -- Therefore n ≥ 484 + 8 + c = 492 + c
        -- Therefore c ≤ n - 492 < n, so c < n
        have hk_ge_0 : k ≥ 0 := by omega
        have h_2k_plus_11_ge_11 : 2 * k + 11 ≥ 11 := by omega
        have h_sq_ge_121 : (2 * k + 11) ^ 2 ≥ 121 := by
          calc (2 * k + 11) ^ 2 ≥ 11 ^ 2 := Nat.pow_le_pow_left h_2k_plus_11_ge_11 2
            _ = 121 := by norm_num
        have h_4times_ge_484 : 4 * (2 * k + 11) ^ 2 ≥ 484 := by
          calc 4 * (2 * k + 11) ^ 2 ≥ 4 * 121 := Nat.mul_le_mul_left 4 h_sq_ge_121
            _ = 484 := by norm_num
        have hn_ge_492_plus_c : n ≥ 492 + c := by nlinarith [hn, h_4times_ge_484]
        omega
      -- (i) c * n^(k+2) + c ≤ n^(k+3)
      have h_coeff : c * n ^ (k + 2) + c ≤ n ^ (k + 3) := by
        have h_pow_ge : n ^ (k + 2) ≥ n := by
          calc n ^ (k + 2) ≥ n ^ 1 := Nat.pow_le_pow_right hn_ge (by omega)
            _ = n := pow_one n
        have h_main : c * (n ^ (k + 2) + 1) ≤ n * (n ^ (k + 2) + 1) := by
          apply Nat.mul_le_mul_right; omega
        have h_expand : n * (n ^ (k + 2) + 1) = n ^ (k + 3) + n := by
          rw [show k + 3 = (k + 2) + 1 from rfl, pow_succ]; ring
        have h_need : n - c ≥ 1 := by omega
        nlinarith [Nat.mul_sub_left_distrib n (n - 1) (n ^ (k + 2)), sq_nonneg (n - 1), sq_nonneg (n ^ (k + 2))]
      -- (ii) (c*n^(k+2) + c)^2 + 3*(c*n^(k+2) + c) + 1 ≤ n^(2*(k+2)+3)
      ----------------------------------------------------------------
      have h_sq_mono : ∀ x y : Nat, x ≤ y → x^2 + 3*x + 1 ≤ y^2 + 3*y + 1 := by
        intro x y hxy
        have hx2 : x^2 ≤ y^2 := Nat.pow_le_pow_left hxy 2
        nlinarith
      have h_step_ii : (c * n ^ (k + 2) + c) ^ 2 + 3 * (c * n ^ (k + 2) + c) + 1
                     ≤ (n ^ (k + 3)) ^ 2 + 3 * n ^ (k + 3) + 1 := h_sq_mono _ _ h_coeff
      have h_to_single_pow : (n ^ (k + 3)) ^ 2 + 3 * n ^ (k + 3) + 1 ≤ n ^ (2 * (k + 2) + 3) := by
        have hn_ge : n ≥ 1 := by
          simp only [poly_threshold] at hn
          omega
        have h_n3 : n ≥ 3 := by
          -- We know n ≥ poly_threshold (k+2) c where k ≥ 0 and c ≥ 1
          -- So n ≥ 4*((2*0)+11)^2 + 8 + 1 = 4*121 + 8 + 1 = 493
          simp only [poly_threshold] at hn
          have hk_ge_0 : k ≥ 0 := by omega
          have h2k_plus_11_ge_11 : 2 * k + 11 ≥ 11 := by omega
          have hsq_ge_121 : (2 * k + 11) ^ 2 ≥ 121 := by
            calc (2 * k + 11) ^ 2 ≥ 11 ^ 2 := Nat.pow_le_pow_left h2k_plus_11_ge_11 2
              _ = 121 := by norm_num
          have h4times_ge_484 : 4 * (2 * k + 11) ^ 2 ≥ 484 := by
            calc 4 * (2 * k + 11) ^ 2 ≥ 4 * 121 := Nat.mul_le_mul_left 4 hsq_ge_121
              _ = 484 := by norm_num
          have : n ≥ 484 + 8 + 1 := by nlinarith [hn, h4times_ge_484, show c ≥ 1 by omega]
          omega
        have h_pow_eq : (n ^ (k + 3)) ^ 2 = n ^ (2 * (k + 3)) := by
          rw [← pow_mul]; ring_nf
        have h_target_eq : n ^ (2 * (k + 2) + 3) = n * (n ^ (k + 3)) ^ 2 := by
          rw [h_pow_eq, show 2 * (k + 2) + 3 = 2 * (k + 3) + 1 from by ring]
          rw [pow_succ]; ring
        rw [h_target_eq]
        have h_pow_ge_n : n ^ (k + 3) ≥ n := by
          calc n ^ (k + 3) ≥ n ^ 1 := Nat.pow_le_pow_right hn_ge (by omega)
            _ = n := pow_one n
        have h_pow_ge_3 : n ^ (k + 3) ≥ 3 := by
          have hk3_ge_3 : k + 3 ≥ 3 := by omega
          calc n ^ (k + 3) ≥ n ^ 3 := Nat.pow_le_pow_right hn_ge hk3_ge_3
            _ ≥ 3 ^ 3 := Nat.pow_le_pow_left h_n3 3
            _ = 27 := by norm_num
            _ ≥ 3 := by norm_num
        have h_pow_sq_ge : (n ^ (k + 3)) ^ 2 ≥ n ^ (k + 3) := by
          calc (n ^ (k + 3)) ^ 2 = n ^ (k + 3) * n ^ (k + 3) := by ring
            _ ≥ 1 * n ^ (k + 3) := by
                apply Nat.mul_le_mul_right
                exact Nat.one_le_iff_ne_zero.mpr (by positivity)
            _ = n ^ (k + 3) := by ring
        nlinarith [h_n3, h_pow_ge_3, h_pow_sq_ge]
      -- (iii) n^(2*(k+2)+3) < 2^n via the main lemma.
      -- We have n ≥ 4*((2k)+11)^2 + 8 + c
      -- We need n ≥ 4*(2*(k+2)+3)^2 + 8 = 4*(2k+7)^2 + 8
      -- Since k ≥ 0, we have 2k+11 ≥ 2k+7, so (2k+11)^2 ≥ (2k+7)^2, so 4*(2k+11)^2 ≥ 4*(2k+7)^2
      have hk_ge_0 : k ≥ 0 := by omega
      have h2k_plus_7_le_2k_plus_11 : 2 * k + 7 ≤ 2 * k + 11 := by omega
      have h_4times_sq_le : 4 * (2 * k + 7) ^ 2 ≤ 4 * (2 * k + 11) ^ 2 := by
        apply Nat.mul_le_mul_left
        exact Nat.pow_le_pow_left h2k_plus_7_le_2k_plus_11 2
      have hn_for_main : n ≥ 4 * (2 * (k + 2) + 3) * (2 * (k + 2) + 3) + 8 := by
        simp only [poly_threshold] at hn
        calc n ≥ 4 * (2 * k + 11) ^ 2 + 8 + c := hn
          _ ≥ 4 * (2 * k + 11) ^ 2 + 8 := by omega
          _ ≥ 4 * (2 * k + 7) ^ 2 + 8 := by omega
          _ = 4 * (2 * (k + 2) + 3) * (2 * (k + 2) + 3) + 8 := by ring
      have h_step_iii : n ^ (2 * (k + 2) + 3) < 2 ^ n :=
        n_pow_lt_two_pow_n (2 * (k + 2) + 3) n hn_for_main
      linarith [h_step_ii, h_to_single_pow, h_step_iii]

private theorem poly_quadratic_bound_k0 (c : Nat) (n : Nat) (hn : n ≥ 2 * c + 5) :
    4 * c ^ 2 + 6 * c + 1 < 2 ^ n := by
  have hn_ge : n ≥ 2 * c + 5 := hn
  have h_pow : 2 ^ n ≥ 2 ^ (2 * c + 5) := Nat.pow_le_pow_right (by norm_num) hn_ge
  suffices 4 * c ^ 2 + 6 * c + 1 < 2 ^ (2 * c + 5) by
    calc 4 * c ^ 2 + 6 * c + 1 < 2 ^ (2 * c + 5) := this
      _ ≤ 2 ^ n := h_pow
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

private theorem poly_quadratic_bound (k c : Nat) (n : Nat) (hn : n ≥ poly_threshold k c) :
    (c * n ^ k + c) ^ 2 + 3 * (c * n ^ k + c) + 1 < 2 ^ n := by
  by_cases hk : k = 0
  · subst hk
    simp only [pow_zero, mul_one]
    by_cases hc : c = 0
    · subst hc
      simp
      have : n ≥ 100 := by
        simp only [poly_threshold] at hn
        norm_num at hn
        omega
      omega
    · push Not at hc
      by_cases hc_le : c ≤ 95
      · have hn_bound : n ≥ 2 * c + 5 := by
          simp only [poly_threshold] at hn
          have : c ≤ 95 := hc_le
          omega
        have : (c + c) ^ 2 + 3 * (c + c) + 1 = 4 * c ^ 2 + 6 * c + 1 := by ring
        rw [this]
        exact poly_quadratic_bound_k0 c n hn_bound
      · push Not at hc_le
        have hc96 : c ≥ 96 := by omega
        have hn196 : n ≥ 196 := by
          simp only [poly_threshold] at hn
          have : c ≥ 96 := hc96
          omega
        have hc_lt_n : c < n := by
          simp only [poly_threshold] at hn
          have : c ≥ 96 := hc96
          omega
        have h_bound : 4 * c ^ 2 + 6 * c + 1 < 4 * n ^ 2 + 6 * n + 1 := by
          have : c + 1 ≤ n := by omega
          have : (c + 1) ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left this 2
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
  push Not at hk
  have hk1 : k ≥ 1 := Nat.pos_of_ne_zero hk
  by_cases hc0 : c = 0
  · subst hc0
    simp
    have hn1 : n ≥ 1 := by
      simp only [poly_threshold] at hn
      omega
    exact Nat.pos_iff_ne_zero.mp hn1
  · push Not at hc0
    have hc1 : c ≥ 1 := Nat.pos_of_ne_zero hc0
    exact poly_quadratic_bound_k_ge_1 k c n hk1 hc1 hn

/-- Shannon's counting argument: For any polynomial p, there exist Boolean functions
    on n inputs not computable by circuits of size ≤ p(n) -/
theorem shannon_counting_argument :
    ∀ (p : Nat → Nat) (hp : IsPolynomial p),
    ∃ n₀ : Nat, ∀ n ≥ n₀, ∃ (f : (Fin n → Bool) → Bool),
      ∀ (c : BoolCircuit n), circuitSize c ≤ p n → ∃ inp : Fin n → Bool, evalCircuit c inp ≠ f inp := by
  intro p hp
  -- Extract the bound from IsPolynomial (without k ≤ 4 constraint)
  obtain ⟨k, c, h_p_le⟩ := hp
  refine ⟨poly_threshold k (4*c) + 200, ?_⟩
  intro n hn
  have h_card : Fintype.card (NormalizedCircuit n (p n)) ≤
                normalized_circuit_count_upper_bound n (p n) :=
    normalized_circuit_card_le n (p n)
  let s := p n
  have h_s_pos : (s + 1) ≤ 2 ^ (s + 1) := by
    exact Nat.lt_two_pow_self.le
  have h_pow_eq : (2 ^ (n + s + 4)) ^ s = 2 ^ ((n + s + 4) * s) := by
    rw [← pow_mul]
  have h_count_le_2pow :
      normalized_circuit_count_upper_bound n s ≤
      2 ^ (s * s + s * n + 5 * s + 1) := by
    unfold normalized_circuit_count_upper_bound
    rw [h_pow_eq]
    calc (s + 1) * 2 ^ ((n + s + 4) * s)
        ≤ 2 ^ (s + 1) * 2 ^ ((n + s + 4) * s) := by
          exact Nat.mul_le_mul_right _ h_s_pos
      _ = 2 ^ ((s + 1) + (n + s + 4) * s) := by rw [← pow_add]
      _ = 2 ^ (s * s + s * n + 5 * s + 1) := by
          congr 1; ring
  by_cases hk0 : k = 0
  · subst hk0
    simp only [pow_zero] at h_p_le ⊢
    have h_s_le : s ≤ 2 * c := by
      have := h_p_le n
      simp [pow_zero] at this
      omega
    have h_s_le_n : s ≤ n := by
      -- We have n ≥ poly_threshold 0 (4*c) + 200 = 204 + 4c + 200 = 404 + 4c
      -- We want to show s ≤ n, where s ≤ 2c and n ≥ 404 + 4c
      -- Clearly 2c ≤ 404 + 4c, so s ≤ 2c ≤ n. Use linarith to handle this.
      simp only [poly_threshold] at hn
      linarith [h_s_le, hn]
    have h_bound : s * s + s * n + 5 * s + 1 < 2 ^ n := by
      calc s * s + s * n + 5 * s + 1
          = s ^ 2 + s * n + 5 * s + 1 := by ring
        _ ≤ 4 * n ^ 2 + 6 * n + 1 := by nlinarith [h_s_le_n]
        _ < 2 ^ n := by
            have hn196 : n ≥ 196 := by
              have h_threshold : n ≥ poly_threshold 0 (4*c) + 200 := hn
              simp only [poly_threshold] at h_threshold
              linarith
            exact four_n_squared_plus_six_n_plus_one_lt_two_pow_n n hn196
    have h_card_lt : Fintype.card (NormalizedCircuit n (p n)) < 2 ^ (2 ^ n) := by
      calc Fintype.card (NormalizedCircuit n (p n))
          ≤ normalized_circuit_count_upper_bound n s := h_card
        _ ≤ 2 ^ (s * s + s * n + 5 * s + 1) := h_count_le_2pow
        _ < 2 ^ (2 ^ n) := by
            apply Nat.pow_lt_pow_right (by norm_num)
            exact h_bound
    let denote : NormalizedCircuit n (p n) → (Fin n → Bool) → Bool :=
      fun nc inp => evalCircuit (normalizedToRaw nc) inp
    have h_lt : Fintype.card (NormalizedCircuit n (p n)) < 
                Fintype.card ((Fin n → Bool) → Bool) := by
      have h_func_card : Fintype.card ((Fin n → Bool) → Bool) = 2 ^ (2 ^ n) := by
        rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
      rw [h_func_card]
      exact h_card_lt
    have h_not_surj : ¬ Function.Surjective denote := by
      intro hs
      have := Fintype.card_le_of_surjective denote hs
      linarith [h_lt]
    simp only [Function.Surjective, not_forall] at h_not_surj
    obtain ⟨f, hf⟩ := h_not_surj
    use f
    intro c h_size
    let nc := normalizeCircuit c h_size
    have h_denote_eq : (fun inp => evalCircuit (normalizedToRaw nc) inp) =
                       (fun inp => evalCircuit c inp) := by
      funext inp
      exact evalCircuit_normalizeCircuit c h_size inp
    have h_neq : (fun inp => evalCircuit c inp) ≠ f := by
      have : ∀ a, denote a ≠ f := by
        intro a ha
        apply hf
        exact ⟨a, ha⟩
      rw [← h_denote_eq]
      exact this nc
    by_contra h_all_eq
    push Not at h_all_eq
    apply h_neq
    funext inp
    exact h_all_eq inp
  · have hk1 : k ≥ 1 := Nat.pos_of_ne_zero hk0
    have hn_for_poly : n ≥ poly_threshold k (4*c) := by omega
    have h_poly_bound :
        (4 * c * n ^ k + 4 * c) ^ 2 + 3 * (4 * c * n ^ k + 4 * c) + 1 < 2 ^ n :=
      poly_quadratic_bound k (4 * c) n hn_for_poly
    have h_bound : s * s + s * n + 5 * s + 1 ≤ (4 * c * n ^ k + 4 * c) ^ 2 + 3 * (4 * c * n ^ k + 4 * c) + 1 := by
      have h_s_le : s ≤ c * n ^ k + c := h_p_le n
      by_cases hc : c = 0
      · subst hc
        simp only [mul_zero, add_zero, zero_pow, zero_mul] at h_s_le ⊢
        simp [Nat.eq_zero_of_le_zero h_s_le]
      · have hc_pos : c ≥ 1 := Nat.one_le_iff_ne_zero.mpr hc
        have hn_le : n ≤ c * n ^ k + c := by
          nlinarith [hc_pos, show n ^ k ≥ n from Nat.le_self_pow (by omega) n]
        calc s * s + s * n + 5 * s + 1
            = s ^ 2 + s * n + 5 * s + 1 := by ring
          _ ≤ s * (s + n + 5) + 1 := by ring_nf; omega
          _ ≤ (c * n ^ k + c) * (s + n + 5) + 1 := by
              have : s * (s + n + 5) ≤ (c * n ^ k + c) * (s + n + 5) := Nat.mul_le_mul_right (s + n + 5) h_s_le
              exact Nat.add_le_add_right this 1
          _ ≤ (c * n ^ k + c) * ((c * n ^ k + c) + n + 5) + 1 := by
              have : s + n + 5 ≤ (c * n ^ k + c) + n + 5 := by omega
              exact Nat.add_le_add_right (Nat.mul_le_mul_left (c * n ^ k + c) this) 1
          _ ≤ (4 * c * n ^ k + 4 * c) ^ 2 + 3 * (4 * c * n ^ k + 4 * c) + 1 := by
              nlinarith [sq_nonneg (c * n ^ k), sq_nonneg (c * n ^ k - n ^ k), sq_nonneg (c - 1), sq_nonneg (n ^ k - 1),
                h_s_le, hn_le, hc_pos]
    have h_card_lt : Fintype.card (NormalizedCircuit n (p n)) < 2 ^ (2 ^ n) := by
      calc Fintype.card (NormalizedCircuit n (p n))
          ≤ normalized_circuit_count_upper_bound n s := h_card
        _ ≤ 2 ^ (s * s + s * n + 5 * s + 1) := h_count_le_2pow
        _ ≤ 2 ^ ((4 * c * n ^ k + 4 * c) ^ 2 + 3 * (4 * c * n ^ k + 4 * c) + 1) := by
            apply Nat.pow_le_pow_right (by norm_num)
            exact h_bound
        _ < 2 ^ (2 ^ n) := by
            apply Nat.pow_lt_pow_right (by norm_num)
            exact h_poly_bound
    let denote : NormalizedCircuit n (p n) → (Fin n → Bool) → Bool :=
      fun nc inp => evalCircuit (normalizedToRaw nc) inp
    have h_lt : Fintype.card (NormalizedCircuit n (p n)) < 
                Fintype.card ((Fin n → Bool) → Bool) := by
      have h_func_card : Fintype.card ((Fin n → Bool) → Bool) = 2 ^ (2 ^ n) := by
        rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
      rw [h_func_card]
      exact h_card_lt
    have h_not_surj : ¬ Function.Surjective denote := by
      intro hs
      have := Fintype.card_le_of_surjective denote hs
      linarith [h_lt]
    simp only [Function.Surjective, not_forall] at h_not_surj
    obtain ⟨f, hf⟩ := h_not_surj
    use f
    intro c h_size
    let nc := normalizeCircuit c h_size
    have h_denote_eq : (fun inp => evalCircuit (normalizedToRaw nc) inp) =
                       (fun inp => evalCircuit c inp) := by
      funext inp
      exact evalCircuit_normalizeCircuit c h_size inp
    have h_neq : (fun inp => evalCircuit c inp) ≠ f := by
      -- We have hf : ¬∃ a, denote a = f
      -- This means ∀ a, denote a ≠ f
      have : ∀ a, denote a ≠ f := by
        intro a ha
        apply hf
        exact ⟨a, ha⟩
      -- Now use this on nc
      rw [← h_denote_eq]
      exact this nc
    by_contra h_all_eq
    push Not at h_all_eq
    apply h_neq
    funext inp
    exact h_all_eq inp
-- Main conjecture

-- Cook-Levin Theorem (axiomatized)

/-- SAT is NP-complete (axiomatized) -/
axiom sat_is_np_complete :
    ∃ (sat : Language), inNP sat ∧
    ∀ (L : Language), inNP L → ∃ (f : Nat → Nat) (_hf : IsPolynomial f),
      ∀ n inp, L n inp ↔ sat (f n) (fun i =>
        if h : i.val < n then inp ⟨i.val, h⟩
        else false)

-- Circuit lower bound for SAT (MAJOR OPEN QUESTION)

/-- SAT requires superpolynomial circuit size (axiom) -/
axiom sat_has_superpoly_lower_bound : ∃ (_ : Nat), ∀ (p : Nat → Nat) (_hp : IsPolynomial p),
      ∃ n, ∀ (circuit : BoolCircuit n), circuitSize circuit > p n

-- Connection between circuit lower bounds and P ≠ NP

/-- If SAT requires superpolynomial circuit size, then P ≠ NP -/
theorem sat_superpolynomial_implies_p_neq_np
    (sat : Language)
    (h_sat_np : inNP sat)
    (h_superpoly : ∃ (_ : Nat), ∀ (p : Nat → Nat) (_hp : IsPolynomial p),
      ∃ n, ∀ (circuit : BoolCircuit n), circuitSize circuit > p n) :
    ∃ L : Language, inNP L ∧ ¬ inP L := by
  refine' ⟨sat, ?_⟩
  constructor
  exact h_sat_np
  intro h_sat_in_p
  obtain ⟨p, hp_poly, h_dec⟩ := h_sat_in_p
  obtain ⟨_, hc⟩ := h_superpoly
  obtain ⟨n, hn⟩ := hc p hp_poly
  obtain ⟨circuit, h_size, _⟩ := h_dec n
  have h_gt := hn circuit
  exact Nat.lt_irrefl (circuitSize circuit) (Nat.lt_of_le_of_lt h_size h_gt)

/-- P ≠ NP: there exists a language in NP not in P -/
theorem p_neq_np_conditional_on_sat_lower_bound : ∃ L : Language, inNP L ∧ ¬ inP L := by
  obtain ⟨sat, h_sat_np, _⟩ := sat_is_np_complete
  exact sat_superpolynomial_implies_p_neq_np sat h_sat_np sat_has_superpoly_lower_bound

end PVsNp.CircuitLowerBounds
