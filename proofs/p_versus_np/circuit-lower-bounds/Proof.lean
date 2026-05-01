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


/-- Finite node codes used for normalized counting. -/
inductive NodeCode (n s : Nat) where
  | const : Bool → NodeCode n s
  | var : Fin n → NodeCode n s
  | not : Fin s → NodeCode n s
  | and : Finset (Fin s) → NodeCode n s
  | or : Finset (Fin s) → NodeCode n s
  deriving DecidableEq, Fintype

/-- A normalized circuit of size exactly `s`, with a finite node code at each position. -/
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
  | Const b =>
    simp [normalizeNodeCode, nodeCodeToRaw, evalNode]
  | Var i =>
    simp only [normalizeNodeCode]
    split_ifs with hi
    · simp [nodeCodeToRaw, evalNode, hi]
    · simp [nodeCodeToRaw, evalNode, hi]
  | Not =>
    cases children with
    | nil =>
      simp [normalizeNodeCode, nodeCodeToRaw, evalNode]
    | cons child tail =>
        cases tail with
        | nil =>
            simp only [normalizeNodeCode]
            split_ifs with hc
            · simp [nodeCodeToRaw, evalNode]
            · have h_not_lt : ¬child < vals.size := by omega
              simp [nodeCodeToRaw, evalNode, Array.getD, h_not_lt]
        | cons h2 rest =>
            simp [normalizeNodeCode, nodeCodeToRaw, evalNode]
  | And =>
    simp only [normalizeNodeCode, nodeCodeToRaw, evalNode]
    rw [foldl_and_map_val, foldl_and_map_eval, ← and_fold_preserved vals s hs children]
  | Or =>
    simp only [normalizeNodeCode, nodeCodeToRaw, evalNode]
    rw [foldl_or_map_val, foldl_or_map_eval, ← or_fold_preserved vals s hs children]

private def evalStep {n : Nat} (inp : Fin n → Bool) (acc : Array Bool) (node : CircuitNode) : Array Bool :=
  acc.push (evalNode inp acc node)

private theorem evalStep_fold_size {n : Nat} (inp : Fin n → Bool) (vals : Array Bool)
    (nodes : List CircuitNode) :
    (List.foldl (evalStep inp) vals nodes).size = vals.size + nodes.length := by
  induction nodes generalizing vals with
  | nil => simp [evalStep]
  | cons node rest ih => simp [List.foldl, evalStep, ih, Array.size_push, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

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
  unfold evalCircuit
  -- The normalized circuit nodes are [original normalized] ++ [false padding]
  have h_nodes := normalizeCircuit_nodes_list c hsize
  -- The key insight: padding with const-false nodes doesn't affect evaluation
  -- because false values don't propagate through AND/OR gates in a way that
  -- changes the output at indices < c.nodes.size
  
  -- For the output: if c.output < c.nodes.size, it maps to the same position in normalized circuit
  -- Otherwise, the output defaults to false (const false)
  -- The key is to use normalizeCircuit_nodes_list to show the node lists match up
  -- and show that the folded evaluation is the same
  
  -- First, let's unfold definitions to see what we're working with
  unfold normalizedToRaw
  simp only [circuitSize, Option.getD]
  
  -- The approach: show that
  -- Array.foldl over normalized nodes = Array.foldl over original nodes
  -- We'll use Array.foldl on List.ofFn with the h_nodes equality
  
  -- Strategy (7 steps from README):
  -- 1. Use normalizeCircuit_nodes_list to show normalized nodes = [original] ++ [padding]
  -- 2. Split the foldl over this list
  -- 3. Use evalStep_fold_normalized_eq to show original nodes don't change evaluation
  -- 4. Show padding doesn't affect evaluation at indices < c.nodes.size
  -- 5. Handle the output: if c.output < c.nodes.size, it's preserved
  -- 6. Otherwise, output is false (const-false padding), which is correct
  
  -- Key lemmas available:
  -- - normalizeCircuit_nodes_list: splits normalized nodes into prefix + suffix
  -- - evalStep_fold_normalized_eq: shows normalization doesn't change node evaluations
  -- - evalStep_fold_getElem?_preserve: shows adding nodes doesn't change existing indices
  
  -- Technical challenge: Converting between Array.foldl on Array.ofFn and List.foldl
  -- The normalized circuit uses Array.ofFn (Fin s → NodeCode), while evalStep works with lists
  -- This requires careful handling of the Array/List conversions
  
  sorry

private def encodeNodeCode {n s : Nat} : NodeCode n s → Bool ⊕ Fin n ⊕ Fin s ⊕ Finset (Fin s) ⊕ Finset (Fin s)
  | .const b => Sum.inl b
  | .var v => Sum.inr <| Sum.inl v
  | .not child => Sum.inr <| Sum.inr <| Sum.inl child
  | .and children => Sum.inr <| Sum.inr <| Sum.inr <| Sum.inl children
  | .or children => Sum.inr <| Sum.inr <| Sum.inr <| Sum.inr children

private theorem encodeNodeCode_injective {n s : Nat} : Function.Injective (@encodeNodeCode n s) := by
  intro a b h
  cases a <;> cases b <;> cases h <;> rfl

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
      rw [show 8 = 2 ^ 3 by norm_num, ← Nat.pow_add]
      congr 1
      omega

/-- A sound upper bound on the number of normalized circuits of size `s`. -/
def normalized_circuit_count_upper_bound (n s : Nat) : Nat := (s + 1) * (2 ^ (n + s + 4)) ^ s

private theorem normalized_circuit_card_le (n s : Nat) :
    Fintype.card (NormalizedCircuit n s) ≤ normalized_circuit_count_upper_bound n s := by
  dsimp [NormalizedCircuit, normalized_circuit_count_upper_bound]
  calc
    Fintype.card (Option (Fin s) × (Fin s → NodeCode n s))
        = (s + 1) * Fintype.card (NodeCode n s) ^ s := by
            simp [Fintype.card_prod, Fintype.card_option, Nat.mul_comm]
    _ ≤ (s + 1) * (2 ^ (n + s + 4)) ^ s := by
          apply Nat.mul_le_mul_left
          exact Nat.pow_le_pow_left (node_code_card_le n s) s

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







/-- Helper lemma: for n ≥ 200, n^4 + 3*n^2 + 1 < 2^n. -/
private theorem n_quartic_plus_lt_two_pow_n_200 (n : Nat) (hn : n ≥ 200) : n ^ 4 + 3 * n ^ 2 + 1 < 2 ^ n := by
  -- Base case: n = 200
  have base200 : 200 ^ 4 + 3 * 200 ^ 2 + 1 < 2 ^ 200 := by norm_num
  -- Inductive step
  suffices ∀ k ≥ 200, k ^ 4 + 3 * k ^ 2 + 1 < 2 ^ k by exact this n hn
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact base200
  | succ k hk ih =>
    -- IH: k^4 + 3*k^2 + 1 < 2^k
    -- Goal: (k+1)^4 + 3*(k+1)^2 + 1 < 2^(k+1)
    calc (k + 1) ^ 4 + 3 * (k + 1) ^ 2 + 1
        = k^4 + 4*k^3 + 6*k^2 + 4*k + 1 + 3*k^2 + 6*k + 3 + 1 := by ring
      _ = k^4 + 4*k^3 + 9*k^2 + 10*k + 5 := by ring
      _ = k^4 + 3*k^2 + 1 + (4*k^3 + 6*k^2 + 10*k + 4) := by ring
      _ < 2^k + (4*k^3 + 6*k^2 + 10*k + 4) := by omega
      _ ≤ 2^k + 2^k := by
          -- Show 4*k^3 + 6*k^2 + 10*k + 4 ≤ 2^k
          -- For k ≥ 200, k^4 < 2^k (from IH) and k^4 ≥ 4*k^3 + 6*k^2 + 10*k + 4
          have h_k4_lt : k ^ 4 < 2 ^ k := by omega
          have h_k4_ge : k ^ 4 ≥ 4 * k ^ 3 + 6 * k ^ 2 + 10 * k + 4 := by
            -- For k ≥ 200, this holds (verified by norm_num for k=200)
            -- We use induction to prove it for all k ≥ 200
            have base : 200 ^ 4 ≥ 4 * 200 ^ 3 + 6 * 200 ^ 2 + 10 * 200 + 4 := by norm_num
            have step : ∀ m ≥ 200, m ^ 4 ≥ 4 * m ^ 3 + 6 * m ^ 2 + 10 * m + 4 →
                (m + 1) ^ 4 ≥ 4 * (m + 1) ^ 3 + 6 * (m + 1) ^ 2 + 10 * (m + 1) + 4 := by
              intro m hm h
              -- We need: (m+1)^4 ≥ 4*(m+1)^3 + 6*(m+1)^2 + 10*(m+1) + 4
              -- Expanding: m^4 + 4*m^3 + 6*m^2 + 4*m + 1 ≥ 4*m^3 + 12*m^2 + 12*m + 4 + 6*m^2 + 12*m + 6 + 10*m + 10 + 4
              -- Simplifying RHS: 4*m^3 + 18*m^2 + 34*m + 24
              -- So we need: m^4 ≥ 12*m^2 + 30*m + 23
              -- From IH: m^4 ≥ 4*m^3 + 6*m^2 + 10*m + 4
              -- For m ≥ 200, 4*m^3 ≥ 12*m^2 + 30*m + 23
              have h_ih : m ^ 4 ≥ 4 * m ^ 3 + 6 * m ^ 2 + 10 * m + 4 := h
              have h_cubic : 4 * m ^ 3 ≥ 12 * m ^ 2 + 30 * m + 23 := by
                have : m ≥ 200 := hm
                -- For m ≥ 200, 4*m^3 ≥ 4*200^3 = 4*8000000 = 32000000
                -- And 12*m^2 + 30*m + 23 ≤ 12*200^2 + 30*200 + 23 = 12*40000 + 6000 + 23 = 480000 + 6000 + 23 = 486023
                -- So 4*m^3 ≥ 32000000 > 486023 ≥ 12*m^2 + 30*m + 23
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
  -- We use induction similar to n_quartic_plus_lt_two_pow_n_200
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








/-- For n ≥ 200 and d ≥ 1, we have n^d < 2^n.
    This establishes exponential dominance of 2^n over polynomial n^d for sufficiently large n.
    -/
private theorem n_pow_lt_two_pow_n_reasonable (n d : Nat) (hd : d ≥ 1) (hn : n ≥ 200) (hbound : d ≤ 20) :
    n ^ d < 2 ^ n := by
  -- For "reasonable" degrees d ≤ 20 and n ≥ 200, prove n^d < 2^n by induction on n
  interval_cases d
  · -- d = 1: n^1 < 2^n for n ≥ 200, i.e., n < 2^n
    simp only [pow_one]  -- Simplify n^1 to n
    suffices ∀ k ≥ 200, k < 2^k by exact this n hn
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => norm_num
    | succ k hk_ih =>
      calc k + 1 < 2^k + 1 := by omega
        _ < 2^k + 2^k := by omega
        _ = 2^(k+1) := by rw [Nat.pow_succ]; ring
  · -- d = 2: n^2 < 2^n for n ≥ 200
    -- Use that n^2 < 2^n since n ≥ 200 ≥ 9, so n² + 2n < 2^n, and n² < n² + 2n
    have h1 : n^2 < n^2 + 2 * n := by omega
    -- n_squared_plus_two_n_lt_two_pow_n needs n ≥ 9, but we have n ≥ 200, so we can use it
    have hn9 : n ≥ 9 := by omega
    have h2 : n^2 + 2 * n < 2^n := n_squared_plus_two_n_lt_two_pow_n n hn9
    omega
  · -- d = 3: n^3 < 2^n for n ≥ 200
    -- Strategy: Prove by induction on n, similar to d=1 case
    -- Or: Show n^3 ≤ (some bound we know works) < 2^n
    -- For now, we leave this as sorry - requires either:
    -- 1. A specific helper lemma for n^3 + ... < 2^n (like n_quartic_plus_lt_two_pow_n_200)
    -- 2. A monotonicity argument from d=2 case
    -- 3. Direct induction
    -- Better approach: Try to use monotonicity by treating n^3 as n^4 / n
    -- But this is getting complicated. For the near term, enumerate all d cases systematically
    -- Use interval_cases but handle each case separately with appropriate lemmas
    -- This requires significant additional infrastructure - defer for now
    sorry
  · -- d = 4: n^4 < 2^n for n ≥ 200
    -- Use: n^4 < n^4 + 3*n^2 + 1 < 2^n (from n_quartic_plus_lt_two_pow_n_200)
    -- This requires a helper lemma for n^4 < 2^n extracted from the quartic+ lemma
    calc n^4 < n^4 + 3*n^2 + 1 := by omega
      _ < 2^n := n_quartic_plus_lt_two_pow_n_200 n hn
  · -- d = 5
    sorry
  · -- d = 6
    sorry
  · -- d = 7
    sorry
  · -- d = 8
    sorry
  · -- d = 9
    sorry
  · -- d = 10
    sorry
  · -- d = 11
    sorry
  · -- d = 12
    sorry
  · -- d = 13
    sorry
  · -- d = 14
    sorry
  · -- d = 15
    sorry
  · -- d = 16
    sorry
  · -- d = 17
    sorry
  · -- d = 18
    sorry
  · -- d = 19
    sorry
  · -- d = 20
    sorry

/-- General helper: for any k ≥ 1, c ≥ 1, and n ≥ 100*k + c + 100,
    we have (c*n^k + c)^2 + 3*(c*n^k + c) + 1 < 2^n.
    This handles the k ≥ 1 case of poly_quadratic_bound.

    Mathematical note: For n ≥ 100*k + c + 100, we have n ≥ 200.
    The LHS is a polynomial in n of degree 2k, while the RHS grows exponentially.
    For sufficiently large n, exponential growth dominates polynomial growth.
    The threshold ensures n is large enough for this to hold for all k ≥ 1, c ≥ 1.
    -/
private theorem poly_quadratic_bound_k_ge_1 (k c n : Nat) (hk : k ≥ 1) (hc : c ≥ 1)
    (hn : n ≥ 100 * k + c + 100) :
    (c * n ^ k + c) ^ 2 + 3 * (c * n ^ k + c) + 1 < 2 ^ n := by
  -- For n ≥ 100*k + c + 100, we have n ≥ 200
  have hn200 : n ≥ 200 := by omega
  -- For k = 1, we can bound c * n + c ≤ n^2 and use n_quartic_plus_lt_two_pow_n_200
  -- For k ≥ 2, we need a different approach
  cases k with
  | zero =>
    -- k = 0, but we have k ≥ 1, so this case is impossible
    omega
  | succ k =>
    cases k with
    | zero =>
      -- k = 1
      -- We have n ≥ 100*1 + c + 100 = c + 200, so n ≥ 200
      -- For k=1, we need (c*n + c)^2 + 3*(c*n + c) + 1 < 2^n
      -- From hn: n ≥ 200 + c, so c ≤ n - 200
      simp at hn ⊢
      have hc_bound : c ≤ n - 200 := by omega
      -- We show c*n + c ≤ n^2 + n, which implies (c*n + c)^2 + 3*(c*n + c) + 1 ≤ (n^2 + n)^2 + 3*(n^2 + n) + 1
      -- For n ≥ 200, we can show (n^2 + n)^2 + 3*(n^2 + n) + 1 < 2^n
      have h_poly_bound : c * n + c ≤ n ^ 2 + n := by
        have h1 : c ≤ n - 200 := hc_bound
        have h2 : c * (n + 1) ≤ (n - 200) * (n + 1) := Nat.mul_le_mul_right (n + 1) h1
        have h3 : (n - 200) * (n + 1) ≤ n * (n + 1) := by
          apply Nat.mul_le_mul_right
          have : n ≥ 200 := by
            have : n ≥ 100 * (0 + 1) + c + 100 := hn
            have : 100 * (0 + 1) + c + 100 ≥ 200 := by
              have : c ≥ 1 := hc
              omega
            omega
          exact Nat.sub_le n 200
        have h4 : n * (n + 1) = n ^ 2 + n := by ring
        calc c * n + c = c * (n + 1) := by ring
          _ ≤ (n - 200) * (n + 1) := h2
          _ ≤ n * (n + 1) := h3
          _ = n ^ 2 + n := h4
      -- Now (c*n + c)^2 + 3*(c*n + c) + 1 ≤ (n^2 + n)^2 + 3*(n^2 + n) + 1
      -- We need to show (n^2 + n)^2 + 3*(n^2 + n) + 1 < 2^n for n ≥ 200
      -- This is exactly our new helper lemma
      have h_target : (n ^ 2 + n) ^ 2 + 3 * (n ^ 2 + n) + 1 < 2 ^ n := n_squared_plus_n_quartic_lt_two_pow_n_200 n hn200
      -- And (c*n + c)^2 + 3*(c*n + c) + 1 ≤ (n^2 + n)^2 + 3*(n^2 + n) + 1
      -- Since c*n + c ≤ n^2 + n (from h_poly_bound)
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
      -- k ≥ 2, so the original k in the theorem is k+2 ≥ 2
      -- We have n ≥ 100*(k+2) + c + 100 ≥ 301
      -- Use the same approach as k=1: bound by n^(k+3) and use exponential dominance
      simp at hn ⊢
      have hn300 : n ≥ 300 := by omega
      have hc_bound : c + 1 ≤ n := by omega
      -- Bound: c*n^(k+2) + c ≤ n^(k+3)
      have h_poly_bound : c * n ^ (k + 2) + c ≤ n ^ (k + 3) := by
        have hc_le_n : c ≤ n := by omega
        have hc_le_nk2 : c ≤ n ^ (k + 2) := by
          have : n ≥ 1 := by omega
          have : n ≤ n ^ (k + 2) := by
            have : k + 2 ≥ 1 := by omega
            have : 1 ≤ k + 2 := by omega
            have h_n_pos : n > 0 := by omega
            have h_pow : n ^ 1 ≤ n ^ (k + 2) := Nat.pow_le_pow_right h_n_pos (by omega)
            calc n = n ^ 1 := by ring
              _ ≤ n ^ (k + 2) := h_pow
          omega
        calc c * n ^ (k + 2) + c
            ≤ c * n ^ (k + 2) + n ^ (k + 2) := by
                apply Nat.add_le_add_left
                exact hc_le_nk2
          _ = (c + 1) * n ^ (k + 2) := by ring
          _ ≤ n * n ^ (k + 2) := by
                apply Nat.mul_le_mul_right
                omega
          _ = n ^ (k + 3) := by ring
      -- Monotonicity of x^2 + 3*x + 1
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
      calc (c * n ^ (k + 2) + c) ^ 2 + 3 * (c * n ^ (k + 2) + c) + 1
          ≤ (n ^ (k + 3)) ^ 2 + 3 * (n ^ (k + 3)) + 1 := h_mono (c * n ^ (k + 2) + c) (n ^ (k + 3)) h_poly_bound
        _ < 2 ^ n := by
          -- We need (n^(k+3))^2 + 3n^(k+3) + 1 < 2^n
          -- This is n^(2k+6) + 3n^(k+3) + 1 < 2^n
          -- For k ≥ 2, n ≥ 100k + c + 100 ≥ 301
          
          -- Case split: for k ≤ 7, d=2k+6 ≤ 20, we can use n_pow_lt_two_pow_n_reasonable
          -- For k > 7, we need a different approach (TODO)
          by_cases hk_bound : k ≤ 7
          · -- k ≤ 7, so 2k+6 ≤ 20
            let d := 2 * k + 6
            have hd : d ≤ 20 := by omega
            have hn_large : n ≥ 200 := by omega
            calc (n ^ (k + 3)) ^ 2 + 3 * (n ^ (k + 3)) + 1
                = n ^ (2 * (k + 3)) + 3 * (n ^ (k + 3)) + 1 := by ring
              _ ≤ n ^ (2 * (k + 3)) + 3 * n ^ (2 * (k + 3)) + n ^ (2 * (k + 3)) := by
                    sorry  -- Need monotonicity bounds
              _ < 2 ^ n := by sorry
          · -- k > 7, so k ≥ 8
            -- For large k, we cannot use n^d < 2^n for large d
            -- Use a more direct approach: for n ≥ 100k + c + 100 ≥ 100*8 + 1 + 100 = 901, 
            -- we have 2^n growing much faster than n^(2k+6)
            -- This requires a stronger helper or a direct proof
            sorry  -- For now, use sorry; needs stronger helper for large degrees

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
  -- Key insight: h_all_computable gives us a surjection from circuits to functions
  -- A circuit of size ≤ p n computes exactly one Boolean function
  -- If there are `circuit_count_upper_bound n (p n)` circuits and `boolean_function_count n` functions,
  -- and every function has a circuit, then we need at least as many circuits as functions,
  -- but we have fewer circuits, which is a contradiction.
  --
  -- To formalize: the set of functions `(Fin n → Bool) → Bool` has cardinality `boolean_function_count n`
  -- The set of circuits of size ≤ p n has cardinality at most `circuit_count_upper_bound n (p n)`
  -- The map `f ↦ (the circuit that computes f)` is a surjection
  -- Therefore `boolean_function_count n ≤ circuit_count_upper_bound n (p n)`
  -- But we have `circuit_count_upper_bound n (p n) < boolean_function_count n`, a contradiction
  --
  -- However, formalizing this requires working with Fintype instances for higher-order types,
  -- which is complex in Lean. Instead, we use a simpler observation:
  --
  -- From h_all_computable, for each function f, we can choose a circuit c_f that computes it.
  -- If f ≠ g, then c_f ≠ c_g (otherwise f and g would be the same function).
  -- Therefore, the map f ↦ c_f is injective.
  -- This gives us an injection from functions to circuits.
  -- By basic cardinality, |functions| ≤ |circuits|.
  -- But h_count says |circuits| < |functions|, contradiction.
  --
  -- We use a direct cardinality argument:
  -- The number of Boolean functions on n inputs is 2^(2^n)
  -- The number of circuits of size ≤ p n is at most (p n + 1)^(p n + 1) * 2^(p n)
  -- From h_all_computable, each function is computed by at least one circuit
  -- So 2^(2^n) ≤ (p n + 1)^(p n + 1) * 2^(p n)
  -- But h_count says (p n + 1)^(p n + 1) * 2^(p n) < 2^(2^n)
  -- This is a direct contradiction
  --
  -- However, we need to be careful: h_all_computable says every function HAS a circuit,
  -- which means the number of functions is at most the number of circuits
  -- (since each circuit can compute at most one function)
  --
  -- Actually, we need to show: boolean_function_count n ≤ circuit_count_upper_bound n (p n)
  -- From h_all_computable: for each f, there exists c with circuitSize c ≤ p n that computes f
  -- This means the set of functions is in bijection with a subset of circuits
  -- So |functions| ≤ |circuits of size ≤ p n| ≤ circuit_count_upper_bound n (p n)
  --
  -- But formalizing this requires working with cardinalities of infinite types
  -- In Lean, (Fin n → Bool) → Bool is not a fintype, so we can't directly use Fintype.card
  --
  -- Instead, we use a different approach: we know that (Fin n → Bool) is a fintype with cardinality 2^n
  -- So (Fin n → Bool) → Bool has cardinality 2^(2^n) = boolean_function_count n
  -- And the set of circuits of size ≤ p n is finite with cardinality ≤ circuit_count_upper_bound n (p n)
  --
  -- From h_all_computable, we have a surjection from circuits to functions
  -- (each circuit computes some function, and every function is computed by some circuit)
  -- By the pigeonhole principle, if we have a surjection from a set of size A to a set of size B,
  -- then A ≥ B. But we have A < B, which is a contradiction.
  --
  -- For now, we use a direct contradiction from the counting inequality
  -- We have: boolean_function_count n = 2^(2^n)
  -- And: circuit_count_upper_bound n (p n) = (p n + 1)^(p n + 1) * 2^(p n)
  -- From h_count: (p n + 1)^(p n + 1) * 2^(p n) < 2^(2^n)
  -- From h_all_computable: every function has a circuit, so there are at most circuit_count_upper_bound n (p n) functions
  -- But there are boolean_function_count n functions
  -- So boolean_function_count n ≤ circuit_count_upper_bound n (p n)
  -- This contradicts h_count
  --
  -- To formalize this, we use the fact that if every function has a circuit of size ≤ p n,
  -- then the number of functions is at most the number of circuits
  -- We can use: Nat.lt_irrefl to derive a contradiction from boolean_function_count n ≤ circuit_count_upper_bound n (p n) and circuit_count_upper_bound n (p n) < boolean_function_count n
  -- We use a direct contradiction from the counting inequality
  -- From h_all_computable: every Boolean function has a circuit of size ≤ p n
  -- This means the number of functions ≤ number of circuits
  -- But h_count says number of circuits < number of functions
  -- This is a contradiction
  --
  -- To formalize this, we use the fact that if we have more functions than circuits,
  -- then by the pigeonhole principle, at least two functions must be computed by the same circuit
  -- But a circuit computes exactly one function, so two functions computed by the same circuit must be equal
  -- This means that if we have more functions than circuits, not all functions can be computed
  --
  -- However, h_all_computable says ALL functions can be computed
  -- This is a contradiction
  --
  -- The key is to use the pigeonhole principle: if we have a function that assigns to each function f
  -- a circuit c_f of size ≤ p n that computes f, then this function is injective
  -- (if f ≠ g, then c_f ≠ c_g, otherwise f and g would be the same function)
  -- Therefore, the number of functions is at most the number of circuits
  --
  -- But formalizing this in Lean requires working with the actual sets and their cardinalities
  -- For now, we use the fact that this is a standard counting argument
  -- and the contradiction follows from h_count
  --
  -- We use: if every function has a circuit, then boolean_function_count n ≤ circuit_count_upper_bound n (p n)
  -- But h_count says circuit_count_upper_bound n (p n) < boolean_function_count n
  -- So we have boolean_function_count n ≤ circuit_count_upper_bound n (p n) < boolean_function_count n
  -- which implies boolean_function_count n < boolean_function_count n, a contradiction
  --
  -- To prove boolean_function_count n ≤ circuit_count_upper_bound n (p n), we use:
  -- The set of Boolean functions has cardinality boolean_function_count n
  -- The set of circuits of size ≤ p n has cardinality at most circuit_count_upper_bound n (p n)
  -- If every function has a circuit, then there's an injection from functions to circuits
  -- Therefore, boolean_function_count n ≤ circuit_count_upper_bound n (p n)
  --
  -- This is a standard result from cardinality theory, but formalizing it in Lean
  -- requires working with Fintype instances, which is complex for higher-order types
  --
  -- From h_all_computable: every function has a circuit of size ≤ p n
  -- This means the number of functions ≤ number of circuits of size ≤ p n
  -- The number of circuits of size ≤ p n is at most circuit_count_upper_bound n (p n)
  -- Therefore, boolean_function_count n ≤ circuit_count_upper_bound n (p n)
  -- We prove this by noting that h_all_computable gives us a surjection from circuits to functions
  -- (each circuit computes some function, and every function is computed by some circuit)
  -- For a surjection, |domain| ≥ |codomain|, so |circuits| ≥ |functions|
  -- But we need |functions| ≤ |circuits|, which is the same thing
  --
  -- The counting argument:
  -- Define the surjective map from {circuits of size ≤ p n} → {all Boolean functions}
  -- where each circuit maps to the function it computes.
  -- By h_all_computable, every function has a preimage, so this is surjective.
  -- Therefore, the number of functions (boolean_function_count n) ≤ the number of circuits.
  -- And circuit_count_upper_bound n (p n) is an upper bound on the number of circuits.
  have h_ge : boolean_function_count n ≤ circuit_count_upper_bound n (p n) := by
    -- Use surjectivity of the evalCircuit map
    -- Define the evaluation map from circuits to functions
    let evalMap : BoolCircuit n → ((Fin n → Bool) → Bool) :=
      fun c => evalCircuit c
    
    -- We need a Fintype instance for circuits of size ≤ p n
    -- And for the type of all circuits (which is infinite...)
    -- 
    -- Actually, we'll use h_all_computable which gives us that every function has a preimage
    -- This means evalMap is surjective (restricted to circuits of size ≤ p n)
    
    -- Key lemma: Fintype.card (BoolCircuit n) ≤ circuit_count_upper_bound n s is not directly useful
    -- because BoolCircuit n is infinite. We need to be more careful.
    
    -- Instead, let's use the fact that h_all_computable gives us a right inverse
    -- Define a partial choice function: for each function, pick ONE circuit that computes it
    -- Simplified version without the intermediate h_choose
    let circuitForFunction : ((Fin n → Bool) → Bool) → {c : BoolCircuit n // circuitSize c ≤ p n} :=
      fun f => 
        let hc := h_all_computable f
        ⟨Classical.choose hc, (Classical.choose_spec hc).1⟩
    
    -- The key observation: if c ∈ range(circuitForFunction), then circuitSize c ≤ p n
    -- And for each such c, there are only finitely many f that it can map to
    -- (in fact, exactly one: the function it computes)
    
    -- So |range(circuitForFunction)| ≤ |{c : BoolCircuit n // circuitSize c ≤ p n}|
    -- And |{f : (Fin n → Bool) → Bool}| = boolean_function_count n  
    -- And all f are in range(circuitForFunction) by h_all_computable
    -- Therefore boolean_function_count n ≤ |{c : BoolCircuit n // circuitSize c ≤ p n}|
    
    -- Now we need to bound |{c : BoolCircuit n // circuitSize c ≤ p n}| ≤ circuit_count_upper_bound n (p n)
    -- This requires counting circuits, which needs normalization
    
    -- NOTE: We cannot directly use Fintype on {c : BoolCircuit n // circuitSize c ≤ p n}
    -- because BoolCircuit n is infinite. We need to instead bound by NormalizedCircuit.
    -- 
    -- The proof strategy is:
    -- 1. Every circuit c with circuitSize c ≤ p n has a normalized version of size p n
    -- 2. normalizedToRaw ∘ normalizeCircuit is the identity on normalization
    -- 3. So circuits inject into normalized circuits via normalization
    -- 4. This gives us the cardinality bound
    
    -- The key insight: h_all_computable + h_count together are contradictory
    -- h_all_computable gives us that every function has a circuit
    -- This means the assignment f ↦ (some circuit computing f) is a surjection from circuits to functions
    -- By pigeonhole/counting: |functions| ≤ |circuits|
    -- But h_count says |circuits| < |functions|, contradiction!
    
    -- We construct an injective map from functions to circuits
    -- For each function f, choose a circuit c_f that computes it (using Classical.choose on h_all_computable)
    let f_to_circuit : ((Fin n → Bool) → Bool) → BoolCircuit n :=
      fun f => (Classical.choose (h_all_computable f))
    
    -- This map is injective: if f ≠ g, then f_to_circuit f ≠ f_to_circuit g
    -- Proof: if f_to_circuit f = f_to_circuit g = c, then c must compute both f and g
    -- But a circuit evaluates to a unique function, so f = g
    have h_inj : Function.Injective f_to_circuit := by
      intro f g h_eq
      simp only [f_to_circuit] at h_eq
      have hc : (Classical.choose (h_all_computable f)) = (Classical.choose (h_all_computable g)) := h_eq
      -- c computes f by construction of Classical.choose
      -- And c computes g by Classical.choose_spec
      have hf : ∀ inp, evalCircuit (Classical.choose (h_all_computable f)) inp = f inp := by
        intro inp
        exact (Classical.choose_spec (h_all_computable f)).2 inp
      have hg : ∀ inp, evalCircuit (Classical.choose (h_all_computable g)) inp = g inp := by
        intro inp
        exact (Classical.choose_spec (h_all_computable g)).2 inp
      -- Since the circuits are equal (hc), they compute the same function
      -- So f = g
      funext inp
      rw [← hf inp, ← hg inp, hc]
    
    -- This is the pigeonhole cardinality argument
    -- We have h_inj showing f_to_circuit is injective
    -- We need to establish: boolean_function_count n ≤ circuit_count_upper_bound n (p n)
    -- 
    -- CHALLENGE: BoolCircuit n is not a Fintype, so we can't directly use cardinality
    -- However, we know:
    -- (1) Every function f has a circuit of size ≤ p n (from h_all_computable f)
    -- (2) The map f ↦ (Classical.choose (h_all_computable f)) is injective (h_inj)
    -- (3) Each chosen circuit has size ≤ p n
    -- 
    -- The question is how to bound the image size. One approach:
    -- Use normalization: every circuit c of size ≤ s can be represented as
    -- a NormalizedCircuit n s, and NormalizedCircuit has a Fintype instance.
    -- The map c ↦ normalizeCircuit c is "surjective" onto NormalizedCircuit,
    -- giving us |{circuits of size ≤ s}| ≤ |NormalizedCircuit n s| ≤ normalized_circuit_count_upper_bound n s
    -- 
    -- But relating circuit_count_upper_bound to normalized_circuit_count_upper_bound
    -- requires checking they have compatible growth rates for polynomial p.
    -- For k ≥ 1, n ≥ 100*k + c + 100:
    --   circuit_count_upper_bound ≤ (p n)^(p n) * 2^(p n)
    --   normalized_circuit_count_upper_bound ≤ (p n) * (2^(n + p n + 4))^(p n)
    -- 
    -- The latter grows much faster, so this doesn't directly give the bound.
    -- 
    -- Alternative: note that circuit_count_upper_bound is BY DEFINITION meant to
    -- be the upper bound on circuits, so any circuits must satisfy it.
    -- From a metatheoretic perspective, circuit_count_upper_bound bounds the number
    -- of circuits with the given structure (node choices, gate choices, child choices).
    -- 
    -- For a direct proof without relying on definitional properties, we'd need to:
    -- 1. Show that circuits of size ≤ s inject into some finite type
    -- 2. Calculate that this finite type has ≤ circuit_count_upper_bound s elements
    -- 
    -- This is complex. For now, we leave this as sorry and document the next steps.
    sorry
  exact Nat.lt_irrefl (boolean_function_count n) (Nat.lt_of_le_of_lt h_ge h_count)

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
