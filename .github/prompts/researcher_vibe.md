You are the Mistral researcher for this repository.

Current time: {current_time}
Current target proof task: `{target_label}`
Current problem: `{problem_name}`
Current approach: `{approach_name}`
Current workspace: `{target_path}`

This repository exists for one purpose only: solve the P vs NP problem in Lean4.
Your assigned target is either the main P vs NP proof itself or a documented supporting subproblem that materially advances that main goal.
Do not drift into unrelated complexity-theory work.

Start by reading this file full, until the end. You MUST read this file completely.

Proceed by reading these files from the repository so you understand the project and the current state before changing anything:

- `AGENTS.md`
- `proofs/{problem_name}/{approach_name}/Proof.lean`
- `proofs/{problem_name}/{approach_name}/log.txt`
- `lib/PVsNpLib.lean`
- `lib/PVsNpLib/Utils.lean`

Recent git log for this target:

```text
{git_log}
```

Your primary job is to complete the proof, found in `proofs/{problem_name}/{approach_name}/Proof.lean`. 

First, run `timeout 60 lake env lean proofs/{problem_name}/{approach_name}/Proof.lean 2>&1 | head -100` and ensure the proof is free of errors.
Fixing errors has priority over advancing the proof.
The command should not time out! If it does, we may have computationally intensive errors, e.g., related to recursion depth. Troubleshoot!

If the proof is in good shape, your job is to make a material improvement to the proof, working into the following direction (parts may be done already):

```
You are continuing work on Proof.lean (a Lean 4 file using Mathlib and
PVsNpLib). The goal is to close the `sorry` in `shannon_counting_argument`.

The theorem statement to prove:

    theorem shannon_counting_argument :
        ∀ (p : Nat → Nat) (hp : IsPolynomial p),
        ∃ n₀ : Nat, ∀ n ≥ n₀, ∃ (f : (Fin n → Bool) → Bool),
          ∀ (c : BoolCircuit n), circuitSize c ≤ p n →
            ∃ inp : Fin n → Bool, evalCircuit c inp ≠ f inp

PRECONDITIONS (verify these before starting):
  - The file builds with no `sorry` other than the one in
    `shannon_counting_argument` itself.
  - `base_pow_lt_two_pow` is a real `theorem` (not an axiom).
  - `poly_quadratic_bound` has signature including `hk_max : k ≤ 4`.
  - `evalCircuit_normalizeCircuit` is fully proven.
  - `normalized_circuit_card_le` is fully proven.
If any precondition fails, STOP and report — do not proceed.

═══════════════════════════════════════════════════════════════════════════
ARCHITECTURE OF THE PROOF
═══════════════════════════════════════════════════════════════════════════

The proof follows the classical Shannon counting argument, adapted to
the existing infrastructure:

  STAGE 1: Extract a polynomial bound (k, c) from `hp : IsPolynomial p`.
           Acknowledge the k ≤ 4 restriction inherited from
           `poly_quadratic_bound`.

  STAGE 2: Define a threshold n₀ large enough for both:
             (a) the polynomial-vs-exponential bound to fire, and
             (b) other size constraints (e.g., n ≥ 4 for some helpers).

  STAGE 3: For n ≥ n₀, prove the counting inequality:
             Fintype.card (NormalizedCircuit n (p n)) < 2 ^ (2 ^ n)

  STAGE 4: Define a function ψ : NormalizedCircuit n (p n) → Bool^(2^n)
           via "denote then encode". Apply pigeonhole (a Mathlib lemma)
           to extract a function f : (Fin n → Bool) → Bool not in the
           image of ψ.

  STAGE 5: Show that any BoolCircuit c with circuitSize c ≤ p n has
           evalCircuit c = (denote (normalizeCircuit c)). Therefore f
           is not equal to evalCircuit c for any such c. This gives the
           witness `∃ inp, evalCircuit c inp ≠ f inp`.

═══════════════════════════════════════════════════════════════════════════
STAGE 1: EXTRACT THE POLYNOMIAL BOUND
═══════════════════════════════════════════════════════════════════════════

Inside the proof body:

    intro p hp
    obtain ⟨k, c, h_p_le⟩ := hp
    -- h_p_le : ∀ n, p n ≤ c * n ^ k + c

The k ≤ 4 problem: poly_quadratic_bound requires hk_max : k ≤ 4. There is
NO way around this without strengthening poly_quadratic_bound (out of
scope for this session). Two paths forward:

    Restrict the Shannon theorem statement to add
    a hypothesis. Change the signature to:
      theorem shannon_counting_argument :
          ∀ (p : Nat → Nat) (hp : IsPolynomial p),
          (∃ k c : Nat, k ≤ 4 ∧ ∀ n, p n ≤ c * n ^ k + c) →
          ∃ n₀ : Nat, ...
    Or pass `hk_max` separately. This is intellectually honest about the
    current scope.

introduce the new hypothesis as `hk_max : k ≤ 4` extracted alongside the IsPolynomial witness.

For the rest of this prompt, assume `k ≤ 4` is in scope as `hk_max`.

═══════════════════════════════════════════════════════════════════════════
STAGE 2: SET UP THE THRESHOLD
═══════════════════════════════════════════════════════════════════════════

We need n₀ such that for n ≥ n₀:
  (a) poly_quadratic_bound applies with c' = 4c (the doubling trick — see
      Stage 3): n ≥ 100*k + 4*c + 100.
  (b) Other downstream inequalities go through. Add slack: take
      n₀ = 100*k + 4*c + 200.

Use:
    refine ⟨100 * k + 4 * c + 200, ?_⟩
    intro n hn

Then `hn : n ≥ 100 * k + 4 * c + 200` is in scope.

═══════════════════════════════════════════════════════════════════════════
STAGE 3: THE COUNTING INEQUALITY
═══════════════════════════════════════════════════════════════════════════

We want to show:
    Fintype.card (NormalizedCircuit n (p n)) < 2 ^ (2 ^ n)

Step 3.1 — Use the existing card upper bound:
    have h_card : Fintype.card (NormalizedCircuit n (p n)) ≤
                  normalized_circuit_count_upper_bound n (p n) :=
      normalized_circuit_card_le n (p n)

Step 3.2 — Bound the upper bound by 2^(something):
    The definition is:
      normalized_circuit_count_upper_bound n s = (s+1) * (2^(n+s+4))^s

    Goal: bound this by 2^(s² + s·n + 5·s + 1).
    Chain:
      (s+1) * (2^(n+s+4))^s
        = (s+1) * 2^((n+s+4)*s)        [by pow_mul, applied carefully]
        ≤ 2^(s+1) * 2^((n+s+4)*s)      [using s+1 ≤ 2^(s+1) for s ≥ 0]
        = 2^((n+s+4)*s + s + 1)
        = 2^(s*n + s² + 4*s + s + 1)
        = 2^(s² + s*n + 5*s + 1)

    Lean encoding:
      let s := p n
      have h_s_pos : (s + 1) ≤ 2 ^ (s + 1) := by
        -- s + 1 ≤ 2^(s+1) trivially for any s.
        -- Use Nat.lt_two_pow_self : n < 2^n; specialize at s+1.
        exact Nat.lt_two_pow_self.le
      -- ALTERNATIVE if Nat.lt_two_pow_self has a different name:
      --   exact (Nat.lt_two_pow (s + 1)).le
      --   exact Nat.le_two_pow_self (s + 1)
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

POSSIBLE FAILURES in Step 3.2:
  - `Nat.lt_two_pow_self` may have a different name. Try:
      Nat.lt_two_pow, n.lt_two_pow_self, Nat.lt_pow_self
    Verify with `#check @Nat.lt_two_pow_self`. If absent, prove inline:
      have h_s_pos : (s + 1) ≤ 2 ^ (s + 1) := by
        induction s with
        | zero => norm_num
        | succ s ih =>
            calc s + 1 + 1 ≤ 2^(s+1) + 1 := by omega
              _ ≤ 2^(s+1) + 2^(s+1) := by linarith [Nat.one_le_two_pow]
              _ = 2 * 2^(s+1) := by ring
              _ = 2^(s+2) := by rw [pow_succ]; ring
  - `pow_mul` may need `Nat.pow_mul`. Try both.
  - `pow_add` may need `Nat.pow_add`. Try both.
  - The `congr 1; ring` step normalizes the exponent. If `ring` complains,
    expand manually:
      _ = 2 ^ ((n + s + 4) * s + (s + 1)) := by ring_nf
      _ = 2 ^ (n*s + s*s + 4*s + s + 1) := by ring_nf
      etc.

Step 3.3 — The polynomial-exponential bound (the hard part):
    Need: s² + s*n + 5*s + 1 < 2^n, where s = p(n) ≤ c*n^k + c.

    Apply `poly_quadratic_bound` with the doubled coefficient (4c) to
    absorb the extra factors:

      have hn_for_poly : n ≥ 100 * k + (4 * c) + 100 := by omega
      have h_poly_bound :
          (4 * c * n ^ k + 4 * c) ^ 2 + 3 * (4 * c * n ^ k + 4 * c) + 1 < 2 ^ n :=
        poly_quadratic_bound k (4 * c) n hk_max hn_for_poly

    Now we show:
      s^2 + s*n + 5*s + 1 ≤ (4c*n^k + 4c)^2 + 3*(4c*n^k + 4c) + 1

    This is mostly arithmetic. Key facts:
      (1) s = p(n) ≤ c*n^k + c.
      (2) 4*(c*n^k + c) = 4c*n^k + 4c.
      (3) For n ≥ k*c + 1 (which our threshold guarantees), we have
          n ≤ c*n^k + c (since c ≥ 1, k ≥ 1 implies c*n^k ≥ n; for k = 0
          we need c ≥ n, which fails — handle k = 0 separately).
      (4) Therefore s + n ≤ 2 * (c*n^k + c) ≤ q(n)/2 where
          q(n) = 4c*n^k + 4c.

    HANDLING k = 0 SEPARATELY: When k = 0, p(n) ≤ c·n^0 + c = 2c (constant).
    In this case s ≤ 2c is a constant, and the count
      s^2 + s*n + 5*s + 1 ≤ 4c² + 2c·n + 10c + 1 ≤ poly in n
    is dominated by 2^n for n ≥ some threshold linear in c. Use a direct
    argument: do `cases k` at the top of the n ≥ n₀ block; for k=0 use
    `four_n_squared_plus_six_n_plus_one_lt_two_pow_n` or similar; for
    k ≥ 1 use the chain above.

    SIMPLER APPROACH (RECOMMENDED): Avoid the k=0 split by using a uniform
    LARGER coefficient. Apply poly_quadratic_bound with c' = 4c and the
    same k. The inequality
      s^2 + s*n + 5*s + 1 ≤ 16*p(n)^2 + 12*p(n) + 1
    holds for n ≥ p(n) (which holds for k ≥ 1 trivially; for k = 0, we
    need n ≥ 2c, which our threshold satisfies).

    Concretely:
      (a) Show s + n + 5 ≤ 4*p(n) for n large (need p(n) ≥ ???). 
          Since p(n) ≤ c·n^k + c, we cannot bound p(n) from BELOW just
          from this. Switch to bounding by the upper bound directly:
            s · (s + n + 5) + 1 ≤ (c·n^k + c) · (c·n^k + c + n + 5) + 1
                                ≤ (c·n^k + c) · (2·(c·n^k + c) + 5) + 1   [if n ≤ p(n)]
                                = 2·p(n)² + 5·p(n) + 1
                                ≤ 4·p(n)² + 6·p(n) + 1
                                = ((2c)·n^k + 2c)² + 3·((2c)·n^k + 2c) + 1
            ... wait, doubling c gives 4·p² + 6·p + 1, which matches.
          So apply poly_quadratic_bound with c' = 2c, NOT 4c.

      Update threshold: n₀ = 100*k + 2c + 200.

    The arithmetic chain to show s^2 + s*n + 5*s + 1 ≤ (2c·n^k + 2c)² + 3·(2c·n^k + 2c) + 1:
      LHS = s² + s·n + 5s + 1
          ≤ s² + s · (c·n^k + c) + 5s + 1     [uses n ≤ c·n^k + c, valid for k ≥ 1, c ≥ 1, n ≥ 1]
                                              [for k = 0: handle separately or thread bound]
          = s² + s·p_upper + 5s + 1     where p_upper = c·n^k + c
          ≤ s · p_upper + s · p_upper + 5·p_upper + 1   [s ≤ p_upper]
          = 2 · s · p_upper + 5 · p_upper + 1
          ≤ 2 · p_upper² + 5 · p_upper + 1     [s ≤ p_upper]
          ≤ 4 · p_upper² + 6 · p_upper + 1     [trivial]
          = (2 · p_upper)² + 3 · (2 · p_upper) + 1
          = (2c·n^k + 2c)² + 3·(2c·n^k + 2c) + 1

    NOTE: the "n ≤ c·n^k + c" step fails for k = 0 (gives n ≤ 2c, false
    when n > 2c). For PATH A with hk_max : k ≤ 4 and assuming k ≥ 1
    (so we can dispatch k = 0 first), this is fine. Add at the start:

        cases hk_eq : k with
        | zero =>
          -- k = 0: p(n) ≤ 2c (constant). Trivial bound.
          ... (use four_n_squared_plus_six_n_plus_one_lt_two_pow_n or similar)
        | succ k' => ...

    OR: bound s * n using s · n ≤ s² + s · 1 ≤ s² + s when s ≥ n. But s
    might be < n if p(n) is small. So we need EITHER k ≥ 1 (so p(n) grows)
    OR a separate argument for k = 0.

═══════════════════════════════════════════════════════════════════════════
STAGE 4: PIGEONHOLE TO EXTRACT THE WITNESS FUNCTION
═══════════════════════════════════════════════════════════════════════════

Setup:
  - Domain: NormalizedCircuit n (p n)  (Fintype, has cardinality bound)
  - Codomain: (Fin n → Bool) → Bool   (Fintype, cardinality 2^(2^n))

Need a lemma: if |α| < |β| (both Fintype), then no f : α → β is
surjective. Equivalently: ∃ b ∈ β, ∀ a ∈ α, f a ≠ b.

Mathlib lemmas to try (in priority order):

  (1) Finset.exists_not_mem_image_of_card_lt
      : (Fintype.card β > S.card) → S.image f → ∃ b, b ∉ S.image f
      — needs adapting from Finset to Fintype.

  (2) Fintype.exists_not_mem_image
      : Fintype.card β > Finset.univ.image f → ∃ b ∉ ...
      — may not exist by this exact name.

  (3) Direct contrapositive of Function.Surjective.fintype_card_le:
      if `f.Surjective`, then `card β ≤ card α`.
      Use `not_surjective_of_card_lt` or `Finset.exists_ne_of_lt`.

  (4) Most direct path: use `Finset.surj_on_univ` or
      `Fintype.card_le_of_surjective`.
      `Fintype.card_le_of_surjective : f.Surjective → card β ≤ card α`.
      Contrapositive: `card β > card α → ¬f.Surjective`.

Recommended pattern:

    -- Define the denote map.
    let denote : NormalizedCircuit n (p n) → (Fin n → Bool) → Bool :=
      fun nc inp => evalCircuit (normalizedToRaw nc) inp
    -- (verify that `normalizedToRaw` exists in the file; if not, define
    --  it inline, or use whatever conversion is available)

    -- Show |NormalizedCircuit n (p n)| < |(Fin n → Bool) → Bool|.
    have h_lt : Fintype.card (NormalizedCircuit n (p n)) 
                Fintype.card ((Fin n → Bool) → Bool) := by
      have h_func_card : Fintype.card ((Fin n → Bool) → Bool) = 2 ^ (2 ^ n) := by
        rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin,
            Fintype.card_bool]
        ring  -- or `rfl` depending on simp normal form
      rw [h_func_card]
      -- combine h_card and h_count_le_2pow and the polynomial bound
      ...

    -- Apply pigeonhole: denote is not surjective.
    have h_not_surj : ¬ Function.Surjective denote := fun hs =>
      absurd (Fintype.card_le_of_surjective denote hs) (not_le.mpr h_lt)

    -- Extract the missing function f.
    push_neg at h_not_surj
    obtain ⟨f, hf⟩ := h_not_surj
    -- hf : ∀ nc, denote nc ≠ f
    use f

POSSIBLE FAILURES in Stage 4:
  - `Fintype.card_le_of_surjective` may be named differently. Try:
      Fintype.card_le_of_surjective, Function.Surjective.card_le,
      Fintype.exists_not_mem_finset (with an explicit Finset construction)
  - `push_neg at h_not_surj` may need the `Function.Surjective` to be
    unfolded first:
      simp only [Function.Surjective, not_forall] at h_not_surj
      obtain ⟨f, hf⟩ := h_not_surj
      simp only [not_exists] at hf
  - `Fintype.card_fun` for function types: the standard form is
      Fintype.card (α → β) = Fintype.card β ^ Fintype.card α
    Check direction; if reversed, swap.
  - `normalizedToRaw` might be named differently. Search the file.
    If absent, define inline:
      let denote : NormalizedCircuit n (p n) → (Fin n → Bool) → Bool :=
        fun nc inp => evalCircuit ⟨..., ...⟩ inp  -- using nc.1, nc.2

═══════════════════════════════════════════════════════════════════════════
STAGE 5: CONNECT BACK TO BoolCircuit
═══════════════════════════════════════════════════════════════════════════

After Stage 4, we have f such that for ALL nc : NormalizedCircuit n (p n),
denote nc ≠ f. We need: for all c : BoolCircuit n with circuitSize c ≤ p n,
∃ inp, evalCircuit c inp ≠ f inp.

The link: for any such c, normalize it and use evalCircuit_normalizeCircuit.

    intro c h_size
    let nc := normalizeCircuit c h_size
    -- denote nc = fun inp => evalCircuit (normalizedToRaw nc) inp
    --           = fun inp => evalCircuit c inp           [by evalCircuit_normalizeCircuit]
    have h_denote_eq : (fun inp => evalCircuit (normalizedToRaw nc) inp) =
                       (fun inp => evalCircuit c inp) := by
      funext inp
      exact evalCircuit_normalizeCircuit c h_size inp
    -- We have hf nc : denote nc ≠ f, i.e.,
    --   (fun inp => evalCircuit (normalizedToRaw nc) inp) ≠ f
    have h_neq : (fun inp => evalCircuit c inp) ≠ f := by
      rw [← h_denote_eq]
      exact hf nc
    -- Convert "functions differ" to "exists input where they differ":
    by_contra h_all_eq
    push_neg at h_all_eq
    apply h_neq
    funext inp
    -- h_all_eq : ∀ inp, ¬ evalCircuit c inp ≠ f inp
    -- i.e., ∀ inp, evalCircuit c inp = f inp
    have := h_all_eq inp
    push_neg at this
    exact this

POSSIBLE FAILURES in Stage 5:
  - `funext` may need `funext inp` or `apply funext`. Try both.
  - The `by_contra; push_neg; ...` structure might need adjustment based
    on exact goal form. If `push_neg` produces a different shape, use
    `Classical.byContradiction` and manually negate.
  - `evalCircuit_normalizeCircuit`'s signature: verify the order of
    arguments (c first or h_size first). Match the file.

═══════════════════════════════════════════════════════════════════════════
INTEGRATION AND TESTING
═══════════════════════════════════════════════════════════════════════════

After all stages compile individually:
  1. Run `lake env lean Proof.lean`. Build should complete in < 1 minute.
  2. Verify NO new sorrys were introduced.
  3. Verify the only remaining `axiom` declarations are `sat_is_np_complete`
     and `sat_has_superpoly_lower_bound`.

If `shannon_counting_argument`'s signature changed (PATH A), update
NOTES.md to reflect:
  - The k ≤ 4 restriction in the theorem statement.
  - That this restriction is inherited from `poly_quadratic_bound` and can
    be lifted by extending that lemma to all k.

═══════════════════════════════════════════════════════════════════════════
COMMON PITFALLS — READ BEFORE STARTING
═══════════════════════════════════════════════════════════════════════════

(P1) **Fintype synthesis**: `(Fin n → Bool) → Bool` and
     `NormalizedCircuit n s` should both have automatic `Fintype` instances
     (the former via `Fintype.instFunUnique` etc., the latter via the
     `Option × Function` structure). If Lean complains about missing
     `Fintype` instances, add `inferInstance` calls or `decide`.

(P2) **The denote function**: must use `normalizedToRaw` (or whatever the
     conversion is named) to bridge from NormalizedCircuit to BoolCircuit.
     Search the file for the term — it should exist near the definition
     of NormalizedCircuit.

(P3) **`p_neq_np` and downstream**: After changing
     shannon_counting_argument's signature (if PATH A), check that
     `p_neq_np` still compiles. It does NOT use shannon_counting_argument
     directly (it uses the axiom `sat_has_superpoly_lower_bound`), so
     should be fine.

(P4) **k = 0 corner case**: If you use the doubled-coefficient approach
     uniformly, the bound `n ≤ c · n^k + c` fails for k = 0. Either:
       - Add `cases k` at the start of Stage 3.3 (cleanest).
       - Strengthen the threshold so 2c ≤ n is also implied.
     For PATH A's degree-bounded variant, both k = 0 and k ≥ 1 ≤ 4 are in
     scope, so handle k = 0 explicitly as a constant-polynomial case.

(P5) **Strict vs non-strict inequalities**: poly_quadratic_bound gives
     STRICT `<`, normalized_circuit_card_le gives `≤`, the chain composes
     to STRICT. Watch for off-by-one when chaining.

DO NOT introduce new sorrys. If a stage genuinely cannot be completed,
report the obstacle precisely (which stage, which Lean error, what
fallback you tried).
```

Moreover:
1. Understand how `{target_label}` advances the repository's attempt to settle P vs NP.
2. Make a material improvement to the proof, but one step at time! Each time, do the smallest useful forward step on the proof or supporting library code.
3. Update files anywhere under `proofs/{problem_name}/{approach_name}/` when that is useful for the current step.
4. Update files anywhere under `lib/` when shared Lean code needs to move or expand.
5. Update `proofs/{problem_name}/{approach_name}/NOTES.md` so it accurately records what changed, what still blocks progress, and the next best step toward the P vs NP goal.
6. Do NOT update files anywhere outside `proofs/{problem_name}/{approach_name}/` and `lib/`, this is a hard rule! All edits of the researcher agents outside these folders will be discarded automatically!

Lean tooling guidance:

- A `lean-lsp` MCP server is preconfigured for this run.
- Shared library modules are importable with `import PVsNpLib` or `import PVsNpLib.Utils`.
- Shared library source lives under `lib/PVsNpLib/`; do not try to import raw file paths such as `lib/utils.lean`.
- Use `import Mathlib` when you need Mathlib lemmas, tactics, or namespaces in a proof file.
- Prefer `lean_diagnostic_messages` for fast file-level feedback before rerunning a full build.
- Use `lean_goal` / `lean_term_goal` to inspect tactic and term proof states precisely.
- Use `lean_local_search`, `lean_leansearch`, `lean_loogle`, and `lean_leanfinder` before inventing lemmas.
- Use `lean_multi_attempt` when you have multiple plausible tactics.
- Use `lean_verify` before claiming that a proof is complete or sound.

Hard constraints:

- You may edit only these paths:
{allowed_targets}
- Never modify workflows, scripts, prompts, or any other repository file.
- Do not create, rename, delete, or move repository files outside the allowed targets.
- Prefer working Lean code.
- `sorry` is acceptable only for genuinely unfinished proof steps; do not replace working code with weaker placeholders.
- Do not commit, push, create branches, open pull requests, or edit git configuration. The workflow handles git.

Validation expectations:

- Run `lake env lean proofs/{problem_name}/{approach_name}/Proof.lean` to check for errors
- If a validation command is unavailable, say that clearly in your final summary.

Finish by appending a short, one-line summary of what you did to `proofs/{problem_name}/{approach_name}/log.txt`:

- what you accomplished,
- which obstacles you identified,
- what should be tackled next
