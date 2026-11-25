module

public import Adian.FinPres
public import Adian.TMHalting
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Computability.Primrec.List
public import Mathlib.Tactic.Linarith

/-!
# Deterministic Modular Machines and Simulation of Binary `TM0`

Following Aanderaa and Cohen (1980) / Rotman, a **modular machine** of modulus `m ≥ 2` consists of
a finite set of quadruples `(a, b, c, dir)` (`0 ≤ a, b < m`, `0 ≤ c < m²`, `dir ∈ {R, L}`) with
distinct residue pairs `(a, b)` and no rule with `(a, b) = (0, 0)`. It acts deterministically on
`ℤ × ℤ` by:
- `R`: `(u * m + a, v * m + b) ↦ (u * m² + c, v)`
- `L`: `(u * m + a, v * m + b) ↦ (u, v * m² + c)`

Main results:
- `modStep_deterministic`, `not_modStep_zero`, `rule_reachesZero_iff`: The halting basin
  `ReachesZero M := { p : ℤ × ℤ | ReflTransGen (ModStep M) p (0, 0) }` is closed under BOTH forward
  and backward rule applications.
- `tmToModularMachine`: Compiles any finite-state binary `TM0` machine with unique halting state
  `qHalt` into a deterministic modular machine of modulus `m = 2 + 3 * Q`.
- `exists_undecidable_modularMachine`: Combines `exists_undecidable_blank_tm0` with
  `tmToModularMachine` to yield a deterministic modular machine `M` and a `Primrec` input encoding
  `encodeInit : ℕ → ℕ × ℕ` such that `fun n => ((encodeInit n).1, (encodeInit n).2) ∈ ReachesZero M`
  is undecidable.
-/

@[expose] public section

open Turing Relation

namespace Adian

/-! ### Part 1: Deterministic Modular Machines on `ℤ × ℤ` -/

/-- Direction of a modular machine quadruple. -/
inductive ModDir
  | R
  | L
  deriving DecidableEq

/-- A single modular machine quadruple `(a, b, c, dir)` of modulus `m`. -/
structure ModQuad (m : ℕ) where
  a : ℕ
  b : ℕ
  c : ℕ
  dir : ModDir
  ha : a < m
  hb : b < m
  hc : c < m * m

/-- Output of quadruple `q` on quotients `(u, v) : ℤ × ℤ`. -/
def ModQuad.applyPair {m : ℕ} (q : ModQuad m) (u v : ℤ) : ℤ × ℤ :=
  match q.dir with
  | .R => (u * ((m * m : ℕ) : ℤ) + (q.c : ℤ), v)
  | .L => (u, v * ((m * m : ℕ) : ℤ) + (q.c : ℤ))

/-- A deterministic modular machine with `(0, 0)` terminal. -/
structure ModularMachine where
  m : ℕ
  hm : 2 ≤ m
  rules : List (ModQuad m)
  deterministic : ∀ i j : Fin rules.length,
    rules[i].a = rules[j].a → rules[i].b = rules[j].b → i = j
  no_zero_rule : ∀ q ∈ rules, ¬ (q.a = 0 ∧ q.b = 0)

/-- One computation step of modular machine `M` on `ℤ × ℤ`. -/
def ModStep (M : ModularMachine) (p p' : ℤ × ℤ) : Prop :=
  ∃ q ∈ M.rules, ∃ u v : ℤ,
    p = (u * (M.m : ℤ) + (q.a : ℤ), v * (M.m : ℤ) + (q.b : ℤ)) ∧
    p' = q.applyPair u v

/-- The set `S₀(M) ⊆ ℤ × ℤ` of configurations halting at `(0, 0)`. -/
def ReachesZero (M : ModularMachine) : Set (ℤ × ℤ) :=
  { p | ReflTransGen (ModStep M) p (0, 0) }

private theorem int_div_mod_eq {m a₁ a₂ : ℕ} {u₁ u₂ : ℤ}
    (ha₁ : a₁ < m) (ha₂ : a₂ < m)
    (heq : u₁ * (m : ℤ) + (a₁ : ℤ) = u₂ * (m : ℤ) + (a₂ : ℤ)) :
    u₁ = u₂ ∧ a₁ = a₂ := by
  have hm : (0 : ℤ) < (m : ℤ) := by omega
  have hmod1 : (u₁ * (m : ℤ) + (a₁ : ℤ)) % (m : ℤ) = (a₁ : ℤ) := by
    rw [Int.mul_add_emod_self_right, Int.emod_eq_of_lt (by omega) (by omega)]
  have hmod2 : (u₂ * (m : ℤ) + (a₂ : ℤ)) % (m : ℤ) = (a₂ : ℤ) := by
    rw [Int.mul_add_emod_self_right, Int.emod_eq_of_lt (by omega) (by omega)]
  have ha : (a₁ : ℤ) = (a₂ : ℤ) := by rw [← hmod1, heq, hmod2]
  have ha_nat : a₁ = a₂ := by omega
  subst ha_nat
  have hmul : u₁ * (m : ℤ) = u₂ * (m : ℤ) := by omega
  exact ⟨mul_right_cancel₀ (by omega : (m : ℤ) ≠ 0) hmul, rfl⟩

theorem modStep_deterministic (M : ModularMachine) {p p₁ p₂ : ℤ × ℤ}
    (h₁ : ModStep M p p₁) (h₂ : ModStep M p p₂) : p₁ = p₂ := by
  rcases h₁ with ⟨q₁, hq₁, u₁, v₁, hp₁, rfl⟩
  rcases h₂ with ⟨q₂, hq₂, u₂, v₂, hp₂, rfl⟩
  have hpair := hp₁.symm.trans hp₂
  simp only [Prod.mk.injEq] at hpair
  obtain ⟨rfl, ha⟩ := int_div_mod_eq q₁.ha q₂.ha hpair.1
  obtain ⟨rfl, hb⟩ := int_div_mod_eq q₁.hb q₂.hb hpair.2
  rw [List.mem_iff_getElem] at hq₁ hq₂
  rcases hq₁ with ⟨i, hi, rfl⟩
  rcases hq₂ with ⟨j, hj, rfl⟩
  have hij : (⟨i, hi⟩ : Fin M.rules.length) = ⟨j, hj⟩ := M.deterministic ⟨i, hi⟩ ⟨j, hj⟩ ha hb
  have hij_val : i = j := congrArg Fin.val hij
  subst hij_val
  rfl

theorem not_modStep_zero (M : ModularMachine) (p' : ℤ × ℤ) : ¬ ModStep M (0, 0) p' := by
  rintro ⟨q, hq, u, v, hp, _⟩
  simp only [Prod.mk.injEq] at hp
  have h1 : (0 : ℤ) * (M.m : ℤ) + (0 : ℕ) = u * (M.m : ℤ) + (q.a : ℤ) := by simpa using hp.1
  have h2 : (0 : ℤ) * (M.m : ℤ) + (0 : ℕ) = v * (M.m : ℤ) + (q.b : ℤ) := by simpa using hp.2
  have hm0 : 0 < M.m := by have := M.hm; omega
  have ha : 0 = q.a := (int_div_mod_eq hm0 q.ha h1).2
  have hb : 0 = q.b := (int_div_mod_eq hm0 q.hb h2).2
  exact M.no_zero_rule q hq ⟨ha.symm, hb.symm⟩

theorem reachesZero_of_modStep (M : ModularMachine) {p p' : ℤ × ℤ}
    (h : ModStep M p p') (hp' : p' ∈ ReachesZero M) : p ∈ ReachesZero M :=
  ReflTransGen.head h hp'

theorem modStep_reachesZero (M : ModularMachine) {p p' : ℤ × ℤ}
    (h : ModStep M p p') (hp : p ∈ ReachesZero M) : p' ∈ ReachesZero M := by
  rcases ReflTransGen.cases_head hp with heq | ⟨p₁, hp₁, hrest⟩
  · exfalso; exact not_modStep_zero M p' (heq ▸ h)
  · rwa [modStep_deterministic M hp₁ h] at hrest

theorem modStep_reachesZero_iff (M : ModularMachine) {p p' : ℤ × ℤ}
    (h : ModStep M p p') : p ∈ ReachesZero M ↔ p' ∈ ReachesZero M :=
  ⟨modStep_reachesZero M h, reachesZero_of_modStep M h⟩

theorem rule_reachesZero_iff (M : ModularMachine) {q : ModQuad M.m}
    (hq : q ∈ M.rules) (u v : ℤ) :
    (u * (M.m : ℤ) + (q.a : ℤ), v * (M.m : ℤ) + (q.b : ℤ)) ∈ ReachesZero M ↔
      q.applyPair u v ∈ ReachesZero M :=
  modStep_reachesZero_iff M ⟨q, hq, u, v, rfl, rfl⟩

/-! ### Part 2: Base-`m` Encoding of Binary `ListBlank` Tapes -/

section TapeEncoding

/-- Convert a Boolean tape symbol to `{0, 1}`. -/
def bitNat (b : Bool) : ℕ := if b then 1 else 0

theorem bitNat_lt (b : Bool) {m : ℕ} (hm : 2 ≤ m) : bitNat b < m := by
  cases b <;> simp [bitNat] <;> omega

/-- Base-`m` encoding of a binary list (head is the least significant digit). -/
def encList (m : ℕ) : List Bool → ℕ
  | [] => 0
  | b :: bs => encList m bs * m + bitNat b

theorem encList_replicate_false (m n : ℕ) : encList m (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, encList, bitNat, ih]

theorem encList_append_replicate_false (m : ℕ) (l : List Bool) (n : ℕ) :
    encList m (l ++ List.replicate n false) = encList m l := by
  induction l with
  | nil => exact encList_replicate_false m n
  | cons b tl ih => simp [encList, ih]

/-- Well-defined base-`m` encoding of a binary half-tape `ListBlank Bool`. -/
def encListBlank (m : ℕ) (L : ListBlank Bool) : ℕ :=
  L.liftOn (encList m) fun a _ ⟨n, hn⟩ => by
    subst hn
    exact (encList_append_replicate_false m a n).symm

@[simp]
theorem encListBlank_mk (m : ℕ) (l : List Bool) :
    encListBlank m (ListBlank.mk l) = encList m l := rfl

@[simp]
theorem encListBlank_empty (m : ℕ) : encListBlank m (∅ : ListBlank Bool) = 0 := rfl

@[simp]
theorem encListBlank_cons (m : ℕ) (b : Bool) (L : ListBlank Bool) :
    encListBlank m (L.cons b) = encListBlank m L * m + bitNat b := by
  refine L.induction_on fun l => ?_
  rfl

theorem encListBlank_eq_tail (m : ℕ) (L : ListBlank Bool) :
    encListBlank m L = encListBlank m L.tail * m + bitNat L.head := by
  conv_lhs => rw [← ListBlank.cons_head_tail L]
  exact encListBlank_cons m L.head L.tail

theorem encListBlank_eq_zero_iff {m : ℕ} (hm : 2 ≤ m) (L : ListBlank Bool) :
    encListBlank m L = 0 ↔ L = ∅ := by
  constructor
  · refine L.induction_on fun l => ?_
    intro h
    induction l with
    | nil => rfl
    | cons b tl ih =>
      simp only [encListBlank_mk, encList] at h
      have hb : b = false := by cases b <;> simp [bitNat] at h ⊢
      have htl : encList m tl = 0 := by
        rw [hb] at h
        simp [bitNat] at h
        omega
      subst hb
      have htl_e : ListBlank.mk tl = (∅ : ListBlank Bool) := ih htl
      change ListBlank.cons false (ListBlank.mk tl) = ∅
      rw [htl_e]
      exact Quotient.sound' (Or.inr ⟨1, rfl⟩)
  · rintro rfl; rfl

theorem primrec_encList (m : ℕ) : Primrec (encList m) := by
  have hbit : Primrec bitNat := Primrec.dom_finite bitNat
  have hfold := Primrec.list_foldr (α := List Bool) (β := Bool) (σ := ℕ)
    Primrec.id (Primrec.const 0)
    (Primrec.to₂ (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.snd.comp Primrec.snd) (Primrec.const m))
      (hbit.comp (Primrec.fst.comp Primrec.snd))))
  refine hfold.of_eq fun l => ?_
  change List.foldr (fun b s => s * m + bitNat b) 0 l = encList m l
  induction l with
  | nil => rfl
  | cons b tl ih => simp [encList, ih]

end TapeEncoding

/-! ### Part 3: Compiling a Blank-Halting Binary `TM0` to a `ModularMachine` -/

section TM0ToModular

/-- Modulus `m = 2 + 3 * Q` for simulating a `Q`-state binary `TM0`. -/
def tmModulus (Q : ℕ) : ℕ := 2 + 3 * Q

/-- Primary state digit `L(q) = 2 + q` (stored in the left coordinate's residue). -/
def tagL (Q : ℕ) (q : Fin Q) : ℕ := 2 + q.val

/-- Right-cleanup state digit `R(q) = 2 + Q + q` (stored in the right coordinate's residue). -/
def tagR (Q : ℕ) (q : Fin Q) : ℕ := 2 + Q + q.val

/-- Middle move-left state digit `M(q) = 2 + 2 * Q + q` (stored in the right coordinate's residue). -/
def tagM (Q : ℕ) (q : Fin Q) : ℕ := 2 + 2 * Q + q.val

theorem tagL_lt {Q : ℕ} (q : Fin Q) : tagL Q q < tmModulus Q := by
  unfold tagL tmModulus; omega

theorem tagR_lt {Q : ℕ} (q : Fin Q) : tagR Q q < tmModulus Q := by
  unfold tagR tmModulus; omega

theorem tagM_lt {Q : ℕ} (q : Fin Q) : tagM Q q < tmModulus Q := by
  unfold tagM tmModulus; omega

theorem digit_pair_lt_sq {m x y : ℕ} (hx : x < m) (hy : y < m) :
    x * m + y < m * m := by
  have : x * m + y < (x + 1) * m := by nlinarith
  have : (x + 1) * m ≤ m * m := Nat.mul_le_mul_right m (Nat.succ_le_of_lt hx)
  omega

/-- Canonical encoding of a `TM0` configuration `(q, T)` into `ℤ × ℤ`. -/
def encCfg (Q : ℕ) (cfg : TM0.Cfg Bool (Fin Q)) : ℤ × ℤ :=
  let m := tmModulus Q
  ((encListBlank m cfg.Tape.left : ℤ) * (m : ℤ) + (tagL Q cfg.q : ℤ),
   (encListBlank m cfg.Tape.right₀ : ℤ))

/-- Primary rules generated from the transition table of `M`. -/
def primaryRules {Q : ℕ} [NeZero Q]
    (M : @TM0.Machine Bool (Fin Q) ⟨⟨0, NeZero.pos Q⟩⟩) : List (ModQuad (tmModulus Q)) :=
  (List.finRange Q).flatMap fun q =>
    ([false, true] : List Bool).filterMap fun b =>
      match M q b with
      | some (q', .move .right) =>
        some ⟨tagL Q q, bitNat b, bitNat b * tmModulus Q + tagL Q q', .R,
          tagL_lt q, bitNat_lt b (by unfold tmModulus; omega),
          digit_pair_lt_sq (bitNat_lt b (by unfold tmModulus; omega)) (tagL_lt q')⟩
      | some (q', .write s) =>
        some ⟨tagL Q q, bitNat b, bitNat s * tmModulus Q + tagR Q q', .L,
          tagL_lt q, bitNat_lt b (by unfold tmModulus; omega),
          digit_pair_lt_sq (bitNat_lt s (by unfold tmModulus; omega)) (tagR_lt q')⟩
      | some (q', .move .left) =>
        some ⟨tagL Q q, bitNat b, bitNat b * tmModulus Q + tagM Q q', .L,
          tagL_lt q, bitNat_lt b (by unfold tmModulus; omega),
          digit_pair_lt_sq (bitNat_lt b (by unfold tmModulus; omega)) (tagM_lt q')⟩
      | none =>
        if b = false then
          some ⟨tagL Q q, 0, 0, .L, tagL_lt q, by unfold tmModulus; omega,
            by unfold tmModulus; positivity⟩
        else none

/-- Cleanup rules `(l, tagR q', l * m + tagL q', R)` shifting the state tag back to the left. -/
def cleanupRules (Q : ℕ) : List (ModQuad (tmModulus Q)) :=
  (List.finRange Q).flatMap fun q =>
    ([false, true] : List Bool).map fun l =>
      ⟨bitNat l, tagR Q q, bitNat l * tmModulus Q + tagL Q q, .R,
        bitNat_lt l (by unfold tmModulus; omega), tagR_lt q,
        digit_pair_lt_sq (bitNat_lt l (by unfold tmModulus; omega)) (tagL_lt q)⟩

/-- Middle rules `(l, tagM q', l * m + tagR q', L)` shifting one symbol from left to right. -/
def middleRules (Q : ℕ) : List (ModQuad (tmModulus Q)) :=
  (List.finRange Q).flatMap fun q =>
    ([false, true] : List Bool).map fun l =>
      ⟨bitNat l, tagM Q q, bitNat l * tmModulus Q + tagR Q q, .L,
        bitNat_lt l (by unfold tmModulus; omega), tagM_lt q,
        digit_pair_lt_sq (bitNat_lt l (by unfold tmModulus; omega)) (tagR_lt q)⟩

private theorem nodup_map_pair_primary {Q : ℕ} [NeZero Q]
    (M : @TM0.Machine Bool (Fin Q) ⟨⟨0, NeZero.pos Q⟩⟩) :
    ((primaryRules M).map fun r => (r.a, r.b)).Nodup := by
  unfold primaryRules
  rw [List.map_flatMap]
  refine List.nodup_flatMap.2 ⟨?_, ?_⟩
  · intro q _
    rw [List.map_filterMap]
    simp only [List.filterMap_cons, List.filterMap_nil]
    cases h0 : M q false with
    | none =>
      cases h1 : M q true with
      | none => simp
      | some val =>
        rcases val with ⟨q', d | s⟩
        · cases d <;> simp [bitNat]
        · simp [bitNat]
    | some val0 =>
      rcases val0 with ⟨q0, d0 | s0⟩
      · cases d0 <;> cases h1 : M q true with
        | none => simp [bitNat]
        | some val1 =>
          rcases val1 with ⟨q1, d1 | s1⟩
          · cases d1 <;> simp [bitNat]
          · simp [bitNat]
      · cases h1 : M q true with
        | none => simp [bitNat]
        | some val1 =>
          rcases val1 with ⟨q1, d1 | s1⟩
          · cases d1 <;> simp [bitNat]
          · simp [bitNat]
  · refine (List.nodup_finRange Q).imp_of_mem ?_
    intro q₁ q₂ _ _ hne p hp₁ hp₂
    simp only [List.mem_map, List.mem_filterMap, List.mem_cons, List.not_mem_nil, or_false] at hp₁ hp₂
    rcases hp₁ with ⟨r₁, ⟨b₁, _, hr₁⟩, rfl⟩
    rcases hp₂ with ⟨r₂, ⟨b₂, _, hr₂⟩, heq⟩
    have ha₁ : r₁.a = tagL Q q₁ := by
      cases h : M q₁ b₁ with
      | none =>
        rw [h] at hr₁; split_ifs at hr₁
        simp only [Option.some.injEq] at hr₁; subst hr₁; rfl
      | some val =>
        rcases val with ⟨q', d | s⟩
        · cases d <;> (rw [h] at hr₁; simp only [Option.some.injEq] at hr₁; subst hr₁; rfl)
        · rw [h] at hr₁; simp only [Option.some.injEq] at hr₁; subst hr₁; rfl
    have ha₂ : r₂.a = tagL Q q₂ := by
      cases h : M q₂ b₂ with
      | none =>
        rw [h] at hr₂; split_ifs at hr₂
        simp only [Option.some.injEq] at hr₂; subst hr₂; rfl
      | some val =>
        rcases val with ⟨q', d | s⟩
        · cases d <;> (rw [h] at hr₂; simp only [Option.some.injEq] at hr₂; subst hr₂; rfl)
        · rw [h] at hr₂; simp only [Option.some.injEq] at hr₂; subst hr₂; rfl
    have hq : tagL Q q₁ = tagL Q q₂ := by
      have := congrArg Prod.fst heq
      dsimp at this
      omega
    exact hne (Fin.ext (by unfold tagL at hq; omega))

private theorem nodup_map_pair_cleanup (Q : ℕ) :
    ((cleanupRules Q).map fun r => (r.a, r.b)).Nodup := by
  unfold cleanupRules
  rw [List.map_flatMap]
  refine List.nodup_flatMap.2 ⟨?_, ?_⟩
  · intro q _; simp [bitNat]
  · refine (List.nodup_finRange Q).imp_of_mem ?_
    intro q₁ q₂ _ _ hne p hp₁ hp₂
    simp only [List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hp₁ hp₂
    rcases hp₁ with ⟨_, ⟨l₁, _, rfl⟩, rfl⟩
    rcases hp₂ with ⟨_, ⟨l₂, _, rfl⟩, heq⟩
    have hb := congrArg Prod.snd heq
    dsimp [tagR] at hb
    exact hne (Fin.ext (by omega))

private theorem nodup_map_pair_middle (Q : ℕ) :
    ((middleRules Q).map fun r => (r.a, r.b)).Nodup := by
  unfold middleRules
  rw [List.map_flatMap]
  refine List.nodup_flatMap.2 ⟨?_, ?_⟩
  · intro q _; simp [bitNat]
  · refine (List.nodup_finRange Q).imp_of_mem ?_
    intro q₁ q₂ _ _ hne p hp₁ hp₂
    simp only [List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hp₁ hp₂
    rcases hp₁ with ⟨_, ⟨l₁, _, rfl⟩, rfl⟩
    rcases hp₂ with ⟨_, ⟨l₂, _, rfl⟩, heq⟩
    have hb := congrArg Prod.snd heq
    dsimp [tagM] at hb
    exact hne (Fin.ext (by omega))

private theorem primaryRules_bounds {Q : ℕ} [NeZero Q]
    (M : @TM0.Machine Bool (Fin Q) ⟨⟨0, NeZero.pos Q⟩⟩)
    {r : ModQuad (tmModulus Q)} (hr : r ∈ primaryRules M) :
    2 ≤ r.a ∧ r.a < 2 + Q ∧ r.b < 2 := by
  simp only [primaryRules, List.mem_flatMap, List.mem_finRange, true_and, List.mem_filterMap,
    List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with ⟨q, b, _, h⟩
  cases hM : M q b with
  | none =>
    rw [hM] at h; split_ifs at h
    simp only [Option.some.injEq] at h; subst h
    dsimp [tagL]; omega
  | some val =>
    rcases val with ⟨q', d | s⟩
    · cases d with
      | left =>
        rw [hM] at h; simp only [Option.some.injEq] at h; subst h
        dsimp [tagL]; cases b <;> simp [bitNat]
      | right =>
        rw [hM] at h; simp only [Option.some.injEq] at h; subst h
        dsimp [tagL]; cases b <;> simp [bitNat]
    · rw [hM] at h; simp only [Option.some.injEq] at h; subst h
      dsimp [tagL]; cases b <;> simp [bitNat]

private theorem cleanupRules_bounds {Q : ℕ} {r : ModQuad (tmModulus Q)} (hr : r ∈ cleanupRules Q) :
    r.a < 2 ∧ 2 + Q ≤ r.b ∧ r.b < 2 + 2 * Q := by
  simp only [cleanupRules, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map,
    List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with ⟨q, l, _, rfl⟩
  unfold tagR; cases l <;> simp [bitNat] <;> omega

private theorem middleRules_bounds {Q : ℕ} {r : ModQuad (tmModulus Q)} (hr : r ∈ middleRules Q) :
    r.a < 2 ∧ 2 + 2 * Q ≤ r.b ∧ r.b < 2 + 3 * Q := by
  simp only [middleRules, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map,
    List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with ⟨q, l, _, rfl⟩
  unfold tagM; cases l <;> simp [bitNat] <;> omega

/-- Compile a finite-state binary `TM0` machine into a deterministic modular machine. -/
def tmToModularMachine {Q : ℕ} [NeZero Q]
    (M : @TM0.Machine Bool (Fin Q) ⟨⟨0, NeZero.pos Q⟩⟩) : ModularMachine where
  m := tmModulus Q
  hm := by unfold tmModulus; omega
  rules := primaryRules M ++ cleanupRules Q ++ middleRules Q
  deterministic := by
    have hnodup : ((primaryRules M ++ cleanupRules Q ++ middleRules Q).map
        fun r => (r.a, r.b)).Nodup := by
      simp only [List.map_append]
      refine List.nodup_append.2 ⟨List.nodup_append.2 ⟨nodup_map_pair_primary M,
        nodup_map_pair_cleanup Q, ?_⟩, nodup_map_pair_middle Q, ?_⟩
      · intro p₁ hp₁ p₂ hp₂ heq
        simp only [List.mem_map] at hp₁ hp₂
        rcases hp₁ with ⟨r₁, hr₁, rfl⟩; rcases hp₂ with ⟨r₂, hr₂, rfl⟩
        have hb₁ := primaryRules_bounds M hr₁
        have hb₂ := cleanupRules_bounds hr₂
        have := congrArg Prod.fst heq; dsimp at this; omega
      · intro p₁ hp₁ p₂ hp₂ heq
        simp only [List.mem_append, List.mem_map] at hp₁ hp₂
        rcases hp₂ with ⟨r₂, hr₂, rfl⟩
        have hb₂ := middleRules_bounds hr₂
        rcases hp₁ with ⟨r₁, hr₁, rfl⟩ | ⟨r₁, hr₁, rfl⟩
        · have hb₁ := primaryRules_bounds M hr₁
          have := congrArg Prod.fst heq; dsimp at this; omega
        · have hb₁ := cleanupRules_bounds hr₁
          have := congrArg Prod.snd heq; dsimp at this; omega
    intro i j ha hb
    have hget : (((primaryRules M ++ cleanupRules Q ++ middleRules Q).map
        fun r => (r.a, r.b))[i.val]'(by simpa using i.isLt)) =
        (((primaryRules M ++ cleanupRules Q ++ middleRules Q).map
        fun r => (r.a, r.b))[j.val]'(by simpa using j.isLt)) := by
      simp only [List.getElem_map]
      exact Prod.ext ha hb
    have hij := (List.nodup_iff_injective_getElem.1 hnodup)
      (a₁ := ⟨i.val, by simpa using i.isLt⟩) (a₂ := ⟨j.val, by simpa using j.isLt⟩) hget
    exact Fin.ext (Fin.mk.inj hij)
  no_zero_rule := by
    intro q hq ⟨ha0, hb0⟩
    simp only [List.mem_append] at hq
    rcases hq with (hq | hq) | hq
    · have := primaryRules_bounds M hq; omega
    · have := cleanupRules_bounds hq; omega
    · have := middleRules_bounds hq; omega

private theorem mem_cleanupRules {Q : ℕ} [NeZero Q]
    (M : @TM0.Machine Bool (Fin Q) ⟨⟨0, NeZero.pos Q⟩⟩) (q : Fin Q) (l : Bool) :
    (⟨bitNat l, tagR Q q, bitNat l * tmModulus Q + tagL Q q, .R,
      bitNat_lt l (by unfold tmModulus; omega), tagR_lt q,
      digit_pair_lt_sq (bitNat_lt l (by unfold tmModulus; omega)) (tagL_lt q)⟩ :
      ModQuad (tmModulus Q)) ∈ (tmToModularMachine M).rules := by
  change _ ∈ primaryRules M ++ cleanupRules Q ++ middleRules Q
  rw [List.mem_append, List.mem_append]
  left; right
  simp only [cleanupRules, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map,
    List.mem_cons, List.not_mem_nil, or_false]
  exact ⟨q, l, by cases l <;> simp, rfl⟩

private theorem mem_middleRules {Q : ℕ} [NeZero Q]
    (M : @TM0.Machine Bool (Fin Q) ⟨⟨0, NeZero.pos Q⟩⟩) (q : Fin Q) (l : Bool) :
    (⟨bitNat l, tagM Q q, bitNat l * tmModulus Q + tagR Q q, .L,
      bitNat_lt l (by unfold tmModulus; omega), tagM_lt q,
      digit_pair_lt_sq (bitNat_lt l (by unfold tmModulus; omega)) (tagR_lt q)⟩ :
      ModQuad (tmModulus Q)) ∈ (tmToModularMachine M).rules := by
  change _ ∈ primaryRules M ++ cleanupRules Q ++ middleRules Q
  rw [List.mem_append]
  right
  simp only [middleRules, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map,
    List.mem_cons, List.not_mem_nil, or_false]
  exact ⟨q, l, by cases l <;> simp, rfl⟩

private theorem not_modStep_of_both_small {Q : ℕ} [NeZero Q]
    (M : @TM0.Machine Bool (Fin Q) ⟨⟨0, NeZero.pos Q⟩⟩)
    {u v : ℤ} {a b : ℕ} (ha : a < 2) (hb : b < 2) (p' : ℤ × ℤ) :
    ¬ ModStep (tmToModularMachine M)
      (u * (tmModulus Q : ℤ) + (a : ℤ), v * (tmModulus Q : ℤ) + (b : ℤ)) p' := by
  rintro ⟨r, hr, u', v', hp, _⟩
  simp only [Prod.mk.injEq] at hp
  have ha_lt : a < tmModulus Q := by unfold tmModulus; omega
  have hb_lt : b < tmModulus Q := by unfold tmModulus; omega
  have ha_eq : a = r.a := (int_div_mod_eq ha_lt r.ha hp.1).2
  have hb_eq : b = r.b := (int_div_mod_eq hb_lt r.hb hp.2).2
  let r' : ModQuad (tmModulus Q) := r
  have hra : r'.a = r.a := rfl
  have hrb : r'.b = r.b := rfl
  have hr' : r' ∈ primaryRules M ++ cleanupRules Q ++ middleRules Q := hr
  rw [List.mem_append, List.mem_append] at hr'
  rcases hr' with (hr' | hr') | hr'
  · have := primaryRules_bounds M hr'; omega
  · have := cleanupRules_bounds hr'; omega
  · have := middleRules_bounds hr'; omega

/-- Forward simulation of a single `TM0` step takes 1, 2, or 3 `ModStep`s and never hits `(0, 0)`
along the way. -/
private theorem tmStep_to_modSteps {Q : ℕ} [NeZero Q]
    (M : @TM0.Machine Bool (Fin Q) ⟨⟨0, NeZero.pos Q⟩⟩)
    {c₁ c₂ : TM0.Cfg Bool (Fin Q)}
    (hstep : c₂ ∈ @TM0.step Bool (Fin Q) ⟨⟨0, NeZero.pos Q⟩⟩ _ M c₁) :
    TransGen (ModStep (tmToModularMachine M)) (encCfg Q c₁) (encCfg Q c₂) := by
  rcases c₁ with ⟨q, T⟩
  simp only [TM0.step, Option.mem_def, Option.map_eq_some_iff] at hstep
  rcases hstep with ⟨⟨q', s⟩, hM, rfl⟩
  let m := tmModulus Q
  have hm2 : 2 ≤ m := by unfold m tmModulus; omega
  have hR₀ : (encListBlank m T.right₀ : ℤ) =
      (encListBlank m T.right : ℤ) * (m : ℤ) + (bitNat T.head : ℤ) := by
    have := encListBlank_cons m T.head T.right
    change (encListBlank m (T.right.cons T.head) : ℤ) = _
    rw [this]; push_cast; ring
  have hL : (encListBlank m T.left : ℤ) =
      (encListBlank m T.left.tail : ℤ) * (m : ℤ) + (bitNat T.left.head : ℤ) := by
    have := encListBlank_eq_tail m T.left
    rw [this]; push_cast; ring
  have hLt : (encListBlank m T.left.tail : ℤ) =
      (encListBlank m T.left.tail.tail : ℤ) * (m : ℤ) + (bitNat T.left.tail.head : ℤ) := by
    have := encListBlank_eq_tail m T.left.tail
    rw [this]; push_cast; ring
  cases s with
  | move d =>
    cases d with
    | right =>
      let r : ModQuad m :=
        ⟨tagL Q q, bitNat T.head, bitNat T.head * m + tagL Q q', .R,
          tagL_lt q, bitNat_lt T.head hm2, digit_pair_lt_sq (bitNat_lt T.head hm2) (tagL_lt q')⟩
      have hr : r ∈ (tmToModularMachine M).rules := by
        change r ∈ primaryRules M ++ cleanupRules Q ++ middleRules Q
        rw [List.mem_append, List.mem_append]
        left; left
        simp only [primaryRules, List.mem_flatMap, List.mem_finRange, true_and, List.mem_filterMap,
          List.mem_cons, List.not_mem_nil, or_false]
        refine ⟨q, T.head, by cases T.head <;> simp, ?_⟩
        rw [hM]
      refine TransGen.single ⟨r, hr, (encListBlank m T.left : ℤ), (encListBlank m T.right : ℤ), ?_, ?_⟩
      · simp only [encCfg, r, m]; exact Prod.ext rfl hR₀
      · simp only [encCfg, ModQuad.applyPair, tmToModularMachine, r, Tape.move, Tape.right₀,
          ListBlank.cons_head_tail, encListBlank_cons, m]
        ext <;> (push_cast; ring)
    | left =>
      let r₁ : ModQuad m :=
        ⟨tagL Q q, bitNat T.head, bitNat T.head * m + tagM Q q', .L,
          tagL_lt q, bitNat_lt T.head hm2, digit_pair_lt_sq (bitNat_lt T.head hm2) (tagM_lt q')⟩
      have hr₁ : r₁ ∈ (tmToModularMachine M).rules := by
        change r₁ ∈ primaryRules M ++ cleanupRules Q ++ middleRules Q
        rw [List.mem_append, List.mem_append]
        left; left
        simp only [primaryRules, List.mem_flatMap, List.mem_finRange, true_and, List.mem_filterMap,
          List.mem_cons, List.not_mem_nil, or_false]
        refine ⟨q, T.head, by cases T.head <;> simp, ?_⟩
        rw [hM]
      let mid₁ : ℤ × ℤ :=
        ((encListBlank m T.left : ℤ), (encListBlank m T.right₀ : ℤ) * (m : ℤ) + (tagM Q q' : ℤ))
      let mid₂ : ℤ × ℤ :=
        ((encListBlank m T.left.tail : ℤ),
          (encListBlank m (T.right₀.cons T.left.head) : ℤ) * (m : ℤ) + (tagR Q q' : ℤ))
      have hstep1 : ModStep (tmToModularMachine M) (encCfg Q ⟨q, T⟩) mid₁ := by
        refine ⟨r₁, hr₁, (encListBlank m T.left : ℤ), (encListBlank m T.right : ℤ), ?_, ?_⟩
        · simp only [encCfg, r₁, m]; exact Prod.ext rfl hR₀
        · simp only [mid₁, ModQuad.applyPair, tmToModularMachine, r₁, m]
          ext
          · rfl
          · rw [hR₀]; push_cast; ring
      have hstep2 : ModStep (tmToModularMachine M) mid₁ mid₂ := by
        refine ⟨_, mem_middleRules M q' T.left.head,
          (encListBlank m T.left.tail : ℤ), (encListBlank m T.right₀ : ℤ), ?_, ?_⟩
        · simp only [mid₁, m]; exact Prod.ext hL rfl
        · simp only [mid₂, ModQuad.applyPair, tmToModularMachine, encListBlank_cons, m]
          ext
          · rfl
          · push_cast; ring
      have hstep3 : ModStep (tmToModularMachine M) mid₂ (encCfg Q ⟨q', T.move .left⟩) := by
        refine ⟨_, mem_cleanupRules M q' T.left.tail.head,
          (encListBlank m T.left.tail.tail : ℤ),
          (encListBlank m (T.right₀.cons T.left.head) : ℤ), ?_, ?_⟩
        · simp only [mid₂, m]; exact Prod.ext hLt rfl
        · simp only [encCfg, ModQuad.applyPair, tmToModularMachine, Tape.move, Tape.right₀, m]
          ext
          · rw [hLt]; push_cast; ring
          · rfl
      exact TransGen.head hstep1 (TransGen.head hstep2 (TransGen.single hstep3))
  | write a =>
    let r₁ : ModQuad m :=
      ⟨tagL Q q, bitNat T.head, bitNat a * m + tagR Q q', .L,
        tagL_lt q, bitNat_lt T.head hm2, digit_pair_lt_sq (bitNat_lt a hm2) (tagR_lt q')⟩
    have hr₁ : r₁ ∈ (tmToModularMachine M).rules := by
      change r₁ ∈ primaryRules M ++ cleanupRules Q ++ middleRules Q
      rw [List.mem_append, List.mem_append]
      left; left
      simp only [primaryRules, List.mem_flatMap, List.mem_finRange, true_and, List.mem_filterMap,
        List.mem_cons, List.not_mem_nil, or_false]
      refine ⟨q, T.head, by cases T.head <;> simp, ?_⟩
      rw [hM]
    let mid : ℤ × ℤ :=
      ((encListBlank m T.left : ℤ),
        (encListBlank m (T.right.cons a) : ℤ) * (m : ℤ) + (tagR Q q' : ℤ))
    have hstep1 : ModStep (tmToModularMachine M) (encCfg Q ⟨q, T⟩) mid := by
      refine ⟨r₁, hr₁, (encListBlank m T.left : ℤ), (encListBlank m T.right : ℤ), ?_, ?_⟩
      · simp only [encCfg, r₁, m]; exact Prod.ext rfl hR₀
      · simp only [mid, ModQuad.applyPair, tmToModularMachine, r₁, encListBlank_cons, m]
        ext
        · rfl
        · push_cast; ring
    have hstep2 : ModStep (tmToModularMachine M) mid (encCfg Q ⟨q', T.write a⟩) := by
      refine ⟨_, mem_cleanupRules M q' T.left.head,
        (encListBlank m T.left.tail : ℤ), (encListBlank m (T.right.cons a) : ℤ), ?_, ?_⟩
      · simp only [mid, m]; exact Prod.ext hL rfl
      · simp only [encCfg, ModQuad.applyPair, tmToModularMachine, Tape.write, Tape.right₀, m]
        ext
        · rw [hL]; push_cast; ring
        · rfl
    exact TransGen.head hstep1 (TransGen.single hstep2)

private def ModStepsN (M : ModularMachine) : ℕ → ℤ × ℤ → ℤ × ℤ → Prop
  | 0, x, y => x = y
  | n + 1, x, y => ∃ z, ModStep M x z ∧ ModStepsN M n z y

private theorem exists_modStepsN_of_reflTransGen (M : ModularMachine) {x y : ℤ × ℤ}
    (h : ReflTransGen (ModStep M) x y) : ∃ n, ModStepsN M n x y := by
  induction h using ReflTransGen.head_induction_on with
  | refl => exact ⟨0, rfl⟩
  | head hstep _ ih =>
    rcases ih with ⟨n, hn⟩
    exact ⟨n + 1, _, hstep, hn⟩

private theorem exists_pos_modStepsN_of_transGen (M : ModularMachine) {x y : ℤ × ℤ}
    (h : TransGen (ModStep M) x y) : ∃ n, 0 < n ∧ ModStepsN M n x y := by
  induction h using TransGen.head_induction_on with
  | single hstep => exact ⟨1, by omega, _, hstep, rfl⟩
  | head hstep _ ih =>
    rcases ih with ⟨n, _, hn⟩
    exact ⟨n + 1, by omega, _, hstep, hn⟩

/-- Exact simulation equivalence: `encCfg Q cfg` reaches `(0, 0)` in `tmToModularMachine M`
iff `cfg` reaches `⟨qHalt, default⟩` in `M`. -/
theorem reachesZero_encCfg_iff {Q : ℕ} [NeZero Q]
    (M : @TM0.Machine Bool (Fin Q) ⟨⟨0, NeZero.pos Q⟩⟩)
    (qHalt : Fin Q) (hHalt : ∀ q b, M q b = none ↔ q = qHalt)
    (cfg : TM0.Cfg Bool (Fin Q)) :
    encCfg Q cfg ∈ ReachesZero (tmToModularMachine M) ↔
      @TM0.Reaches Bool (Fin Q) ⟨⟨0, NeZero.pos Q⟩⟩ _ M cfg ⟨qHalt, default⟩ := by
  let MM := tmToModularMachine M
  let m := tmModulus Q
  have hm2 : 2 ≤ m := by unfold m tmModulus; omega
  have hhalt_rule :
      (⟨tagL Q qHalt, 0, 0, .L, tagL_lt qHalt, by unfold m tmModulus; omega,
        by unfold m tmModulus; positivity⟩ : ModQuad m) ∈ MM.rules := by
    change _ ∈ primaryRules M ++ cleanupRules Q ++ middleRules Q
    rw [List.mem_append, List.mem_append]
    left; left
    simp only [primaryRules, List.mem_flatMap, List.mem_finRange, true_and, List.mem_filterMap,
      List.mem_cons, List.not_mem_nil, or_false]
    refine ⟨qHalt, false, Or.inl rfl, ?_⟩
    rw [(hHalt qHalt false).2 rfl]
    rfl
  constructor
  · -- Reverse direction: any modular path from `encCfg Q cfg` to `(0, 0)` simulates a TM0 path.
    intro hreach
    obtain ⟨n, hn⟩ := exists_modStepsN_of_reflTransGen MM hreach
    clear hreach
    induction n using Nat.strong_induction_on generalizing cfg with
    | ind n ih =>
      cases hM : M cfg.q cfg.Tape.head with
      | none =>
        have hq : cfg.q = qHalt := (hHalt cfg.q cfg.Tape.head).1 hM
        cases n with
        | zero =>
          simp only [ModStepsN] at hn
          have h1 := congrArg Prod.fst hn
          simp only [encCfg] at h1
          have h0 : (0 : ℤ) * (m : ℤ) + (0 : ℕ) =
              (encListBlank m cfg.Tape.left : ℤ) * (m : ℤ) + (tagL Q cfg.q : ℤ) := by
            simpa using h1.symm
          have htag0 : 0 = tagL Q cfg.q := (int_div_mod_eq (by omega) (tagL_lt cfg.q) h0).2
          unfold tagL at htag0; omega
        | succ n' =>
          rcases hn with ⟨p₁, hstep, hrest⟩
          cases hhd : cfg.Tape.head with
          | true =>
            exfalso
            rcases hstep with ⟨r, hr, u, v, hp, _⟩
            simp only [encCfg, Prod.mk.injEq] at hp
            have hR₀ : (encListBlank m cfg.Tape.right₀ : ℤ) =
                (encListBlank m cfg.Tape.right : ℤ) * (m : ℤ) + (1 : ℕ) := by
              have := encListBlank_cons m cfg.Tape.head cfg.Tape.right
              rw [hhd] at this
              change (encListBlank m (cfg.Tape.right.cons cfg.Tape.head) : ℤ) = _
              rw [hhd, this]; simp [bitNat]
            have hMM_m : MM.m = m := rfl
            have ha_eq : tagL Q cfg.q = r.a := (int_div_mod_eq (tagL_lt cfg.q) r.ha hp.1).2
            have hb_eq : 1 = r.b :=
              (int_div_mod_eq (by rw [hMM_m]; omega) r.hb (hR₀.symm.trans hp.2)).2
            let r' : ModQuad (tmModulus Q) := r
            have hra : r'.a = r.a := rfl
            have hrb : r'.b = r.b := rfl
            have hr' : r' ∈ primaryRules M ++ cleanupRules Q ++ middleRules Q := hr
            rw [List.mem_append, List.mem_append] at hr'
            rcases hr' with (hr' | hr') | hr'
            · simp only [primaryRules, List.mem_flatMap, List.mem_finRange, true_and,
                List.mem_filterMap, List.mem_cons, List.not_mem_nil, or_false] at hr'
              rcases hr' with ⟨q₁, b₁, _, hrule⟩
              have hq₁ : q₁ = cfg.q := by
                have hr_a : r'.a = tagL Q q₁ := by
                  cases hm1 : M q₁ b₁ with
                  | none =>
                    rw [hm1] at hrule; split_ifs at hrule
                    simp only [Option.some.injEq] at hrule; subst hrule; rfl
                  | some val =>
                    rcases val with ⟨_, d | _⟩
                    · cases d <;> (rw [hm1] at hrule; simp only [Option.some.injEq] at hrule; subst hrule; rfl)
                    · rw [hm1] at hrule; simp only [Option.some.injEq] at hrule; subst hrule; rfl
                exact Fin.ext (by unfold tagL at ha_eq hr_a; omega)
              subst hq₁
              have hm_none : M cfg.q b₁ = none := (hHalt cfg.q b₁).2 hq
              rw [hm_none] at hrule
              split_ifs at hrule
              simp only [Option.some.injEq] at hrule
              subst hrule
              simp at hb_eq
            · have := cleanupRules_bounds hr'; unfold tagL at ha_eq; omega
            · have := middleRules_bounds hr'; unfold tagL at ha_eq; omega
          | false =>
            have hR₀ : (encListBlank m cfg.Tape.right₀ : ℤ) =
                (encListBlank m cfg.Tape.right : ℤ) * (m : ℤ) + (0 : ℕ) := by
              have := encListBlank_cons m cfg.Tape.head cfg.Tape.right
              rw [hhd] at this
              change (encListBlank m (cfg.Tape.right.cons cfg.Tape.head) : ℤ) = _
              rw [hhd, this]; simp [bitNat]
            have hhalt_step : ModStep MM (encCfg Q cfg)
                ((encListBlank m cfg.Tape.left : ℤ),
                  (encListBlank m cfg.Tape.right : ℤ) * ((m * m : ℕ) : ℤ)) := by
              refine ⟨_, hhalt_rule, (encListBlank m cfg.Tape.left : ℤ),
                (encListBlank m cfg.Tape.right : ℤ), ?_, ?_⟩
              · simp only [encCfg, hq, m]; exact Prod.ext rfl hR₀
              · simp [ModQuad.applyPair, MM, tmToModularMachine, m]
            have hp₁_eq : p₁ = ((encListBlank m cfg.Tape.left : ℤ),
                (encListBlank m cfg.Tape.right : ℤ) * ((m * m : ℕ) : ℤ)) :=
              modStep_deterministic MM hstep hhalt_step
            subst hp₁_eq
            have hp₁_stuck : ∀ p', ¬ ModStep MM
                ((encListBlank m cfg.Tape.left : ℤ),
                  (encListBlank m cfg.Tape.right : ℤ) * ((m * m : ℕ) : ℤ)) p' := by
              intro p'
              have hL_eq : (encListBlank m cfg.Tape.left : ℤ) =
                  (encListBlank m cfg.Tape.left.tail : ℤ) * (m : ℤ) +
                    (bitNat cfg.Tape.left.head : ℤ) := by
                have := encListBlank_eq_tail m cfg.Tape.left
                rw [this]; push_cast; ring
              have hR_eq : (encListBlank m cfg.Tape.right : ℤ) * ((m * m : ℕ) : ℤ) =
                  ((encListBlank m cfg.Tape.right : ℤ) * (m : ℤ)) * (m : ℤ) + (0 : ℕ) := by
                push_cast; ring
              rw [hL_eq, hR_eq]
              exact not_modStep_of_both_small M (by cases cfg.Tape.left.head <;> simp [bitNat])
                (by omega) p'
            cases n' with
            | succ n'' =>
              rcases hrest with ⟨p₂, hstep2, _⟩
              exact (hp₁_stuck p₂ hstep2).elim
            | zero =>
              simp only [ModStepsN, Prod.mk.injEq] at hrest
              have hL0 : encListBlank m cfg.Tape.left = 0 := by omega
              have hR0 : encListBlank m cfg.Tape.right = 0 := by
                have hm_pos : (0 : ℤ) < ((m * m : ℕ) : ℤ) := by positivity
                have hrz : (encListBlank m cfg.Tape.right : ℤ) = 0 :=
                  (mul_eq_zero.mp hrest.2).resolve_right (by omega)
                omega
              have hleft_empty : cfg.Tape.left = ∅ := (encListBlank_eq_zero_iff hm2 _).1 hL0
              have hright_empty : cfg.Tape.right = ∅ := (encListBlank_eq_zero_iff hm2 _).1 hR0
              have htape_def : cfg.Tape = default := by
                cases hT : cfg.Tape with
                | mk hd L R =>
                  rw [hT] at hhd hleft_empty hright_empty
                  dsimp at hhd hleft_empty hright_empty
                  subst hhd hleft_empty hright_empty
                  rfl
              have hcfg_eq : cfg = ⟨qHalt, default⟩ := by
                cases cfg; simp_all
              rw [hcfg_eq]
              exact ReflTransGen.refl
      | some val =>
        rcases val with ⟨q', s⟩
        let cfg' : TM0.Cfg Bool (Fin Q) :=
          ⟨q', match s with | .move d => cfg.Tape.move d | .write a => cfg.Tape.write a⟩
        have htm_step : cfg' ∈ @TM0.step Bool (Fin Q) ⟨⟨0, NeZero.pos Q⟩⟩ _ M cfg := by
          cases s <;> simp [TM0.step, hM, cfg']
        have hmod_trans : TransGen (ModStep MM) (encCfg Q cfg) (encCfg Q cfg') :=
          tmStep_to_modSteps M htm_step
        obtain ⟨d, hd_pos, hd_pow⟩ := exists_pos_modStepsN_of_transGen MM hmod_trans
        have hsplit : ∀ (k₁ k₂ : ℕ) (x y : ℤ × ℤ),
            ModStepsN MM k₁ x y →
            ModStepsN MM k₂ x (0, 0) →
            k₁ ≤ k₂ ∧ ModStepsN MM (k₂ - k₁) y (0, 0) := by
          intro k₁
          induction k₁ with
          | zero =>
            intro k₂ x y h1 h2
            simp only [ModStepsN] at h1
            subst h1
            exact ⟨Nat.zero_le _, by simpa using h2⟩
          | succ k₁ ih₁ =>
            intro k₂ x y h1 h2
            rcases h1 with ⟨x₁, hxx₁, hx₁y⟩
            cases k₂ with
            | zero =>
              simp only [ModStepsN] at h2
              subst h2
              exact (not_modStep_zero MM x₁ hxx₁).elim
            | succ k₂ =>
              rcases h2 with ⟨x₂, hxx₂, hx₂z⟩
              have heq : x₁ = x₂ := modStep_deterministic MM hxx₁ hxx₂
              subst heq
              obtain ⟨hle, hrem⟩ := ih₁ k₂ x₁ y hx₁y hx₂z
              exact ⟨Nat.succ_le_succ hle, by simpa [Nat.succ_sub_succ] using hrem⟩
        obtain ⟨hd_le, hrem⟩ := hsplit d n (encCfg Q cfg) (encCfg Q cfg') hd_pow hn
        exact ReflTransGen.head htm_step (ih (n - d) (by omega) cfg' hrem)
  · -- Forward direction: by induction on `TM0.Reaches M cfg ⟨qHalt, default⟩`.
    intro hreach
    induction hreach using ReflTransGen.head_induction_on with
    | refl =>
      refine ReflTransGen.single ⟨_, hhalt_rule, 0, 0, ?_, ?_⟩
      · have hL : encListBlank m (default : Tape Bool).left = 0 := rfl
        have hR : encListBlank m (default : Tape Bool).right₀ = 0 := by
          change encListBlank m ((∅ : ListBlank Bool).cons false) = 0
          simp [bitNat]
        simp [encCfg, hL, hR, m]
      · simp [ModQuad.applyPair]
    | head hstep _ ih =>
      exact (tmStep_to_modSteps M hstep).to_reflTransGen.trans ih

/-- Main export of this module: there exists a deterministic modular machine `M` with terminal
`(0, 0)` and a primitive recursive input encoding `encodeInit : ℕ → ℕ × ℕ` such that the halting
problem `fun n => ((encodeInit n).1, (encodeInit n).2) ∈ ReachesZero M` is undecidable. -/
theorem exists_undecidable_modularMachine :
    ∃ (M : ModularMachine) (encodeInit : ℕ → ℕ × ℕ),
      Primrec encodeInit ∧
      ¬ ComputablePred (fun n => (((encodeInit n).1 : ℤ), ((encodeInit n).2 : ℤ)) ∈ ReachesZero M) := by
  obtain ⟨Q, hQ, M_tm, qHalt, inputBits, hbits_prim, hHalt, hundec⟩ := exists_undecidable_blank_tm0
  let : NeZero Q := hQ
  let MM := tmToModularMachine M_tm
  let encodeInit : ℕ → ℕ × ℕ := fun n => (2, encList (tmModulus Q) (inputBits n))
  have henc_prim : Primrec encodeInit :=
    Primrec.pair (Primrec.const 2) ((primrec_encList (tmModulus Q)).comp hbits_prim)
  refine ⟨MM, encodeInit, henc_prim, ?_⟩
  intro hcomp
  apply hundec
  refine hcomp.of_eq fun n => ?_
  have hinit_eq : (((encodeInit n).1 : ℤ), ((encodeInit n).2 : ℤ)) =
      encCfg Q (@TM0.init Bool (Fin Q) ⟨⟨0, NeZero.pos Q⟩⟩ _ (inputBits n)) := by
    simp [encodeInit, encCfg, TM0.init, Tape.mk₁, Tape.mk₂, tagL, encList]
  rw [hinit_eq]
  exact reachesZero_encCfg_iff M_tm qHalt hHalt _

end TM0ToModular

end Adian
