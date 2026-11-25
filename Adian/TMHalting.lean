module

public import Adian.FinPres
public import Mathlib.Computability.Halting
public import Mathlib.Computability.PartrecBasis
public import Mathlib.Computability.Primrec.List
public import Mathlib.Computability.TuringMachine.ToPartrec

/-!
# Undecidable Blank-Tape Halting Problem for Binary `TM0`

Starting from Mathlib's `ComputablePred.halting_problem 0`, we compile the universal halting
predicate through Mathlib's verified compiler stack:
`Partrec` → `Nat.Partrec'` → `ToPartrec.Code` (composed with `Code.nil`) → `PartrecToTM2` →
`TM2to1` → `TM1to1` (alphabet `Bool`) → `TM1to0` → finite `Fin Q₀` → tape-erasing wrapper `Fin Q`.

Because composing with `ToPartrec.Code.nil` forces all four TM2 stacks to be empty on termination,
the resulting binary `TM0` machine halts (when it does) in a single fixed tape state `Tape.mk₁ B`
of fixed length `k`, which our `2*k + 1`-state eraser clears to `default : Turing.Tape Bool`.

The main export `exists_undecidable_blank_tm0` provides a finite-state binary `TM0` machine with
unique halting state `qHalt` and a primitive recursive input encoding `inputBits : ℕ → List Bool`
whose blank-tape halting predicate is undecidable.
-/

@[expose] public section

open Turing StateTransition Relation

namespace Adian

section PrimrecHelpers

private def gammaEquivFin4 : PartrecToTM2.Γ' ≃ Fin 4 where
  toFun
    | .consₗ => 0
    | .cons => 1
    | .bit0 => 2
    | .bit1 => 3
  invFun
    | ⟨0, _⟩ => .consₗ
    | ⟨1, _⟩ => .cons
    | ⟨2, _⟩ => .bit0
    | ⟨3, _⟩ => .bit1
  left_inv x := by cases x <;> rfl
  right_inv x := by
    rcases x with ⟨n, hn⟩
    match n, hn with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
    | 3, _ => rfl

private instance instPrimcodableGamma' : Primcodable PartrecToTM2.Γ' :=
  Primcodable.ofEquiv (Fin 4) gammaEquivFin4

private def kEquivFin4 : PartrecToTM2.K' ≃ Fin 4 where
  toFun
    | .main => 0
    | .rev => 1
    | .aux => 2
    | .stack => 3
  invFun
    | ⟨0, _⟩ => .main
    | ⟨1, _⟩ => .rev
    | ⟨2, _⟩ => .aux
    | ⟨3, _⟩ => .stack
  left_inv x := by cases x <;> rfl
  right_inv x := by
    rcases x with ⟨n, hn⟩
    match n, hn with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
    | 3, _ => rfl

private instance instFintypeK' : Fintype PartrecToTM2.K' :=
  Fintype.ofEquiv (Fin 4) kEquivFin4.symm

/-- Binary increment on little-endian `PartrecToTM2.Γ'` bit lists. -/
private def trNatSucc : List PartrecToTM2.Γ' → List PartrecToTM2.Γ'
  | [] => [.bit1]
  | .bit0 :: l => .bit1 :: l
  | .bit1 :: l => .bit0 :: trNatSucc l
  | a :: l => a :: l

private theorem trPosNum_succ (p : PosNum) :
    PartrecToTM2.trPosNum p.succ = trNatSucc (PartrecToTM2.trPosNum p) := by
  induction p with
  | one => rfl
  | bit0 p _ => rfl
  | bit1 p ih =>
    simp only [PosNum.succ, PartrecToTM2.trPosNum, trNatSucc, ih]

private theorem trNat_succ (n : ℕ) :
    PartrecToTM2.trNat (n + 1) = trNatSucc (PartrecToTM2.trNat n) := by
  unfold PartrecToTM2.trNat
  rw [Nat.cast_succ, Num.add_one]
  cases h : (n : Num) with
  | zero => rfl
  | pos p => exact trPosNum_succ p

private theorem primrec_trNatSucc : Primrec trNatSucc := by
  let step : List PartrecToTM2.Γ' →
      PartrecToTM2.Γ' × List PartrecToTM2.Γ' × List PartrecToTM2.Γ' →
      List PartrecToTM2.Γ' :=
    fun _ p =>
      match p.1 with
      | PartrecToTM2.Γ'.bit0 => PartrecToTM2.Γ'.bit1 :: p.2.1
      | PartrecToTM2.Γ'.bit1 => PartrecToTM2.Γ'.bit0 :: p.2.2
      | a => a :: p.2.1
  have hstep : Primrec₂ step := by
    have h1 : Primrec fun q : List PartrecToTM2.Γ' ×
        (PartrecToTM2.Γ' × List PartrecToTM2.Γ' × List PartrecToTM2.Γ') =>
        if q.2.1 = PartrecToTM2.Γ'.bit0 then (PartrecToTM2.Γ'.bit1 :: q.2.2.1 : List PartrecToTM2.Γ')
        else if q.2.1 = PartrecToTM2.Γ'.bit1 then PartrecToTM2.Γ'.bit0 :: q.2.2.2
        else q.2.1 :: q.2.2.1 := by
      refine Primrec.ite
        (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const PartrecToTM2.Γ'.bit0))
        (Primrec.list_cons.comp (Primrec.const PartrecToTM2.Γ'.bit1)
          (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))) ?_
      exact Primrec.ite
        (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const PartrecToTM2.Γ'.bit1))
        (Primrec.list_cons.comp (Primrec.const PartrecToTM2.Γ'.bit0)
          (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
        (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
          (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
    exact h1.of_eq fun ⟨_, a, l, ih⟩ => by cases a <;> rfl
  refine (Primrec.list_rec Primrec.id (Primrec.const [PartrecToTM2.Γ'.bit1]) hstep).of_eq fun l => ?_
  induction l with
  | nil => rfl
  | cons a tl ih =>
    cases a
    · rfl
    · rfl
    · rfl
    · exact congrArg (List.cons PartrecToTM2.Γ'.bit0) ih

private theorem primrec_trNat : Primrec PartrecToTM2.trNat := by
  refine (Primrec.nat_rec' Primrec.id (Primrec.const ([] : List PartrecToTM2.Γ'))
    (primrec_trNatSucc.comp (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun n => ?_
  induction n with
  | zero => exact PartrecToTM2.trNat_zero.symm
  | succ n ih =>
    dsimp only [id] at ih ⊢
    change trNatSucc (Nat.rec [] (fun _ IH => trNatSucc IH) n) = PartrecToTM2.trNat (n + 1)
    rw [ih, trNat_succ]

end PrimrecHelpers

section CompilerStages

/-- Eraser lemma: writing `false` and moving right `k` times clears `Tape.mk₁ bs` when
`bs.length = k`. -/
private theorem erase_tape_aux (k : ℕ) :
    ∀ (l : List Bool) (bs : List Bool),
      bs.length = k →
      (∀ x ∈ l, x = false) →
      let M_erase : Fin (2 * k + 1) → Bool → Option (Fin (2 * k + 1) × TM0.Stmt Bool) :=
        fun i _ =>
          if h : i.val < 2 * k then
            if i.val % 2 = 0 then some (⟨i.val + 1, by omega⟩, TM0.Stmt.write false)
            else some (⟨i.val + 1, by omega⟩, TM0.Stmt.move Dir.right)
          else none
      ∀ (j : ℕ) (hj : j ≤ k),
        @TM0.Reaches Bool (Fin (2 * k + 1)) ⟨⟨0, by omega⟩⟩ _ M_erase
          ⟨⟨2 * j, by omega⟩, Tape.mk₂ (List.replicate j false ++ l) (bs.drop j)⟩
          ⟨⟨2 * k, by omega⟩, Tape.mk₂ (List.replicate k false ++ l) []⟩ := by
  intro l bs hlen hl M_erase j hj
  induction hdiff : k - j generalizing j with
  | zero =>
    have hjk : j = k := by omega
    subst hjk
    have hdrop : bs.drop j = [] := List.drop_eq_nil_of_le (by omega)
    rw [hdrop]
    exact ReflTransGen.refl
  | succ d ih =>
    have hj_lt : j < k := by omega
    have hstep1 :
        ⟨⟨2 * j + 1, by omega⟩,
          (Tape.mk₂ (List.replicate j false ++ l) (bs.drop j)).write false⟩ ∈
        @TM0.step Bool (Fin (2 * k + 1)) ⟨⟨0, by omega⟩⟩ _ M_erase
          ⟨⟨2 * j, by omega⟩, Tape.mk₂ (List.replicate j false ++ l) (bs.drop j)⟩ := by
      have h1 : 2 * j < 2 * k := by omega
      have h2 : (2 * j) % 2 = 0 := by omega
      simp [TM0.step, M_erase, h1, h2]
    have hstep2 :
        ⟨⟨2 * (j + 1), by omega⟩,
          ((Tape.mk₂ (List.replicate j false ++ l) (bs.drop j)).write false).move Dir.right⟩ ∈
        @TM0.step Bool (Fin (2 * k + 1)) ⟨⟨0, by omega⟩⟩ _ M_erase
          ⟨⟨2 * j + 1, by omega⟩,
            (Tape.mk₂ (List.replicate j false ++ l) (bs.drop j)).write false⟩ := by
      have h1 : 2 * j + 1 < 2 * k := by omega
      simp only [TM0.step, Option.mem_def, Option.map_eq_some_iff, M_erase, h1, ↓reduceDIte]
      have h2 : (2 * j + 1) % 2 ≠ 0 := by omega
      simp only [h2, ↓reduceIte]
      refine ⟨⟨⟨2 * j + 1 + 1, by omega⟩, TM0.Stmt.move Dir.right⟩, rfl, ?_⟩
      congr 2
    have htape :
        ((Tape.mk₂ (List.replicate j false ++ l) (bs.drop j)).write false).move Dir.right =
          Tape.mk₂ (List.replicate (j + 1) false ++ l) (bs.drop (j + 1)) := by
      have hdrop_cons : ∃ b tl, bs.drop j = b :: tl ∧ tl = bs.drop (j + 1) := by
        have hlt : j < bs.length := by omega
        refine ⟨bs[j], bs.drop (j + 1), (List.cons_getElem_drop_succ (h := hlt)).symm, rfl⟩
      rcases hdrop_cons with ⟨b, tl, hcons, htl⟩
      rw [hcons, ← htl]
      simp only [Tape.mk₂, Tape.write_mk', Tape.move_right_mk', ListBlank.tail_mk,
        ListBlank.cons_mk, ListBlank.head_mk, List.headI_cons, List.tail_cons,
        List.replicate_succ, List.cons_append]
    rw [htape] at hstep2
    exact ReflTransGen.head hstep1 (ReflTransGen.head hstep2 (ih (j + 1) (by omega) (by omega)))

/-- Any `ListBlank Bool` built from all `false`s is equal to `∅`. -/
private theorem listBlank_replicate_false (k : ℕ) :
    ListBlank.mk (List.replicate k false) = (∅ : ListBlank Bool) :=
  Quotient.sound' (Or.inr ⟨k, rfl⟩)

set_option backward.isDefEq.respectTransparency false in
/-- Compile any finitely supported TM2 machine that halts with all stacks empty and local variable
`vHalt` into a finite-state binary `TM0` machine with an explicit bit-vector encoding `enc`. -/
private theorem compile_tm2_to_fin_tm0
    {K : Type} [DecidableEq K] [Fintype K]
    {Γ : K → Type} [∀ k, Fintype (Γ k)]
    {Λ : Type} [Inhabited Λ]
    {σ : Type} [Inhabited σ] [Fintype σ]
    (M₂ : Λ → TM2.Stmt Γ Λ σ) (S₂ : Finset Λ) (hS₂ : TM2.Supports M₂ S₂)
    (k_in : K) (vHalt : σ) :
    ∃ (k_enc : ℕ) (enc : TM2to1.Γ' K Γ → List.Vector Bool k_enc)
      (Q₀ : ℕ) (hQ₀ : 0 < Q₀)
      (M_fin : @TM0.Machine Bool (Fin Q₀) ⟨⟨0, hQ₀⟩⟩)
      (q_halt : Fin Q₀),
      ∀ (L : List (Γ k_in)) (P : Prop),
        (∀ cfg, cfg ∈ StateTransition.eval (TM2.step M₂) (TM2.init k_in L) ↔
          cfg = ⟨none, vHalt, fun _ => []⟩ ∧ P) →
        let L_bits : List Bool := (TM2to1.trInit k_in L).flatMap (fun x => (enc x).toList)
        let haltBits : List Bool := (enc (true, fun _ => none)).toList
        ∀ cfg, cfg ∈ @StateTransition.eval (TM0.Cfg Bool (Fin Q₀))
            (@TM0.step Bool (Fin Q₀) ⟨⟨0, hQ₀⟩⟩ _ M_fin)
            (@TM0.init Bool (Fin Q₀) ⟨⟨0, hQ₀⟩⟩ _ L_bits) ↔
          cfg = ⟨q_halt, Tape.mk₁ haltBits⟩ ∧ P := by
  classical
  -- Stage 1: TM2 → TM1 over `Γ₁ = TM2to1.Γ' K Γ`.
  let Γ₁ := TM2to1.Γ' K Γ
  let M₁ := TM2to1.tr M₂
  let S₁ := TM2to1.trSupp M₂ S₂
  have hS₁ : TM1.Supports M₁ S₁ := TM2to1.tr_supports M₂ hS₂
  let c₁_halt : TM1.Cfg Γ₁ (TM2to1.Λ' K Γ Λ σ) σ :=
    ⟨none, vHalt, Tape.mk₁ [(true, fun _ => none)]⟩
  have htr_halt : ∀ b, TM2to1.TrCfg (⟨none, vHalt, fun _ => []⟩ : TM2.Cfg Γ Λ σ) b →
      b = c₁_halt := by
    intro b hb
    cases hb with
    | mk L hL =>
      have hL_empty : L = (∅ : ListBlank (∀ k, Option (Γ k))) := by
        refine ListBlank.ext fun i => funext fun k => ?_
        have hk := congrArg (fun lb => lb.nth i) (hL k)
        rw [proj_map_nth] at hk
        simp only [List.map_nil, List.reverse_nil, ListBlank.nth_mk, List.getI_nil] at hk
        rw [hk]
        rfl
      subst hL_empty
      have hadd : TM2to1.addBottom (∅ : ListBlank (∀ k, Option (Γ k))) =
          ListBlank.mk [(true, fun _ => none)] := by
        refine ListBlank.ext fun i => ?_
        cases i with
        | zero => rfl
        | succ i =>
          simp only [TM2to1.addBottom, ListBlank.nth_succ]
          rfl
      simp only [c₁_halt, Tape.mk₁, Tape.mk₂, Option.map_none]
      rw [hadd]
      rfl
  -- Stage 2: TM1(Γ₁) → TM1(Bool).
  obtain ⟨k_enc, enc, dec, henc0, hencdec⟩ := TM1to1.exists_enc_dec (Γ := Γ₁)
  let M₁b := TM1to1.tr enc dec M₁
  let S₁b := TM1to1.trSupp M₁ S₁
  have hS₁b : TM1.Supports M₁b S₁b := TM1to1.tr_supports enc dec M₁ hS₁
  let haltBits : List Bool := (enc (true, fun _ => none)).toList
  let c₁b_halt : TM1.Cfg Bool (TM1to1.Λ' Γ₁ (TM2to1.Λ' K Γ Λ σ) σ) σ :=
    ⟨none, vHalt, Tape.mk₁ haltBits⟩
  have htrCfg1_halt : TM1to1.trCfg enc henc0 c₁_halt = c₁b_halt := by
    simp only [TM1to1.trCfg, c₁_halt, c₁b_halt, TM1to1.trTape, TM1to1.trTape', Tape.mk₁, Tape.mk₂,
      Tape.mk'_left, Tape.mk'_right₀, ListBlank.flatMap_mk, List.flatMap_nil, haltBits,
      Option.map_none]
    congr 2
    rw [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  -- Stage 3: TM1(Bool) → TM0(Bool).
  let M₀ := TM1to0.tr M₁b
  let S₀ : Finset (TM1to0.Λ' M₁b) := TM1to0.trStmts M₁b S₁b
  have hS₀ : TM0.Supports M₀ ↑S₀ := TM1to0.tr_supports M₁b hS₁b
  let q₀_halt : TM1to0.Λ' M₁b := (none, vHalt)
  let c₀_halt : TM0.Cfg Bool (TM1to0.Λ' M₁b) := ⟨q₀_halt, Tape.mk₁ haltBits⟩
  -- Stage 4: Compress `S₀` to `Fin Q₀`.
  let Q₀ : ℕ := S₀.card
  have hdef_mem : (default : TM1to0.Λ' M₁b) ∈ S₀ := hS₀.1
  have hQ₀ : 0 < Q₀ := Finset.card_pos.mpr ⟨default, hdef_mem⟩
  let : Inhabited (Fin Q₀) := ⟨⟨0, hQ₀⟩⟩
  let e₀ : S₀ ≃ Fin Q₀ := (Fintype.equivFin S₀).trans (finCongr (Fintype.card_coe S₀))
  let idxDef : Fin Q₀ := e₀ ⟨default, hdef_mem⟩
  let e : S₀ ≃ Fin Q₀ := e₀.trans (Equiv.swap idxDef ⟨0, hQ₀⟩)
  have he_def : e ⟨default, hdef_mem⟩ = default := by
    change Equiv.swap idxDef ⟨0, hQ₀⟩ (e₀ ⟨default, hdef_mem⟩) = ⟨0, hQ₀⟩
    simp [idxDef]
  let g₁ : PointedMap (TM1to0.Λ' M₁b) (Fin Q₀) :=
    ⟨fun q => if h : q ∈ S₀ then e ⟨q, h⟩ else default, by simp [hdef_mem, he_def]⟩
  let g₂ : Fin Q₀ → TM1to0.Λ' M₁b := fun i => (e.symm i).1
  have hg₂₁ : ∀ q ∈ (S₀ : Set (TM1to0.Λ' M₁b)), g₂ (g₁ q) = q := by
    intro q hq
    have hq' : q ∈ S₀ := hq
    simp [g₁, g₂, hq']
  let idBool : PointedMap Bool Bool := ⟨id, rfl⟩
  let M_fin : TM0.Machine Bool (Fin Q₀) := M₀.map idBool idBool g₁ g₂
  let q_halt : Fin Q₀ := g₁ q₀_halt
  refine ⟨k_enc, enc, Q₀, hQ₀, M_fin, q_halt, ?_⟩
  intro L P htm2 L_bits haltBits' cfg
  have htm1 : ∀ cfg₁, cfg₁ ∈ StateTransition.eval (TM1.step M₁) (TM1.init (TM2to1.trInit k_in L)) ↔
      cfg₁ = c₁_halt ∧ P := by
    intro cfg₁
    constructor
    · intro h
      obtain ⟨c₂, hc₂_rel, hc₂_eval⟩ :=
        StateTransition.tr_eval_rev (TM2to1.tr_respects M₂) (TM2to1.trCfg_init k_in L) h
      rcases (htm2 c₂).mp hc₂_eval with ⟨rfl, hP⟩
      exact ⟨htr_halt cfg₁ hc₂_rel, hP⟩
    · rintro ⟨rfl, hP⟩
      have h2 := (htm2 ⟨none, vHalt, fun _ => []⟩).mpr ⟨rfl, hP⟩
      obtain ⟨b, hb_rel, hb_eval⟩ :=
        StateTransition.tr_eval (TM2to1.tr_respects M₂) (TM2to1.trCfg_init k_in L) h2
      rwa [htr_halt b hb_rel] at hb_eval
  have htrCfg1_init : TM1to1.trCfg enc henc0 (TM1.init (TM2to1.trInit k_in L)) =
      (TM1.init L_bits : TM1.Cfg Bool (TM1to1.Λ' Γ₁ (TM2to1.Λ' K Γ Λ σ) σ) σ) := by
    simp only [TM1to1.trCfg, TM1.init, TM1to1.trTape, TM1to1.trTape', Tape.mk₁, Tape.mk₂,
      Tape.mk'_left, Tape.mk'_right₀, ListBlank.flatMap_mk, List.flatMap_nil, L_bits]
    rfl
  have htm1b : ∀ cfg₁b, cfg₁b ∈ StateTransition.eval (TM1.step M₁b) (TM1.init L_bits) ↔
      cfg₁b = c₁b_halt ∧ P := by
    intro cfg₁b
    have htr := StateTransition.tr_eval' (TM1.step M₁) (TM1.step M₁b)
      (TM1to1.trCfg enc henc0) (TM1to1.tr_respects dec M₁ hencdec)
      (TM1.init (TM2to1.trInit k_in L))
    rw [htrCfg1_init] at htr
    rw [htr, Part.map_eq_map, Part.mem_map_iff]
    constructor
    · rintro ⟨c₁, hc₁, rfl⟩
      rcases (htm1 c₁).mp hc₁ with ⟨rfl, hP⟩
      exact ⟨htrCfg1_halt, hP⟩
    · rintro ⟨rfl, hP⟩
      exact ⟨c₁_halt, (htm1 c₁_halt).mpr ⟨rfl, hP⟩, htrCfg1_halt⟩
  have htm0_inf : ∀ cfg₀, cfg₀ ∈ StateTransition.eval (TM0.step M₀) (TM0.init L_bits) ↔
      cfg₀ = c₀_halt ∧ P := by
    intro cfg₀
    have htr := StateTransition.tr_eval' (TM1.step M₁b) (TM0.step M₀)
      (TM1to0.trCfg M₁b) (TM1to0.tr_respects M₁b) (TM1.init L_bits)
    have hinit0 : TM1to0.trCfg M₁b (TM1.init L_bits) = TM0.init L_bits := rfl
    rw [hinit0] at htr
    rw [htr, Part.map_eq_map, Part.mem_map_iff]
    constructor
    · rintro ⟨c₁b, hc₁b, rfl⟩
      rcases (htm1b c₁b).mp hc₁b with ⟨rfl, hP⟩
      exact ⟨rfl, hP⟩
    · rintro ⟨rfl, hP⟩
      exact ⟨c₁b_halt, (htm1b c₁b_halt).mpr ⟨rfl, hP⟩, rfl⟩
  have hresp := M₀.map_respects idBool idBool g₁ g₂ hS₀ (fun _ => rfl) hg₂₁
  have hrel_init : (TM0.init L_bits : TM0.Cfg Bool (TM1to0.Λ' M₁b)).q ∈ (S₀ : Set _) ∧
      TM0.Cfg.map idBool g₁ (TM0.init L_bits) = TM0.init L_bits := by
    refine ⟨hS₀.1, ?_⟩
    rw [TM0.map_init]
    simp [idBool]
  have hmap_halt : TM0.Cfg.map idBool g₁ c₀_halt = ⟨q_halt, Tape.mk₁ haltBits'⟩ := by
    simp only [TM0.Cfg.map, c₀_halt, q_halt, Tape.map_mk₁, idBool, haltBits, haltBits']
    simp
  constructor
  · intro h
    obtain ⟨c₀, ⟨_, hc₀_map⟩, hc₀_eval⟩ := StateTransition.tr_eval_rev hresp hrel_init h
    rcases (htm0_inf c₀).mp hc₀_eval with ⟨rfl, hP⟩
    exact ⟨hc₀_map.symm.trans hmap_halt, hP⟩
  · rintro ⟨rfl, hP⟩
    have h0 := (htm0_inf c₀_halt).mpr ⟨rfl, hP⟩
    obtain ⟨b, ⟨_, hb_map⟩, hb_eval⟩ := StateTransition.tr_eval hresp hrel_init h0
    rwa [← hb_map, hmap_halt] at hb_eval

/-- Append a `2 * k + 1`-state tape eraser to a finite-state binary `TM0` machine that always halts
on `Tape.mk₁ haltBits` (`haltBits.length = k`), producing a finite-state binary `TM0` machine with
a unique halting state `qHalt` and blank halting tape `default`. -/
private theorem wrap_blank_eraser
    (Q₀ : ℕ) (hQ₀ : 0 < Q₀)
    (M_fin : @TM0.Machine Bool (Fin Q₀) ⟨⟨0, hQ₀⟩⟩)
    (q_fin_halt : Fin Q₀) (haltBits : List Bool) :
    let k := haltBits.length
    let Q := Q₀ + (2 * k + 1)
    ∃ (_hQ : NeZero Q) (M_clean : @TM0.Machine Bool (Fin Q) ⟨⟨0, NeZero.pos Q⟩⟩) (qHalt : Fin Q),
      (∀ q b, M_clean q b = none ↔ q = qHalt) ∧
      ∀ (L : List Bool) (P : Prop),
        (∀ cfg, cfg ∈ @StateTransition.eval (TM0.Cfg Bool (Fin Q₀))
            (@TM0.step Bool (Fin Q₀) ⟨⟨0, hQ₀⟩⟩ _ M_fin)
            (@TM0.init Bool (Fin Q₀) ⟨⟨0, hQ₀⟩⟩ _ L) ↔
          cfg = ⟨q_fin_halt, Tape.mk₁ haltBits⟩ ∧ P) →
        (@TM0.Reaches Bool (Fin Q) ⟨⟨0, NeZero.pos Q⟩⟩ _ M_clean
          (@TM0.init Bool (Fin Q) ⟨⟨0, NeZero.pos Q⟩⟩ _ L) ⟨qHalt, default⟩ ↔ P) := by
  intro k Q
  have hQ : NeZero Q := ⟨by omega⟩
  let embL : Fin Q₀ → Fin Q := fun q => ⟨q.val, by omega⟩
  let embR : Fin (2 * k + 1) → Fin Q := fun j => ⟨Q₀ + j.val, by omega⟩
  let qHalt : Fin Q := embR ⟨2 * k, by omega⟩
  let M_clean : @TM0.Machine Bool (Fin Q) ⟨⟨0, NeZero.pos Q⟩⟩ := fun q b =>
    if hq : q.val < Q₀ then
      match M_fin ⟨q.val, hq⟩ b with
      | some (q', s) => some (embL q', s)
      | none => some (embR ⟨0, by omega⟩, TM0.Stmt.write b)
    else
      let j : ℕ := q.val - Q₀
      if hj : j < 2 * k then
        if j % 2 = 0 then some (embR ⟨j + 1, by omega⟩, TM0.Stmt.write false)
        else some (embR ⟨j + 1, by omega⟩, TM0.Stmt.move Dir.right)
      else none
  have hM_clean_halt_iff : ∀ q b, M_clean q b = none ↔ q = qHalt := by
    intro q b
    constructor
    · intro h
      simp only [M_clean] at h
      by_cases hq : q.val < Q₀
      · simp only [hq, ↓reduceDIte] at h
        cases hfin : M_fin ⟨q.val, hq⟩ b with
        | none => simp [hfin] at h
        | some val => simp [hfin] at h
      · simp only [hq, ↓reduceDIte] at h
        by_cases hj : q.val - Q₀ < 2 * k
        · simp only [hj, ↓reduceDIte] at h
          split_ifs at h
        · apply Fin.ext
          change q.val = Q₀ + 2 * k
          omega
    · rintro rfl
      have h1 : ¬ (Q₀ + 2 * k < Q₀) := by omega
      simp [M_clean, qHalt, embR, h1]
  have hsim_step : ∀ {c₁ c₂ : TM0.Cfg Bool (Fin Q₀)},
      c₂ ∈ @TM0.step Bool (Fin Q₀) ⟨⟨0, hQ₀⟩⟩ _ M_fin c₁ →
      (⟨embL c₂.q, c₂.Tape⟩ : TM0.Cfg Bool (Fin Q)) ∈
        @TM0.step Bool (Fin Q) ⟨⟨0, NeZero.pos Q⟩⟩ _ M_clean ⟨embL c₁.q, c₁.Tape⟩ := by
    rintro ⟨q₁, T₁⟩ ⟨q₂, T₂⟩ hstep
    simp only [TM0.step, Option.mem_def, Option.map_eq_some_iff] at hstep ⊢
    rcases hstep with ⟨⟨q', s⟩, hM, hcfg⟩
    cases hcfg
    refine ⟨⟨embL q', s⟩, ?_, rfl⟩
    simp only [M_clean, embL, q₁.isLt, ↓reduceDIte]
    rw [Fin.eta, hM]
  have hsim_reaches : ∀ {c₁ c₂ : TM0.Cfg Bool (Fin Q₀)},
      @TM0.Reaches Bool (Fin Q₀) ⟨⟨0, hQ₀⟩⟩ _ M_fin c₁ c₂ →
      @TM0.Reaches Bool (Fin Q) ⟨⟨0, NeZero.pos Q⟩⟩ _ M_clean
        ⟨embL c₁.q, c₁.Tape⟩ ⟨embL c₂.q, c₂.Tape⟩ := by
    intro c₁ c₂ h
    induction h with
    | refl => exact ReflTransGen.refl
    | tail _ hstep ih => exact ih.tail (hsim_step hstep)
  have hclean_inv : ∀ (c0 : TM0.Cfg Bool (Fin Q₀)) (c : TM0.Cfg Bool (Fin Q)),
      @TM0.Reaches Bool (Fin Q) ⟨⟨0, NeZero.pos Q⟩⟩ _ M_clean ⟨embL c0.q, c0.Tape⟩ c →
      (∃ c' : TM0.Cfg Bool (Fin Q₀),
        @TM0.Reaches Bool (Fin Q₀) ⟨⟨0, hQ₀⟩⟩ _ M_fin c0 c' ∧ c = ⟨embL c'.q, c'.Tape⟩) ∨
      (∃ c_h : TM0.Cfg Bool (Fin Q₀),
        c_h ∈ StateTransition.eval (@TM0.step Bool (Fin Q₀) ⟨⟨0, hQ₀⟩⟩ _ M_fin) c0) := by
    intro c0 c hreach
    induction hreach with
    | refl => exact Or.inl ⟨c0, ReflTransGen.refl, rfl⟩
    | tail _ hstep ih =>
      rcases ih with ⟨c', hc'_reach, rfl⟩ | hdom
      · simp only [TM0.step, Option.mem_def, Option.map_eq_some_iff, M_clean, embL, c'.q.isLt,
          ↓reduceDIte, Fin.eta] at hstep
        cases hM : M_fin c'.q c'.Tape.1 with
        | none =>
          right
          refine ⟨c', StateTransition.mem_eval.mpr ⟨hc'_reach, ?_⟩⟩
          simp [TM0.step, hM]
        | some val =>
          rcases val with ⟨q', s⟩
          rw [hM] at hstep
          rcases hstep with ⟨⟨q'', s'⟩, hpair, rfl⟩
          simp only [Option.some.injEq, Prod.mk.injEq] at hpair
          rcases hpair with ⟨rfl, rfl⟩
          cases s with
          | move d =>
            left
            refine ⟨⟨q', c'.Tape.move d⟩, hc'_reach.tail ?_, rfl⟩
            simp [TM0.step, hM]
          | write a =>
            left
            refine ⟨⟨q', c'.Tape.write a⟩, hc'_reach.tail ?_, rfl⟩
            simp [TM0.step, hM]
      · exact Or.inr hdom
  have herase_lift :
      @TM0.Reaches Bool (Fin Q) ⟨⟨0, NeZero.pos Q⟩⟩ _ M_clean
        ⟨embR ⟨0, by omega⟩, Tape.mk₁ haltBits⟩ ⟨qHalt, default⟩ := by
    let M_erase : Fin (2 * k + 1) → Bool → Option (Fin (2 * k + 1) × TM0.Stmt Bool) :=
      fun i _ =>
        if h : i.val < 2 * k then
          if i.val % 2 = 0 then some (⟨i.val + 1, by omega⟩, TM0.Stmt.write false)
          else some (⟨i.val + 1, by omega⟩, TM0.Stmt.move Dir.right)
        else none
    have h0 := erase_tape_aux k [] haltBits rfl (by simp) 0 (Nat.zero_le _)
    have hstep_emb : ∀ {a b : TM0.Cfg Bool (Fin (2 * k + 1))},
        b ∈ @TM0.step Bool (Fin (2 * k + 1)) ⟨⟨0, by omega⟩⟩ _ M_erase a →
        (⟨embR b.q, b.Tape⟩ : TM0.Cfg Bool (Fin Q)) ∈
          @TM0.step Bool (Fin Q) ⟨⟨0, NeZero.pos Q⟩⟩ _ M_clean ⟨embR a.q, a.Tape⟩ := by
      rintro ⟨j₁, T₁⟩ ⟨j₂, T₂⟩ hs
      simp only [TM0.step, Option.mem_def, Option.map_eq_some_iff] at hs ⊢
      rcases hs with ⟨⟨j', s⟩, hMe, hcfg⟩
      cases hcfg
      refine ⟨⟨embR j', s⟩, ?_, rfl⟩
      have hnotlt : ¬ (Q₀ + j₁.val < Q₀) := by omega
      have hsub : Q₀ + j₁.val - Q₀ = j₁.val := by omega
      simp only [M_clean, embR, hnotlt, ↓reduceDIte, hsub]
      simp only [M_erase] at hMe
      by_cases h1 : j₁.val < 2 * k
      · simp only [h1, ↓reduceDIte] at hMe ⊢
        by_cases h2 : j₁.val % 2 = 0
        · simp only [h2, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hMe ⊢
          rcases hMe with ⟨rfl, rfl⟩
          exact ⟨rfl, rfl⟩
        · simp only [h2, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hMe ⊢
          rcases hMe with ⟨rfl, rfl⟩
          exact ⟨rfl, rfl⟩
      · simp only [h1, ↓reduceDIte] at hMe
        cases hMe
    have hreach_emb : ∀ {a b : TM0.Cfg Bool (Fin (2 * k + 1))},
        @TM0.Reaches Bool (Fin (2 * k + 1)) ⟨⟨0, by omega⟩⟩ _ M_erase a b →
        @TM0.Reaches Bool (Fin Q) ⟨⟨0, NeZero.pos Q⟩⟩ _ M_clean
          ⟨embR a.q, a.Tape⟩ ⟨embR b.q, b.Tape⟩ := by
      intro a b hr
      induction hr with
      | refl => exact ReflTransGen.refl
      | tail _ hs ih => exact ih.tail (hstep_emb hs)
    have h1 := hreach_emb h0
    have hstart : Tape.mk₂ (List.replicate 0 false ++ []) (haltBits.drop 0) = Tape.mk₁ haltBits := rfl
    have hend : Tape.mk₂ (List.replicate k false ++ []) ([] : List Bool) = default := by
      simp only [List.append_nil, Tape.mk₂, listBlank_replicate_false]
      rfl
    simpa only [hstart, hend, qHalt] using h1
  refine ⟨hQ, M_clean, qHalt, hM_clean_halt_iff, ?_⟩
  intro L P htm0_fin
  have hinit_clean :
      (@TM0.init Bool (Fin Q) ⟨⟨0, NeZero.pos Q⟩⟩ _ L) =
        ⟨embL (@TM0.init Bool (Fin Q₀) ⟨⟨0, hQ₀⟩⟩ _ L).q,
          (@TM0.init Bool (Fin Q₀) ⟨⟨0, hQ₀⟩⟩ _ L).Tape⟩ := rfl
  constructor
  · intro hreach
    rw [hinit_clean] at hreach
    rcases hclean_inv (@TM0.init Bool (Fin Q₀) ⟨⟨0, hQ₀⟩⟩ _ L) ⟨qHalt, default⟩ hreach with
      ⟨c', _, heq⟩ | ⟨c_h, hc_h⟩
    · have hval := congrArg (fun x : TM0.Cfg Bool (Fin Q) => x.q.val) heq
      simp only [qHalt, embR, embL] at hval
      omega
    · exact ((htm0_fin c_h).mp hc_h).2
  · intro hP
    have heval : ⟨q_fin_halt, Tape.mk₁ haltBits⟩ ∈
        StateTransition.eval (@TM0.step Bool (Fin Q₀) ⟨⟨0, hQ₀⟩⟩ _ M_fin)
          (@TM0.init Bool (Fin Q₀) ⟨⟨0, hQ₀⟩⟩ _ L) :=
      (htm0_fin _).mpr ⟨rfl, hP⟩
    obtain ⟨hfin_reach, hfin_none⟩ := StateTransition.mem_eval.mp heval
    have hM_fin_none : M_fin q_fin_halt (Tape.mk₁ haltBits).1 = none := by
      simp only [TM0.step, Option.map_eq_none_iff] at hfin_none
      exact hfin_none
    have hjmp :
        (⟨embR ⟨0, by omega⟩, Tape.mk₁ haltBits⟩ : TM0.Cfg Bool (Fin Q)) ∈
          @TM0.step Bool (Fin Q) ⟨⟨0, NeZero.pos Q⟩⟩ _ M_clean
            ⟨embL q_fin_halt, Tape.mk₁ haltBits⟩ := by
      simp only [TM0.step, Option.mem_def, Option.map_eq_some_iff, M_clean, embL, q_fin_halt.isLt,
        ↓reduceDIte, Fin.eta, hM_fin_none]
      exact ⟨⟨embR ⟨0, by omega⟩, TM0.Stmt.write (Tape.mk₁ haltBits).1⟩, rfl, by
        simp [Tape.write_self]⟩
    rw [hinit_clean]
    exact ((hsim_reaches hfin_reach).tail hjmp).trans herase_lift

end CompilerStages

section UniversalTM

/-- Diagonal partial recursive function `n ↦ eval (ofNat n) 0`. -/
private def diagFn : ℕ →. ℕ :=
  fun n => (Denumerable.ofNat Nat.Partrec.Code n).eval 0

private theorem diagFn_partrec : Partrec diagFn :=
  Nat.Partrec.Code.eval_part.comp
    (Primrec.ofNat Nat.Partrec.Code).to_comp (Computable.const 0)

private theorem not_computablePred_diagFn_dom :
    ¬ ComputablePred (fun n : ℕ => (diagFn n).Dom) := by
  intro h
  have hcode : ComputablePred (fun c : Nat.Partrec.Code => (c.eval 0).Dom) :=
    computablePred_of_reduction (f := Encodable.encode)
      (p := fun c : Nat.Partrec.Code => (c.eval 0).Dom)
      (q := fun n : ℕ => (diagFn n).Dom)
      Primrec.encode.to_comp
      (fun c => by simp [diagFn])
      h
  exact ComputablePred.halting_problem 0 hcode

set_option backward.isDefEq.respectTransparency false in
/-- Main theorem: there exists a finite-state binary `TM0` machine with a unique halting state
`qHalt` and a primitive recursive input encoding `inputBits : ℕ → List Bool` whose blank-tape
halting problem is undecidable. -/
theorem exists_undecidable_blank_tm0 :
    ∃ (Q : ℕ) (_ : NeZero Q) (M : @TM0.Machine Bool (Fin Q) ⟨⟨0, NeZero.pos Q⟩⟩)
      (qHalt : Fin Q) (inputBits : ℕ → List Bool),
      Primrec inputBits ∧
      (∀ q b, M q b = none ↔ q = qHalt) ∧
      ¬ ComputablePred (fun n =>
        @TM0.Reaches Bool (Fin Q) ⟨⟨0, NeZero.pos Q⟩⟩ _ M
          (@TM0.init Bool (Fin Q) ⟨⟨0, NeZero.pos Q⟩⟩ _ (inputBits n))
          ⟨qHalt, default⟩) := by
  -- Step 1: Compile `diagFn` to a `ToPartrec.Code` whose output is always `[]`.
  have hpart' : @Nat.Partrec' 1 (fun v => diagFn v.head) :=
    Nat.Partrec'.part_iff₁.mpr diagFn_partrec
  obtain ⟨c₀, hc₀⟩ := ToPartrec.Code.exists_code hpart'
  let c : ToPartrec.Code := ToPartrec.Code.nil.comp c₀
  have hc_eval : ∀ n : ℕ, ∀ v, v ∈ c.eval [n] ↔ v = [] ∧ (diagFn n).Dom := by
    intro n v
    have hc₀n : c₀.eval [n] = Part.map (fun x => [x]) (diagFn n) := hc₀ ⟨[n], rfl⟩
    have hcomp : c.eval [n] = Part.bind (c₀.eval [n]) ToPartrec.Code.nil.eval := rfl
    rw [hcomp, hc₀n, Part.mem_bind_iff]
    constructor
    · rintro ⟨w, hw, hv⟩
      rw [Part.mem_map_iff] at hw
      rcases hw with ⟨y, hy, _⟩
      simp only [ToPartrec.Code.nil_eval, Part.pure_eq_some, Part.mem_some_iff] at hv
      exact ⟨hv, Part.dom_iff_mem.mpr ⟨y, hy⟩⟩
    · rintro ⟨rfl, hdom⟩
      refine ⟨[Part.get (diagFn n) hdom], ?_, by simp⟩
      rw [Part.mem_map_iff]
      exact ⟨Part.get (diagFn n) hdom, Part.get_mem hdom, rfl⟩
  -- Step 2: Apply our modular TM2 → finite binary TM0 compiler using `Inhabited Λ'` at `c`.
  have htm2_halt_eq : PartrecToTM2.halt [] = (⟨none, none, fun _ => []⟩ : PartrecToTM2.Cfg') := by
    simp only [PartrecToTM2.halt, PartrecToTM2.trList]
    congr 1
    funext k
    cases k <;> rfl
  obtain ⟨k_enc, enc, Q₀, hQ₀, M_fin, q_fin_halt, hfin⟩ :=
    @compile_tm2_to_fin_tm0
      PartrecToTM2.K' _ _ (fun _ => PartrecToTM2.Γ') _
      PartrecToTM2.Λ' ⟨PartrecToTM2.trNormal c PartrecToTM2.Cont'.halt⟩
      (Option PartrecToTM2.Γ') _ _
      PartrecToTM2.tr (PartrecToTM2.codeSupp c PartrecToTM2.Cont'.halt)
      (PartrecToTM2.tr_supports c PartrecToTM2.Cont'.halt)
      PartrecToTM2.K'.main none
  -- Step 3: Wrap `M_fin` with the tape eraser.
  let haltBits : List Bool := (enc (true, fun _ => none)).toList
  obtain ⟨hQ, M_clean, qHalt, hM_clean_halt_iff, hclean⟩ :=
    wrap_blank_eraser Q₀ hQ₀ M_fin q_fin_halt haltBits
  let L₁ : ℕ → List (TM2to1.Γ' PartrecToTM2.K' (fun _ => PartrecToTM2.Γ')) :=
    fun n => TM2to1.trInit (K := PartrecToTM2.K') (Γ := fun _ => PartrecToTM2.Γ')
      PartrecToTM2.K'.main (PartrecToTM2.trList [n])
  let L₁b : ℕ → List Bool := fun n => (L₁ n).flatMap (fun x => (enc x).toList)
  -- Step 4: Connect `PartrecToTM2.tr_eval` to `hfin` and `hclean`.
  have hiff : ∀ n : ℕ,
      @TM0.Reaches Bool (Fin (Q₀ + (2 * haltBits.length + 1))) ⟨⟨0, NeZero.pos _⟩⟩ _ M_clean
        (@TM0.init Bool (Fin (Q₀ + (2 * haltBits.length + 1))) ⟨⟨0, NeZero.pos _⟩⟩ _ (L₁b n))
        ⟨qHalt, default⟩ ↔ (diagFn n).Dom := by
    intro n
    have hinit2 : PartrecToTM2.init c [n] =
        @TM2.init PartrecToTM2.K' (fun _ => PartrecToTM2.Γ') PartrecToTM2.Λ'
          (Option PartrecToTM2.Γ') ⟨PartrecToTM2.trNormal c PartrecToTM2.Cont'.halt⟩ _ _
          PartrecToTM2.K'.main (PartrecToTM2.trList [n]) := by
      simp only [PartrecToTM2.init, TM2.init]
      congr 1
      funext k
      cases k <;> rfl
    have htm2 : ∀ cfg,
        cfg ∈ StateTransition.eval (TM2.step PartrecToTM2.tr)
          (@TM2.init PartrecToTM2.K' (fun _ => PartrecToTM2.Γ') PartrecToTM2.Λ'
            (Option PartrecToTM2.Γ') ⟨PartrecToTM2.trNormal c PartrecToTM2.Cont'.halt⟩ _ _
            PartrecToTM2.K'.main (PartrecToTM2.trList [n])) ↔
        cfg = ⟨none, none, fun _ => []⟩ ∧ (diagFn n).Dom := by
      intro cfg
      rw [← hinit2, PartrecToTM2.tr_eval c [n], Part.map_eq_map, Part.mem_map_iff]
      constructor
      · rintro ⟨v, hv, rfl⟩
        rcases (hc_eval n v).mp hv with ⟨rfl, hdom⟩
        exact ⟨htm2_halt_eq, hdom⟩
      · rintro ⟨rfl, hdom⟩
        exact ⟨[], (hc_eval n []).mpr ⟨rfl, hdom⟩, htm2_halt_eq⟩
    exact hclean (L₁b n) (diagFn n).Dom (hfin (PartrecToTM2.trList [n]) (diagFn n).Dom htm2)
  -- Step 5: Prove `L₁b` is `Primrec`.
  have hL₁b_prim : Primrec L₁b := by
    let headBits : List Bool :=
      (enc (true, Function.update (fun _ => none) PartrecToTM2.K'.main
        (some PartrecToTM2.Γ'.cons))).toList
    let charBits : PartrecToTM2.Γ' → List Bool :=
      fun a => (enc (false, Function.update (fun _ => none) PartrecToTM2.K'.main (some a))).toList
    have hL₁b_eq : ∀ n, L₁b n = headBits ++ ((PartrecToTM2.trNat n).reverse.flatMap charBits) := by
      intro n
      have hrev : (PartrecToTM2.trList [n]).reverse =
          PartrecToTM2.Γ'.cons :: (PartrecToTM2.trNat n).reverse := by
        simp [PartrecToTM2.trList]
      dsimp only [L₁b, L₁, TM2to1.trInit, headBits, charBits]
      rw [hrev, List.map_cons, List.headI_cons, List.tail_cons, List.flatMap_cons, List.flatMap_map]
    have hchar_prim : Primrec charBits := Primrec.dom_finite charBits
    have hprim : Primrec (fun n => headBits ++ (PartrecToTM2.trNat n).reverse.flatMap charBits) :=
      Primrec.list_append.comp (Primrec.const headBits)
        (Primrec.list_flatMap (Primrec.list_reverse.comp primrec_trNat)
          (hchar_prim.comp Primrec.snd))
    exact hprim.of_eq fun n => (hL₁b_eq n).symm
  refine ⟨Q₀ + (2 * haltBits.length + 1), hQ, M_clean, qHalt, L₁b, hL₁b_prim,
    hM_clean_halt_iff, ?_⟩
  intro hcomp
  exact not_computablePred_diagFn_dom (hcomp.of_eq fun n => hiff n)

end UniversalTM

end Adian
