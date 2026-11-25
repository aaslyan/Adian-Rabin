module

public import Mathlib.Computability.Primrec.List
public import Mathlib.Computability.RE
public import Mathlib.GroupTheory.FinitelyPresentedGroup
public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.GroupTheory.Coprod.Basic

/-!
# Finite Group Presentations and Computability Layer

This file defines concrete finite group presentations `FinPres`, establishes their equivalence
with Mathlib's `Group.IsFinitelyPresented`, defines free-product presentations `FinPres.coprod`,
and equips `FinPres` with a `Primcodable` instance so that `ComputablePred` and `Primrec` can be
stated directly over finite presentations.
-/

@[expose] public section

namespace Adian

section Words

variable {α β : Type*}

/-- Formal inverse of a raw group word over `α`. -/
def wordInv (w : List (α × Bool)) : List (α × Bool) :=
  (w.map fun p => (p.1, !p.2)).reverse

/-- Nonnegative power of a raw group word. -/
def wordPow (w : List (α × Bool)) : ℕ → List (α × Bool)
  | 0 => []
  | n + 1 => w ++ wordPow w n

/-- Integer power of a raw group word. -/
def wordZPow (w : List (α × Bool)) : ℤ → List (α × Bool)
  | Int.ofNat n => wordPow w n
  | Int.negSucc n => wordPow (wordInv w) (n + 1)

/-- Conjugation `g⁻¹ * w * g` as a raw group word. -/
def wordConj (g w : List (α × Bool)) : List (α × Bool) :=
  wordInv g ++ w ++ g

/-- Conjugation `g * w * g⁻¹` as a raw group word. -/
def wordConjL (g w : List (α × Bool)) : List (α × Bool) :=
  g ++ w ++ wordInv g

/-- Commutator `a * b * a⁻¹ * b⁻¹` as a raw group word. -/
def wordComm (a b : List (α × Bool)) : List (α × Bool) :=
  a ++ b ++ wordInv a ++ wordInv b

/-- Relator `u * v⁻¹` encoding the equation `u = v`. -/
def wordRel (u v : List (α × Bool)) : List (α × Bool) :=
  u ++ wordInv v

/-- Single generator word. -/
def wordOf (a : α) : List (α × Bool) := [(a, true)]

/-- Single inverse generator word. -/
def wordOfInv (a : α) : List (α × Bool) := [(a, false)]

/-- Map generator indices in a raw word. -/
def mapWord (f : α → β) (w : List (α × Bool)) : List (β × Bool) :=
  w.map fun p => (f p.1, p.2)

theorem freeGroup_mk_nil : (FreeGroup.mk ([] : List (α × Bool))) = 1 := rfl

theorem freeGroup_mk_append (u v : List (α × Bool)) :
    FreeGroup.mk (u ++ v) = FreeGroup.mk u * FreeGroup.mk v := rfl

theorem freeGroup_mk_wordOf (a : α) : FreeGroup.mk (wordOf a) = FreeGroup.of a := rfl

theorem freeGroup_mk_wordOfInv (a : α) : FreeGroup.mk (wordOfInv a) = (FreeGroup.of a)⁻¹ := rfl

theorem freeGroup_mk_wordInv (w : List (α × Bool)) :
    FreeGroup.mk (wordInv w) = (FreeGroup.mk w)⁻¹ := by
  induction w with
  | nil => rfl
  | cons p ws ih =>
    rcases p with ⟨a, b⟩
    have h1 : FreeGroup.mk ((a, b) :: ws) = FreeGroup.mk [(a, b)] * FreeGroup.mk ws := rfl
    rw [wordInv, List.map_cons, List.reverse_cons, freeGroup_mk_append, h1, mul_inv_rev]
    rw [show (ws.map fun p => (p.1, !p.2)).reverse = wordInv ws from rfl, ih]
    cases b <;> rfl

theorem freeGroup_mk_wordPow (w : List (α × Bool)) (n : ℕ) :
    FreeGroup.mk (wordPow w n) = (FreeGroup.mk w) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [wordPow, freeGroup_mk_append, ih, pow_succ']

theorem freeGroup_mk_wordZPow (w : List (α × Bool)) (z : ℤ) :
    FreeGroup.mk (wordZPow w z) = (FreeGroup.mk w) ^ z := by
  cases z with
  | ofNat n =>
    rw [wordZPow, freeGroup_mk_wordPow, Int.ofNat_eq_natCast, zpow_natCast]
  | negSucc n =>
    rw [wordZPow, freeGroup_mk_wordPow, freeGroup_mk_wordInv, zpow_negSucc, inv_pow]

theorem freeGroup_mk_wordConj (g w : List (α × Bool)) :
    FreeGroup.mk (wordConj g w) = (FreeGroup.mk g)⁻¹ * FreeGroup.mk w * FreeGroup.mk g := by
  rw [wordConj, freeGroup_mk_append, freeGroup_mk_append, freeGroup_mk_wordInv]

theorem freeGroup_mk_wordConjL (g w : List (α × Bool)) :
    FreeGroup.mk (wordConjL g w) = FreeGroup.mk g * FreeGroup.mk w * (FreeGroup.mk g)⁻¹ := by
  rw [wordConjL, freeGroup_mk_append, freeGroup_mk_append, freeGroup_mk_wordInv]

theorem freeGroup_mk_wordComm (a b : List (α × Bool)) :
    FreeGroup.mk (wordComm a b) =
      FreeGroup.mk a * FreeGroup.mk b * (FreeGroup.mk a)⁻¹ * (FreeGroup.mk b)⁻¹ := by
  rw [wordComm, freeGroup_mk_append, freeGroup_mk_append, freeGroup_mk_append,
    freeGroup_mk_wordInv, freeGroup_mk_wordInv]

theorem freeGroup_mk_wordRel (u v : List (α × Bool)) :
    FreeGroup.mk (wordRel u v) = FreeGroup.mk u * (FreeGroup.mk v)⁻¹ := by
  rw [wordRel, freeGroup_mk_append, freeGroup_mk_wordInv]

theorem freeGroup_mk_mapWord (f : α → β) (w : List (α × Bool)) :
    FreeGroup.mk (mapWord f w) = FreeGroup.map f (FreeGroup.mk w) := by
  induction w with
  | nil => rfl
  | cons p ws ih =>
    rcases p with ⟨a, b⟩
    have h1 : FreeGroup.mk ((a, b) :: ws) = FreeGroup.mk [(a, b)] * FreeGroup.mk ws := rfl
    have h2 : FreeGroup.mk ((f a, b) :: mapWord f ws) =
        FreeGroup.mk [(f a, b)] * FreeGroup.mk (mapWord f ws) := rfl
    rw [mapWord, List.map_cons]
    change FreeGroup.mk ((f a, b) :: mapWord f ws) = _
    rw [h2, h1, map_mul, ih]
    congr 1

end Words

/-- A concrete finite group presentation: `numGens` generators indexed by `Fin numGens` and
a finite list of relators (each a word in generators and their inverses). -/
structure FinPres where
  /-- Number of generators. -/
  numGens : ℕ
  /-- Finite list of defining relators. -/
  relators : List (List (Fin numGens × Bool))
  deriving DecidableEq

namespace FinPres

/-- The finite set of defining relators in `FreeGroup (Fin P.numGens)`. -/
def relSet (P : FinPres) : Set (FreeGroup (Fin P.numGens)) :=
  FreeGroup.mk '' {r | r ∈ P.relators}

/-- The group presented by `P`. -/
abbrev Group (P : FinPres) : Type :=
  PresentedGroup P.relSet

/-- The canonical generator image in `P.Group`. -/
def ofGen {P : FinPres} (i : Fin P.numGens) : P.Group :=
  PresentedGroup.of i

/-- Evaluate a raw word in `P.Group`. -/
def mkWord {P : FinPres} (w : List (Fin P.numGens × Bool)) : P.Group :=
  PresentedGroup.mk P.relSet (FreeGroup.mk w)

@[simp]
theorem mkWord_nil {P : FinPres} : P.mkWord [] = 1 := rfl

@[simp]
theorem mkWord_append {P : FinPres} (u v : List (Fin P.numGens × Bool)) :
    P.mkWord (u ++ v) = P.mkWord u * P.mkWord v := by
  rw [mkWord, freeGroup_mk_append, map_mul]; rfl

@[simp]
theorem mkWord_wordOf {P : FinPres} (i : Fin P.numGens) : P.mkWord (wordOf i) = P.ofGen i := rfl

@[simp]
theorem mkWord_wordOfInv {P : FinPres} (i : Fin P.numGens) :
    P.mkWord (wordOfInv i) = (P.ofGen i)⁻¹ := by
  rw [mkWord, freeGroup_mk_wordOfInv, map_inv]; rfl

@[simp]
theorem mkWord_wordInv {P : FinPres} (w : List (Fin P.numGens × Bool)) :
    P.mkWord (wordInv w) = (P.mkWord w)⁻¹ := by
  rw [mkWord, freeGroup_mk_wordInv, map_inv]; rfl

@[simp]
theorem mkWord_wordPow {P : FinPres} (w : List (Fin P.numGens × Bool)) (n : ℕ) :
    P.mkWord (wordPow w n) = (P.mkWord w) ^ n := by
  rw [mkWord, freeGroup_mk_wordPow, map_pow]; rfl

@[simp]
theorem mkWord_wordZPow {P : FinPres} (w : List (Fin P.numGens × Bool)) (z : ℤ) :
    P.mkWord (wordZPow w z) = (P.mkWord w) ^ z := by
  rw [mkWord, freeGroup_mk_wordZPow, map_zpow]; rfl

@[simp]
theorem mkWord_wordConj {P : FinPres} (g w : List (Fin P.numGens × Bool)) :
    P.mkWord (wordConj g w) = (P.mkWord g)⁻¹ * P.mkWord w * P.mkWord g := by
  rw [mkWord, freeGroup_mk_wordConj, map_mul, map_mul, map_inv]; rfl

@[simp]
theorem mkWord_wordConjL {P : FinPres} (g w : List (Fin P.numGens × Bool)) :
    P.mkWord (wordConjL g w) = P.mkWord g * P.mkWord w * (P.mkWord g)⁻¹ := by
  rw [mkWord, freeGroup_mk_wordConjL, map_mul, map_mul, map_inv]; rfl

@[simp]
theorem mkWord_wordComm {P : FinPres} (a b : List (Fin P.numGens × Bool)) :
    P.mkWord (wordComm a b) =
      P.mkWord a * P.mkWord b * (P.mkWord a)⁻¹ * (P.mkWord b)⁻¹ := by
  rw [mkWord, freeGroup_mk_wordComm, map_mul, map_mul, map_mul, map_inv, map_inv]; rfl

theorem mkWord_eq_one_of_mem {P : FinPres} {r : List (Fin P.numGens × Bool)} (hr : r ∈ P.relators) :
    P.mkWord r = 1 :=
  PresentedGroup.one_of_mem ⟨r, hr, rfl⟩

theorem mkWord_eq_of_wordRel_mem {P : FinPres} {u v : List (Fin P.numGens × Bool)}
    (h : wordRel u v ∈ P.relators) : P.mkWord u = P.mkWord v := by
  have h1 := mkWord_eq_one_of_mem h
  rw [mkWord, freeGroup_mk_wordRel, map_mul, map_inv] at h1
  exact mul_inv_eq_one.mp h1

/-- Every `P.Group` is finitely presented in the sense of Mathlib. -/
instance isFinitelyPresented (P : FinPres) : _root_.Group.IsFinitelyPresented P.Group := by
  have hfin : P.relSet.Finite := P.relators.finite_toSet.image FreeGroup.mk
  have : Finite P.relSet := hfin.to_subtype
  infer_instance

/-- Helper to lift a map `f : Fin P.numGens → G` to `P.Group →* G` by checking raw relators. -/
def lift {P : FinPres} {G : Type*} [_root_.Group G] (f : Fin P.numGens → G)
    (hf : ∀ r ∈ P.relators, FreeGroup.lift f (FreeGroup.mk r) = 1) : P.Group →* G :=
  PresentedGroup.toGroup (f := f) fun _ hr => by
    rcases hr with ⟨r, hr, rfl⟩
    exact hf r hr

@[simp]
theorem lift_ofGen {P : FinPres} {G : Type*} [_root_.Group G] (f : Fin P.numGens → G)
    (hf : ∀ r ∈ P.relators, FreeGroup.lift f (FreeGroup.mk r) = 1) (i : Fin P.numGens) :
    P.lift f hf (P.ofGen i) = f i :=
  PresentedGroup.toGroup.of (f := f) _

@[simp]
theorem lift_mkWord {P : FinPres} {G : Type*} [_root_.Group G] (f : Fin P.numGens → G)
    (hf : ∀ r ∈ P.relators, FreeGroup.lift f (FreeGroup.mk r) = 1)
    (w : List (Fin P.numGens × Bool)) :
    P.lift f hf (P.mkWord w) = FreeGroup.lift f (FreeGroup.mk w) := rfl

theorem hom_ext {P : FinPres} {G : Type*} [_root_.Group G] {φ ψ : P.Group →* G}
    (h : ∀ i : Fin P.numGens, φ (P.ofGen i) = ψ (P.ofGen i)) : φ = ψ :=
  PresentedGroup.ext h

/-- Characterization of `Group.IsFinitelyPresented` via `FinPres`. -/
theorem isFinitelyPresented_iff (G : Type) [_root_.Group G] :
    _root_.Group.IsFinitelyPresented G ↔ ∃ P : FinPres, Nonempty (G ≃* P.Group) := by
  constructor
  · intro hG
    obtain ⟨n, s, hs, ⟨e⟩⟩ := _root_.Group.IsFinitelyPresented.exists_mulEquiv_presentedGroup (G := G)
    classical
    let toWord : FreeGroup (Fin n) → List (Fin n × Bool) := Quot.out
    let rs : List (List (Fin n × Bool)) := hs.toFinset.toList.map toWord
    refine ⟨⟨n, rs⟩, ?_⟩
    have hrel : (⟨n, rs⟩ : FinPres).relSet = s := by
      ext x
      constructor
      · rintro ⟨w, hw, rfl⟩
        change w ∈ hs.toFinset.toList.map toWord at hw
        rw [List.mem_map] at hw
        rcases hw with ⟨y, hy, rfl⟩
        rw [Finset.mem_toList, Set.Finite.mem_toFinset] at hy
        have hq : FreeGroup.mk (toWord y) = y := Quot.out_eq y
        rwa [hq]
      · intro hx
        refine ⟨toWord x, ?_, Quot.out_eq x⟩
        change toWord x ∈ hs.toFinset.toList.map toWord
        exact List.mem_map_of_mem (Finset.mem_toList.mpr (hs.mem_toFinset.mpr hx))
    exact ⟨e.trans (QuotientGroup.quotientMulEquivOfEq (congrArg Subgroup.normalClosure hrel.symm))⟩
  · rintro ⟨P, ⟨e⟩⟩
    exact _root_.Group.IsFinitelyPresented.equiv e.symm

/-- Free product (disjoint union) of two finite presentations. -/
abbrev coprod (P Q : FinPres) : FinPres where
  numGens := P.numGens + Q.numGens
  relators :=
    P.relators.map (mapWord (Fin.castAdd Q.numGens)) ++
    Q.relators.map (mapWord (Fin.natAdd P.numGens))

/-- Canonical isomorphism `(P.coprod Q).Group ≃* P.Group ∗ Q.Group`. -/
def coprodEquiv (P Q : FinPres) : (P.coprod Q).Group ≃* Monoid.Coprod P.Group Q.Group := by
  let gmap : Fin (P.numGens + Q.numGens) → Monoid.Coprod P.Group Q.Group :=
    Fin.addCases (fun i => Monoid.Coprod.inl (P.ofGen i))
                 (fun j => Monoid.Coprod.inr (Q.ofGen j))
  let toFun : (P.coprod Q).Group →* Monoid.Coprod P.Group Q.Group :=
    (P.coprod Q).lift gmap (by
      intro r hr
      simp only [coprod, List.mem_append, List.mem_map] at hr
      rcases hr with ⟨r₁, hr₁, rfl⟩ | ⟨r₂, hr₂, rfl⟩
      · rw [freeGroup_mk_mapWord]
        have hcomp :
            (FreeGroup.lift gmap).comp (FreeGroup.map (Fin.castAdd Q.numGens)) =
            Monoid.Coprod.inl.comp (PresentedGroup.mk P.relSet) := by
          ext i
          simp [gmap, ofGen, PresentedGroup.of]
        change ((FreeGroup.lift gmap).comp (FreeGroup.map (Fin.castAdd Q.numGens)))
          (FreeGroup.mk r₁) = 1
        rw [hcomp, MonoidHom.comp_apply,
          show PresentedGroup.mk P.relSet (FreeGroup.mk r₁) = 1 from P.mkWord_eq_one_of_mem hr₁,
          map_one]
      · rw [freeGroup_mk_mapWord]
        have hcomp :
            (FreeGroup.lift gmap).comp (FreeGroup.map (Fin.natAdd P.numGens)) =
            Monoid.Coprod.inr.comp (PresentedGroup.mk Q.relSet) := by
          ext j
          simp [gmap, ofGen, PresentedGroup.of]
        change ((FreeGroup.lift gmap).comp (FreeGroup.map (Fin.natAdd P.numGens)))
          (FreeGroup.mk r₂) = 1
        rw [hcomp, MonoidHom.comp_apply,
          show PresentedGroup.mk Q.relSet (FreeGroup.mk r₂) = 1 from Q.mkWord_eq_one_of_mem hr₂,
          map_one])
  let invL : P.Group →* (P.coprod Q).Group :=
    P.lift (fun i => (P.coprod Q).ofGen (Fin.castAdd Q.numGens i)) fun r hr => by
      have h : FreeGroup.lift (fun i => (P.coprod Q).ofGen (Fin.castAdd Q.numGens i)) =
          (PresentedGroup.mk (P.coprod Q).relSet).comp (FreeGroup.map (Fin.castAdd Q.numGens)) := by
        ext i; rfl
      rw [h, MonoidHom.comp_apply, ← freeGroup_mk_mapWord]
      exact (P.coprod Q).mkWord_eq_one_of_mem (List.mem_append_left _ (List.mem_map_of_mem hr))
  let invR : Q.Group →* (P.coprod Q).Group :=
    Q.lift (fun j => (P.coprod Q).ofGen (Fin.natAdd P.numGens j)) fun r hr => by
      have h : FreeGroup.lift (fun j => (P.coprod Q).ofGen (Fin.natAdd P.numGens j)) =
          (PresentedGroup.mk (P.coprod Q).relSet).comp (FreeGroup.map (Fin.natAdd P.numGens)) := by
        ext j; rfl
      rw [h, MonoidHom.comp_apply, ← freeGroup_mk_mapWord]
      exact (P.coprod Q).mkWord_eq_one_of_mem (List.mem_append_right _ (List.mem_map_of_mem hr))
  let invFun : Monoid.Coprod P.Group Q.Group →* (P.coprod Q).Group :=
    Monoid.Coprod.lift invL invR
  refine MonoidHom.toMulEquiv toFun invFun ?_ ?_
  · apply FinPres.hom_ext
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro i₁
      change invFun (toFun ((P.coprod Q).ofGen (Fin.castAdd Q.numGens i₁))) = _
      simp [toFun, gmap, invFun, invL]
    · intro i₂
      change invFun (toFun ((P.coprod Q).ofGen (Fin.natAdd P.numGens i₂))) = _
      simp [toFun, gmap, invFun, invR]
  · apply Monoid.Coprod.hom_ext
    · apply FinPres.hom_ext
      intro i
      change toFun (invFun (Monoid.Coprod.inl (P.ofGen i))) = _
      simp [toFun, gmap, invFun, invL]
    · apply FinPres.hom_ext
      intro j
      change toFun (invFun (Monoid.Coprod.inr (Q.ofGen j))) = _
      simp [toFun, gmap, invFun, invR]

@[simp]
theorem coprodEquiv_ofGen_castAdd (P Q : FinPres) (i : Fin P.numGens) :
    coprodEquiv P Q ((P.coprod Q).ofGen (Fin.castAdd Q.numGens i)) =
      Monoid.Coprod.inl (P.ofGen i) := by
  simp [coprodEquiv]

@[simp]
theorem coprodEquiv_ofGen_natAdd (P Q : FinPres) (j : Fin Q.numGens) :
    coprodEquiv P Q ((P.coprod Q).ofGen (Fin.natAdd P.numGens j)) =
      Monoid.Coprod.inr (Q.ofGen j) := by
  simp [coprodEquiv]

@[simp]
theorem coprodEquiv_symm_inl_ofGen (P Q : FinPres) (i : Fin P.numGens) :
    (coprodEquiv P Q).symm (Monoid.Coprod.inl (P.ofGen i)) =
      (P.coprod Q).ofGen (Fin.castAdd Q.numGens i) := by
  rw [MulEquiv.symm_apply_eq, coprodEquiv_ofGen_castAdd]

@[simp]
theorem coprodEquiv_symm_inr_ofGen (P Q : FinPres) (j : Fin Q.numGens) :
    (coprodEquiv P Q).symm (Monoid.Coprod.inr (Q.ofGen j)) =
      (P.coprod Q).ofGen (Fin.natAdd P.numGens j) := by
  rw [MulEquiv.symm_apply_eq, coprodEquiv_ofGen_natAdd]

/-! ### Primcodable structure on `FinPres` -/

/-- Raw encoding of a finite presentation as `(numGens, relators)` with natural-number indices. -/
def toRaw (P : FinPres) : ℕ × List (List (ℕ × Bool)) :=
  (P.numGens, P.relators.map (mapWord Fin.val))

/-- Validity predicate for a raw presentation: all generator indices are `< numGens`. -/
def validRaw (p : ℕ × List (List (ℕ × Bool))) : Bool :=
  p.2.all fun r => r.all fun l => decide (l.1 < p.1)

theorem validRaw_iff {p : ℕ × List (List (ℕ × Bool))} :
    validRaw p = true ↔ ∀ r ∈ p.2, ∀ l ∈ r, l.1 < p.1 := by
  simp [validRaw, List.all_eq_true]

theorem validRaw_toRaw (P : FinPres) : validRaw P.toRaw = true := by
  rw [validRaw_iff]
  intro r hr l hl
  simp only [toRaw, List.mem_map, mapWord] at hr
  rcases hr with ⟨r', _, rfl⟩
  simp only [List.mem_map] at hl
  rcases hl with ⟨⟨i, b⟩, _, rfl⟩
  exact i.isLt

/-- Construct a `FinPres` from a validated raw presentation. -/
def ofValidRaw (p : { p : ℕ × List (List (ℕ × Bool)) // validRaw p = true }) : FinPres where
  numGens := p.1.1
  relators :=
    p.1.2.attach.map fun ⟨r, hr⟩ =>
      r.attach.map fun ⟨⟨k, b⟩, hl⟩ =>
        (⟨k, validRaw_iff.mp p.2 r hr (k, b) hl⟩, b)

/-- Equivalence between `FinPres` and the subtype of valid raw presentations. -/
def equivValidRaw : FinPres ≃ { p : ℕ × List (List (ℕ × Bool)) // validRaw p = true } where
  toFun P := ⟨P.toRaw, validRaw_toRaw P⟩
  invFun := ofValidRaw
  left_inv P := by
    rcases P with ⟨n, rs⟩
    simp only [ofValidRaw, toRaw]
    congr 1
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [List.getElem_map]
      apply List.ext_getElem
      · simp [mapWord]
      · intro j hj1 hj2
        simp [mapWord]
  right_inv p := by
    rcases p with ⟨⟨n, rs⟩, hp⟩
    ext1
    simp only [ofValidRaw, toRaw]
    congr 1
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [List.getElem_map]
      apply List.ext_getElem
      · simp [mapWord]
      · intro j hj1 hj2
        simp [mapWord]

theorem primrec_validRaw : Primrec validRaw := by
  have hinner : Primrec₂ (fun (n : ℕ) (r : List (ℕ × Bool)) =>
      r.all fun l => decide (l.1 < n)) := by
    have h := Primrec.list_foldr (α := ℕ × List (ℕ × Bool)) (β := ℕ × Bool) (σ := Bool)
      Primrec.snd (Primrec.const true)
      (Primrec.to₂ (Primrec.and.comp
        (Primrec.nat_lt.decide.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
          (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp Primrec.snd)))
    refine h.of_eq fun ⟨n, r⟩ => ?_
    induction r with
    | nil => rfl
    | cons l r ih =>
      simp [List.all_cons, ih]
  have houter := Primrec.list_foldr (α := ℕ × List (List (ℕ × Bool))) (β := List (ℕ × Bool))
    (σ := Bool) Primrec.snd (Primrec.const true)
    (Primrec.to₂ (Primrec.and.comp
      (hinner.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)))
  refine houter.of_eq fun ⟨n, rs⟩ => ?_
  simp only [validRaw]
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp [List.all_cons, ih]

theorem primrecPred_validRaw : PrimrecPred (fun p => validRaw p = true) :=
  Primrec.eq.comp primrec_validRaw (Primrec.const true)

@[instance_reducible]
def validRawPrimcodable :
    Primcodable { p : ℕ × List (List (ℕ × Bool)) // validRaw p = true } :=
  Primcodable.subtype primrecPred_validRaw

instance : Primcodable FinPres :=
  letI := validRawPrimcodable
  Primcodable.ofEquiv { p : ℕ × List (List (ℕ × Bool)) // validRaw p = true } equivValidRaw

/-- A function into `FinPres` is primitive recursive iff its raw representation is. -/
theorem primrec_iff {α : Type*} [Primcodable α] {f : α → FinPres} :
    Primrec f ↔ Primrec (fun a => (f a).toRaw) := by
  let _ := validRawPrimcodable
  have h1 : Primrec f ↔ Primrec (fun a => equivValidRaw (f a)) :=
    (Primrec.of_equiv_iff equivValidRaw).symm
  have h2 : Primrec (fun a => equivValidRaw (f a)) ↔ Primrec (fun a => (equivValidRaw (f a)).1) :=
    (Primrec.subtype_val_iff (hp := primrecPred_validRaw)).symm
  exact h1.trans h2

theorem primrec_toRaw : Primrec toRaw :=
  primrec_iff.mp Primrec.id

theorem toRaw_coprod (P Q : FinPres) :
    (P.coprod Q).toRaw =
      (P.numGens + Q.numGens,
        P.toRaw.2 ++ Q.toRaw.2.map (List.map fun l => (P.numGens + l.1, l.2))) := by
  simp only [coprod, toRaw, List.map_append, List.map_map]
  congr 1
  congr 1
  · apply List.map_congr_left
    intro r _
    simp [mapWord]
  · apply List.map_congr_left
    intro r _
    simp [mapWord]

theorem primrec_coprod : Primrec₂ coprod := by
  rw [Primrec₂, primrec_iff]
  have hf : Primrec (fun p : FinPres × FinPres => p.1.toRaw) := primrec_toRaw.comp Primrec.fst
  have hg : Primrec (fun p : FinPres × FinPres => p.2.toRaw) := primrec_toRaw.comp Primrec.snd
  have hnum : Primrec (fun p : FinPres × FinPres => p.1.toRaw.1 + p.2.toRaw.1) :=
    Primrec.nat_add.comp (Primrec.fst.comp hf) (Primrec.fst.comp hg)
  have hshiftWord : Primrec₂ (fun (n : ℕ) (r : List (ℕ × Bool)) =>
      r.map fun l => (n + l.1, l.2)) :=
    Primrec.list_map Primrec.snd
      (Primrec.to₂ (Primrec.pair
        (Primrec.nat_add.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd)))
  have hshiftList : Primrec (fun p : FinPres × FinPres =>
      p.2.toRaw.2.map (List.map fun l => (p.1.toRaw.1 + l.1, l.2))) :=
    Primrec.list_map (Primrec.snd.comp hg)
      (Primrec.to₂ (hshiftWord.comp (Primrec.fst.comp (hf.comp Primrec.fst)) Primrec.snd))
  have hrels : Primrec (fun p : FinPres × FinPres =>
      p.1.toRaw.2 ++ p.2.toRaw.2.map (List.map fun l => (p.1.toRaw.1 + l.1, l.2))) :=
    Primrec.list_append.comp (Primrec.snd.comp hf) hshiftList
  exact (Primrec.pair hnum hrels).of_eq fun ⟨P, Q⟩ => (toRaw_coprod P Q).symm

end FinPres

/-! ### Primrec helpers for raw words and reductions -/

theorem primrec_wordInv {α : Type*} [Primcodable α] :
    Primrec (wordInv (α := α)) := by
  unfold wordInv
  exact Primrec.list_reverse.comp <|
    Primrec.list_map Primrec.id
      (Primrec.to₂ (Primrec.pair (Primrec.fst.comp Primrec.snd)
        (Primrec.not.comp (Primrec.snd.comp Primrec.snd))))

theorem primrec_wordPow {α : Type*} [Primcodable α] :
    Primrec₂ (wordPow (α := α)) := by
  have h := Primrec.nat_rec (α := List (α × Bool)) (β := List (α × Bool))
    (Primrec.const [])
    (Primrec.to₂ (Primrec.list_append.comp Primrec.fst (Primrec.snd.comp Primrec.snd)))
  refine h.of_eq fun w n => ?_
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [wordPow, ih]

theorem primrec_wordComm {α : Type*} [Primcodable α] :
    Primrec₂ (wordComm (α := α)) := by
  unfold wordComm
  exact Primrec.list_append.comp
    (Primrec.list_append.comp
      (Primrec.list_append.comp Primrec.fst Primrec.snd)
      (primrec_wordInv.comp Primrec.fst))
    (primrec_wordInv.comp Primrec.snd)

/-- Many-one reduction for `ComputablePred`. -/
theorem computablePred_of_reduction {α β : Type*} [Primcodable α] [Primcodable β]
    {p : α → Prop} {q : β → Prop} {f : α → β}
    (hf : Computable f) (hiff : ∀ a, p a ↔ q (f a)) (hq : ComputablePred q) :
    ComputablePred p := by
  obtain ⟨decq, hcomp⟩ := hq
  let _ : DecidablePred q := decq
  let decp : DecidablePred p := fun a => decidable_of_iff (q (f a)) (hiff a).symm
  refine ⟨decp, (hcomp.comp hf).of_eq fun a => ?_⟩
  change decide (q (f a)) = @decide (p a) (decp a)
  by_cases h : q (f a)
  · have hp : p a := (hiff a).mpr h
    simp [h, hp]
  · have hp : ¬ p a := mt (hiff a).mp h
    simp [h, hp]

/-- Contrapositive form of many-one reduction for undecidability. -/
theorem not_computablePred_of_reduction {α β : Type*} [Primcodable α] [Primcodable β]
    {p : α → Prop} {q : β → Prop} {f : α → β}
    (hf : Computable f) (hiff : ∀ a, p a ↔ q (f a)) (hp : ¬ ComputablePred p) :
    ¬ ComputablePred q :=
  fun hq => hp (computablePred_of_reduction hf hiff hq)

end Adian
