module

public import Mathlib.GroupTheory.HNNExtension
public import Mathlib.GroupTheory.Coprod.Basic

/-!
# Multi-Letter HNN Extensions and Amalgamated Free Product Embeddings

This file builds two key combinatorial group theory tools directly on top of Mathlib's
`HNNExtension` and `Monoid.Coprod`:

1. **Amalgamated Free Product Embedding (`AmalgamTarget`)**:
   Given groups `A`, `B`, subgroups `H₁ ≤ A`, `H₂ ≤ B`, and an isomorphism `θ : H₁ ≃* H₂`,
   we construct a group `E` (as a single HNN extension of `A ∗ B`) with injective homomorphisms
   `α : A →* E` and `β : B →* E` agreeing on `θ`.

2. **Multi-Letter HNN Extensions (`MultiHNN`)**:
   Given a base group `G` and a finite family of pairs of isomorphic subgroups `(A_i, B_i, φ_i)`,
   we construct the multi-letter HNN extension as iterated Mathlib `HNNExtension`s and prove
   **Multi-Letter Britton's Lemma** by induction on the number of stable letters.
-/

@[expose] public section

open Monoid Subgroup

namespace Adian

noncomputable section

/-- Subgroup isomorphism `H ≃* H.map f` induced by an injective homomorphism `f : G →* K`. -/
def subgroupMapEquiv {G K : Type*} [Group G] [Group K] (f : G →* K)
    (hf : Function.Injective f) (H : Subgroup G) : H ≃* H.map f :=
  let φ : H →* H.map f :=
    { toFun := fun x => ⟨f x, ⟨x, x.2, rfl⟩⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp }
  MulEquiv.ofBijective φ
    ⟨fun x y h => by
        ext
        exact hf (congrArg Subtype.val h),
     fun ⟨_, x, hx, hy⟩ => ⟨⟨x, hx⟩, by ext; exact hy⟩⟩

@[simp]
theorem subgroupMapEquiv_apply {G K : Type*} [Group G] [Group K] (f : G →* K)
    (hf : Function.Injective f) (H : Subgroup G) (x : H) :
    (subgroupMapEquiv f hf H x : K) = f x := rfl

@[simp]
theorem subgroupMapEquiv_symm_apply {G K : Type*} [Group G] [Group K] (f : G →* K)
    (hf : Function.Injective f) (H : Subgroup G) (x : H) :
    (subgroupMapEquiv f hf H).symm ⟨f x, ⟨x, x.2, rfl⟩⟩ = x :=
  (subgroupMapEquiv f hf H).symm_apply_apply x

/-! ### Part 1: Amalgamated Free Product Embedding via HNN Extension -/

section Amalgam

variable {A B : Type*} [Group A] [Group B]

/-- Lift an isomorphism `θ : H₁ ≃* H₂` between subgroups of `A` and `B` to an isomorphism
between `H₁.map inl` and `H₂.map inr` inside `A ∗ B`. -/
def amalgamSubgroupEquiv (H₁ : Subgroup A) (H₂ : Subgroup B) (θ : H₁ ≃* H₂) :
    H₁.map (Coprod.inl : A →* Coprod A B) ≃* H₂.map (Coprod.inr : B →* Coprod A B) :=
  ((subgroupMapEquiv (Coprod.inl : A →* Coprod A B) Coprod.inl_injective H₁).symm.trans θ).trans
    (subgroupMapEquiv (Coprod.inr : B →* Coprod A B) Coprod.inr_injective H₂)

/-- Target group witnessing the embedding of `A` and `B` into their amalgamated free product. -/
abbrev AmalgamTarget (H₁ : Subgroup A) (H₂ : Subgroup B) (θ : H₁ ≃* H₂) : Type _ :=
  HNNExtension (Coprod A B) (H₁.map Coprod.inl) (H₂.map Coprod.inr)
    (amalgamSubgroupEquiv H₁ H₂ θ)

/-- Left embedding `A →* AmalgamTarget H₁ H₂ θ`, given by `a ↦ t * of (inl a) * t⁻¹`. -/
def amalgamInl (H₁ : Subgroup A) (H₂ : Subgroup B) (θ : H₁ ≃* H₂) :
    A →* AmalgamTarget H₁ H₂ θ :=
  (MulAut.conj (HNNExtension.t (G := Coprod A B)
      (A := H₁.map Coprod.inl) (B := H₂.map Coprod.inr)
      (φ := amalgamSubgroupEquiv H₁ H₂ θ))).toMonoidHom.comp
    (HNNExtension.of.comp Coprod.inl)

/-- Right embedding `B →* AmalgamTarget H₁ H₂ θ`, given by `b ↦ of (inr b)`. -/
def amalgamInr (H₁ : Subgroup A) (H₂ : Subgroup B) (θ : H₁ ≃* H₂) :
    B →* AmalgamTarget H₁ H₂ θ :=
  HNNExtension.of.comp Coprod.inr

theorem amalgamInl_injective (H₁ : Subgroup A) (H₂ : Subgroup B) (θ : H₁ ≃* H₂) :
    Function.Injective (amalgamInl H₁ H₂ θ) := by
  have h1 : Function.Injective (HNNExtension.of (G := Coprod A B)
      (A := H₁.map Coprod.inl) (B := H₂.map Coprod.inr)
      (φ := amalgamSubgroupEquiv H₁ H₂ θ)) :=
    HNNExtension.of_injective (amalgamSubgroupEquiv H₁ H₂ θ)
  have h2 : Function.Injective (Coprod.inl : A →* Coprod A B) := Coprod.inl_injective
  have h3 : Function.Injective (MulAut.conj (HNNExtension.t (G := Coprod A B)
      (A := H₁.map Coprod.inl) (B := H₂.map Coprod.inr)
      (φ := amalgamSubgroupEquiv H₁ H₂ θ))) := MulEquiv.injective _
  exact h3.comp (h1.comp h2)

theorem amalgamInr_injective (H₁ : Subgroup A) (H₂ : Subgroup B) (θ : H₁ ≃* H₂) :
    Function.Injective (amalgamInr H₁ H₂ θ) := by
  have h1 : Function.Injective (HNNExtension.of (G := Coprod A B)
      (A := H₁.map Coprod.inl) (B := H₂.map Coprod.inr)
      (φ := amalgamSubgroupEquiv H₁ H₂ θ)) :=
    HNNExtension.of_injective (amalgamSubgroupEquiv H₁ H₂ θ)
  have h2 : Function.Injective (Coprod.inr : B →* Coprod A B) := Coprod.inr_injective
  exact h1.comp h2

theorem amalgam_comm (H₁ : Subgroup A) (H₂ : Subgroup B) (θ : H₁ ≃* H₂) (h : H₁) :
    amalgamInl H₁ H₂ θ h = amalgamInr H₁ H₂ θ (θ h) := by
  let x : H₁.map (Coprod.inl : A →* Coprod A B) := ⟨Coprod.inl (h : A), ⟨h, h.2, rfl⟩⟩
  have hx : (amalgamSubgroupEquiv H₁ H₂ θ x : Coprod A B) = Coprod.inr (θ h : B) := by
    simp [amalgamSubgroupEquiv, x]
  have heq := HNNExtension.equiv_eq_conj (φ := amalgamSubgroupEquiv H₁ H₂ θ) x
  rw [hx] at heq
  simpa [amalgamInl, amalgamInr, MulAut.conj_apply, x] using heq.symm

end Amalgam

/-! ### Part 2: Multi-Letter HNN Extensions and Multi-Letter Britton's Lemma -/

/-- Data for a single HNN stable letter over a base group `G`: two subgroups `A`, `B` and an
isomorphism `iso : A ≃* B`. The relation in the HNN extension is `t * of a = of (iso a) * t`. -/
structure HNNData (G : Type u) [Group G] where
  /-- Domain subgroup `A ≤ G`. -/
  A : Subgroup G
  /-- Codomain subgroup `B ≤ G`. -/
  B : Subgroup G
  /-- Isomorphism `A ≃* B`. -/
  iso : A ≃* B

/-- The subgroup associated to sign `u : ℤˣ` (`1 ↦ A`, `-1 ↦ B`). -/
def HNNData.toSubgroup {G : Type u} [Group G] (d : HNNData G) (u : ℤˣ) : Subgroup G :=
  HNNExtension.toSubgroup d.A d.B u

/-- The subgroup isomorphism associated to sign `u : ℤˣ` (`1 ↦ iso`, `-1 ↦ iso.symm`). -/
def HNNData.toSubgroupEquiv {G : Type u} [Group G] (d : HNNData G) (u : ℤˣ) :
    d.toSubgroup u ≃* d.toSubgroup (-u) :=
  HNNExtension.toSubgroupEquiv d.iso u

/-- Bundled intermediate object in the iterated HNN extension construction. -/
structure MultiHNNObj (G : Type u) [Group G] : Type (u + 1) where
  carrier : Type u
  instGroup : Group carrier
  of : G →* carrier
  of_injective : Function.Injective of

section MultiHNNDef

universe u
variable {G : Type u} [Group G]

/-- Map an `HNNData G` along an injective homomorphism `f : G →* H`. -/
def HNNData.mapInjective {H : Type*} [Group H] (f : G →* H)
    (hf : Function.Injective f) (d : HNNData G) : HNNData H where
  A := d.A.map f
  B := d.B.map f
  iso :=
    ((subgroupMapEquiv f hf d.A).symm.trans d.iso).trans (subgroupMapEquiv f hf d.B)

theorem HNNData.mapInjective_iso_apply {H : Type*} [Group H] (f : G →* H)
    (hf : Function.Injective f) (d : HNNData G) (a : d.A) :
    ((d.mapInjective f hf).iso ⟨f a, ⟨a, a.2, rfl⟩⟩ : H) = f (d.iso a) := by
  change (subgroupMapEquiv f hf d.B
    (d.iso ((subgroupMapEquiv f hf d.A).symm ⟨f a, ⟨a, a.2, rfl⟩⟩)) : H) = f (d.iso a)
  rw [subgroupMapEquiv_apply, subgroupMapEquiv_symm_apply]

/-- Recursive construction of the `n`-letter HNN extension over `G`. -/
def multiHNNRec : ∀ (n : ℕ), (Fin n → HNNData G) → MultiHNNObj G
  | 0, _ =>
    { carrier := G
      instGroup := inferInstance
      of := MonoidHom.id G
      of_injective := Function.injective_id }
  | n + 1, S =>
    let prev := multiHNNRec n (fun i => S i.castSucc)
    letI : Group prev.carrier := prev.instGroup
    let d := (S (Fin.last n)).mapInjective prev.of prev.of_injective
    { carrier := HNNExtension prev.carrier d.A d.B d.iso
      instGroup := inferInstance
      of := HNNExtension.of.comp prev.of
      of_injective := (HNNExtension.of_injective d.iso).comp prev.of_injective }

/-- The multi-letter HNN extension of `G` with respect to `S : Fin n → HNNData G`. -/
abbrev MultiHNN {n : ℕ} (S : Fin n → HNNData G) : Type u :=
  (multiHNNRec n S).carrier

instance instGroupMultiHNN {n : ℕ} (S : Fin n → HNNData G) : Group (MultiHNN S) :=
  (multiHNNRec n S).instGroup

namespace MultiHNN

/-- Canonical embedding of the base group `G` into `MultiHNN S`. -/
def of {n : ℕ} (S : Fin n → HNNData G) : G →* MultiHNN S :=
  (multiHNNRec n S).of

theorem of_injective {n : ℕ} (S : Fin n → HNNData G) : Function.Injective (of S) :=
  (multiHNNRec n S).of_injective

/-- The HNN data for the last stable letter `Fin.last n` lifted into `MultiHNN (S ∘ castSucc)`. -/
abbrev lastData {n : ℕ} (S : Fin (n + 1) → HNNData G) :
    HNNData (MultiHNN (fun i : Fin n => S i.castSucc)) :=
  (S (Fin.last n)).mapInjective (of fun i : Fin n => S i.castSucc)
    (of_injective fun i : Fin n => S i.castSucc)

/-- Step inclusion from the `n`-letter extension into the `(n + 1)`-letter extension. -/
def stepOf {n : ℕ} (S : Fin (n + 1) → HNNData G) :
    MultiHNN (fun i : Fin n => S i.castSucc) →* MultiHNN S :=
  HNNExtension.of (φ := (lastData S).iso)

theorem stepOf_injective {n : ℕ} (S : Fin (n + 1) → HNNData G) :
    Function.Injective (stepOf S) :=
  HNNExtension.of_injective (lastData S).iso

@[simp]
theorem stepOf_of {n : ℕ} (S : Fin (n + 1) → HNNData G) (g : G) :
    stepOf S (of (fun i : Fin n => S i.castSucc) g) = of S g := rfl

/-- The `i`-th stable letter in `MultiHNN S`. -/
def t : ∀ {n : ℕ} (S : Fin n → HNNData G), Fin n → MultiHNN S
  | 0, _, i => i.elim0
  | _ + 1, S, i =>
    Fin.lastCases (HNNExtension.t (φ := (lastData S).iso))
      (fun j => stepOf S (t (fun k => S k.castSucc) j)) i

@[simp]
theorem t_last {n : ℕ} (S : Fin (n + 1) → HNNData G) :
    t S (Fin.last n) = HNNExtension.t (φ := (lastData S).iso) :=
  Fin.lastCases_last

@[simp]
theorem t_castSucc {n : ℕ} (S : Fin (n + 1) → HNNData G) (j : Fin n) :
    t S j.castSucc = stepOf S (t (fun k => S k.castSucc) j) :=
  Fin.lastCases_castSucc j

theorem t_mul_of : ∀ {n : ℕ} (S : Fin n → HNNData G) (i : Fin n) (a : (S i).A),
    t S i * of S a = of S ((S i).iso a) * t S i
  | 0, _, i, _ => i.elim0
  | n + 1, S, i, a => by
    refine Fin.lastCases ?_ ?_ i a
    · intro a
      let S' : Fin n → HNNData G := fun k => S k.castSucc
      let a' : (lastData S).A := ⟨of S' a, ⟨a, a.2, rfl⟩⟩
      have h := HNNExtension.t_mul_of (φ := (lastData S).iso) a'
      have hval : ((lastData S).iso a' : MultiHNN S') = of S' ((S (Fin.last n)).iso a) :=
        HNNData.mapInjective_iso_apply (of S') (of_injective S') (S (Fin.last n)) a
      rw [hval] at h
      rw [t_last, ← stepOf_of S a, ← stepOf_of S ((S (Fin.last n)).iso a)]
      exact h
    · intro j a
      rw [t_castSucc, ← stepOf_of S a, ← stepOf_of S ((S j.castSucc).iso a), ← map_mul, ← map_mul]
      exact congrArg (stepOf S) (t_mul_of (fun k => S k.castSucc) j a)

theorem equiv_eq_conj {n : ℕ} (S : Fin n → HNNData G) (i : Fin n) (a : (S i).A) :
    of S ((S i).iso a) = t S i * of S a * (t S i)⁻¹ := by
  rw [t_mul_of]; simp

theorem equiv_symm_eq_conj {n : ℕ} (S : Fin n → HNNData G) (i : Fin n) (b : (S i).B) :
    of S ((S i).iso.symm b) = (t S i)⁻¹ * of S b * t S i := by
  have h := t_mul_of S i ((S i).iso.symm b)
  simp only [MulEquiv.apply_symm_apply] at h
  rw [mul_assoc, ← h, inv_mul_cancel_left]

theorem toSubgroupEquiv_eq_conj {n : ℕ} (S : Fin n → HNNData G) (i : Fin n) (u : ℤˣ)
    (a : (S i).toSubgroup u) :
    of S ((S i).toSubgroupEquiv u a) =
      t S i ^ (u : ℤ) * of S a * (t S i ^ (u : ℤ))⁻¹ := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · change of S ((S i).iso a) = t S i ^ (1 : ℤ) * of S a * (t S i ^ (1 : ℤ))⁻¹
    simpa using equiv_eq_conj S i a
  · change of S ((S i).iso.symm a) = t S i ^ (-1 : ℤ) * of S a * (t S i ^ (-1 : ℤ))⁻¹
    simpa using equiv_symm_eq_conj S i a

/-- Auxiliary bundled lift returning the homomorphism along with its equations on `of S` and `t S`. -/
def liftAux {H : Type*} [Group H] :
    ∀ {n : ℕ} (S : Fin n → HNNData G) (f : G →* H) (xs : Fin n → H)
      (_ : ∀ i (a : (S i).A), xs i * f a = f ((S i).iso a) * xs i),
      { φ : MultiHNN S →* H // (∀ g, φ (of S g) = f g) ∧ (∀ i, φ (t S i) = xs i) }
  | 0, _, f, _, _ => ⟨f, fun _ => rfl, fun i => i.elim0⟩
  | n + 1, S, f, xs, hxs =>
    let S' : Fin n → HNNData G := fun k => S k.castSucc
    let prev := liftAux S' f (fun k => xs k.castSucc) (fun k a => hxs k.castSucc a)
    let hx : ∀ a : (lastData S).A,
        xs (Fin.last n) * prev.1 a = prev.1 ((lastData S).iso a) * xs (Fin.last n) := by
      rintro ⟨_, ⟨a, ha, rfl⟩⟩
      have hval : ((lastData S).iso ⟨of S' a, ⟨a, ha, rfl⟩⟩ : MultiHNN S') =
          of S' ((S (Fin.last n)).iso ⟨a, ha⟩) :=
        HNNData.mapInjective_iso_apply (of S') (of_injective S') (S (Fin.last n)) ⟨a, ha⟩
      rw [hval, prev.2.1, prev.2.1]
      exact hxs (Fin.last n) ⟨a, ha⟩
    let φ : MultiHNN S →* H := HNNExtension.lift (φ := (lastData S).iso) prev.1 (xs (Fin.last n)) hx
    ⟨φ,
      fun g => by
        change HNNExtension.lift (φ := (lastData S).iso) prev.1 (xs (Fin.last n)) hx
          (HNNExtension.of (φ := (lastData S).iso) (of S' g)) = f g
        rw [HNNExtension.lift_of, prev.2.1],
      fun i => by
        refine Fin.lastCases ?_ ?_ i
        · rw [t_last]
          exact HNNExtension.lift_t prev.1 (xs (Fin.last n)) hx
        · intro j
          rw [t_castSucc]
          change HNNExtension.lift (φ := (lastData S).iso) prev.1 (xs (Fin.last n)) hx
            (HNNExtension.of (φ := (lastData S).iso) (t S' j)) = xs j.castSucc
          rw [HNNExtension.lift_of, prev.2.2]⟩

/-- Universal property of `MultiHNN`: lift a homomorphism `f : G →* H` together with images
`xs : Fin n → H` of the stable letters satisfying the conjugation relations. -/
def lift {H : Type*} [Group H] {n : ℕ} (S : Fin n → HNNData G) (f : G →* H) (xs : Fin n → H)
    (hxs : ∀ i (a : (S i).A), xs i * f a = f ((S i).iso a) * xs i) :
    MultiHNN S →* H :=
  (liftAux S f xs hxs).1

@[simp]
theorem lift_of {H : Type*} [Group H] {n : ℕ} (S : Fin n → HNNData G)
    (f : G →* H) (xs : Fin n → H)
    (hxs : ∀ i (a : (S i).A), xs i * f a = f ((S i).iso a) * xs i) (g : G) :
    lift S f xs hxs (of S g) = f g :=
  (liftAux S f xs hxs).2.1 g

@[simp]
theorem lift_t {H : Type*} [Group H] {n : ℕ} (S : Fin n → HNNData G) (f : G →* H) (xs : Fin n → H)
    (hxs : ∀ i (a : (S i).A), xs i * f a = f ((S i).iso a) * xs i) (i : Fin n) :
    lift S f xs hxs (t S i) = xs i :=
  (liftAux S f xs hxs).2.2 i

theorem hom_ext {H : Type*} [Group H] :
    ∀ {n : ℕ} {S : Fin n → HNNData G} {φ ψ : MultiHNN S →* H},
      φ.comp (of S) = ψ.comp (of S) → (∀ i : Fin n, φ (t S i) = ψ (t S i)) → φ = ψ
  | 0, _, _, _, hof, _ => hof
  | n + 1, S, φ, ψ, hof, ht => by
    apply HNNExtension.hom_ext (φ := (lastData S).iso)
    · apply hom_ext (S := fun k => S k.castSucc)
      · exact hof
      · intro j
        change φ (stepOf S (t (fun k => S k.castSucc) j)) =
          ψ (stepOf S (t (fun k => S k.castSucc) j))
        rw [← t_castSucc]
        exact ht j.castSucc
    · rw [← t_last]
      exact ht (Fin.last n)

/-! ### Multi-Letter Britton's Lemma -/

/-- Product of a list of `(index, sign, base element)` letters in `MultiHNN S`. -/
def wordProd {n : ℕ} (S : Fin n → HNNData G) (head : G)
    (l : List (Fin n × ℤˣ × G)) : MultiHNN S :=
  of S head * (l.map fun x => t S x.1 ^ (x.2.1 : ℤ) * of S x.2.2).prod

/-- A list of stable-letter segments has no pinch if no two adjacent entries share the same
stable letter index `i` with opposite signs and intervening base element in `(S i).toSubgroup u`. -/
def NoPinch {n : ℕ} (S : Fin n → HNNData G) (l : List (Fin n × ℤˣ × G)) : Prop :=
  l.IsChain fun a b => a.1 = b.1 → a.2.2 ∈ (S a.1).toSubgroup a.2.1 → a.2.1 = b.2.1

/-- Split a list of `(Fin (n + 1) × ℤˣ × G)` segments at every occurrence of `Fin.last n`.
Returns `(prefixSegments, rest)` where `prefixSegments` uses only indices `< n`, and each entry of
`rest` is `(u, segs)` representing `t_{last}^u * (prod of segs)`. -/
def splitLast {n : ℕ} :
    List (Fin (n + 1) × ℤˣ × G) →
      List (Fin n × ℤˣ × G) × List (ℤˣ × G × List (Fin n × ℤˣ × G))
  | [] => ([], [])
  | (i, u, g) :: rest =>
    let (pre, tail) := splitLast rest
    Fin.lastCases
      ([], (u, g, pre) :: tail)
      (fun j => ((j, u, g) :: pre, tail))
      i

theorem splitLast_noPinch {n : ℕ} (S : Fin (n + 1) → HNNData G)
    (l : List (Fin (n + 1) × ℤˣ × G)) (hnp : NoPinch S l) :
    NoPinch (fun j : Fin n => S j.castSucc) (splitLast l).1 ∧
    (∀ x ∈ (splitLast l).2, NoPinch (fun j : Fin n => S j.castSucc) x.2.2) ∧
    (splitLast l).2.IsChain (fun a b =>
      a.2.2 = [] → a.2.1 ∈ (S (Fin.last n)).toSubgroup a.1 → a.1 = b.1) := by
  induction l with
  | nil =>
    exact ⟨List.isChain_nil, by simp [splitLast], List.isChain_nil⟩
  | cons a rest ih =>
    rcases a with ⟨i, u, g⟩
    have hrest : NoPinch S rest := hnp.tail
    obtain ⟨hpre, hall, hch⟩ := ih hrest
    refine Fin.lastCases ?_ ?_ i hnp
    · intro hnp
      simp only [splitLast, Fin.lastCases_last]
      refine ⟨List.isChain_nil, ?_, ?_⟩
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hpre
        · exact hall x hx
      · refine List.isChain_cons.2 ⟨?_, hch⟩
        intro b hb hpre_nil hgmem
        cases rest with
        | nil => simp [splitLast] at hb
        | cons c rest' =>
          rcases c with ⟨ic, uc, gc⟩
          have hc_eq : ic = Fin.last n ∧ uc = b.1 := by
            revert hb hpre_nil
            refine Fin.lastCases ?_ ?_ ic
            · simp only [splitLast, Fin.lastCases_last, List.head?_cons, Option.mem_def,
                Option.some.injEq, true_and]
              rintro rfl _
              rfl
            · intro j
              simp [splitLast]
          have hlink := (List.isChain_cons_cons.1 hnp).1
          exact (hlink hc_eq.1.symm hgmem).trans hc_eq.2
    · intro j hnp
      simp only [splitLast, Fin.lastCases_castSucc]
      refine ⟨?_, hall, hch⟩
      refine List.isChain_cons.2 ⟨?_, hpre⟩
      intro b hb hij hgmem
      cases rest with
      | nil => simp [splitLast] at hb
      | cons c rest' =>
        rcases c with ⟨ic, uc, gc⟩
        have hc_eq : ic = b.1.castSucc ∧ uc = b.2.1 := by
          revert hb
          refine Fin.lastCases ?_ ?_ ic
          · simp [splitLast]
          · intro jc
            simp only [splitLast, Fin.lastCases_castSucc, List.head?_cons, Option.mem_def,
              Option.some.injEq]
            rintro rfl
            exact ⟨rfl, rfl⟩
        have hlink := (List.isChain_cons_cons.1 hnp).1
        dsimp at hij hgmem
        have hcast : j.castSucc = ic := by rw [hc_eq.1, hij]
        exact (hlink hcast hgmem).trans hc_eq.2

theorem splitLast_prod {n : ℕ} (S : Fin (n + 1) → HNNData G) (head : G)
    (l : List (Fin (n + 1) × ℤˣ × G)) :
    let S' : Fin n → HNNData G := fun j => S j.castSucc
    let (pre, tail) := splitLast l
    wordProd S head l =
      stepOf S (wordProd S' head pre) *
        (tail.map fun x =>
          t S (Fin.last n) ^ (x.1 : ℤ) * stepOf S (wordProd S' x.2.1 x.2.2)).prod := by
  induction l generalizing head with
  | nil =>
    simp [splitLast, wordProd]
  | cons a rest ih =>
    rcases a with ⟨i, u, g⟩
    have ih_g := ih g
    dsimp only at ih_g ⊢
    refine Fin.lastCases ?_ ?_ i
    · simp only [splitLast, Fin.lastCases_last, wordProd, List.map_cons, List.prod_cons,
        List.map_nil, List.prod_nil, mul_one, stepOf_of]
      simp only [wordProd] at ih_g
      calc
        of S head * (t S (Fin.last n) ^ (u : ℤ) * of S g *
            (rest.map fun x => t S x.1 ^ (x.2.1 : ℤ) * of S x.2.2).prod)
            = of S head * (t S (Fin.last n) ^ (u : ℤ) *
              (of S g * (rest.map fun x => t S x.1 ^ (x.2.1 : ℤ) * of S x.2.2).prod)) := by
              simp [mul_assoc]
        _ = of S head * (t S (Fin.last n) ^ (u : ℤ) *
              (stepOf S (of (fun j => S j.castSucc) g *
                  ((splitLast rest).1.map fun x =>
                    t (fun j => S j.castSucc) x.1 ^ (x.2.1 : ℤ) *
                      of (fun j => S j.castSucc) x.2.2).prod) *
                ((splitLast rest).2.map fun x =>
                  t S (Fin.last n) ^ (x.1 : ℤ) *
                    stepOf S (of (fun j => S j.castSucc) x.2.1 *
                      (x.2.2.map fun x =>
                        t (fun j => S j.castSucc) x.1 ^ (x.2.1 : ℤ) *
                          of (fun j => S j.castSucc) x.2.2).prod)).prod)) := by
              rw [ih_g]
        _ = _ := by simp [mul_assoc]
    · intro j
      simp only [splitLast, Fin.lastCases_castSucc, wordProd, List.map_cons, List.prod_cons]
      simp only [wordProd] at ih_g
      calc
        of S head * (t S j.castSucc ^ (u : ℤ) * of S g *
            (rest.map fun x => t S x.1 ^ (x.2.1 : ℤ) * of S x.2.2).prod)
            = of S head * (t S j.castSucc ^ (u : ℤ) *
              (of S g * (rest.map fun x => t S x.1 ^ (x.2.1 : ℤ) * of S x.2.2).prod)) := by
              simp [mul_assoc]
        _ = of S head * (t S j.castSucc ^ (u : ℤ) *
              (stepOf S (of (fun j => S j.castSucc) g *
                  ((splitLast rest).1.map fun x =>
                    t (fun j => S j.castSucc) x.1 ^ (x.2.1 : ℤ) *
                      of (fun j => S j.castSucc) x.2.2).prod) *
                ((splitLast rest).2.map fun x =>
                  t S (Fin.last n) ^ (x.1 : ℤ) *
                    stepOf S (of (fun j => S j.castSucc) x.2.1 *
                      (x.2.2.map fun x =>
                        t (fun j => S j.castSucc) x.1 ^ (x.2.1 : ℤ) *
                          of (fun j => S j.castSucc) x.2.2).prod)).prod)) := by
              rw [ih_g]
        _ = _ := by
              simp only [t_castSucc, ← stepOf_of, map_mul, map_zpow, mul_assoc]

/-- **Multi-Letter Britton's Lemma**: If a word in `MultiHNN S` contains at least one stable letter
and has no pinch, then it does not lie in the image of the base group `G`. -/
theorem not_mem_of_range_of_noPinch :
    ∀ {n : ℕ} (S : Fin n → HNNData G) (head : G) (l : List (Fin n × ℤˣ × G)),
      l ≠ [] → NoPinch S l → wordProd S head l ∉ (of S).range
  | 0, _, _, l, hne, _ => by
    cases l with
    | nil => exact (hne rfl).elim
    | cons a _ => exact a.1.elim0
  | n + 1, S, head, l, hne, hnp => by
    let S' : Fin n → HNNData G := fun j => S j.castSucc
    have hsplit := splitLast_noPinch S l hnp
    have hprod := splitLast_prod S head l
    rcases hsp : splitLast l with ⟨pre, tail⟩
    rw [hsp] at hsplit hprod
    obtain ⟨hpre_np, htail_np, htail_ch⟩ := hsplit
    cases tail with
    | nil =>
      have hpre_ne : pre ≠ [] := by
        intro hnil
        cases l with
        | nil => exact hne rfl
        | cons a rest =>
          rcases a with ⟨i, u, g⟩
          revert hsp
          refine Fin.lastCases ?_ ?_ i <;> simp [splitLast, hnil]
      intro hmem
      rcases hmem with ⟨g₀, hg₀⟩
      rw [hprod, List.map_nil, List.prod_nil, mul_one, ← stepOf_of S g₀] at hg₀
      have hpre_eq : wordProd S' head pre = of S' g₀ := stepOf_injective S hg₀.symm
      exact not_mem_of_range_of_noPinch S' head pre hpre_ne hpre_np ⟨g₀, hpre_eq.symm⟩
    | cons first tail' =>
      intro hmem
      rcases hmem with ⟨g₀, hg₀⟩
      have hsub : ∀ (u : ℤˣ) (x : MultiHNN S'),
          x ∈ HNNExtension.toSubgroup (lastData S).A (lastData S).B u ↔
            ∃ g ∈ (S (Fin.last n)).toSubgroup u, of S' g = x := by
        intro u x
        rcases Int.units_eq_one_or u with rfl | rfl <;>
          simp [HNNExtension.toSubgroup, HNNData.toSubgroup, lastData, HNNData.mapInjective, S']
      let rw_list : List (ℤˣ × MultiHNN S') :=
        (first :: tail').map fun x => (x.1, wordProd S' x.2.1 x.2.2)
      have hchain : rw_list.IsChain (fun a b =>
          a.2 ∈ HNNExtension.toSubgroup (lastData S).A (lastData S).B a.1 → a.1 = b.1) := by
        rw [List.isChain_map]
        have hch_all : ∀ (xs : List (ℤˣ × G × List (Fin n × ℤˣ × G))),
            (∀ x ∈ xs, NoPinch S' x.2.2) →
            xs.IsChain (fun a b =>
              a.2.2 = [] → a.2.1 ∈ (S (Fin.last n)).toSubgroup a.1 → a.1 = b.1) →
            xs.IsChain (fun a b =>
              wordProd S' a.2.1 a.2.2 ∈
                HNNExtension.toSubgroup (lastData S).A (lastData S).B a.1 → a.1 = b.1) := by
          intro xs hall hch
          induction xs with
          | nil => exact List.isChain_nil
          | cons a xs ih =>
            cases xs with
            | nil => exact List.isChain_singleton _
            | cons b xs =>
              rw [List.isChain_cons_cons] at hch ⊢
              refine ⟨?_, ih (fun x hx => hall x (List.mem_cons_of_mem _ hx)) hch.2⟩
              intro hmem_sub
              rw [hsub] at hmem_sub
              rcases hmem_sub with ⟨g', hg'_mem, hg'_eq⟩
              have ha_nil : a.2.2 = [] := by
                by_contra hne_a
                exact not_mem_of_range_of_noPinch S' a.2.1 a.2.2 hne_a
                  (hall a List.mem_cons_self) ⟨g', hg'_eq⟩
              have hg_eq : a.2.1 = g' := by
                apply of_injective S'
                simpa [wordProd, ha_nil] using hg'_eq.symm
              exact hch.1 ha_nil (hg_eq ▸ hg'_mem)
        exact hch_all (first :: tail') htail_np htail_ch
      let rw_word : HNNExtension.NormalWord.ReducedWord (MultiHNN S') (lastData S).A (lastData S).B :=
        { head := wordProd S' head pre
          toList := rw_list
          chain := hchain }
      have hrw_prod : rw_word.prod (lastData S).iso = wordProd S head l := by
        rw [hprod]
        simp only [HNNExtension.NormalWord.ReducedWord.prod, rw_word, rw_list, List.map_map, t_last]
        rfl
      have hmem_step : rw_word.prod (lastData S).iso ∈
          (HNNExtension.of (φ := (lastData S).iso)).range := by
        rw [hrw_prod, ← hg₀]
        exact ⟨of S' g₀, rfl⟩
      have hnil := HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range (lastData S).iso
        rw_word hmem_step
      simp [rw_word, rw_list] at hnil

/-- Pinch extraction lemma: if a nonempty word in `MultiHNN S` evaluates into the base group `G`,
then it contains a pinch `(i, u, g)` immediately followed by `(i, -u, g')` with
`g ∈ (S i).toSubgroup u`. -/
theorem exists_pinch_of_mem_of_range {n : ℕ} (S : Fin n → HNNData G) (head : G)
    (l : List (Fin n × ℤˣ × G)) (hne : l ≠ []) (hmem : wordProd S head l ∈ (of S).range) :
    ∃ (l₁ l₂ : List (Fin n × ℤˣ × G)) (i : Fin n) (u : ℤˣ) (g g' : G),
      l = l₁ ++ (i, u, g) :: (i, -u, g') :: l₂ ∧ g ∈ (S i).toSubgroup u := by
  have hnotnp : ¬ NoPinch S l := fun hnp =>
    not_mem_of_range_of_noPinch S head l hne hnp hmem
  clear hmem hne
  induction l with
  | nil => exact (hnotnp List.isChain_nil).elim
  | cons a rest ih =>
    cases rest with
    | nil => exact (hnotnp (List.isChain_singleton a)).elim
    | cons b rest' =>
      rw [NoPinch, List.isChain_cons_cons] at hnotnp
      by_cases h1 : a.1 = b.1 → a.2.2 ∈ (S a.1).toSubgroup a.2.1 → a.2.1 = b.2.1
      · have h2 : ¬ NoPinch S (b :: rest') := fun h => hnotnp ⟨h1, h⟩
        obtain ⟨l₁, l₂, i, u, g, g', heq, hg⟩ := ih h2
        exact ⟨a :: l₁, l₂, i, u, g, g', by simp [heq], hg⟩
      · push Not at h1
        obtain ⟨hi, hg, hne_u⟩ := h1
        have hu : b.2.1 = -a.2.1 := by
          rcases Int.units_eq_one_or a.2.1 with ha | ha <;>
          rcases Int.units_eq_one_or b.2.1 with hb | hb <;> simp_all
        refine ⟨[], rest', a.1, a.2.1, a.2.2, b.2.2, ?_, hg⟩
        rcases a with ⟨i₁, u₁, g₁⟩
        rcases b with ⟨i₂, u₂, g₂⟩
        dsimp at hi hu
        subst hi hu
        rfl

end MultiHNN

end MultiHNNDef

end

end Adian
