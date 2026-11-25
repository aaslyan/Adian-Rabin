module

public import Adian.FinPres
public import Adian.MultiHNN
public import Adian.FreeProductLemmas

/-!
# Rabin's Collapse-and-Embedding Construction

Given a finite presentation `K : FinPres` and a raw word `w : List (Fin K.numGens × Bool)`,
we construct a finite presentation `rabinPres K w` (depending primitive recursively on `w`)
together with a canonical homomorphism `rabinIncl K w : K.Group →* (rabinPres K w).Group`
such that:

1. **Collapse** (`rabinPres_subsingleton_of_eq_one`): If `K.mkWord w = 1`, then
   `(rabinPres K w).Group` is trivial (`Subsingleton`).
2. **Embedding** (`rabinIncl_injective_of_ne_one`): If `K.mkWord w ≠ 1`, then
   `rabinIncl K w : K.Group →* (rabinPres K w).Group` is injective.
3. **Computability** (`primrec_rabinPres`): `rabinPres K : List (Fin K.numGens × Bool) → FinPres`
   is primitive recursive.

The embedding proof uses `commutator_zpow_eq_one`, `AffQ`, `rabinP_injective` /
`rabinP_lift_not_inl`, `rabinQ_injective` / `rabinQ_lift_not_inl`, `hnn_free_pair_injective`,
and `AmalgamTarget` (with the right-hand Baumslag–Solitar tower `B` built directly as a
single HNN extension of `AffQ`).
-/

@[expose] public section

open Monoid Subgroup

namespace Adian

/-! ### Part 1: Presentation `rabinPres K w` and Canonical Inclusion `rabinIncl K w` -/

section RabinDef

variable (K : FinPres)

/-- Generator index for original generator `x_i` (`0 ≤ i < K.numGens`) in `rabinPres K w`. -/
def rGenX (i : Fin K.numGens) : Fin (K.numGens + 7) := Fin.castAdd 7 i
/-- Auxiliary generator `z` in `rabinPres K w`. -/
def rGenZ : Fin (K.numGens + 7) := ⟨K.numGens, by omega⟩
/-- Auxiliary generator `b` in `rabinPres K w`. -/
def rGenB : Fin (K.numGens + 7) := ⟨K.numGens + 1, by omega⟩
/-- Auxiliary generator `c` in `rabinPres K w`. -/
def rGenC : Fin (K.numGens + 7) := ⟨K.numGens + 2, by omega⟩
/-- Auxiliary generator `d` in `rabinPres K w`. -/
def rGenD : Fin (K.numGens + 7) := ⟨K.numGens + 3, by omega⟩
/-- Auxiliary generator `f` in `rabinPres K w`. -/
def rGenF : Fin (K.numGens + 7) := ⟨K.numGens + 4, by omega⟩
/-- Auxiliary generator `e` in `rabinPres K w`. -/
def rGenE : Fin (K.numGens + 7) := ⟨K.numGens + 5, by omega⟩
/-- Auxiliary generator `s` in `rabinPres K w`. -/
def rGenS : Fin (K.numGens + 7) := ⟨K.numGens + 6, by omega⟩

/-- The `K.numGens + 3` words `g_0 = 1, g_1..g_n = x_0..x_{n-1}, g_{n+1} = z, g_{n+2} = d`
absorbed by the `e`-HNN relations in `rabinPres K w`. -/
def rabinWordG (i : Fin (K.numGens + 3)) : List (Fin (K.numGens + 7) × Bool) :=
  if _ : i.val = 0 then []
  else if h1 : i.val ≤ K.numGens then
    wordOf (rGenX K ⟨i.val - 1, by omega⟩)
  else if _ : i.val = K.numGens + 1 then
    wordOf (rGenZ K)
  else
    wordOf (rGenD K)

/-- The `e`-conjugation relator for index `i : Fin (K.numGens + 3)`:
`e * (f^(i+1) b f^(-(i+1))) * e⁻¹ = f^(i+1) b f b f^(-(i+1)) g_i`. -/
def rabinERelator (i : Fin (K.numGens + 3)) : List (Fin (K.numGens + 7) × Bool) :=
  let fPos := wordPow (wordOf (rGenF K)) (i.val + 1)
  let fNeg := wordInv fPos
  let wB := wordOf (rGenB K)
  let wF := wordOf (rGenF K)
  let wE := wordOf (rGenE K)
  wordRel
    (wordConjL wE (fPos ++ wB ++ fNeg))
    (fPos ++ wB ++ wF ++ wB ++ fNeg ++ rabinWordG K i)

/-- The `d`-conjugation relator depending on `w`:
`d * [w, z] * d⁻¹ = [w, z] * c⁻¹`. -/
def rabinDRelator (w : List (Fin K.numGens × Bool)) : List (Fin (K.numGens + 7) × Bool) :=
  let wU := wordComm (mapWord (rGenX K) w) (wordOf (rGenZ K))
  wordRel (wordConjL (wordOf (rGenD K)) wU) (wU ++ wordOfInv (rGenC K))

/-- Constant relators of `rabinPres K w` that do not depend on `w`. -/
def rabinConstRelators : List (List (Fin (K.numGens + 7) × Bool)) :=
  K.relators.map (mapWord (rGenX K)) ++
  [ wordRel (wordConj (wordOf (rGenC K)) (wordOf (rGenB K))) (wordPow (wordOf (rGenB K)) 2),
    wordRel (wordConj (wordOf (rGenB K)) (wordOf (rGenS K))) (wordPow (wordOf (rGenS K)) 2),
    wordRel (wordConj (wordOf (rGenS K)) (wordOf (rGenE K))) (wordPow (wordOf (rGenE K)) 2) ] ++
  (List.finRange (K.numGens + 3)).map (rabinERelator K)

/-- Rabin's finite presentation `Π(K, w)`. -/
abbrev rabinPres (w : List (Fin K.numGens × Bool)) : FinPres where
  numGens := K.numGens + 7
  relators := rabinDRelator K w :: rabinConstRelators K

/-- Canonical homomorphism `K.Group →* (rabinPres K w).Group`. -/
def rabinIncl (w : List (Fin K.numGens × Bool)) : K.Group →* (rabinPres K w).Group :=
  K.lift (fun i => (rabinPres K w).ofGen (rGenX K i)) fun r hr => by
    have hcomp : FreeGroup.lift (fun i => (rabinPres K w).ofGen (rGenX K i)) =
        (PresentedGroup.mk (rabinPres K w).relSet).comp (FreeGroup.map (rGenX K)) := by
      ext i; rfl
    rw [hcomp, MonoidHom.comp_apply, ← freeGroup_mk_mapWord]
    exact (rabinPres K w).mkWord_eq_one_of_mem <| by
      simp only [rabinPres, rabinConstRelators, List.mem_cons, List.mem_append, List.mem_map]
      right; left; left; exact ⟨r, hr, rfl⟩

@[simp]
theorem rabinIncl_ofGen (w : List (Fin K.numGens × Bool)) (i : Fin K.numGens) :
    rabinIncl K w (K.ofGen i) = (rabinPres K w).ofGen (rGenX K i) :=
  K.lift_ofGen _ _ i

theorem rabinIncl_mkWord (w u : List (Fin K.numGens × Bool)) :
    rabinIncl K w (K.mkWord u) = (rabinPres K w).mkWord (mapWord (rGenX K) u) := by
  change FreeGroup.lift (fun i => (rabinPres K w).ofGen (rGenX K i)) (FreeGroup.mk u) = _
  have hcomp : FreeGroup.lift (fun i => (rabinPres K w).ofGen (rGenX K i)) =
      (PresentedGroup.mk (rabinPres K w).relSet).comp (FreeGroup.map (rGenX K)) := by
    ext i; rfl
  rw [hcomp, MonoidHom.comp_apply, ← freeGroup_mk_mapWord]
  rfl

/-! ### Part 2: Primitive Recursiveness of `rabinPres K` -/

theorem primrec_rabinPres : Primrec (rabinPres K) := by
  rw [FinPres.primrec_iff]
  have hmap : Primrec (fun w : List (Fin K.numGens × Bool) =>
      mapWord Fin.val (mapWord (rGenX K) w)) := by
    have h : Primrec (fun w : List (Fin K.numGens × Bool) =>
        w.map fun p => (p.1.val, p.2)) :=
      Primrec.list_map Primrec.id
        (Primrec.to₂ (Primrec.pair
          ((Primrec.dom_finite (Fin.val : Fin K.numGens → ℕ)).comp (Primrec.fst.comp Primrec.snd))
          (Primrec.snd.comp Primrec.snd)))
    refine h.of_eq fun w => ?_
    simp [mapWord, rGenX]
  have hU : Primrec (fun w : List (Fin K.numGens × Bool) =>
      mapWord Fin.val (wordComm (mapWord (rGenX K) w) (wordOf (rGenZ K)))) := by
    have h := primrec_wordComm.comp hmap (Primrec.const [(K.numGens, true)])
    refine h.of_eq fun w => ?_
    simp [wordComm, wordInv, wordOf, mapWord, rGenZ, List.map_reverse]
  have hD : Primrec (fun w : List (Fin K.numGens × Bool) =>
      mapWord Fin.val (rabinDRelator K w)) := by
    have h := Primrec.list_append.comp
      (Primrec.list_append.comp
        (Primrec.list_append.comp (Primrec.const [(K.numGens + 3, true)]) hU)
        (Primrec.const [(K.numGens + 3, false)]))
      (primrec_wordInv.comp (Primrec.list_append.comp hU (Primrec.const [(K.numGens + 2, false)])))
    refine h.of_eq fun w => ?_
    simp [rabinDRelator, wordRel, wordConjL, wordInv, wordOf, wordOfInv, mapWord, rGenD, rGenC,
      List.map_reverse]
  have hrels : Primrec (fun w : List (Fin K.numGens × Bool) =>
      mapWord Fin.val (rabinDRelator K w) :: (rabinConstRelators K).map (mapWord Fin.val)) :=
    Primrec.list_cons.comp hD (Primrec.const ((rabinConstRelators K).map (mapWord Fin.val)))
  exact (Primrec.pair (Primrec.const (K.numGens + 7)) hrels).of_eq fun w => by
    simp [FinPres.toRaw, rabinPres]

/-! ### Part 3: Collapse when `K.mkWord w = 1` -/

/-- If `K.mkWord w = 1`, then `(rabinPres K w).Group` collapses to the trivial group. -/
theorem rabinPres_subsingleton_of_eq_one (w : List (Fin K.numGens × Bool))
    (hw : K.mkWord w = 1) : Subsingleton (rabinPres K w).Group := by
  let z : (rabinPres K w).Group := (rabinPres K w).ofGen (rGenZ K)
  let b : (rabinPres K w).Group := (rabinPres K w).ofGen (rGenB K)
  let c : (rabinPres K w).Group := (rabinPres K w).ofGen (rGenC K)
  let d : (rabinPres K w).Group := (rabinPres K w).ofGen (rGenD K)
  let f : (rabinPres K w).Group := (rabinPres K w).ofGen (rGenF K)
  let e : (rabinPres K w).Group := (rabinPres K w).ofGen (rGenE K)
  let s : (rabinPres K w).Group := (rabinPres K w).ofGen (rGenS K)
  have hw_one : (rabinPres K w).mkWord (mapWord (rGenX K) w) = 1 := by
    rw [← rabinIncl_mkWord K w w, hw, map_one]
  have hc : c = 1 := by
    have hrel := (rabinPres K w).mkWord_eq_of_wordRel_mem
      (u := wordConjL (wordOf (rGenD K)) (wordComm (mapWord (rGenX K) w) (wordOf (rGenZ K))))
      (v := wordComm (mapWord (rGenX K) w) (wordOf (rGenZ K)) ++ wordOfInv (rGenC K))
      (by simp [rabinPres, rabinDRelator])
    simp only [FinPres.mkWord, freeGroup_mk_wordConjL, freeGroup_mk_wordComm, freeGroup_mk_append,
      freeGroup_mk_wordOf, freeGroup_mk_wordOfInv, map_mul, map_inv] at hrel
    rw [show PresentedGroup.mk (rabinPres K w).relSet (FreeGroup.mk (mapWord (rGenX K) w)) = 1 from hw_one] at hrel
    simp only [one_mul, inv_one, mul_one, mul_inv_cancel] at hrel
    exact inv_eq_one.mp hrel.symm
  have hb : b = 1 := by
    have hmem : wordRel (wordConj (wordOf (rGenC K)) (wordOf (rGenB K)))
        (wordPow (wordOf (rGenB K)) 2) ∈ (rabinPres K w).relators := by
      simp [rabinPres, rabinConstRelators]
    have hrel := (rabinPres K w).mkWord_eq_of_wordRel_mem hmem
    simp only [FinPres.mkWord, freeGroup_mk_wordConj, freeGroup_mk_wordPow, freeGroup_mk_wordOf,
      map_mul, map_inv, map_pow] at hrel
    change c⁻¹ * b * c = b ^ 2 at hrel
    rw [hc, inv_one, one_mul, mul_one, sq] at hrel
    have h1 : b * 1 = b * b := by simpa using hrel
    exact (mul_left_cancel h1).symm
  have hs : s = 1 := by
    have hmem : wordRel (wordConj (wordOf (rGenB K)) (wordOf (rGenS K)))
        (wordPow (wordOf (rGenS K)) 2) ∈ (rabinPres K w).relators := by
      simp [rabinPres, rabinConstRelators]
    have hrel := (rabinPres K w).mkWord_eq_of_wordRel_mem hmem
    simp only [FinPres.mkWord, freeGroup_mk_wordConj, freeGroup_mk_wordPow, freeGroup_mk_wordOf,
      map_mul, map_inv, map_pow] at hrel
    change b⁻¹ * s * b = s ^ 2 at hrel
    rw [hb, inv_one, one_mul, mul_one, sq] at hrel
    have h1 : s * 1 = s * s := by simpa using hrel
    exact (mul_left_cancel h1).symm
  have he : e = 1 := by
    have hmem : wordRel (wordConj (wordOf (rGenS K)) (wordOf (rGenE K)))
        (wordPow (wordOf (rGenE K)) 2) ∈ (rabinPres K w).relators := by
      simp [rabinPres, rabinConstRelators]
    have hrel := (rabinPres K w).mkWord_eq_of_wordRel_mem hmem
    simp only [FinPres.mkWord, freeGroup_mk_wordConj, freeGroup_mk_wordPow, freeGroup_mk_wordOf,
      map_mul, map_inv, map_pow] at hrel
    change s⁻¹ * e * s = e ^ 2 at hrel
    rw [hs, inv_one, one_mul, mul_one, sq] at hrel
    have h1 : e * 1 = e * e := by simpa using hrel
    exact (mul_left_cancel h1).symm
  have hf_mul_g : ∀ i : Fin (K.numGens + 3), f * (rabinPres K w).mkWord (rabinWordG K i) = 1 := by
    intro i
    have hmem : rabinERelator K i ∈ (rabinPres K w).relators := by
      simp only [rabinPres, rabinConstRelators, List.mem_cons, List.mem_append, List.mem_map,
        List.mem_finRange, true_and]
      right; right; exact ⟨i, rfl⟩
    have hrel := (rabinPres K w).mkWord_eq_of_wordRel_mem hmem
    simp only [FinPres.mkWord, freeGroup_mk_wordConjL, freeGroup_mk_append, freeGroup_mk_wordInv,
      freeGroup_mk_wordPow, freeGroup_mk_wordOf, map_mul, map_inv, map_pow] at hrel
    change e * (f ^ (i.val + 1) * b * (f ^ (i.val + 1))⁻¹) * e⁻¹ =
      f ^ (i.val + 1) * b * f * b * (f ^ (i.val + 1))⁻¹ * (rabinPres K w).mkWord (rabinWordG K i) at hrel
    rw [hb, he] at hrel
    simp only [mul_one, inv_one, mul_inv_cancel] at hrel
    have hfconj : f ^ (i.val + 1) * f * (f ^ (i.val + 1))⁻¹ = f := by
      rw [← pow_succ, pow_succ', mul_assoc, mul_inv_cancel, mul_one]
    rw [hfconj] at hrel
    exact hrel.symm
  have hf : f = 1 := by
    have h0 := hf_mul_g ⟨0, by omega⟩
    simp [rabinWordG] at h0
    exact h0
  have hg_one : ∀ i : Fin (K.numGens + 3), (rabinPres K w).mkWord (rabinWordG K i) = 1 := by
    intro i
    have hi := hf_mul_g i
    rw [hf, one_mul] at hi
    exact hi
  have hall_gen : ∀ idx : Fin (K.numGens + 7), (rabinPres K w).ofGen idx = 1 := by
    intro idx
    by_cases h0 : idx.val < K.numGens
    · have hi := hg_one ⟨idx.val + 1, by omega⟩
      have hne0 : idx.val + 1 ≠ 0 := by omega
      have hle : idx.val + 1 ≤ K.numGens := by omega
      simp only [rabinWordG, hne0, ↓reduceDIte, hle, rGenX] at hi
      have heq : idx = Fin.castAdd 7 ⟨idx.val + 1 - 1, by omega⟩ := Fin.ext (by simp)
      rw [heq]; exact hi
    · have hcase : idx.val = K.numGens ∨ idx.val = K.numGens + 1 ∨ idx.val = K.numGens + 2 ∨
          idx.val = K.numGens + 3 ∨ idx.val = K.numGens + 4 ∨ idx.val = K.numGens + 5 ∨
          idx.val = K.numGens + 6 := by omega
      rcases hcase with h | h | h | h | h | h | h
      · have hi := hg_one ⟨K.numGens + 1, by omega⟩
        have h1 : K.numGens + 1 ≠ 0 := by omega
        have h2 : ¬ K.numGens + 1 ≤ K.numGens := by omega
        simp only [rabinWordG, h1, h2, ↓reduceDIte] at hi
        rw [show idx = rGenZ K from Fin.ext h]; exact hi
      · rw [show idx = rGenB K from Fin.ext h]; exact hb
      · rw [show idx = rGenC K from Fin.ext h]; exact hc
      · have hi := hg_one ⟨K.numGens + 2, by omega⟩
        have h1 : K.numGens + 2 ≠ 0 := by omega
        have h2 : ¬ K.numGens + 2 ≤ K.numGens := by omega
        have h3 : K.numGens + 2 ≠ K.numGens + 1 := by omega
        simp only [rabinWordG, h1, h2, h3, ↓reduceDIte] at hi
        rw [show idx = rGenD K from Fin.ext h]; exact hi
      · rw [show idx = rGenF K from Fin.ext h]; exact hf
      · rw [show idx = rGenE K from Fin.ext h]; exact he
      · rw [show idx = rGenS K from Fin.ext h]; exact hs
  have hid : MonoidHom.id (rabinPres K w).Group = (1 : (rabinPres K w).Group →* (rabinPres K w).Group) := by
    apply FinPres.hom_ext
    intro idx
    exact hall_gen idx
  exact ⟨fun x y => by
    have hx : x = 1 := congrArg (fun φ => φ x) hid
    have hy : y = 1 := congrArg (fun φ => φ y) hid
    rw [hx, hy]⟩

end RabinDef

/-! ### Part 4: Embedding when `K.mkWord w ≠ 1` -/

noncomputable section RabinEmbed

/-- Helper: isomorphism `zpowers x ≃* zpowers y` sending `x ↦ y` for infinite-order elements. -/
def zpowersEquivOfInfOrder {G : Type*} [Group G] {x y : G}
    (hx : ∀ k : ℤ, x ^ k = 1 → k = 0) (hy : ∀ k : ℤ, y ^ k = 1 → k = 0) :
    Subgroup.zpowers x ≃* Subgroup.zpowers y := by
  let fx : Multiplicative ℤ →* Subgroup.zpowers x :=
    { toFun := fun n => ⟨x ^ Multiplicative.toAdd n, ⟨Multiplicative.toAdd n, rfl⟩⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by
        ext; change x ^ (Multiplicative.toAdd a + Multiplicative.toAdd b) = _; rw [zpow_add]; rfl }
  let fy : Multiplicative ℤ →* Subgroup.zpowers y :=
    { toFun := fun n => ⟨y ^ Multiplicative.toAdd n, ⟨Multiplicative.toAdd n, rfl⟩⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by
        ext; change y ^ (Multiplicative.toAdd a + Multiplicative.toAdd b) = _; rw [zpow_add]; rfl }
  have hfx : Function.Bijective fx := by
    refine ⟨?_, fun ⟨_, n, rfl⟩ => ⟨Multiplicative.ofAdd n, by ext; rfl⟩⟩
    intro a b hab
    have hval : x ^ Multiplicative.toAdd a = x ^ Multiplicative.toAdd b := congrArg Subtype.val hab
    have hsub : x ^ (Multiplicative.toAdd a - Multiplicative.toAdd b) = 1 := by
      rw [zpow_sub, hval, mul_inv_cancel]
    have h0 := hx _ hsub
    exact Multiplicative.toAdd.injective (sub_eq_zero.mp h0)
  have hfy : Function.Bijective fy := by
    refine ⟨?_, fun ⟨_, n, rfl⟩ => ⟨Multiplicative.ofAdd n, by ext; rfl⟩⟩
    intro a b hab
    have hval : y ^ Multiplicative.toAdd a = y ^ Multiplicative.toAdd b := congrArg Subtype.val hab
    have hsub : y ^ (Multiplicative.toAdd a - Multiplicative.toAdd b) = 1 := by
      rw [zpow_sub, hval, mul_inv_cancel]
    have h0 := hy _ hsub
    exact Multiplicative.toAdd.injective (sub_eq_zero.mp h0)
  exact (MulEquiv.ofBijective fx hfx).symm.trans (MulEquiv.ofBijective fy hfy)

theorem zpowersEquivOfInfOrder_apply_gen {G : Type*} [Group G] {x y : G}
    (hx : ∀ k : ℤ, x ^ k = 1 → k = 0) (hy : ∀ k : ℤ, y ^ k = 1 → k = 0) :
    (zpowersEquivOfInfOrder hx hy ⟨x, Subgroup.mem_zpowers x⟩ : G) = y := by
  let fx : Multiplicative ℤ →* Subgroup.zpowers x :=
    { toFun := fun n => ⟨x ^ Multiplicative.toAdd n, ⟨Multiplicative.toAdd n, rfl⟩⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by
        ext; change x ^ (Multiplicative.toAdd a + Multiplicative.toAdd b) = _; rw [zpow_add]; rfl }
  have hfx : Function.Bijective fx := by
    refine ⟨?_, fun ⟨_, n, rfl⟩ => ⟨Multiplicative.ofAdd n, by ext; rfl⟩⟩
    intro a b hab
    have hval : x ^ Multiplicative.toAdd a = x ^ Multiplicative.toAdd b := congrArg Subtype.val hab
    have hsub : x ^ (Multiplicative.toAdd a - Multiplicative.toAdd b) = 1 := by
      rw [zpow_sub, hval, mul_inv_cancel]
    exact Multiplicative.toAdd.injective (sub_eq_zero.mp (hx _ hsub))
  have h1 : (MulEquiv.ofBijective fx hfx).symm ⟨x, Subgroup.mem_zpowers x⟩ =
      Multiplicative.ofAdd (1 : ℤ) := by
    rw [MulEquiv.symm_apply_eq]
    ext; simp [fx]
  change (y ^ Multiplicative.toAdd ((MulEquiv.ofBijective fx hfx).symm
    ⟨x, Subgroup.mem_zpowers x⟩) : G) = y
  rw [h1]; simp

/-- Right-hand group `B` of Rabin's amalgamated free product: an HNN extension of `AffQ`
realizing `b⁻¹ s b = s²` and `s⁻¹ e s = e²` with `⟨b, e⟩` free of rank 2. -/
private def rabinB_phi :
    Subgroup.zpowers AffQ.genC ≃* Subgroup.zpowers (AffQ.genC ^ (2 : ℕ)) :=
  zpowersEquivOfInfOrder
    (fun k hk => (AffQ.genC_zpow_eq_one_iff k).1 hk)
    (fun k hk => by
      have h1 : AffQ.genC ^ (2 * k) = 1 := by
        rw [zpow_mul]; simpa [zpow_ofNat] using hk
      have h2 := (AffQ.genC_zpow_eq_one_iff (2 * k)).1 h1
      omega)

private abbrev RabinB : Type :=
  HNNExtension AffQ (Subgroup.zpowers AffQ.genC) (Subgroup.zpowers (AffQ.genC ^ (2 : ℕ))) rabinB_phi

private def rabinB_s : RabinB := HNNExtension.of AffQ.genC
private def rabinB_e : RabinB := HNNExtension.of AffQ.genB
private def rabinB_b : RabinB := (HNNExtension.t (φ := rabinB_phi))⁻¹

private theorem rabinB_rel_bs : rabinB_b⁻¹ * rabinB_s * rabinB_b = rabinB_s ^ (2 : ℕ) := by
  have h := HNNExtension.equiv_eq_conj (φ := rabinB_phi) ⟨AffQ.genC, Subgroup.mem_zpowers _⟩
  have hv : (rabinB_phi ⟨AffQ.genC, Subgroup.mem_zpowers _⟩ : AffQ) = AffQ.genC ^ (2 : ℕ) :=
    zpowersEquivOfInfOrder_apply_gen _ _
  rw [hv, map_pow] at h
  simpa [rabinB_b, rabinB_s] using h.symm

private theorem rabinB_rel_se : rabinB_s⁻¹ * rabinB_e * rabinB_s = rabinB_e ^ (2 : ℕ) := by
  simp only [rabinB_s, rabinB_e, ← map_inv, ← map_mul, ← map_pow, AffQ.conj_rel]

private theorem rabinB_pair_injective :
    Function.Injective (FreeGroup.lift fun i : Fin 2 => if i = 0 then rabinB_b else rabinB_e) := by
  have hfree := hnn_free_pair_injective rabinB_phi AffQ.genB
    (fun k hk => (AffQ.genB_zpow_eq_one_iff k).1 hk)
    (fun n hn hmem => by
      rcases hmem with ⟨k, hk⟩
      have := (AffQ.genB_zpow_eq_genC_zpow_iff n k).1 hk.symm
      exact hn this.1)
    (fun n hn hmem => by
      rcases hmem with ⟨k, hk⟩
      have h1 : AffQ.genB ^ n = AffQ.genC ^ (2 * k) := by
        rw [zpow_mul]; simpa [zpow_ofNat] using hk.symm
      have := (AffQ.genB_zpow_eq_genC_zpow_iff n (2 * k)).1 h1
      exact hn this.1)
  -- Swap + invert automorphism of `FreeGroup (Fin 2)` sending `0 ↦ (of 1)⁻¹, 1 ↦ of 0`.
  let swapTo : FreeGroup (Fin 2) →* FreeGroup (Fin 2) :=
    FreeGroup.lift fun i : Fin 2 => if i = 0 then (FreeGroup.of 1)⁻¹ else FreeGroup.of 0
  let swapInv : FreeGroup (Fin 2) →* FreeGroup (Fin 2) :=
    FreeGroup.lift fun i : Fin 2 => if i = 0 then FreeGroup.of 1 else (FreeGroup.of 0)⁻¹
  have hswap_inj : Function.Injective swapTo := by
    have hcomp : swapInv.comp swapTo = MonoidHom.id _ := by
      apply FreeGroup.ext_hom
      intro i
      fin_cases i <;> simp [swapTo, swapInv]
    exact Function.LeftInverse.injective fun x => congrArg (fun f => f x) hcomp
  have hfact : (FreeGroup.lift fun i : Fin 2 => if i = 0 then rabinB_b else rabinB_e) =
      (FreeGroup.lift fun i : Fin 2 =>
        if i = 0 then (HNNExtension.of AffQ.genB : RabinB) else HNNExtension.t).comp swapTo := by
    apply FreeGroup.ext_hom
    intro i
    fin_cases i <;> simp [swapTo, rabinB_b, rabinB_e]
  rw [hfact]
  exact hfree.comp hswap_inj

/-- If `K.mkWord w ≠ 1`, then the canonical map `rabinIncl K w : K.Group →* (rabinPres K w).Group`
is injective. -/
theorem rabinIncl_injective_of_ne_one (K : FinPres) (w : List (Fin K.numGens × Bool))
    (hw : K.mkWord w ≠ 1) : Function.Injective (rabinIncl K w) := by
  -- Step 1: K₀ = K.Group ∗ ℤ, with infinite-order commutator u₀ = [w, z₀].
  let K0 := Coprod K.Group (Multiplicative ℤ)
  let z0 : K0 := Coprod.inr (Multiplicative.ofAdd (1 : ℤ))
  let u0 : K0 := Coprod.inl (K.mkWord w) * z0 * (Coprod.inl (K.mkWord w))⁻¹ * z0⁻¹
  have hu0_inf : ∀ k : ℤ, u0 ^ k = 1 → k = 0 := commutator_zpow_eq_one hw
  -- Step 2: M₀ = K₀ ∗ AffQ, with infinite-order elements uM₀ and uM₀ * c₀⁻¹.
  let M0 := Coprod K0 AffQ
  let uM0 : M0 := Coprod.inl u0
  let b0 : M0 := Coprod.inr AffQ.genB
  let c0 : M0 := Coprod.inr AffQ.genC
  have huM0_inf : ∀ k : ℤ, uM0 ^ k = 1 → k = 0 := by
    intro k hk
    apply hu0_inf k
    exact Coprod.inl_injective ((map_zpow (Coprod.inl : K0 →* M0) u0 k).trans (hk.trans (map_one _).symm))
  have huM0c_inf : ∀ k : ℤ, (uM0 * c0⁻¹) ^ k = 1 → k = 0 := by
    intro k hk
    apply hu0_inf k
    have hfst := congrArg (Coprod.fst : M0 →* K0) hk
    have hc_inv : (Coprod.fst : M0 →* K0) c0⁻¹ = 1 := by
      have h := MonoidHom.map_inv (Coprod.fst : M0 →* K0) c0
      rw [h]; exact inv_one
    have hu_fst : (Coprod.fst : M0 →* K0) uM0 = u0 := rfl
    rw [map_zpow, map_mul, hu_fst, hc_inv, mul_one, map_one] at hfst
    exact hfst
  -- Step 3: M₁ = HNNExtension M₀ ⟨uM₀⟩ ⟨uM₀ * c₀⁻¹⟩ φ₁ (stable letter d₁).
  let φ1 : Subgroup.zpowers uM0 ≃* Subgroup.zpowers (uM0 * c0⁻¹) :=
    zpowersEquivOfInfOrder huM0_inf huM0c_inf
  let M1 := HNNExtension M0 (Subgroup.zpowers uM0) (Subgroup.zpowers (uM0 * c0⁻¹)) φ1
  let d1 : M1 := HNNExtension.t (φ := φ1)
  let b1 : M1 := HNNExtension.of b0
  have hb1_inf : ∀ k : ℤ, b1 ^ k = 1 → k = 0 := by
    intro k hk
    have h1 : b0 ^ k = 1 :=
      HNNExtension.of_injective φ1 ((map_zpow (HNNExtension.of (φ := φ1)) b0 k).trans (hk.trans (map_one _).symm))
    have h2 : AffQ.genB ^ k = 1 :=
      Coprod.inr_injective ((map_zpow (Coprod.inr : AffQ →* M0) AffQ.genB k).trans (h1.trans (map_one _).symm))
    exact (AffQ.genB_zpow_eq_one_iff k).1 h2
  -- Images g₁ : Fin (K.numGens + 3) → M₁ matching `rabinWordG K`.
  let ιK_M1 : K.Group →* M1 :=
    (HNNExtension.of (φ := φ1)).comp (Coprod.inl.comp Coprod.inl)
  let g1 : Fin (K.numGens + 3) → M1 := fun i =>
    if _ : i.val = 0 then 1
    else if h1 : i.val ≤ K.numGens then
      ιK_M1 (K.ofGen ⟨i.val - 1, by omega⟩)
    else if _ : i.val = K.numGens + 1 then
      HNNExtension.of (Coprod.inl z0)
    else
      d1
  -- Step 4: M₂ = M₁ ∗ ℤ, with Rabin's free subgroups P and Q.
  let M2 := Coprod M1 (Multiplicative ℤ)
  let f2 : M2 := Coprod.inr (Multiplicative.ofAdd (1 : ℤ))
  let b2 : M2 := Coprod.inl b1
  let pHom : FreeGroup (Fin (K.numGens + 3)) →* M2 := FreeGroup.lift (rabinP b1)
  let qHom : FreeGroup (Fin (K.numGens + 3)) →* M2 := FreeGroup.lift (rabinQ b1 g1)
  have hp_inj : Function.Injective pHom := rabinP_injective hb1_inf
  have hq_inj : Function.Injective qHom := rabinQ_injective hb1_inf g1
  let φ2 : pHom.range ≃* qHom.range :=
    (MulEquiv.ofBijective pHom.rangeRestrict
      ⟨fun _ _ h => hp_inj (congrArg Subtype.val h), pHom.rangeRestrict_surjective⟩).symm.trans
    (MulEquiv.ofBijective qHom.rangeRestrict
      ⟨fun _ _ h => hq_inj (congrArg Subtype.val h), qHom.rangeRestrict_surjective⟩)
  have hφ2_of : ∀ i : Fin (K.numGens + 3),
      (φ2 ⟨rabinP b1 i, ⟨FreeGroup.of i, by simp [pHom]⟩⟩ : M2) = rabinQ b1 g1 i := by
    intro i
    let eP := MulEquiv.ofBijective pHom.rangeRestrict
      ⟨fun _ _ h => hp_inj (congrArg Subtype.val h), pHom.rangeRestrict_surjective⟩
    have h1 : eP.symm ⟨rabinP b1 i, ⟨FreeGroup.of i, by simp [pHom]⟩⟩ = FreeGroup.of i := by
      rw [MulEquiv.symm_apply_eq]
      apply Subtype.ext
      change rabinP b1 i = pHom (FreeGroup.of i)
      simp [pHom]
    change (qHom.rangeRestrict (eP.symm ⟨rabinP b1 i, ⟨FreeGroup.of i, by simp [pHom]⟩⟩) : M2) = _
    rw [h1]; simp [qHom]
  -- Step 5: A = HNNExtension M₂ P Q φ₂ (stable letter eA), with ⟨bA, eA⟩ free of rank 2.
  let A := HNNExtension M2 pHom.range qHom.range φ2
  let eA : A := HNNExtension.t (φ := φ2)
  let bA : A := HNNExtension.of b2
  have hb2_inf : ∀ k : ℤ, b2 ^ k = 1 → k = 0 := by
    intro k hk
    exact hb1_inf k (Coprod.inl_injective
      ((map_zpow (Coprod.inl : M1 →* M2) b1 k).trans (hk.trans (map_one _).symm)))
  have hpairA_inj :
      Function.Injective (FreeGroup.lift fun i : Fin 2 => if i = 0 then bA else eA) :=
    hnn_free_pair_injective φ2 b2 hb2_inf
      (fun n hn ⟨v, hv⟩ => by
        have hv_ne : v ≠ 1 := by
          intro h1; rw [h1, map_one] at hv
          exact hn (hb2_inf n hv.symm)
        exact rabinP_lift_not_inl hb1_inf v hv_ne
          ⟨b1 ^ n, (map_zpow (Coprod.inl : M1 →* M2) b1 n).trans hv.symm⟩)
      (fun n hn ⟨v, hv⟩ => by
        have hv_ne : v ≠ 1 := by
          intro h1; rw [h1, map_one] at hv
          exact hn (hb2_inf n hv.symm)
        exact rabinQ_lift_not_inl hb1_inf g1 v hv_ne
          ⟨b1 ^ n, (map_zpow (Coprod.inl : M1 →* M2) b1 n).trans hv.symm⟩)
  -- Step 6: AmalgamTarget T of A and RabinB along ⟨bA, eA⟩ ≃* ⟨rabinB_b, rabinB_e⟩.
  let pairA : FreeGroup (Fin 2) →* A := FreeGroup.lift fun i : Fin 2 => if i = 0 then bA else eA
  let pairB : FreeGroup (Fin 2) →* RabinB :=
    FreeGroup.lift fun i : Fin 2 => if i = 0 then rabinB_b else rabinB_e
  let θ : pairA.range ≃* pairB.range :=
    (MulEquiv.ofBijective pairA.rangeRestrict
      ⟨fun _ _ h => hpairA_inj (congrArg Subtype.val h), pairA.rangeRestrict_surjective⟩).symm.trans
    (MulEquiv.ofBijective pairB.rangeRestrict
      ⟨fun _ _ h => rabinB_pair_injective (congrArg Subtype.val h), pairB.rangeRestrict_surjective⟩)
  let T := AmalgamTarget pairA.range pairB.range θ
  let inlT : A →* T := amalgamInl pairA.range pairB.range θ
  let inrT : RabinB →* T := amalgamInr pairA.range pairB.range θ
  have hθ_b : inlT bA = inrT rabinB_b := by
    let eA_iso := MulEquiv.ofBijective pairA.rangeRestrict
      ⟨fun _ _ h => hpairA_inj (congrArg Subtype.val h), pairA.rangeRestrict_surjective⟩
    have h0 : eA_iso.symm ⟨bA, ⟨FreeGroup.of 0, by simp [pairA]⟩⟩ = FreeGroup.of 0 := by
      rw [MulEquiv.symm_apply_eq]
      apply Subtype.ext
      change bA = pairA (FreeGroup.of 0)
      simp [pairA]
    have hθ0 : (θ ⟨bA, ⟨FreeGroup.of 0, by simp [pairA]⟩⟩ : RabinB) = rabinB_b := by
      change (pairB.rangeRestrict (eA_iso.symm ⟨bA, ⟨FreeGroup.of 0, by simp [pairA]⟩⟩) : RabinB) = _
      rw [h0]; simp [pairB]
    have hcomm := amalgam_comm pairA.range pairB.range θ ⟨bA, ⟨FreeGroup.of 0, by simp [pairA]⟩⟩
    rw [hθ0] at hcomm
    exact hcomm
  have hθ_e : inlT eA = inrT rabinB_e := by
    let eA_iso := MulEquiv.ofBijective pairA.rangeRestrict
      ⟨fun _ _ h => hpairA_inj (congrArg Subtype.val h), pairA.rangeRestrict_surjective⟩
    have h1 : eA_iso.symm ⟨eA, ⟨FreeGroup.of 1, by simp [pairA]⟩⟩ = FreeGroup.of 1 := by
      rw [MulEquiv.symm_apply_eq]
      apply Subtype.ext
      change eA = pairA (FreeGroup.of 1)
      simp [pairA]
    have hθ1 : (θ ⟨eA, ⟨FreeGroup.of 1, by simp [pairA]⟩⟩ : RabinB) = rabinB_e := by
      change (pairB.rangeRestrict (eA_iso.symm ⟨eA, ⟨FreeGroup.of 1, by simp [pairA]⟩⟩) : RabinB) = _
      rw [h1]; simp [pairB]
    have hcomm := amalgam_comm pairA.range pairB.range θ ⟨eA, ⟨FreeGroup.of 1, by simp [pairA]⟩⟩
    rw [hθ1] at hcomm
    exact hcomm
  -- Step 7: Homomorphism (rabinPres K w).Group →* T whose composition with rabinIncl is injective.
  let ιM1_A : M1 →* A := (HNNExtension.of (φ := φ2)).comp Coprod.inl
  let ιK_A : K.Group →* A := ιM1_A.comp ιK_M1
  let ιK_T : K.Group →* T := inlT.comp ιK_A
  let genMap : Fin (K.numGens + 7) → T := fun idx =>
    if h0 : idx.val < K.numGens then ιK_T (K.ofGen ⟨idx.val, h0⟩)
    else if idx.val = K.numGens then inlT (ιM1_A (HNNExtension.of (Coprod.inl z0)))
    else if idx.val = K.numGens + 1 then inlT bA
    else if idx.val = K.numGens + 2 then inlT (ιM1_A (HNNExtension.of c0))
    else if idx.val = K.numGens + 3 then inlT (ιM1_A d1)
    else if idx.val = K.numGens + 4 then inlT (HNNExtension.of f2)
    else if idx.val = K.numGens + 5 then inlT eA
    else inrT rabinB_s
  have hgenX : ∀ i : Fin K.numGens, genMap (rGenX K i) = ιK_T (K.ofGen i) := fun i => by
    simp [genMap, rGenX, i.isLt]
  have hgenZ : genMap (rGenZ K) = inlT (ιM1_A (HNNExtension.of (Coprod.inl z0))) := by
    simp [genMap, rGenZ]
  have hgenB : genMap (rGenB K) = inlT bA := by
    simp [genMap, rGenB]
  have hgenC : genMap (rGenC K) = inlT (ιM1_A (HNNExtension.of c0)) := by
    simp [genMap, rGenC]
  have hgenD : genMap (rGenD K) = inlT (ιM1_A d1) := by
    simp [genMap, rGenD]
  have hgenF : genMap (rGenF K) = inlT (HNNExtension.of f2) := by
    simp [genMap, rGenF]
  have hgenE : genMap (rGenE K) = inlT eA := by
    simp [genMap, rGenE]
  have hgenS : genMap (rGenS K) = inrT rabinB_s := by
    simp [genMap, rGenS]
  have hmap_word : ∀ u : List (Fin K.numGens × Bool),
      FreeGroup.lift genMap (FreeGroup.mk (mapWord (rGenX K) u)) = ιK_T (K.mkWord u) := by
    intro u
    rw [freeGroup_mk_mapWord]
    have hcomp : (FreeGroup.lift genMap).comp (FreeGroup.map (rGenX K)) =
        ιK_T.comp (PresentedGroup.mk K.relSet) := by
      apply FreeGroup.ext_hom
      intro i
      simp [hgenX, FinPres.ofGen, PresentedGroup.of]
    exact congrArg (fun φ => φ (FreeGroup.mk u)) hcomp
  have hrels : ∀ r ∈ (rabinPres K w).relators, FreeGroup.lift genMap (FreeGroup.mk r) = 1 := by
    intro r hr
    simp only [rabinPres, rabinConstRelators, List.mem_cons, List.mem_append, List.mem_map,
      List.mem_finRange, List.not_mem_nil, or_false, true_and] at hr
    rcases hr with rfl | ((⟨rK, hrK, rfl⟩ | (rfl | rfl | rfl)) | ⟨i, rfl⟩)
    · -- d * [w, z] * d⁻¹ = [w, z] * c⁻¹
      simp only [rabinDRelator, freeGroup_mk_wordRel, freeGroup_mk_wordConjL, freeGroup_mk_wordComm,
        freeGroup_mk_append, freeGroup_mk_wordOf, freeGroup_mk_wordOfInv, map_mul, map_inv,
        FreeGroup.lift_apply_of, hmap_word, hgenD, hgenZ, hgenC]
      rw [mul_inv_eq_one]
      have hcomm_u : ιK_T (K.mkWord w) * inlT (ιM1_A (HNNExtension.of (Coprod.inl z0))) *
          (ιK_T (K.mkWord w))⁻¹ * (inlT (ιM1_A (HNNExtension.of (Coprod.inl z0))))⁻¹ =
          inlT (ιM1_A (HNNExtension.of uM0)) := by
        have h1 : (HNNExtension.of (φ := φ1) uM0 : M1) =
            ιK_M1 (K.mkWord w) * HNNExtension.of (Coprod.inl z0) *
              (ιK_M1 (K.mkWord w))⁻¹ * (HNNExtension.of (Coprod.inl z0))⁻¹ := by
          simp only [ιK_M1, MonoidHom.comp_apply, uM0, u0, map_mul, map_inv]
        rw [h1]
        simp only [ιK_T, ιK_A, MonoidHom.comp_apply, map_mul, map_inv]
      rw [hcomm_u]
      have hrel_M1 : d1 * HNNExtension.of (φ := φ1) uM0 * d1⁻¹ =
          HNNExtension.of (φ := φ1) uM0 * (HNNExtension.of (φ := φ1) c0)⁻¹ := by
        have h1 := HNNExtension.equiv_eq_conj (φ := φ1) ⟨uM0, Subgroup.mem_zpowers uM0⟩
        have hv : (φ1 ⟨uM0, Subgroup.mem_zpowers uM0⟩ : M0) = uM0 * c0⁻¹ :=
          zpowersEquivOfInfOrder_apply_gen huM0_inf huM0c_inf
        rw [hv, map_mul, MonoidHom.map_inv (HNNExtension.of (φ := φ1)) c0] at h1
        exact h1.symm
      have hrel_T := congrArg (inlT.comp ιM1_A) hrel_M1
      simpa only [MonoidHom.comp_apply, map_mul, map_inv] using hrel_T
    · -- Relators of K
      rw [hmap_word, K.mkWord_eq_one_of_mem hrK, map_one]
    · -- c⁻¹ * b * c = b²
      simp only [freeGroup_mk_wordRel, freeGroup_mk_wordConj, freeGroup_mk_wordPow,
        freeGroup_mk_wordOf, map_mul, map_inv, map_pow, FreeGroup.lift_apply_of, hgenC, hgenB]
      rw [mul_inv_eq_one]
      have hbc : c0⁻¹ * b0 * c0 = b0 ^ (2 : ℕ) := by
        have h := congrArg (Coprod.inr : AffQ →* M0) AffQ.conj_rel
        simpa only [b0, c0, map_mul, map_inv, map_pow] using h
      have hbc_T := congrArg (inlT.comp (ιM1_A.comp (HNNExtension.of (φ := φ1)))) hbc
      change (inlT (ιM1_A (HNNExtension.of (φ := φ1) c0)))⁻¹ *
          inlT (ιM1_A (HNNExtension.of (φ := φ1) b0)) *
          inlT (ιM1_A (HNNExtension.of (φ := φ1) c0)) =
        (inlT (ιM1_A (HNNExtension.of (φ := φ1) b0))) ^ (2 : ℕ)
      simp only [MonoidHom.comp_apply, map_mul, map_pow] at hbc_T
      rw [MonoidHom.map_inv (HNNExtension.of (φ := φ1)) c0, map_inv, map_inv] at hbc_T
      exact hbc_T
    · -- b⁻¹ * s * b = s²
      simp only [freeGroup_mk_wordRel, freeGroup_mk_wordConj, freeGroup_mk_wordPow,
        freeGroup_mk_wordOf, map_mul, map_inv, map_pow, FreeGroup.lift_apply_of, hgenB, hgenS, hθ_b]
      rw [mul_inv_eq_one]
      have hT := congrArg inrT rabinB_rel_bs
      simpa only [map_mul, map_inv, map_pow] using hT
    · -- s⁻¹ * e * s = e²
      simp only [freeGroup_mk_wordRel, freeGroup_mk_wordConj, freeGroup_mk_wordPow,
        freeGroup_mk_wordOf, map_mul, map_inv, map_pow, FreeGroup.lift_apply_of, hgenS, hgenE, hθ_e]
      rw [mul_inv_eq_one]
      have hT := congrArg inrT rabinB_rel_se
      simpa only [map_mul, map_inv, map_pow] using hT
    · -- e * p_i * e⁻¹ = q_i
      have hg_map : FreeGroup.lift genMap (FreeGroup.mk (rabinWordG K i)) = inlT (ιM1_A (g1 i)) := by
        unfold rabinWordG g1
        split_ifs with h0 h1 h2
        · simp
        · simp [freeGroup_mk_wordOf, hgenX, ιK_T, ιK_A]
        · simp [freeGroup_mk_wordOf, hgenZ]
        · simp [freeGroup_mk_wordOf, hgenD]
      simp only [rabinERelator, freeGroup_mk_wordRel, freeGroup_mk_wordConjL, freeGroup_mk_append,
        freeGroup_mk_wordInv, freeGroup_mk_wordPow, freeGroup_mk_wordOf, map_mul, map_inv,
        map_pow, FreeGroup.lift_apply_of, hgenE, hgenF, hgenB, hg_map]
      rw [mul_inv_eq_one]
      have hconj := HNNExtension.equiv_eq_conj (φ := φ2)
        ⟨rabinP b1 i, ⟨FreeGroup.of i, by simp [pHom]⟩⟩
      rw [hφ2_of i] at hconj
      have hconjT := congrArg inlT hconj.symm
      have hfpow : ∀ k : ℕ, (inlT (HNNExtension.of f2)) ^ k =
          inlT (HNNExtension.of (f2 ^ (k : ℤ))) := fun k => by
        simp [← map_pow, zpow_natCast]
      have hfinv : ∀ k : ℕ, ((inlT (HNNExtension.of f2)) ^ k)⁻¹ =
          inlT (HNNExtension.of (f2 ^ (-(k : ℤ)))) := fun k => by
        simp [← map_pow, ← map_inv, zpow_neg, zpow_natCast]
      rw [hfinv, hfpow]
      simpa only [rabinP, rabinQ, eA, bA, b2, ιM1_A, f2, MonoidHom.comp_apply, map_mul, map_inv]
        using hconjT
  let ψ : (rabinPres K w).Group →* T := (rabinPres K w).lift genMap hrels
  have hcomp : ψ.comp (rabinIncl K w) = ιK_T := by
    apply FinPres.hom_ext
    intro i
    simp [ψ, hgenX]
  have hιK_inj : Function.Injective ιK_T :=
    (amalgamInl_injective pairA.range pairB.range θ).comp <|
      (HNNExtension.of_injective φ2).comp <|
        Coprod.inl_injective.comp <|
          (HNNExtension.of_injective φ1).comp <|
            Coprod.inl_injective.comp Coprod.inl_injective
  intro x y hxy
  apply hιK_inj
  have h1 := congrArg (fun f => f x) hcomp
  have h2 := congrArg (fun f => f y) hcomp
  simp only [MonoidHom.comp_apply] at h1 h2
  rw [← h1, ← h2, hxy]

end RabinEmbed

end Adian
