module

public import Adian.FinPres
public import Adian.NovikovBoone
public import Adian.Rabin

/-!
# The Adian–Rabin Theorem

This file proves the **Adian–Rabin theorem** (Adian 1955, Rabin 1958): no Markov property of
finitely presented groups is algorithmically decidable.

## Main Definitions and Theorems

- `GroupProp`: an abstract property of groups (`∀ (G : Type) [Group G], Prop`).
- `GroupProp.IsAbstract`: invariance under group isomorphism (`G ≃* H → (P G ↔ P H)`).
- `IsMarkovProperty`: an abstract property satisfied by some finitely presented group `Π₁.Group`
  and failing for every finitely presented group into which some finitely presented group `Π₂.Group`
  embeds.
- `adian_rabin_of_undecidable_word_problem`: reduces the word problem of any finite presentation
  `H` to deciding any Markov property `P` on `FinPres`.
- `adian_rabin`: the unconditional Adian–Rabin theorem, instantiating `H` via `novikov_boone`.
- Concrete undecidability corollaries:
  - `undecidable_trivial` (triviality)
  - `undecidable_finite` (finiteness)
  - `undecidable_abelian` (commutativity / abelianness)
  - `undecidable_torsionFree` (torsion-freeness)
  - `undecidable_free` (being a free group)
-/

@[expose] public section

open Monoid

namespace Adian

/-! ### Part 1: Markov Properties and the Adian–Rabin Theorem -/

/-- A property of groups (living in `Type`). -/
abbrev GroupProp : Type 1 := ∀ (G : Type) [Group G], Prop

/-- A group property is abstract if it is invariant under group isomorphism. -/
def GroupProp.IsAbstract (P : GroupProp) : Prop :=
  ∀ {G H : Type} [Group G] [Group H], (G ≃* H) → (P G ↔ P H)

/-- A **Markov property** of finitely presented groups:
1. It is invariant under group isomorphism (`abstract`).
2. Some finitely presented group satisfies `P` (`exists_pos`).
3. Some finitely presented group `Π₂.Group` cannot embed into any finitely presented group
   satisfying `P` (`exists_neg`). -/
structure IsMarkovProperty (P : GroupProp) : Prop where
  abstract : P.IsAbstract
  exists_pos : ∃ F₁ : FinPres, P F₁.Group
  exists_neg : ∃ F₂ : FinPres,
    ∀ (G : Type) [Group G], Group.IsFinitelyPresented G →
      (∃ f : F₂.Group →* G, Function.Injective f) → ¬ P G

private noncomputable def coprodSubsingletonLeftEquiv (A B : Type*) [Group A] [Group B]
    [Subsingleton A] : Coprod A B ≃* B := by
  let toFun : Coprod A B →* B := Coprod.lift (1 : A →* B) (MonoidHom.id B)
  let invFun : B →* Coprod A B := Coprod.inr
  refine MonoidHom.toMulEquiv toFun invFun ?_ ?_
  · apply Coprod.hom_ext
    · apply MonoidHom.ext; intro a
      have ha : a = 1 := Subsingleton.elim a 1
      subst ha
      simp [toFun, invFun]
    · apply MonoidHom.ext; intro b
      simp [toFun, invFun]
  · apply MonoidHom.ext; intro b
    simp [toFun, invFun]

/-- Conditional Adian–Rabin reduction: if `H` is a finite presentation with undecidable word
problem, then no Markov property is decidable on `FinPres`. -/
theorem adian_rabin_of_undecidable_word_problem (H : FinPres)
    (hH : ¬ ComputablePred (fun w : List (Fin H.numGens × Bool) => H.mkWord w = 1))
    (P : GroupProp) (hP : IsMarkovProperty P) :
    ¬ ComputablePred (fun F : FinPres => P F.Group) := by
  obtain ⟨F₁, hF₁⟩ := hP.exists_pos
  obtain ⟨F₂, hF₂⟩ := hP.exists_neg
  let K : FinPres := H.coprod F₂
  let castW : List (Fin H.numGens × Bool) → List (Fin K.numGens × Bool) :=
    mapWord (Fin.castAdd F₂.numGens)
  let Ψ : List (Fin H.numGens × Bool) → FinPres := fun w => (rabinPres K (castW w)).coprod F₁
  have hcast_prim : Primrec castW := by
    unfold castW mapWord
    exact Primrec.list_map Primrec.id
      (Primrec.to₂ (Primrec.pair
        ((Primrec.dom_finite (Fin.castAdd F₂.numGens)).comp (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd)))
  have hΨ_prim : Primrec Ψ :=
    FinPres.primrec_coprod.comp ((primrec_rabinPres K).comp hcast_prim) (Primrec.const F₁)
  have hmk_cast : ∀ w : List (Fin H.numGens × Bool),
      K.mkWord (castW w) = 1 ↔ H.mkWord w = 1 := by
    intro w
    have hcomp :
        (FinPres.coprodEquiv H F₂).toMonoidHom.comp
          ((PresentedGroup.mk K.relSet).comp (FreeGroup.map (Fin.castAdd F₂.numGens))) =
        Coprod.inl.comp (PresentedGroup.mk H.relSet) := by
      apply FreeGroup.ext_hom
      intro i
      change FinPres.coprodEquiv H F₂ (K.ofGen (Fin.castAdd F₂.numGens i)) = Coprod.inl (H.ofGen i)
      exact FinPres.coprodEquiv_ofGen_castAdd H F₂ i
    have heval : FinPres.coprodEquiv H F₂ (K.mkWord (castW w)) = Coprod.inl (H.mkWord w) := by
      change FinPres.coprodEquiv H F₂ (PresentedGroup.mk K.relSet (FreeGroup.mk (castW w))) = _
      rw [show FreeGroup.mk (castW w) = FreeGroup.map (Fin.castAdd F₂.numGens) (FreeGroup.mk w) from
        freeGroup_mk_mapWord _ _]
      exact congrArg (fun φ => φ (FreeGroup.mk w)) hcomp
    rw [← (FinPres.coprodEquiv H F₂).map_eq_one_iff, heval]
    exact ⟨fun h => Coprod.inl_injective (h.trans (map_one _).symm), fun h => by rw [h, map_one]⟩
  have hiff : ∀ w : List (Fin H.numGens × Bool), H.mkWord w = 1 ↔ P (Ψ w).Group := by
    intro w
    constructor
    · intro hw
      have hKw : K.mkWord (castW w) = 1 := (hmk_cast w).mpr hw
      have : Subsingleton (rabinPres K (castW w)).Group :=
        rabinPres_subsingleton_of_eq_one K (castW w) hKw
      let e : (Ψ w).Group ≃* F₁.Group :=
        (FinPres.coprodEquiv (rabinPres K (castW w)) F₁).trans
          (coprodSubsingletonLeftEquiv (rabinPres K (castW w)).Group F₁.Group)
      exact (hP.abstract e).mpr hF₁
    · intro hPΨ
      by_contra hne
      have hKne : K.mkWord (castW w) ≠ 1 := mt (hmk_cast w).mp hne
      let f₁ : F₂.Group →* K.Group :=
        (FinPres.coprodEquiv H F₂).symm.toMonoidHom.comp Coprod.inr
      let f₂ : K.Group →* (rabinPres K (castW w)).Group := rabinIncl K (castW w)
      let f₃ : (rabinPres K (castW w)).Group →* (Ψ w).Group :=
        (FinPres.coprodEquiv (rabinPres K (castW w)) F₁).symm.toMonoidHom.comp Coprod.inl
      have hf₁ : Function.Injective f₁ :=
        ((FinPres.coprodEquiv H F₂).symm.injective).comp Coprod.inr_injective
      have hf₂ : Function.Injective f₂ := rabinIncl_injective_of_ne_one K (castW w) hKne
      have hf₃ : Function.Injective f₃ :=
        ((FinPres.coprodEquiv (rabinPres K (castW w)) F₁).symm.injective).comp Coprod.inl_injective
      have hf_inj : Function.Injective (f₃.comp (f₂.comp f₁)) := hf₃.comp (hf₂.comp hf₁)
      exact hF₂ (Ψ w).Group (FinPres.isFinitelyPresented (Ψ w)) ⟨f₃.comp (f₂.comp f₁), hf_inj⟩ hPΨ
  exact not_computablePred_of_reduction hΨ_prim.to_comp hiff hH

/-- **The Adian–Rabin Theorem**: No Markov property of finitely presented groups is decidable. -/
theorem adian_rabin (P : GroupProp) (hP : IsMarkovProperty P) :
    ¬ ComputablePred (fun F : FinPres => P F.Group) := by
  obtain ⟨H, hH⟩ := novikov_boone
  exact adian_rabin_of_undecidable_word_problem H hH P hP

/-! ### Part 2: Standard Witness Presentations and Concrete Corollaries -/

/-- Presentation `⟨ | ⟩` of the trivial group. -/
abbrev trivialPres : FinPres := ⟨0, []⟩

theorem trivialPres_subsingleton : Subsingleton trivialPres.Group := by
  have hid : MonoidHom.id trivialPres.Group = (1 : trivialPres.Group →* trivialPres.Group) := by
    apply FinPres.hom_ext
    intro i
    exact i.elim0
  exact ⟨fun x y => by
    have hx : x = 1 := congrArg (fun φ => φ x) hid
    have hy : y = 1 := congrArg (fun φ => φ y) hid
    rw [hx, hy]⟩

/-- Presentation `⟨ a | ⟩` of the infinite cyclic group `ℤ`. -/
abbrev intPres : FinPres := ⟨1, []⟩

theorem intPres_ofGen_pow_injective :
    Function.Injective (fun n : ℕ => intPres.ofGen (0 : Fin 1) ^ n) := by
  let φ : intPres.Group →* Multiplicative ℤ :=
    intPres.lift (fun _ => Multiplicative.ofAdd (1 : ℤ)) (fun _ hr => by cases hr)
  intro m n hmn
  have h1 := congrArg φ hmn
  simp only [map_pow, φ, FinPres.lift_ofGen, ← ofAdd_nsmul, nsmul_eq_mul, mul_one] at h1
  have h2 : (m : ℤ) = (n : ℤ) := Multiplicative.ofAdd.injective h1
  omega

/-- Presentation `⟨ a, b | ⟩` of the free group `F₂` of rank 2. -/
abbrev free2Pres : FinPres := ⟨2, []⟩

theorem free2Pres_not_comm :
    free2Pres.ofGen (0 : Fin 2) * free2Pres.ofGen (1 : Fin 2) ≠
      free2Pres.ofGen (1 : Fin 2) * free2Pres.ofGen (0 : Fin 2) := by
  let s01 : Equiv.Perm (Fin 3) := Equiv.swap 0 1
  let s12 : Equiv.Perm (Fin 3) := Equiv.swap 1 2
  let φ : free2Pres.Group →* Equiv.Perm (Fin 3) :=
    free2Pres.lift (fun i => if i.val = 0 then s01 else s12) (fun _ hr => by cases hr)
  intro heq
  have h1 := congrArg (fun g => (φ g) 0) heq
  simp only [map_mul, φ, FinPres.lift_ofGen, Equiv.Perm.mul_apply, s01, s12] at h1
  change (Equiv.swap (0 : Fin 3) 1) (Equiv.swap (1 : Fin 3) 2 0) =
    (Equiv.swap (1 : Fin 3) 2) (Equiv.swap (0 : Fin 3) 1 0) at h1
  revert h1
  decide

/-- Presentation `⟨ a | a² ⟩` of `ℤ / 2ℤ`. -/
abbrev zmod2Pres : FinPres := ⟨1, [wordPow (wordOf (0 : Fin 1)) 2]⟩

theorem zmod2Pres_gen_ne_one : zmod2Pres.ofGen (0 : Fin 1) ≠ 1 := by
  let φ : zmod2Pres.Group →* ℤˣ :=
    zmod2Pres.lift (fun _ => (-1 : ℤˣ)) fun r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      simp [freeGroup_mk_wordPow, freeGroup_mk_wordOf]
  intro h1
  have h2 := congrArg φ h1
  simp [φ] at h2

theorem zmod2Pres_gen_sq : zmod2Pres.ofGen (0 : Fin 1) ^ (2 : ℕ) = 1 := by
  have h := zmod2Pres.mkWord_eq_one_of_mem (r := wordPow (wordOf (0 : Fin 1)) 2)
    (List.mem_singleton_self _)
  simp only [FinPres.mkWord, freeGroup_mk_wordPow, freeGroup_mk_wordOf, map_pow] at h
  exact h

private theorem freeGroup_mk_eq_one_of_sq {ι : Type*} :
    ∀ (n : ℕ) (l : List (ι × Bool)),
      l.length = n → FreeGroup.IsReduced l → FreeGroup.mk l * FreeGroup.mk l = 1 →
        FreeGroup.mk l = 1 := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro l hn hl_red hmul
    cases l with
    | nil => rfl
    | cons a rest =>
      cases rest using List.reverseRecOn with
      | nil =>
        have hred2 : FreeGroup.IsReduced [a, a] := by
          simp [FreeGroup.IsReduced]
        have hsq : FreeGroup.mk [a, a] = 1 := by
          change FreeGroup.mk ([a] ++ [a]) = 1
          rw [freeGroup_mk_append]
          exact hmul
        have htw := congrArg FreeGroup.toWord hsq
        rw [FreeGroup.toWord_mk, hred2.reduce_eq, FreeGroup.toWord_one] at htw
        simp at htw
      | append_singleton mid b =>
        by_cases hinv : b = (a.1, !a.2)
        · subst hinv
          have hmid_red : FreeGroup.IsReduced mid := by
            have h1 : List.IsChain (fun x y : ι × Bool => x.1 = y.1 → x.2 = y.2)
                (mid ++ [(a.1, !a.2)]) := hl_red.tail
            exact (List.isChain_append.1 h1).1
          let ga : FreeGroup ι := FreeGroup.mk [a]
          let w' : FreeGroup ι := FreeGroup.mk mid
          have hfa : FreeGroup.mk [(a.1, !a.2)] = ga⁻¹ := by
            rcases a with ⟨x, s⟩; cases s <;> rfl
          have hw_eq : FreeGroup.mk (a :: (mid ++ [(a.1, !a.2)])) = ga * w' * ga⁻¹ := by
            rw [show a :: (mid ++ [(a.1, !a.2)]) = [a] ++ mid ++ [(a.1, !a.2)] by simp,
              freeGroup_mk_append, freeGroup_mk_append, hfa]
          have hw'_sq : w' * w' = 1 := by
            rw [hw_eq] at hmul
            have h1 : ga * (w' * w') * ga⁻¹ = 1 := by
              calc ga * (w' * w') * ga⁻¹
                  = (ga * w' * ga⁻¹) * (ga * w' * ga⁻¹) := by group
                _ = 1 := hmul
            have h2 := congrArg (fun z => ga⁻¹ * z * ga) h1
            simpa [mul_assoc] using h2
          have hw'_one : w' = 1 :=
            ih mid.length (by rw [← hn]; simp) mid rfl hmid_red hw'_sq
          rw [hw_eq, hw'_one, mul_one, mul_inv_cancel]
        · have hne_inv : ¬ (b.1 = a.1 ∧ b.2 = !a.2) := by
            rintro ⟨h1, h2⟩
            exact hinv (Prod.ext h1 h2)
          let full : List (ι × Bool) := a :: (mid ++ [b])
          have hred_app : FreeGroup.IsReduced (full ++ full) := by
            rw [FreeGroup.IsReduced, List.isChain_append]
            refine ⟨hl_red, hl_red, ?_⟩
            intro x hx y hy
            have hlast : full.getLast? = some b := by
              simp [full, List.getLast?_cons_of_ne_nil]
            have hx_eq : x = b := by
              rw [hlast] at hx
              exact Option.some.inj hx.symm
            have hy_eq : y = a := by
              simp only [full, List.head?_cons, Option.mem_def, Option.some.injEq] at hy
              exact hy.symm
            rw [hx_eq, hy_eq]
            intro h1
            cases ha : a.2 <;> cases hb : b.2 <;> simp_all
          have hsq : FreeGroup.mk (full ++ full) = 1 := by
            rw [freeGroup_mk_append]
            exact hmul
          have htw := congrArg FreeGroup.toWord hsq
          rw [FreeGroup.toWord_mk, hred_app.reduce_eq, FreeGroup.toWord_one] at htw
          simp [full] at htw

/-- No free group contains a nontrivial element of order 2. -/
theorem freeGroup_eq_one_of_sq_eq_one {ι : Type*} (w : FreeGroup ι) (hw : w ^ (2 : ℕ) = 1) :
    w = 1 := by
  classical
  have hmul : FreeGroup.mk w.toWord * FreeGroup.mk w.toWord = 1 := by
    rw [FreeGroup.mk_toWord]
    simpa [sq] using hw
  have h1 := freeGroup_mk_eq_one_of_sq w.toWord.length w.toWord rfl FreeGroup.isReduced_toWord hmul
  rwa [FreeGroup.mk_toWord] at h1

/-- **Corollary 1**: Triviality of finitely presented groups is undecidable. -/
theorem undecidable_trivial :
    ¬ ComputablePred (fun F : FinPres => Subsingleton F.Group) := by
  refine adian_rabin (fun G _ => Subsingleton G) ⟨?_, ?_, ?_⟩
  · intro G H _ _ e
    exact ⟨fun _ => e.symm.injective.subsingleton, fun _ => e.injective.subsingleton⟩
  · exact ⟨trivialPres, trivialPres_subsingleton⟩
  · refine ⟨intPres, fun G _ _ ⟨f, hf⟩ hsub => ?_⟩
    have h01 : intPres.ofGen (0 : Fin 1) ^ 0 = intPres.ofGen (0 : Fin 1) ^ 1 :=
      hf (Subsingleton.elim _ _)
    have := intPres_ofGen_pow_injective h01
    omega

/-- **Corollary 2**: Finiteness of finitely presented groups is undecidable. -/
theorem undecidable_finite :
    ¬ ComputablePred (fun F : FinPres => Finite F.Group) := by
  refine adian_rabin (fun G _ => Finite G) ⟨?_, ?_, ?_⟩
  · intro G H _ _ e
    exact ⟨fun _ => Finite.of_equiv G e.toEquiv, fun _ => Finite.of_equiv H e.symm.toEquiv⟩
  · have := trivialPres_subsingleton
    exact ⟨trivialPres, Finite.of_subsingleton⟩
  · refine ⟨intPres, fun G _ _ ⟨f, hf⟩ hfin => ?_⟩
    have hinf : Infinite G :=
      Infinite.of_injective (fun n : ℕ => f (intPres.ofGen (0 : Fin 1) ^ n))
        (hf.comp intPres_ofGen_pow_injective)
    exact not_finite_iff_infinite.mpr hinf hfin

/-- **Corollary 3**: Abelianness (commutativity) of finitely presented groups is undecidable. -/
theorem undecidable_abelian :
    ¬ ComputablePred (fun F : FinPres => ∀ x y : F.Group, x * y = y * x) := by
  refine adian_rabin (fun G _ => ∀ x y : G, x * y = y * x) ⟨?_, ?_, ?_⟩
  · intro G H _ _ e
    constructor
    · intro hG x y
      have := congrArg e (hG (e.symm x) (e.symm y))
      simpa using this
    · intro hH x y
      have := congrArg e.symm (hH (e x) (e y))
      simpa using this
  · have := trivialPres_subsingleton
    exact ⟨trivialPres, fun x y => Subsingleton.elim _ _⟩
  · refine ⟨free2Pres, fun G _ _ ⟨f, hf⟩ hab => ?_⟩
    apply free2Pres_not_comm
    apply hf
    rw [map_mul, map_mul]
    exact hab _ _

/-- **Corollary 4**: Torsion-freeness of finitely presented groups is undecidable. -/
theorem undecidable_torsionFree :
    ¬ ComputablePred (fun F : FinPres => ∀ g : F.Group, g ≠ 1 → ∀ n : ℕ, 0 < n → g ^ n ≠ 1) := by
  refine adian_rabin (fun G _ => ∀ g : G, g ≠ 1 → ∀ n : ℕ, 0 < n → g ^ n ≠ 1) ⟨?_, ?_, ?_⟩
  · intro G H _ _ e
    constructor
    · intro hG g hg n hn hgn
      apply hG (e.symm g) (fun h => hg (by simpa using congrArg e h)) n hn
      rw [← map_pow, hgn, map_one]
    · intro hH g hg n hn hgn
      apply hH (e g) (fun h => hg (by simpa using congrArg e.symm h)) n hn
      rw [← map_pow, hgn, map_one]
  · have := trivialPres_subsingleton
    exact ⟨trivialPres, fun g hg => (hg (Subsingleton.elim g 1)).elim⟩
  · refine ⟨zmod2Pres, fun G _ _ ⟨f, hf⟩ htf => ?_⟩
    have hne : f (zmod2Pres.ofGen (0 : Fin 1)) ≠ 1 := fun h =>
      zmod2Pres_gen_ne_one (hf (h.trans (map_one f).symm))
    apply htf _ hne 2 (by omega)
    rw [← map_pow, zmod2Pres_gen_sq, map_one]

/-- **Corollary 5**: Being a free group is undecidable for finitely presented groups. -/
theorem undecidable_free :
    ¬ ComputablePred (fun F : FinPres => ∃ ι : Type, Nonempty (F.Group ≃* FreeGroup ι)) := by
  refine adian_rabin (fun G _ => ∃ ι : Type, Nonempty (G ≃* FreeGroup ι)) ⟨?_, ?_, ?_⟩
  · intro G H _ _ e
    exact ⟨fun ⟨ι, ⟨eG⟩⟩ => ⟨ι, ⟨e.symm.trans eG⟩⟩, fun ⟨ι, ⟨eH⟩⟩ => ⟨ι, ⟨e.trans eH⟩⟩⟩
  · have := trivialPres_subsingleton
    have : Subsingleton (FreeGroup PEmpty) := by
      have hid : MonoidHom.id (FreeGroup PEmpty) = (1 : FreeGroup PEmpty →* FreeGroup PEmpty) := by
        apply FreeGroup.ext_hom
        intro i; exact i.elim
      exact ⟨fun x y => by
        have hx : x = 1 := congrArg (fun φ => φ x) hid
        have hy : y = 1 := congrArg (fun φ => φ y) hid
        rw [hx, hy]⟩
    refine ⟨trivialPres, PEmpty, ⟨{
      toFun := fun _ => 1
      invFun := fun _ => 1
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun _ => Subsingleton.elim _ _
      map_mul' := fun _ _ => Subsingleton.elim _ _ }⟩⟩
  · refine ⟨zmod2Pres, fun G _ _ ⟨f, hf⟩ ⟨ι, ⟨e⟩⟩ => ?_⟩
    have hsq : (e (f (zmod2Pres.ofGen (0 : Fin 1)))) ^ (2 : ℕ) = 1 := by
      rw [← map_pow, ← map_pow, zmod2Pres_gen_sq, map_one, map_one]
    have h1 := freeGroup_eq_one_of_sq_eq_one _ hsq
    have h2 : f (zmod2Pres.ofGen (0 : Fin 1)) = 1 := e.injective (h1.trans (map_one e).symm)
    exact zmod2Pres_gen_ne_one (hf (h2.trans (map_one f).symm))

end Adian
