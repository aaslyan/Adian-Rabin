module

public import Adian.FinPres
public import Adian.MultiHNN
public import Adian.FreeProductLemmas
public import Adian.ModularMachine

/-!
# The Novikov–Boone Theorem via the Aanderaa–Cohen Modular Machine Group

Given a deterministic modular machine `M` (from `Adian/ModularMachine.lean`), we build the
Aanderaa–Cohen finitely presented group `modPres M` as a 2-layer HNN extension over
`ModBase = (ℤ × ℤ) ∗ ℤ`:

1. **Layer 1 (`ModH1 M`)**: Multi-letter HNN extension `MultiHNN (modHNNData M)` with one stable
   letter `r_i` per quadruple `q_i = (a_i, b_i, c_i, dir_i)` of `M`, associating the isomorphic
   subgroups `α_i(ModBase)` and `β_i(ModBase)` so that
   `r_i * t_{(u*m + a_i, v*m + b_i)} * r_i⁻¹ = t_{q_i.applyPair u v}`.
2. **Layer 2 (`ModGroup M`)**: Single HNN extension of `ModH1 M` with stable letter `k` commuting
   with `t` and every `r_i`.

Using `kerProjBasis`, `map_mem_closure_of_iff`, `rule_reachesZero_iff`, and Multi-Letter Britton's
Lemma (`MultiHNN.exists_pinch_of_mem_of_range`), we prove:
`[k, t_{(α, β)}] = 1` in `ModGroup M` iff `(α, β) ∈ ReachesZero M`.

Combining this with `exists_undecidable_modularMachine` yields the unconditional **Novikov–Boone
theorem**: there exists a finite presentation `P : FinPres` with undecidable word problem.
-/

@[expose] public section

open Monoid Subgroup

namespace Adian

noncomputable section

/-! ### Part 1: Injective Endomorphisms of `ModBase` for Modular Rules -/

/-- Scaling homomorphism `(u, v) ↦ (u * k₁, v * k₂)` on `Multiplicative (ℤ × ℤ)`. -/
def scaleZ2 (k₁ k₂ : ℤ) : Multiplicative (ℤ × ℤ) →* Multiplicative (ℤ × ℤ) where
  toFun x := Multiplicative.ofAdd ((Multiplicative.toAdd x).1 * k₁, (Multiplicative.toAdd x).2 * k₂)
  map_one' := by
    change Multiplicative.ofAdd ((0 : ℤ) * k₁, (0 : ℤ) * k₂) = 1
    simp
  map_mul' x y := by
    change Multiplicative.ofAdd
      (((Multiplicative.toAdd x).1 + (Multiplicative.toAdd y).1) * k₁,
       ((Multiplicative.toAdd x).2 + (Multiplicative.toAdd y).2) * k₂) = _
    rw [← ofAdd_add]
    congr 1
    ext <;> dsimp <;> ring

theorem scaleZ2_injective {k₁ k₂ : ℤ} (h₁ : k₁ ≠ 0) (h₂ : k₂ ≠ 0) :
    Function.Injective (scaleZ2 k₁ k₂) := by
  intro x y hxy
  have h := Multiplicative.ofAdd.injective hxy
  simp only [Prod.mk.injEq] at h
  apply Multiplicative.toAdd.injective
  exact Prod.ext (mul_right_cancel₀ h₁ h.1) (mul_right_cancel₀ h₂ h.2)

/-- Scaling homomorphism on `ModBase` fixing the `t` factor. -/
def scaleModBase (k₁ k₂ : ℤ) : ModBase →* ModBase :=
  Coprod.map (scaleZ2 k₁ k₂) (MonoidHom.id (Multiplicative ℤ))

theorem scaleModBase_injective {k₁ k₂ : ℤ} (h₁ : k₁ ≠ 0) (h₂ : k₂ ≠ 0) :
    Function.Injective (scaleModBase k₁ k₂) :=
  coprod_map_injective (scaleZ2 k₁ k₂) (MonoidHom.id (Multiplicative ℤ))
    (scaleZ2_injective h₁ h₂) Function.injective_id

/-- Conjugated scaling endomorphism `x ↦ (mbG p)⁻¹ * scaleModBase k₁ k₂ x * mbG p` of `ModBase`. -/
def conjModBase (p : ℤ × ℤ) (k₁ k₂ : ℤ) : ModBase →* ModBase :=
  (MulAut.conj (mbG p)⁻¹).toMonoidHom.comp (scaleModBase k₁ k₂)

theorem conjModBase_injective (p : ℤ × ℤ) {k₁ k₂ : ℤ} (h₁ : k₁ ≠ 0) (h₂ : k₂ ≠ 0) :
    Function.Injective (conjModBase p k₁ k₂) :=
  (MulEquiv.injective (MulAut.conj (mbG p)⁻¹)).comp (scaleModBase_injective h₁ h₂)

theorem conjModBase_mbG (p : ℤ × ℤ) (k₁ k₂ : ℤ) (q : ℤ × ℤ) :
    conjModBase p k₁ k₂ (mbG q) = mbG (q.1 * k₁, q.2 * k₂) := by
  change (mbG p)⁻¹ * Coprod.inl (scaleZ2 k₁ k₂ (Multiplicative.ofAdd q)) * ((mbG p)⁻¹)⁻¹ = _
  rw [inv_inv]
  have hs : Coprod.inl (scaleZ2 k₁ k₂ (Multiplicative.ofAdd q)) =
      (mbG (q.1 * k₁, q.2 * k₂) : ModBase) := rfl
  rw [hs, ← mbG_neg, ← mbG_add, ← mbG_add]
  congr 1
  ext <;> dsimp <;> omega

theorem conjModBase_mbT (p : ℤ × ℤ) (k₁ k₂ : ℤ) :
    conjModBase p k₁ k₂ mbT = mbConjT p := by
  change (mbG p)⁻¹ * Coprod.inr (Multiplicative.ofAdd (1 : ℤ)) * ((mbG p)⁻¹)⁻¹ = _
  rw [inv_inv]
  rfl

theorem conjModBase_mbConjT (p : ℤ × ℤ) (k₁ k₂ : ℤ) (q : ℤ × ℤ) :
    conjModBase p k₁ k₂ (mbConjT q) = mbConjT (q.1 * k₁ + p.1, q.2 * k₂ + p.2) := by
  simp only [mbConjT, map_mul, map_inv, conjModBase_mbG, conjModBase_mbT]
  simp only [← mbG_neg, mul_assoc]
  rw [← mul_assoc (mbG _), ← mbG_add, ← mbG_add]
  congr 1
  · congr 1; ext <;> dsimp <;> omega
  · congr 1; congr 1; ext <;> dsimp <;> omega

theorem mbProj_conjModBase (p : ℤ × ℤ) (k₁ k₂ : ℤ) (h : ModBase) :
    mbProj (conjModBase p k₁ k₂ h) = scaleZ2 k₁ k₂ (mbProj h) := by
  have hhom : mbProj.comp (conjModBase p k₁ k₂) = (scaleZ2 k₁ k₂).comp mbProj := by
    apply Coprod.hom_ext
    · apply MonoidHom.ext; intro x
      simp only [MonoidHom.comp_apply]
      have hx : Coprod.inl x = mbG (Multiplicative.toAdd x) := rfl
      rw [hx, conjModBase_mbG, mbProj_mbG, mbProj_mbG]
      rfl
    · apply MonoidHom.ext; intro y
      simp only [MonoidHom.comp_apply]
      have hs : scaleModBase k₁ k₂ (Coprod.inr y) = Coprod.inr y := by
        simp [scaleModBase, Coprod.map]
      have hp_inr : mbProj (Coprod.inr y) = 1 := by
        simp [mbProj, Coprod.fst]
      change mbProj ((mbG p)⁻¹ * scaleModBase k₁ k₂ (Coprod.inr y) * ((mbG p)⁻¹)⁻¹) = _
      rw [hs, inv_inv, map_mul, map_mul, map_inv, hp_inr, mul_one, inv_mul_cancel, map_one]
  exact congrArg (fun f => f h) hhom

theorem conjModBase_mbConjTHom (p : ℤ × ℤ) (k₁ k₂ : ℤ) (w : FreeGroup (ℤ × ℤ)) :
    conjModBase p k₁ k₂ (mbConjTHom w) =
      mbConjTHom (FreeGroup.map (fun q : ℤ × ℤ => (q.1 * k₁ + p.1, q.2 * k₂ + p.2)) w) := by
  have hhom : (conjModBase p k₁ k₂).comp mbConjTHom =
      mbConjTHom.comp (FreeGroup.map fun q : ℤ × ℤ => (q.1 * k₁ + p.1, q.2 * k₂ + p.2)) := by
    apply FreeGroup.ext_hom
    intro q
    simp only [MonoidHom.comp_apply, FreeGroup.map.of, mbConjTHom, FreeGroup.lift_apply_of]
    exact conjModBase_mbConjT p k₁ k₂ q
  exact congrArg (fun f => f w) hhom

/-! ### Part 2: The Aanderaa–Cohen 2-Layer HNN Group `ModGroup M` -/

section ModGroupDef

variable (M : ModularMachine)

private theorem modM_ne_zero : (M.m : ℤ) ≠ 0 := by
  have := M.hm; omega

private theorem modM_sq_ne_zero : ((M.m * M.m : ℕ) : ℤ) ≠ 0 := by
  have := M.hm; positivity

/-- Domain endomorphism `α_i : ModBase →* ModBase` for the `i`-th rule of `M`. -/
def modAlpha (i : Fin M.rules.length) : ModBase →* ModBase :=
  let q := M.rules[i]
  conjModBase ((q.a : ℤ), (q.b : ℤ)) (M.m : ℤ) (M.m : ℤ)

/-- Codomain endomorphism `β_i : ModBase →* ModBase` for the `i`-th rule of `M`. -/
def modBeta (i : Fin M.rules.length) : ModBase →* ModBase :=
  match M.rules[i.val].dir with
  | .R => conjModBase ((M.rules[i.val].c : ℤ), 0) ((M.m * M.m : ℕ) : ℤ) 1
  | .L => conjModBase (0, (M.rules[i.val].c : ℤ)) 1 ((M.m * M.m : ℕ) : ℤ)

theorem modAlpha_injective (i : Fin M.rules.length) : Function.Injective (modAlpha M i) :=
  conjModBase_injective _ (modM_ne_zero M) (modM_ne_zero M)

theorem modBeta_injective (i : Fin M.rules.length) : Function.Injective (modBeta M i) := by
  unfold modBeta
  cases M.rules[i.val].dir
  · exact conjModBase_injective _ (modM_sq_ne_zero M) one_ne_zero
  · exact conjModBase_injective _ one_ne_zero (modM_sq_ne_zero M)

/-- Coordinate map `fA_i(u, v) = (u * m + a_i, v * m + b_i)` corresponding to `modAlpha M i`. -/
def modFA (i : Fin M.rules.length) (p : ℤ × ℤ) : ℤ × ℤ :=
  (p.1 * (M.m : ℤ) + (M.rules[i.val].a : ℤ), p.2 * (M.m : ℤ) + (M.rules[i.val].b : ℤ))

/-- Coordinate map `fB_i(u, v) = q_i.applyPair u v` corresponding to `modBeta M i`. -/
def modFB (i : Fin M.rules.length) (p : ℤ × ℤ) : ℤ × ℤ :=
  M.rules[i.val].applyPair p.1 p.2

theorem modFA_injective (i : Fin M.rules.length) : Function.Injective (modFA M i) := by
  intro ⟨u₁, v₁⟩ ⟨u₂, v₂⟩ h
  simp only [modFA, Prod.mk.injEq] at h
  have h1 : u₁ * (M.m : ℤ) = u₂ * (M.m : ℤ) := by omega
  have h2 : v₁ * (M.m : ℤ) = v₂ * (M.m : ℤ) := by omega
  exact Prod.ext (mul_right_cancel₀ (modM_ne_zero M) h1) (mul_right_cancel₀ (modM_ne_zero M) h2)

theorem modFB_injective (i : Fin M.rules.length) : Function.Injective (modFB M i) := by
  intro ⟨u₁, v₁⟩ ⟨u₂, v₂⟩ h
  simp only [modFB, ModQuad.applyPair] at h
  cases hdir : M.rules[i.val].dir <;> rw [hdir] at h <;> simp only [Prod.mk.injEq] at h
  · have h1 : u₁ * ((M.m * M.m : ℕ) : ℤ) = u₂ * ((M.m * M.m : ℕ) : ℤ) := by omega
    exact Prod.ext (mul_right_cancel₀ (modM_sq_ne_zero M) h1) h.2
  · have h2 : v₁ * ((M.m * M.m : ℕ) : ℤ) = v₂ * ((M.m * M.m : ℕ) : ℤ) := by omega
    exact Prod.ext h.1 (mul_right_cancel₀ (modM_sq_ne_zero M) h2)

theorem modAlpha_mbConjTHom (i : Fin M.rules.length) (w : FreeGroup (ℤ × ℤ)) :
    modAlpha M i (mbConjTHom w) = mbConjTHom (FreeGroup.map (modFA M i) w) :=
  conjModBase_mbConjTHom _ _ _ w

theorem modBeta_mbConjTHom (i : Fin M.rules.length) (w : FreeGroup (ℤ × ℤ)) :
    modBeta M i (mbConjTHom w) = mbConjTHom (FreeGroup.map (modFB M i) w) := by
  unfold modBeta
  cases hdir : M.rules[i.val].dir with
  | R =>
    rw [conjModBase_mbConjTHom]
    apply congrArg mbConjTHom
    apply congrArg (fun f => FreeGroup.map f w)
    funext ⟨u, v⟩
    simp [modFB, ModQuad.applyPair, hdir]
  | L =>
    rw [conjModBase_mbConjTHom]
    apply congrArg mbConjTHom
    apply congrArg (fun f => FreeGroup.map f w)
    funext ⟨u, v⟩
    simp [modFB, ModQuad.applyPair, hdir]

/-- HNN data for the `i`-th rule of `M` over `ModBase`. -/
def modHNNData (i : Fin M.rules.length) : HNNData ModBase where
  A := (modAlpha M i).range
  B := (modBeta M i).range
  iso :=
    (MulEquiv.ofBijective (modAlpha M i).rangeRestrict
      ⟨fun _ _ h => modAlpha_injective M i (congrArg Subtype.val h),
       (modAlpha M i).rangeRestrict_surjective⟩).symm.trans
    (MulEquiv.ofBijective (modBeta M i).rangeRestrict
      ⟨fun _ _ h => modBeta_injective M i (congrArg Subtype.val h),
       (modBeta M i).rangeRestrict_surjective⟩)

theorem modHNNData_iso_apply (i : Fin M.rules.length) (h : ModBase) :
    ((modHNNData M i).iso ⟨modAlpha M i h, ⟨h, rfl⟩⟩ : ModBase) = modBeta M i h := by
  let eA := MulEquiv.ofBijective (modAlpha M i).rangeRestrict
    ⟨fun _ _ h => modAlpha_injective M i (congrArg Subtype.val h),
     (modAlpha M i).rangeRestrict_surjective⟩
  have h1 : eA.symm ⟨modAlpha M i h, ⟨h, rfl⟩⟩ = h := eA.symm_apply_apply h
  change ((modBeta M i).rangeRestrict (eA.symm ⟨modAlpha M i h, ⟨h, rfl⟩⟩) : ModBase) = _
  rw [h1]; rfl

theorem modHNNData_iso_symm_apply (i : Fin M.rules.length) (h : ModBase) :
    ((modHNNData M i).iso.symm ⟨modBeta M i h, ⟨h, rfl⟩⟩ : ModBase) = modAlpha M i h := by
  have heq := modHNNData_iso_apply M i h
  have hsub : (modHNNData M i).iso ⟨modAlpha M i h, ⟨h, rfl⟩⟩ = ⟨modBeta M i h, ⟨h, rfl⟩⟩ :=
    Subtype.ext heq
  have hsymm := (modHNNData M i).iso.symm_apply_eq.mpr hsub.symm
  exact congrArg Subtype.val hsymm

/-- Layer 1: Multi-letter HNN extension of `ModBase` by the modular rules of `M`. -/
abbrev ModH1 : Type := MultiHNN (modHNNData M)

/-- Subgroup `C = ⟨t, r_0, ..., r_{N-1}⟩ ≤ ModH1 M`. -/
def modC : Subgroup (ModH1 M) :=
  Subgroup.closure ({MultiHNN.of (modHNNData M) mbT} ∪ Set.range (MultiHNN.t (modHNNData M)))

/-- Layer 2: Aanderaa–Cohen group `HNNExtension (ModH1 M) C C id`. -/
abbrev ModGroup : Type :=
  HNNExtension (ModH1 M) (modC M) (modC M) (MulEquiv.refl (modC M))

/-- Canonical inclusion `ModBase →* ModGroup M`. -/
def mgOfBase : ModBase →* ModGroup M :=
  HNNExtension.of.comp (MultiHNN.of (modHNNData M))

/-- Stable letter `k` of `ModGroup M`. -/
def mgK : ModGroup M :=
  HNNExtension.t (φ := MulEquiv.refl (modC M))

/-- Stable letter `r_i` inside `ModGroup M`. -/
def mgR (i : Fin M.rules.length) : ModGroup M :=
  HNNExtension.of (MultiHNN.t (modHNNData M) i)

theorem mgR_conj_modAlpha (i : Fin M.rules.length) (h : ModBase) :
    mgR M i * mgOfBase M (modAlpha M i h) * (mgR M i)⁻¹ = mgOfBase M (modBeta M i h) := by
  have h1 := MultiHNN.equiv_eq_conj (modHNNData M) i ⟨modAlpha M i h, ⟨h, rfl⟩⟩
  rw [modHNNData_iso_apply M i h] at h1
  have h2 := congrArg (HNNExtension.of (φ := MulEquiv.refl (modC M))) h1.symm
  simpa [mgR, mgOfBase, map_mul, map_inv] using h2

theorem mgK_comm_of_mem_modC {x : ModH1 M} (hx : x ∈ modC M) :
    mgK M * HNNExtension.of x * (mgK M)⁻¹ = HNNExtension.of x := by
  have h := HNNExtension.equiv_eq_conj (φ := MulEquiv.refl (modC M)) ⟨x, hx⟩
  simpa [mgK] using h.symm

end ModGroupDef

/-! ### Part 3: Concrete Finite Presentation `modPres M` and Isomorphism -/

section ModPresDef

variable (M : ModularMachine)

/-- Generator index for `x` in `modPres M`. -/
def modGenX : Fin (4 + M.rules.length) := ⟨0, by omega⟩
/-- Generator index for `y` in `modPres M`. -/
def modGenY : Fin (4 + M.rules.length) := ⟨1, by omega⟩
/-- Generator index for `t` in `modPres M`. -/
def modGenT : Fin (4 + M.rules.length) := ⟨2, by omega⟩
/-- Generator index for `k` in `modPres M`. -/
def modGenK : Fin (4 + M.rules.length) := ⟨3, by omega⟩
/-- Generator index for `r_i` in `modPres M`. -/
def modGenR (i : Fin M.rules.length) : Fin (4 + M.rules.length) := ⟨4 + i.val, by omega⟩

/-- The four relators associated to modular rule `i`. -/
def modRuleRelators (i : Fin M.rules.length) : List (List (Fin (4 + M.rules.length) × Bool)) :=
  let q := M.rules[i]
  let m := M.m
  let wX := wordOf (modGenX M)
  let wY := wordOf (modGenY M)
  let wT := wordOf (modGenT M)
  let wK := wordOf (modGenK M)
  let wR := wordOf (modGenR M i)
  [ wordComm wK wR,
    wordRel (wordConjL wR (wordPow wX m))
      (match q.dir with | .R => wordPow wX (m * m) | .L => wX),
    wordRel (wordConjL wR (wordPow wY m))
      (match q.dir with | .R => wY | .L => wordPow wY (m * m)),
    wordRel (wordConjL wR (wordConj (wordPow wX q.a ++ wordPow wY q.b) wT))
      (match q.dir with
       | .R => wordConj (wordPow wX q.c) wT
       | .L => wordConj (wordPow wY q.c) wT) ]

/-- Finite presentation of the Aanderaa–Cohen modular machine group of `M`. -/
abbrev modPres : FinPres where
  numGens := 4 + M.rules.length
  relators :=
    [ wordComm (wordOf (modGenX M)) (wordOf (modGenY M)),
      wordComm (wordOf (modGenK M)) (wordOf (modGenT M)) ] ++
    (List.finRange M.rules.length).flatMap (modRuleRelators M)

/-- Generator map from `modPres M` into `ModGroup M`. -/
def modPresGenMap (idx : Fin (4 + M.rules.length)) : ModGroup M :=
  match h : idx.val with
  | 0 => mgOfBase M mbX
  | 1 => mgOfBase M mbY
  | 2 => mgOfBase M mbT
  | 3 => mgK M
  | n + 4 => mgR M ⟨n, by omega⟩

@[simp] theorem modPresGenMap_X : modPresGenMap M (modGenX M) = mgOfBase M mbX := rfl
@[simp] theorem modPresGenMap_Y : modPresGenMap M (modGenY M) = mgOfBase M mbY := rfl
@[simp] theorem modPresGenMap_T : modPresGenMap M (modGenT M) = mgOfBase M mbT := rfl
@[simp] theorem modPresGenMap_K : modPresGenMap M (modGenK M) = mgK M := rfl
@[simp] theorem modPresGenMap_R (i : Fin M.rules.length) :
    modPresGenMap M (modGenR M i) = mgR M i := by
  simp only [modPresGenMap, modGenR]
  split
  · omega
  · omega
  · omega
  · omega
  · congr 1; apply Fin.ext; dsimp; omega

theorem modPres_relators_hold (r : List (Fin (4 + M.rules.length) × Bool))
    (hr : r ∈ (modPres M).relators) :
    FreeGroup.lift (modPresGenMap M) (FreeGroup.mk r) = 1 := by
  simp only [modPres, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatMap, List.mem_finRange, true_and] at hr
  rcases hr with (rfl | rfl) | ⟨i, hi⟩
  · -- [x, y] = 1
    simp only [freeGroup_mk_wordComm, freeGroup_mk_wordOf, map_mul, map_inv,
      FreeGroup.lift_apply_of, modPresGenMap_X, modPresGenMap_Y]
    have hxy : mbX * mbY * mbX⁻¹ * mbY⁻¹ = 1 := by
      simp only [mbX, mbY, ← mbG_neg, ← mbG_add]
      rw [show (1, 0) + (0, 1) + -(1, 0) + -(0, 1) = ((0, 0) : ℤ × ℤ) by ext <;> decide]
      exact mbG_zero
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, hxy, map_one]
  · -- [k, t] = 1
    simp only [freeGroup_mk_wordComm, freeGroup_mk_wordOf, map_mul, map_inv,
      FreeGroup.lift_apply_of, modPresGenMap_K, modPresGenMap_T]
    have ht : MultiHNN.of (modHNNData M) mbT ∈ modC M :=
      Subgroup.subset_closure (Or.inl rfl)
    have hc := mgK_comm_of_mem_modC M ht
    change mgK M * mgOfBase M mbT * (mgK M)⁻¹ * (mgOfBase M mbT)⁻¹ = 1
    rw [show mgOfBase M mbT = HNNExtension.of (MultiHNN.of (modHNNData M) mbT) from rfl, hc,
      mul_inv_cancel]
  · -- Rule i relators
    simp only [modRuleRelators, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · -- [k, r_i] = 1
      simp only [freeGroup_mk_wordComm, freeGroup_mk_wordOf, map_mul, map_inv,
        FreeGroup.lift_apply_of, modPresGenMap_K, modPresGenMap_R]
      have hri : MultiHNN.t (modHNNData M) i ∈ modC M :=
        Subgroup.subset_closure (Or.inr ⟨i, rfl⟩)
      have hc := mgK_comm_of_mem_modC M hri
      change mgK M * mgR M i * (mgK M)⁻¹ * (mgR M i)⁻¹ = 1
      rw [show mgR M i = HNNExtension.of (MultiHNN.t (modHNNData M) i) from rfl, hc,
        mul_inv_cancel]
    · -- r_i * x^m * r_i⁻¹ = x^(m²) or x
      have hα : modAlpha M i mbX = mbX ^ M.m := by
        have h1 : modAlpha M i mbX = mbG ((M.m : ℤ), 0) := by
          simpa [modAlpha, mbX] using
            conjModBase_mbG ((M.rules[i].a : ℤ), (M.rules[i].b : ℤ)) (M.m : ℤ) (M.m : ℤ) (1, 0)
        rw [h1, mbG_eq_zpow]; simp
      have hconj := mgR_conj_modAlpha M i mbX
      rw [hα, map_pow] at hconj
      simp only [freeGroup_mk_wordRel, freeGroup_mk_wordConjL, freeGroup_mk_wordPow,
        freeGroup_mk_wordOf, map_mul, map_inv, map_pow, FreeGroup.lift_apply_of,
        modPresGenMap_R, modPresGenMap_X]
      rw [mul_inv_eq_one, hconj]
      cases hdir : M.rules[i.val].dir
      · have hβ : modBeta M i mbX = mbX ^ (M.m * M.m) := by
          have h1 : modBeta M i mbX = mbG (((M.m * M.m : ℕ) : ℤ), 0) := by
            unfold modBeta; rw [hdir]
            simpa [mbX] using
              conjModBase_mbG ((M.rules[i.val].c : ℤ), 0) ((M.m * M.m : ℕ) : ℤ) 1 (1, 0)
          rw [h1, mbG_eq_zpow]; simp only [zpow_zero, mul_one, zpow_natCast]
        rw [hβ, map_pow]; simp [freeGroup_mk_wordPow, freeGroup_mk_wordOf]
      · have hβ : modBeta M i mbX = mbX := by
          unfold modBeta; rw [hdir]
          simpa [mbX] using
            conjModBase_mbG (0, (M.rules[i.val].c : ℤ)) 1 ((M.m * M.m : ℕ) : ℤ) (1, 0)
        rw [hβ]; simp [freeGroup_mk_wordOf]
    · -- r_i * y^m * r_i⁻¹ = y or y^(m²)
      have hα : modAlpha M i mbY = mbY ^ M.m := by
        have h1 : modAlpha M i mbY = mbG (0, (M.m : ℤ)) := by
          simpa [modAlpha, mbY] using
            conjModBase_mbG ((M.rules[i].a : ℤ), (M.rules[i].b : ℤ)) (M.m : ℤ) (M.m : ℤ) (0, 1)
        rw [h1, mbG_eq_zpow]; simp
      have hconj := mgR_conj_modAlpha M i mbY
      rw [hα, map_pow] at hconj
      simp only [freeGroup_mk_wordRel, freeGroup_mk_wordConjL, freeGroup_mk_wordPow,
        freeGroup_mk_wordOf, map_mul, map_inv, map_pow, FreeGroup.lift_apply_of,
        modPresGenMap_R, modPresGenMap_Y]
      rw [mul_inv_eq_one, hconj]
      cases hdir : M.rules[i.val].dir
      · have hβ : modBeta M i mbY = mbY := by
          unfold modBeta; rw [hdir]
          simpa [mbY] using
            conjModBase_mbG ((M.rules[i.val].c : ℤ), 0) ((M.m * M.m : ℕ) : ℤ) 1 (0, 1)
        rw [hβ]; simp [freeGroup_mk_wordOf]
      · have hβ : modBeta M i mbY = mbY ^ (M.m * M.m) := by
          have h1 : modBeta M i mbY = mbG (0, ((M.m * M.m : ℕ) : ℤ)) := by
            unfold modBeta; rw [hdir]
            simpa [mbY] using
              conjModBase_mbG (0, (M.rules[i.val].c : ℤ)) 1 ((M.m * M.m : ℕ) : ℤ) (0, 1)
          rw [h1, mbG_eq_zpow]; simp only [zpow_zero, one_mul, zpow_natCast]
        rw [hβ, map_pow]; simp [freeGroup_mk_wordPow, freeGroup_mk_wordOf]
    · -- r_i * t_{(a, b)} * r_i⁻¹ = t_{(c, 0)} or t_{(0, c)}
      have hα : modAlpha M i mbT = mbConjT ((M.rules[i].a : ℤ), (M.rules[i].b : ℤ)) :=
        conjModBase_mbT _ _ _
      have hconj := mgR_conj_modAlpha M i mbT
      rw [hα] at hconj
      have ht_ab : mgOfBase M (mbConjT ((M.rules[i].a : ℤ), (M.rules[i].b : ℤ))) =
          (mgOfBase M mbX ^ M.rules[i].a * mgOfBase M mbY ^ M.rules[i].b)⁻¹ *
            mgOfBase M mbT * (mgOfBase M mbX ^ M.rules[i].a * mgOfBase M mbY ^ M.rules[i].b) := by
        simp only [mbConjT, mbG_eq_zpow, zpow_natCast, map_mul, map_inv, map_pow]
      rw [ht_ab] at hconj
      simp only [freeGroup_mk_wordRel, freeGroup_mk_wordConjL, freeGroup_mk_wordConj,
        freeGroup_mk_append, freeGroup_mk_wordPow, freeGroup_mk_wordOf, map_mul, map_inv,
        map_pow, FreeGroup.lift_apply_of, modPresGenMap_R, modPresGenMap_X, modPresGenMap_Y,
        modPresGenMap_T]
      rw [mul_inv_eq_one, hconj]
      cases hdir : M.rules[i.val].dir
      · have hβ : modBeta M i mbT = mbConjT ((M.rules[i.val].c : ℤ), 0) := by
          unfold modBeta; rw [hdir]
          exact conjModBase_mbT ((M.rules[i.val].c : ℤ), 0) ((M.m * M.m : ℕ) : ℤ) 1
        rw [hβ]
        simp only [mbConjT, mbG_eq_zpow, zpow_natCast, zpow_zero, mul_one, map_mul, map_inv,
          map_pow, freeGroup_mk_wordConj, freeGroup_mk_wordPow, freeGroup_mk_wordOf,
          FreeGroup.lift_apply_of, modPresGenMap_X, modPresGenMap_T]
        rfl
      · have hβ : modBeta M i mbT = mbConjT (0, (M.rules[i.val].c : ℤ)) := by
          unfold modBeta; rw [hdir]
          exact conjModBase_mbT (0, (M.rules[i.val].c : ℤ)) 1 ((M.m * M.m : ℕ) : ℤ)
        rw [hβ]
        simp only [mbConjT, mbG_eq_zpow, zpow_natCast, zpow_zero, one_mul, map_mul, map_inv,
          map_pow, freeGroup_mk_wordConj, freeGroup_mk_wordPow, freeGroup_mk_wordOf,
          FreeGroup.lift_apply_of, modPresGenMap_Y, modPresGenMap_T]
        rfl

/-- Canonical isomorphism `(modPres M).Group ≃* ModGroup M`. -/
def modPresEquiv : (modPres M).Group ≃* ModGroup M := by
  let x : (modPres M).Group := (modPres M).ofGen (modGenX M)
  let y : (modPres M).Group := (modPres M).ofGen (modGenY M)
  let t : (modPres M).Group := (modPres M).ofGen (modGenT M)
  let k : (modPres M).Group := (modPres M).ofGen (modGenK M)
  let r : Fin M.rules.length → (modPres M).Group := fun i => (modPres M).ofGen (modGenR M i)
  have hxy : Commute x y := by
    have h1 := (modPres M).mkWord_eq_one_of_mem (r := wordComm (wordOf (modGenX M)) (wordOf (modGenY M)))
      (by simp [modPres])
    simp only [FinPres.mkWord, freeGroup_mk_wordComm, freeGroup_mk_wordOf, map_mul, map_inv] at h1
    change x * y * x⁻¹ * y⁻¹ = 1 at h1
    have h2 : x * y * x⁻¹ = y := mul_inv_eq_one.mp h1
    rw [Commute, SemiconjBy]
    calc x * y = (x * y * x⁻¹) * x := by simp [mul_assoc]
      _ = y * x := by rw [h2]
  have hkt : k * t = t * k := by
    have h1 := (modPres M).mkWord_eq_one_of_mem (r := wordComm (wordOf (modGenK M)) (wordOf (modGenT M)))
      (by simp [modPres])
    simp only [FinPres.mkWord, freeGroup_mk_wordComm, freeGroup_mk_wordOf, map_mul, map_inv] at h1
    change k * t * k⁻¹ * t⁻¹ = 1 at h1
    have h2 : k * t * k⁻¹ = t := mul_inv_eq_one.mp h1
    calc k * t = (k * t * k⁻¹) * k := by simp [mul_assoc]
      _ = t * k := by rw [h2]
  have hkr : ∀ i, k * r i = r i * k := by
    intro i
    have hmem : wordComm (wordOf (modGenK M)) (wordOf (modGenR M i)) ∈ (modPres M).relators := by
      simp only [modPres, List.mem_append, List.mem_flatMap, List.mem_finRange, true_and]
      right; exact ⟨i, by simp [modRuleRelators]⟩
    have h1 := (modPres M).mkWord_eq_one_of_mem hmem
    simp only [FinPres.mkWord, freeGroup_mk_wordComm, freeGroup_mk_wordOf, map_mul, map_inv] at h1
    change k * r i * k⁻¹ * (r i)⁻¹ = 1 at h1
    have h2 : k * r i * k⁻¹ = r i := mul_inv_eq_one.mp h1
    calc k * r i = (k * r i * k⁻¹) * k := by simp [mul_assoc]
      _ = r i * k := by rw [h2]
  let z2ToPres : Multiplicative (ℤ × ℤ) →* (modPres M).Group :=
    { toFun := fun p => x ^ (Multiplicative.toAdd p).1 * y ^ (Multiplicative.toAdd p).2
      map_one' := by simp
      map_mul' := fun p q => by
        change x ^ ((Multiplicative.toAdd p).1 + (Multiplicative.toAdd q).1) *
            y ^ ((Multiplicative.toAdd p).2 + (Multiplicative.toAdd q).2) = _
        rw [zpow_add, zpow_add]
        have hcomm : Commute (y ^ (Multiplicative.toAdd p).2) (x ^ (Multiplicative.toAdd q).1) :=
          (hxy.symm.zpow_left _).zpow_right _
        calc x ^ (Multiplicative.toAdd p).1 * x ^ (Multiplicative.toAdd q).1 *
              (y ^ (Multiplicative.toAdd p).2 * y ^ (Multiplicative.toAdd q).2)
            = x ^ (Multiplicative.toAdd p).1 *
              ((x ^ (Multiplicative.toAdd q).1 * y ^ (Multiplicative.toAdd p).2) *
                y ^ (Multiplicative.toAdd q).2) := by simp [mul_assoc]
          _ = x ^ (Multiplicative.toAdd p).1 *
              ((y ^ (Multiplicative.toAdd p).2 * x ^ (Multiplicative.toAdd q).1) *
                y ^ (Multiplicative.toAdd q).2) := by rw [hcomm.symm.eq]
          _ = _ := by simp [mul_assoc] }
  let zToPres : Multiplicative ℤ →* (modPres M).Group :=
    { toFun := fun n => t ^ Multiplicative.toAdd n
      map_one' := by simp
      map_mul' := fun a b => by
        change t ^ (Multiplicative.toAdd a + Multiplicative.toAdd b) = _
        rw [zpow_add] }
  let baseToPres : ModBase →* (modPres M).Group := Coprod.lift z2ToPres zToPres
  have hbase_mbG : ∀ p : ℤ × ℤ, baseToPres (mbG p) = x ^ p.1 * y ^ p.2 := fun _ => rfl
  have hbase_mbX : baseToPres mbX = x := by simp [hbase_mbG, mbX]
  have hbase_mbY : baseToPres mbY = y := by simp [hbase_mbG, mbY]
  have hbase_mbT : baseToPres mbT = t := by simp [baseToPres, mbT, zToPres]
  have hrule_rel : ∀ i (h : ModBase),
      r i * baseToPres (modAlpha M i h) * (r i)⁻¹ = baseToPres (modBeta M i h) := by
    intro i
    have hhom : ((MulAut.conj (r i)).toMonoidHom.comp (baseToPres.comp (modAlpha M i))) =
        baseToPres.comp (modBeta M i) := by
      have hmem_x : wordRel (wordConjL (wordOf (modGenR M i)) (wordPow (wordOf (modGenX M)) M.m))
          (match M.rules[i.val].dir with | .R => wordPow (wordOf (modGenX M)) (M.m * M.m) | .L => wordOf (modGenX M)) ∈ (modPres M).relators := by
        simp only [modPres, List.mem_append, List.mem_flatMap, List.mem_finRange, true_and]
        right; exact ⟨i, by simp [modRuleRelators]⟩
      have hmem_y : wordRel (wordConjL (wordOf (modGenR M i)) (wordPow (wordOf (modGenY M)) M.m))
          (match M.rules[i.val].dir with | .R => wordOf (modGenY M) | .L => wordPow (wordOf (modGenY M)) (M.m * M.m)) ∈ (modPres M).relators := by
        simp only [modPres, List.mem_append, List.mem_flatMap, List.mem_finRange, true_and]
        right; exact ⟨i, by simp [modRuleRelators]⟩
      have hmem_t : wordRel (wordConjL (wordOf (modGenR M i))
            (wordConj (wordPow (wordOf (modGenX M)) M.rules[i.val].a ++ wordPow (wordOf (modGenY M)) M.rules[i.val].b)
              (wordOf (modGenT M))))
          (match M.rules[i.val].dir with
           | .R => wordConj (wordPow (wordOf (modGenX M)) M.rules[i.val].c) (wordOf (modGenT M))
           | .L => wordConj (wordPow (wordOf (modGenY M)) M.rules[i.val].c) (wordOf (modGenT M))) ∈ (modPres M).relators := by
        simp only [modPres, List.mem_append, List.mem_flatMap, List.mem_finRange, true_and]
        right; exact ⟨i, by simp [modRuleRelators]⟩
      have hrx : r i * baseToPres (modAlpha M i mbX) * (r i)⁻¹ = baseToPres (modBeta M i mbX) := by
        have h1 := (modPres M).mkWord_eq_of_wordRel_mem hmem_x
        simp only [FinPres.mkWord, freeGroup_mk_wordConjL, freeGroup_mk_wordPow, freeGroup_mk_wordOf,
          map_mul, map_inv, map_pow] at h1
        have hα : modAlpha M i mbX = mbG ((M.m : ℤ), 0) := by
          simpa [modAlpha, mbX] using
            conjModBase_mbG ((M.rules[i].a : ℤ), (M.rules[i].b : ℤ)) (M.m : ℤ) (M.m : ℤ) (1, 0)
        rw [hα, hbase_mbG]; simp only [zpow_natCast, zpow_zero, mul_one]
        cases hdir : M.rules[i.val].dir
        · rw [hdir] at h1
          simp only [freeGroup_mk_wordPow, freeGroup_mk_wordOf, map_pow] at h1
          have hβ : modBeta M i mbX = mbG (((M.m * M.m : ℕ) : ℤ), 0) := by
            unfold modBeta; rw [hdir]
            simpa [mbX] using
              conjModBase_mbG ((M.rules[i.val].c : ℤ), 0) ((M.m * M.m : ℕ) : ℤ) 1 (1, 0)
          rw [hβ, hbase_mbG]; simp only [zpow_zero, mul_one, zpow_natCast]; exact h1
        · rw [hdir] at h1; simp only [freeGroup_mk_wordOf] at h1
          have hβ : modBeta M i mbX = mbX := by
            unfold modBeta; rw [hdir]
            simpa [mbX] using
              conjModBase_mbG (0, (M.rules[i.val].c : ℤ)) 1 ((M.m * M.m : ℕ) : ℤ) (1, 0)
          rw [hβ, hbase_mbX]; exact h1
      have hry : r i * baseToPres (modAlpha M i mbY) * (r i)⁻¹ = baseToPres (modBeta M i mbY) := by
        have h1 := (modPres M).mkWord_eq_of_wordRel_mem hmem_y
        simp only [FinPres.mkWord, freeGroup_mk_wordConjL, freeGroup_mk_wordPow, freeGroup_mk_wordOf,
          map_mul, map_inv, map_pow] at h1
        have hα : modAlpha M i mbY = mbG (0, (M.m : ℤ)) := by
          simpa [modAlpha, mbY] using
            conjModBase_mbG ((M.rules[i].a : ℤ), (M.rules[i].b : ℤ)) (M.m : ℤ) (M.m : ℤ) (0, 1)
        rw [hα, hbase_mbG]; simp only [zpow_natCast, zpow_zero, one_mul]
        cases hdir : M.rules[i.val].dir
        · rw [hdir] at h1; simp only [freeGroup_mk_wordOf] at h1
          have hβ : modBeta M i mbY = mbY := by
            unfold modBeta; rw [hdir]
            simpa [mbY] using
              conjModBase_mbG ((M.rules[i.val].c : ℤ), 0) ((M.m * M.m : ℕ) : ℤ) 1 (0, 1)
          rw [hβ, hbase_mbY]; exact h1
        · rw [hdir] at h1
          simp only [freeGroup_mk_wordPow, freeGroup_mk_wordOf, map_pow] at h1
          have hβ : modBeta M i mbY = mbG (0, ((M.m * M.m : ℕ) : ℤ)) := by
            unfold modBeta; rw [hdir]
            simpa [mbY] using
              conjModBase_mbG (0, (M.rules[i.val].c : ℤ)) 1 ((M.m * M.m : ℕ) : ℤ) (0, 1)
          rw [hβ, hbase_mbG]; simp only [zpow_zero, one_mul, zpow_natCast]; exact h1
      have hrt : r i * baseToPres (modAlpha M i mbT) * (r i)⁻¹ = baseToPres (modBeta M i mbT) := by
        have h1 := (modPres M).mkWord_eq_of_wordRel_mem hmem_t
        simp only [FinPres.mkWord, freeGroup_mk_wordConjL, freeGroup_mk_wordConj,
          freeGroup_mk_append, freeGroup_mk_wordPow, freeGroup_mk_wordOf, map_mul, map_inv,
          map_pow] at h1
        have hα : modAlpha M i mbT = mbConjT ((M.rules[i].a : ℤ), (M.rules[i].b : ℤ)) :=
          conjModBase_mbT _ _ _
        rw [hα, mbConjT, map_mul, map_mul, map_inv, hbase_mbG, hbase_mbT]
        simp only [zpow_natCast]
        cases hdir : M.rules[i.val].dir
        · rw [hdir] at h1
          simp only [freeGroup_mk_wordConj, freeGroup_mk_wordPow, freeGroup_mk_wordOf,
            map_mul, map_inv, map_pow] at h1
          have hβ : modBeta M i mbT = mbConjT ((M.rules[i.val].c : ℤ), 0) := by
            unfold modBeta; rw [hdir]
            exact conjModBase_mbT ((M.rules[i.val].c : ℤ), 0) ((M.m * M.m : ℕ) : ℤ) 1
          rw [hβ, mbConjT, map_mul, map_mul, map_inv, hbase_mbG, hbase_mbT]
          simp only [zpow_zero, mul_one, zpow_natCast]; exact h1
        · rw [hdir] at h1
          simp only [freeGroup_mk_wordConj, freeGroup_mk_wordPow, freeGroup_mk_wordOf,
            map_mul, map_inv, map_pow] at h1
          have hβ : modBeta M i mbT = mbConjT (0, (M.rules[i.val].c : ℤ)) := by
            unfold modBeta; rw [hdir]
            exact conjModBase_mbT (0, (M.rules[i.val].c : ℤ)) 1 ((M.m * M.m : ℕ) : ℤ)
          rw [hβ, mbConjT, map_mul, map_mul, map_inv, hbase_mbG, hbase_mbT]
          simp only [zpow_zero, one_mul, zpow_natCast]; exact h1
      apply Coprod.hom_ext
      · apply MonoidHom.ext; intro p
        change r i * baseToPres (modAlpha M i (Coprod.inl p)) * (r i)⁻¹ =
          baseToPres (modBeta M i (Coprod.inl p))
        have hp : (Coprod.inl p : ModBase) =
            mbX ^ (Multiplicative.toAdd p).1 * mbY ^ (Multiplicative.toAdd p).2 := by
          simpa [mbG] using mbG_eq_zpow (Multiplicative.toAdd p)
        rw [hp]
        simp only [map_mul, map_zpow]
        calc r i * (baseToPres (modAlpha M i mbX) ^ (Multiplicative.toAdd p).1 *
              baseToPres (modAlpha M i mbY) ^ (Multiplicative.toAdd p).2) * (r i)⁻¹
            = (r i * baseToPres (modAlpha M i mbX) * (r i)⁻¹) ^ (Multiplicative.toAdd p).1 *
              (r i * baseToPres (modAlpha M i mbY) * (r i)⁻¹) ^ (Multiplicative.toAdd p).2 := by
              rw [conj_zpow, conj_zpow]; group
          _ = baseToPres (modBeta M i mbX) ^ (Multiplicative.toAdd p).1 *
              baseToPres (modBeta M i mbY) ^ (Multiplicative.toAdd p).2 := by
              rw [hrx, hry]
      · apply MonoidHom.ext; intro n
        change r i * baseToPres (modAlpha M i (Coprod.inr n)) * (r i)⁻¹ =
          baseToPres (modBeta M i (Coprod.inr n))
        have hn : (Coprod.inr n : ModBase) = mbT ^ (Multiplicative.toAdd n) := by
          simp [mbT, ← map_zpow, ← ofAdd_zsmul]
        rw [hn, map_zpow, map_zpow, map_zpow, map_zpow, ← conj_zpow, hrt]
    intro h
    exact congrArg (fun f => f h) hhom
  let h1ToPres : ModH1 M →* (modPres M).Group :=
    MultiHNN.lift (modHNNData M) baseToPres r fun i a => by
      rcases a with ⟨_, ⟨h, rfl⟩⟩
      rw [modHNNData_iso_apply M i h, ← hrule_rel i h]
      group
  let invFun : ModGroup M →* (modPres M).Group :=
    HNNExtension.lift (φ := MulEquiv.refl (modC M)) h1ToPres k fun ⟨c, hc⟩ => by
      change k * h1ToPres c = h1ToPres c * k
      refine Subgroup.closure_induction
        (p := fun z _ => k * h1ToPres z = h1ToPres z * k) ?_ ?_ ?_ ?_ hc
      · intro z hz
        rcases hz with rfl | ⟨i, rfl⟩
        · simpa [h1ToPres, hbase_mbT] using hkt
        · simpa [h1ToPres] using hkr i
      · simp
      · intro a b _ _ ha hb
        simp only [map_mul]
        calc k * (h1ToPres a * h1ToPres b) = (k * h1ToPres a) * h1ToPres b := by rw [mul_assoc]
          _ = (h1ToPres a * k) * h1ToPres b := by rw [ha]
          _ = h1ToPres a * (k * h1ToPres b) := by rw [mul_assoc]
          _ = h1ToPres a * (h1ToPres b * k) := by rw [hb]
          _ = (h1ToPres a * h1ToPres b) * k := by rw [mul_assoc]
      · intro a _ ha
        simp only [map_inv]
        have h1 : (h1ToPres a)⁻¹ * (k * h1ToPres a) * (h1ToPres a)⁻¹ =
            (h1ToPres a)⁻¹ * (h1ToPres a * k) * (h1ToPres a)⁻¹ := by rw [ha]
        simpa [mul_assoc] using h1.symm
  let toFun : (modPres M).Group →* ModGroup M := (modPres M).lift (modPresGenMap M) (modPres_relators_hold M)
  refine MonoidHom.toMulEquiv toFun invFun ?_ ?_
  · apply FinPres.hom_ext
    intro idx
    change invFun (toFun ((modPres M).ofGen idx)) = (modPres M).ofGen idx
    simp only [toFun, FinPres.lift_ofGen]
    rcases idx with ⟨v, hv⟩
    match v with
    | 0 => simp [modPresGenMap, invFun, mgOfBase, h1ToPres, hbase_mbX, x, modGenX]
    | 1 => simp [modPresGenMap, invFun, mgOfBase, h1ToPres, hbase_mbY, y, modGenY]
    | 2 => simp [modPresGenMap, invFun, mgOfBase, h1ToPres, hbase_mbT, t, modGenT]
    | 3 => simp [modPresGenMap, invFun, mgK, k, modGenK]
    | n + 4 =>
      simp only [modPresGenMap, mgR, invFun, HNNExtension.lift_of, h1ToPres, MultiHNN.lift_t, r,
        modGenR]
      congr 1; apply Fin.ext; dsimp; omega
  · apply HNNExtension.hom_ext
    · apply MultiHNN.hom_ext
      · apply Coprod.hom_ext
        · apply MonoidHom.ext; intro p
          change toFun (invFun (mgOfBase M (Coprod.inl p))) = mgOfBase M (Coprod.inl p)
          have hin : invFun (mgOfBase M (Coprod.inl p)) =
              x ^ (Multiplicative.toAdd p).1 * y ^ (Multiplicative.toAdd p).2 := by
            simp [mgOfBase, invFun, h1ToPres, baseToPres, z2ToPres]
          rw [hin, map_mul, map_zpow, map_zpow]
          simp only [toFun, x, y, FinPres.lift_ofGen, modPresGenMap_X, modPresGenMap_Y]
          rw [← map_zpow, ← map_zpow, ← map_mul]
          congr 1
          simpa [mbG] using (mbG_eq_zpow (Multiplicative.toAdd p)).symm
        · apply MonoidHom.ext; intro n
          change toFun (invFun (mgOfBase M (Coprod.inr n))) = mgOfBase M (Coprod.inr n)
          have hin : invFun (mgOfBase M (Coprod.inr n)) = t ^ Multiplicative.toAdd n := by
            simp [mgOfBase, invFun, h1ToPres, baseToPres, zToPres]
          rw [hin, map_zpow]
          simp only [toFun, t, FinPres.lift_ofGen, modPresGenMap_T]
          rw [← map_zpow]
          congr 1
          simp [mbT, ← map_zpow, ← ofAdd_zsmul]
      · intro i
        change toFun (invFun (mgR M i)) = mgR M i
        simp [mgR, invFun, h1ToPres, r, toFun]
    · change toFun (invFun (mgK M)) = mgK M
      simp [mgK, invFun, k, toFun]

theorem modPresEquiv_ofGen_X : modPresEquiv M ((modPres M).ofGen (modGenX M)) = mgOfBase M mbX := by
  simp [modPresEquiv]

theorem modPresEquiv_ofGen_Y : modPresEquiv M ((modPres M).ofGen (modGenY M)) = mgOfBase M mbY := by
  simp [modPresEquiv]

theorem modPresEquiv_ofGen_T : modPresEquiv M ((modPres M).ofGen (modGenT M)) = mgOfBase M mbT := by
  simp [modPresEquiv]

theorem modPresEquiv_ofGen_K : modPresEquiv M ((modPres M).ofGen (modGenK M)) = mgK M := by
  simp [modPresEquiv]

end ModPresDef

/-! ### Part 4: Word Problem Characterization via Britton's Lemma -/

section WordProblem

variable (M : ModularMachine)

/-- Subgroup `T(M) = ⟨t_p | p ∈ ReachesZero M⟩ ≤ ModBase`. -/
def modT : Subgroup ModBase :=
  Subgroup.closure (mbConjT '' ReachesZero M)

theorem modT_le_kerProj : modT M ≤ mbProj.ker := by
  rw [modT, Subgroup.closure_le]
  rintro _ ⟨p, _, rfl⟩
  exact mbConjT_mem_ker p

theorem mem_modT_iff_kerProj (w : FreeGroup (ℤ × ℤ)) :
    mbConjTHom w ∈ modT M ↔ w ∈ Subgroup.closure (FreeGroup.of '' ReachesZero M) := by
  have himg : (Subgroup.closure (FreeGroup.of '' ReachesZero M)).map mbConjTHom = modT M := by
    rw [MonoidHom.map_closure, modT]
    congr 1
    ext x
    simp [mbConjTHom]
  rw [← himg]
  exact ⟨fun ⟨u, hu, heq⟩ => mbConjTHom_injective heq ▸ hu, fun hw => ⟨w, hw, rfl⟩⟩

theorem modAlpha_mem_modT_iff_modBeta (i : Fin M.rules.length) (h : ModBase) :
    modAlpha M i h ∈ modT M ↔ modBeta M i h ∈ modT M := by
  have hpre : modFA M i ⁻¹' ReachesZero M = modFB M i ⁻¹' ReachesZero M := by
    ext ⟨u, v⟩
    exact rule_reachesZero_iff M (List.getElem_mem i.isLt) u v
  constructor
  · intro hα
    have hker_α : modAlpha M i h ∈ mbProj.ker := modT_le_kerProj M hα
    have hker_h : h ∈ mbProj.ker := by
      rw [MonoidHom.mem_ker] at hker_α ⊢
      have hp := mbProj_conjModBase ((M.rules[i].a : ℤ), (M.rules[i].b : ℤ)) (M.m : ℤ) (M.m : ℤ) h
      change mbProj (modAlpha M i h) = scaleZ2 (M.m : ℤ) (M.m : ℤ) (mbProj h) at hp
      rw [hker_α] at hp
      exact scaleZ2_injective (modM_ne_zero M) (modM_ne_zero M) (hp.symm.trans (map_one _).symm)
    let w : FreeGroup (ℤ × ℤ) := kerProjBasis.symm ⟨h, hker_h⟩
    have hw : mbConjTHom w = h := by
      have := kerProjBasis.apply_symm_apply ⟨h, hker_h⟩
      exact congrArg Subtype.val this
    rw [← hw, modAlpha_mbConjTHom, mem_modT_iff_kerProj,
      map_mem_closure_of_iff (modFA_injective M i), hpre,
      ← map_mem_closure_of_iff (modFB_injective M i), ← mem_modT_iff_kerProj,
      ← modBeta_mbConjTHom, hw] at hα
    exact hα
  · intro hβ
    have hker_β : modBeta M i h ∈ mbProj.ker := modT_le_kerProj M hβ
    have hker_h : h ∈ mbProj.ker := by
      rw [MonoidHom.mem_ker] at hker_β ⊢
      unfold modBeta at hker_β
      cases hdir : M.rules[i.val].dir with
      | R =>
        rw [hdir] at hker_β
        have hp := mbProj_conjModBase ((M.rules[i.val].c : ℤ), 0) ((M.m * M.m : ℕ) : ℤ) 1 h
        rw [hker_β] at hp
        exact scaleZ2_injective (modM_sq_ne_zero M) one_ne_zero (hp.symm.trans (map_one _).symm)
      | L =>
        rw [hdir] at hker_β
        have hp := mbProj_conjModBase (0, (M.rules[i.val].c : ℤ)) 1 ((M.m * M.m : ℕ) : ℤ) h
        rw [hker_β] at hp
        exact scaleZ2_injective one_ne_zero (modM_sq_ne_zero M) (hp.symm.trans (map_one _).symm)
    let w : FreeGroup (ℤ × ℤ) := kerProjBasis.symm ⟨h, hker_h⟩
    have hw : mbConjTHom w = h := by
      have := kerProjBasis.apply_symm_apply ⟨h, hker_h⟩
      exact congrArg Subtype.val this
    rw [← hw, modBeta_mbConjTHom, mem_modT_iff_kerProj,
      map_mem_closure_of_iff (modFB_injective M i), ← hpre,
      ← map_mem_closure_of_iff (modFA_injective M i), ← mem_modT_iff_kerProj,
      ← modAlpha_mbConjTHom, hw] at hβ
    exact hβ

theorem modIso_mem_modT (i : Fin M.rules.length) (u : ℤˣ) (g : (modHNNData M i).toSubgroup u)
    (hg : (g : ModBase) ∈ modT M) :
    ((modHNNData M i).toSubgroupEquiv u g : ModBase) ∈ modT M := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · rcases g with ⟨_, ⟨h, rfl⟩⟩
    change ((modHNNData M i).iso ⟨modAlpha M i h, ⟨h, rfl⟩⟩ : ModBase) ∈ modT M
    rw [modHNNData_iso_apply]
    exact (modAlpha_mem_modT_iff_modBeta M i h).1 hg
  · rcases g with ⟨_, ⟨h, rfl⟩⟩
    change ((modHNNData M i).iso.symm ⟨modBeta M i h, ⟨h, rfl⟩⟩ : ModBase) ∈ modT M
    rw [modHNNData_iso_symm_apply]
    exact (modAlpha_mem_modT_iff_modBeta M i h).2 hg

/-- Helper: multiplying two `wordProd`s preserves membership of all base letters in `modT M`. -/
private theorem wordProd_mul_closed {head₁ head₂ : ModBase}
    {l₁ l₂ : List (Fin M.rules.length × ℤˣ × ModBase)}
    (h1 : head₁ ∈ modT M) (hl₁ : ∀ x ∈ l₁, x.2.2 ∈ modT M)
    (h2 : head₂ ∈ modT M) (hl₂ : ∀ x ∈ l₂, x.2.2 ∈ modT M) :
    ∃ (head : ModBase) (l : List (Fin M.rules.length × ℤˣ × ModBase)),
      head ∈ modT M ∧ (∀ x ∈ l, x.2.2 ∈ modT M) ∧
      MultiHNN.wordProd (modHNNData M) head l =
        MultiHNN.wordProd (modHNNData M) head₁ l₁ * MultiHNN.wordProd (modHNNData M) head₂ l₂ := by
  induction l₁ using List.reverseRecOn with
  | nil =>
    refine ⟨head₁ * head₂, l₂, mul_mem h1 h2, hl₂, ?_⟩
    simp [MultiHNN.wordProd, mul_assoc]
  | append_singleton init last _ =>
    rcases last with ⟨j, v, hlast⟩
    have hlast_mem : hlast ∈ modT M := hl₁ (j, v, hlast) (by simp)
    refine ⟨head₁, init ++ (j, v, hlast * head₂) :: l₂, h1, ?_, ?_⟩
    · intro x hx
      simp only [List.mem_append, List.mem_cons] at hx
      rcases hx with hx | rfl | hx
      · exact hl₁ x (by simp [hx])
      · exact mul_mem hlast_mem h2
      · exact hl₂ x hx
    · simp [MultiHNN.wordProd, List.map_append, List.prod_append, mul_assoc]

/-- Helper: inverting a `wordProd` preserves membership of all base letters in `modT M`. -/
private theorem wordProd_inv_closed {head : ModBase}
    {l : List (Fin M.rules.length × ℤˣ × ModBase)}
    (hhead : head ∈ modT M) (hl : ∀ x ∈ l, x.2.2 ∈ modT M) :
    ∃ (head' : ModBase) (l' : List (Fin M.rules.length × ℤˣ × ModBase)),
      head' ∈ modT M ∧ (∀ x ∈ l', x.2.2 ∈ modT M) ∧
      MultiHNN.wordProd (modHNNData M) head' l' =
        (MultiHNN.wordProd (modHNNData M) head l)⁻¹ := by
  induction l generalizing head with
  | nil =>
    refine ⟨head⁻¹, [], inv_mem hhead, by simp, ?_⟩
    simp [MultiHNN.wordProd]
  | cons a rest ih =>
    rcases a with ⟨i, u, g⟩
    have hg : g ∈ modT M := hl (i, u, g) List.mem_cons_self
    have hrest : ∀ x ∈ rest, x.2.2 ∈ modT M := fun x hx => hl x (List.mem_cons_of_mem _ hx)
    obtain ⟨hd', l', hhd', hl', heq⟩ := ih hg hrest
    obtain ⟨hd'', l'', hhd'', hl'', hmul⟩ :=
      wordProd_mul_closed M hhd' hl' (one_mem (modT M))
        (l₂ := [(i, -u, head⁻¹)]) (by simp [inv_mem hhead])
    refine ⟨hd'', l'', hhd'', hl'', ?_⟩
    rw [hmul, heq]
    simp only [MultiHNN.wordProd, List.map_cons, List.prod_cons, List.map_nil, List.prod_nil,
      mul_one, map_one, one_mul, map_inv, Units.val_neg, zpow_neg, mul_inv_rev, mul_assoc]

/-- Every element of `modC M` is represented by a `wordProd` whose base letters all lie in `modT M`. -/
theorem exists_wordProd_modT_of_mem_modC {x : ModH1 M} (hx : x ∈ modC M) :
    ∃ (head : ModBase) (l : List (Fin M.rules.length × ℤˣ × ModBase)),
      head ∈ modT M ∧ (∀ e ∈ l, e.2.2 ∈ modT M) ∧
      MultiHNN.wordProd (modHNNData M) head l = x := by
  refine Subgroup.closure_induction
    (p := fun z _ => ∃ head l, head ∈ modT M ∧ (∀ e ∈ l, e.2.2 ∈ modT M) ∧
      MultiHNN.wordProd (modHNNData M) head l = z) ?_ ?_ ?_ ?_ hx
  · intro z hz
    rcases hz with rfl | ⟨i, rfl⟩
    · have ht_mem : mbT ∈ modT M := by
        have : mbT = mbConjT (0, 0) := by simp [mbConjT]
        rw [this]
        exact Subgroup.subset_closure ⟨(0, 0), Relation.ReflTransGen.refl, rfl⟩
      exact ⟨mbT, [], ht_mem, by simp, by simp [MultiHNN.wordProd]⟩
    · exact ⟨1, [(i, 1, 1)], one_mem _, by simp [one_mem], by simp [MultiHNN.wordProd]⟩
  · exact ⟨1, [], one_mem _, by simp, by simp [MultiHNN.wordProd]⟩
  · rintro a b _ _ ⟨hd₁, l₁, h1, hl1, rfl⟩ ⟨hd₂, l₂, h2, hl2, rfl⟩
    exact wordProd_mul_closed M h1 hl1 h2 hl2
  · rintro a _ ⟨hd, l, h, hl, rfl⟩
    exact wordProd_inv_closed M h hl

/-- Britton induction in `ModH1 M`: if a `wordProd` with all base letters in `modT M` evaluates
to `MultiHNN.of _ g`, then `g ∈ modT M`. -/
theorem mem_modT_of_wordProd_eq_of (head : ModBase) (l : List (Fin M.rules.length × ℤˣ × ModBase))
    (hhead : head ∈ modT M) (hl : ∀ e ∈ l, e.2.2 ∈ modT M)
    {g : ModBase} (heq : MultiHNN.wordProd (modHNNData M) head l = MultiHNN.of (modHNNData M) g) :
    g ∈ modT M := by
  obtain ⟨n, hn⟩ : ∃ n, l.length = n := ⟨l.length, rfl⟩
  induction n using Nat.strong_induction_on generalizing head l with
  | ind n ih =>
    cases l with
    | nil =>
      simp only [MultiHNN.wordProd, List.map_nil, List.prod_nil, mul_one] at heq
      exact MultiHNN.of_injective (modHNNData M) heq ▸ hhead
    | cons a rest =>
      have hne : a :: rest ≠ [] := List.cons_ne_nil _ _
      obtain ⟨l₁, l₂, i, u, g₁, g₂, hsplit, hg₁_sub⟩ :=
        MultiHNN.exists_pinch_of_mem_of_range (modHNNData M) head (a :: rest) hne ⟨g, heq.symm⟩
      have hg₁_T : g₁ ∈ modT M := hl (i, u, g₁) (by rw [hsplit]; simp)
      have hg₂_T : g₂ ∈ modT M := hl (i, -u, g₂) (by rw [hsplit]; simp)
      let g₁' : ModBase := ((modHNNData M i).toSubgroupEquiv u ⟨g₁, hg₁_sub⟩ : ModBase)
      have hg₁'_T : g₁' ∈ modT M := modIso_mem_modT M i u ⟨g₁, hg₁_sub⟩ hg₁_T
      have hpinch :
          MultiHNN.t (modHNNData M) i ^ (u : ℤ) * MultiHNN.of (modHNNData M) g₁ *
            (MultiHNN.t (modHNNData M) i ^ ((-u : ℤˣ) : ℤ) * MultiHNN.of (modHNNData M) g₂) =
          MultiHNN.of (modHNNData M) (g₁' * g₂) := by
        have hconj := MultiHNN.toSubgroupEquiv_eq_conj (modHNNData M) i u ⟨g₁, hg₁_sub⟩
        change MultiHNN.of (modHNNData M) g₁' =
          MultiHNN.t (modHNNData M) i ^ (u : ℤ) * MultiHNN.of (modHNNData M) g₁ *
            (MultiHNN.t (modHNNData M) i ^ (u : ℤ))⁻¹ at hconj
        rw [map_mul, hconj]
        simp only [Units.val_neg, zpow_neg, mul_assoc]
      cases l₁ using List.reverseRecOn with
      | nil =>
        have hlen : l₂.length < n := by
          rw [← hn, hsplit]; simp
        have heq' : MultiHNN.wordProd (modHNNData M) (head * (g₁' * g₂)) l₂ =
            MultiHNN.of (modHNNData M) g := by
          rw [← heq, hsplit]
          simp only [MultiHNN.wordProd, List.nil_append, List.map_cons, List.prod_cons, map_mul]
          rw [← mul_assoc (MultiHNN.t (modHNNData M) i ^ (u : ℤ) * MultiHNN.of (modHNNData M) g₁),
            hpinch, map_mul, mul_assoc]
        exact ih l₂.length hlen (head * (g₁' * g₂)) l₂ (mul_mem hhead (mul_mem hg₁'_T hg₂_T))
          (fun e he => hl e (by rw [hsplit]; simp [he])) heq' rfl
      | append_singleton init last =>
        rcases last with ⟨j, v, hlast⟩
        have hlast_T : hlast ∈ modT M := hl (j, v, hlast) (by rw [hsplit]; simp)
        let l' := init ++ (j, v, hlast * (g₁' * g₂)) :: l₂
        have hlen : l'.length < n := by
          rw [← hn, hsplit]; simp [l']
        have heq' : MultiHNN.wordProd (modHNNData M) head l' = MultiHNN.of (modHNNData M) g := by
          rw [← heq, hsplit]
          simp only [l', MultiHNN.wordProd, List.map_append, List.prod_append, List.map_cons,
            List.prod_cons, List.map_nil, List.prod_nil, mul_one, map_mul, mul_assoc]
          congr 2
          congr 2
          have hpinch' :
              MultiHNN.t (modHNNData M) i ^ (u : ℤ) *
                (MultiHNN.of (modHNNData M) g₁ *
                  (MultiHNN.t (modHNNData M) i ^ ((-u : ℤˣ) : ℤ) *
                    (MultiHNN.of (modHNNData M) g₂ *
                      (l₂.map fun x => MultiHNN.t (modHNNData M) x.1 ^ (x.2.1 : ℤ) *
                        MultiHNN.of (modHNNData M) x.2.2).prod))) =
              MultiHNN.of (modHNNData M) g₁' *
                (MultiHNN.of (modHNNData M) g₂ *
                  (l₂.map fun x => MultiHNN.t (modHNNData M) x.1 ^ (x.2.1 : ℤ) *
                    MultiHNN.of (modHNNData M) x.2.2).prod) := by
            have := congrArg (fun z => z * (l₂.map fun x => MultiHNN.t (modHNNData M) x.1 ^
              (x.2.1 : ℤ) * MultiHNN.of (modHNNData M) x.2.2).prod) hpinch
            simpa [map_mul, mul_assoc] using this
          rw [hpinch']
        exact ih l'.length hlen head l' hhead (fun e he => by
          simp only [l', List.mem_append, List.mem_cons] at he
          rcases he with he | rfl | he
          · exact hl e (by rw [hsplit]; simp [he])
          · exact mul_mem hlast_T (mul_mem hg₁'_T hg₂_T)
          · exact hl e (by rw [hsplit]; simp [he])) heq' rfl

/-- Exact characterization of the word problem in `ModGroup M`:
`[k, t_p] = 1` iff `p ∈ ReachesZero M`. -/
theorem comm_mgK_mbConjT_eq_one_iff (p : ℤ × ℤ) :
    mgK M * mgOfBase M (mbConjT p) * (mgK M)⁻¹ * (mgOfBase M (mbConjT p))⁻¹ = 1 ↔
      p ∈ ReachesZero M := by
  rw [mul_inv_eq_one]
  constructor
  · intro hcomm
    let x : ModH1 M := MultiHNN.of (modHNNData M) (mbConjT p)
    have hx_mem : x ∈ modC M := by
      by_contra hnot
      let w : HNNExtension.NormalWord.ReducedWord (ModH1 M) (modC M) (modC M) :=
        { head := 1
          toList := [(1, x), (-1, 1)]
          chain := List.isChain_cons_cons.2 ⟨fun h => (hnot h).elim, List.isChain_singleton _⟩ }
      have hprod : w.prod (MulEquiv.refl (modC M)) = HNNExtension.of x := by
        simp only [HNNExtension.NormalWord.ReducedWord.prod, w, List.map_cons, List.map_nil,
          List.prod_cons, List.prod_nil, map_one, one_mul, mul_one, Units.val_one, zpow_one,
          Units.val_neg, zpow_neg]
        exact hcomm
      have hnil := HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range
        (MulEquiv.refl (modC M)) w ⟨x, hprod.symm⟩
      simp [w] at hnil
    obtain ⟨head, l, hhead, hl, heq⟩ := exists_wordProd_modT_of_mem_modC M hx_mem
    have hT : mbConjT p ∈ modT M := mem_modT_of_wordProd_eq_of M head l hhead hl heq
    have hfree : FreeGroup.of p ∈ Subgroup.closure (FreeGroup.of '' ReachesZero M) :=
      (mem_modT_iff_kerProj M (FreeGroup.of p)).1 (by simpa [mbConjTHom] using hT)
    exact (of_mem_closure_of_iff (ReachesZero M) p).1 hfree
  · intro hp
    have hx_mem : MultiHNN.of (modHNNData M) (mbConjT p) ∈ modC M := by
      induction hp using Relation.ReflTransGen.head_induction_on with
      | refl =>
        have h0 : mbConjT (0, 0) = mbT := by simp [mbConjT]
        rw [h0]
        exact Subgroup.subset_closure (Or.inl rfl)
      | @head a b hstep _ ih =>
        rcases hstep with ⟨q, hq, u, v, rfl, hq'⟩
        rw [List.mem_iff_getElem] at hq
        rcases hq with ⟨idx, hidx, rfl⟩
        let i : Fin M.rules.length := ⟨idx, hidx⟩
        have hα : modAlpha M i (mbConjT (u, v)) =
            mbConjT (u * (M.m : ℤ) + (M.rules[i].a : ℤ), v * (M.m : ℤ) + (M.rules[i].b : ℤ)) :=
          conjModBase_mbConjT _ _ _ (u, v)
        have hβ : modBeta M i (mbConjT (u, v)) = mbConjT (M.rules[i].applyPair u v) := by
          have := modBeta_mbConjTHom M i (FreeGroup.of (u, v))
          simpa [mbConjTHom, modFB] using this
        have hconj := MultiHNN.equiv_eq_conj (modHNNData M) i
          ⟨modAlpha M i (mbConjT (u, v)), ⟨mbConjT (u, v), rfl⟩⟩
        rw [modHNNData_iso_apply M i] at hconj
        change MultiHNN.of (modHNNData M) (modBeta M i (mbConjT (u, v))) =
          MultiHNN.t (modHNNData M) i * MultiHNN.of (modHNNData M) (modAlpha M i (mbConjT (u, v))) *
            (MultiHNN.t (modHNNData M) i)⁻¹ at hconj
        change b = M.rules[i].applyPair u v at hq'
        rw [hα, hβ, ← hq'] at hconj
        have hinv : MultiHNN.of (modHNNData M)
            (mbConjT (u * (M.m : ℤ) + (M.rules[i].a : ℤ), v * (M.m : ℤ) + (M.rules[i].b : ℤ))) =
            (MultiHNN.t (modHNNData M) i)⁻¹ * MultiHNN.of (modHNNData M) (mbConjT b) *
              MultiHNN.t (modHNNData M) i := by
          rw [hconj]; group
        change MultiHNN.of (modHNNData M)
            (mbConjT (u * (M.m : ℤ) + (M.rules[i].a : ℤ), v * (M.m : ℤ) + (M.rules[i].b : ℤ))) ∈ modC M
        rw [hinv]
        have hri : MultiHNN.t (modHNNData M) i ∈ modC M :=
          Subgroup.subset_closure (Or.inr ⟨i, rfl⟩)
        exact mul_mem (mul_mem (inv_mem hri) ih) hri
    exact mgK_comm_of_mem_modC M hx_mem

end WordProblem

/-! ### Part 5: The Unconditional Novikov–Boone Theorem -/

/-- Encode a pair `(a, b) : ℕ × ℕ` as the raw commutator word `[k, (x^a y^b)⁻¹ t (x^a y^b)]`
in `modPres M`. -/
def modWordOfPair (M : ModularMachine) (p : ℕ × ℕ) : List (Fin (4 + M.rules.length) × Bool) :=
  wordComm (wordOf (modGenK M))
    (wordConj (wordPow (wordOf (modGenX M)) p.1 ++ wordPow (wordOf (modGenY M)) p.2)
      (wordOf (modGenT M)))

theorem modPres_mkWord_modWordOfPair_eq_one_iff (M : ModularMachine) (p : ℕ × ℕ) :
    (modPres M).mkWord (modWordOfPair M p) = 1 ↔ ((p.1 : ℤ), (p.2 : ℤ)) ∈ ReachesZero M := by
  rw [← (modPresEquiv M).map_eq_one_iff]
  simp only [modWordOfPair, FinPres.mkWord, freeGroup_mk_wordComm, freeGroup_mk_wordConj,
    freeGroup_mk_append, freeGroup_mk_wordPow, freeGroup_mk_wordOf, map_mul, map_inv, map_pow]
  change (modPresEquiv M) ((modPres M).ofGen (modGenK M)) *
      (((modPresEquiv M) ((modPres M).ofGen (modGenX M)) ^ p.1 *
        (modPresEquiv M) ((modPres M).ofGen (modGenY M)) ^ p.2)⁻¹ *
        (modPresEquiv M) ((modPres M).ofGen (modGenT M)) *
        ((modPresEquiv M) ((modPres M).ofGen (modGenX M)) ^ p.1 *
          (modPresEquiv M) ((modPres M).ofGen (modGenY M)) ^ p.2)) *
      ((modPresEquiv M) ((modPres M).ofGen (modGenK M)))⁻¹ *
      (((modPresEquiv M) ((modPres M).ofGen (modGenX M)) ^ p.1 *
        (modPresEquiv M) ((modPres M).ofGen (modGenY M)) ^ p.2)⁻¹ *
        (modPresEquiv M) ((modPres M).ofGen (modGenT M)) *
        ((modPresEquiv M) ((modPres M).ofGen (modGenX M)) ^ p.1 *
          (modPresEquiv M) ((modPres M).ofGen (modGenY M)) ^ p.2))⁻¹ = 1 ↔ _
  rw [modPresEquiv_ofGen_X, modPresEquiv_ofGen_Y, modPresEquiv_ofGen_T, modPresEquiv_ofGen_K]
  have ht : (mgOfBase M mbX ^ p.1 * mgOfBase M mbY ^ p.2)⁻¹ * mgOfBase M mbT *
      (mgOfBase M mbX ^ p.1 * mgOfBase M mbY ^ p.2) =
      mgOfBase M (mbConjT ((p.1 : ℤ), (p.2 : ℤ))) := by
    simp only [mbConjT, mbG_eq_zpow, zpow_natCast, map_mul, map_inv, map_pow]
  rw [ht]
  exact comm_mgK_mbConjT_eq_one_iff M ((p.1 : ℤ), (p.2 : ℤ))

theorem primrec_modWordOfPair (M : ModularMachine) : Primrec (modWordOfPair M) := by
  unfold modWordOfPair wordConj
  have hx : Primrec (fun p : ℕ × ℕ => wordPow (wordOf (modGenX M)) p.1) :=
    primrec_wordPow.comp (Primrec.const (wordOf (modGenX M))) Primrec.fst
  have hy : Primrec (fun p : ℕ × ℕ => wordPow (wordOf (modGenY M)) p.2) :=
    primrec_wordPow.comp (Primrec.const (wordOf (modGenY M))) Primrec.snd
  have hxy : Primrec (fun p : ℕ × ℕ =>
      wordPow (wordOf (modGenX M)) p.1 ++ wordPow (wordOf (modGenY M)) p.2) :=
    Primrec.list_append.comp hx hy
  have hconj : Primrec (fun p : ℕ × ℕ =>
      wordInv (wordPow (wordOf (modGenX M)) p.1 ++ wordPow (wordOf (modGenY M)) p.2) ++
        wordOf (modGenT M) ++
        (wordPow (wordOf (modGenX M)) p.1 ++ wordPow (wordOf (modGenY M)) p.2)) :=
    Primrec.list_append.comp
      (Primrec.list_append.comp (primrec_wordInv.comp hxy) (Primrec.const (wordOf (modGenT M))))
      hxy
  exact primrec_wordComm.comp (Primrec.const (wordOf (modGenK M))) hconj

/-- **The Novikov–Boone Theorem**: There exists a finitely presented group whose word problem
is algorithmically undecidable. -/
theorem novikov_boone :
    ∃ P : FinPres,
      ¬ ComputablePred (fun w : List (Fin P.numGens × Bool) => P.mkWord w = 1) := by
  obtain ⟨M, encodeInit, henc_prim, hundec⟩ := exists_undecidable_modularMachine
  refine ⟨modPres M, ?_⟩
  exact not_computablePred_of_reduction
    ((primrec_modWordOfPair M).comp henc_prim).to_comp
    (fun n => (modPres_mkWord_modWordOfPair_eq_one_iff M (encodeInit n)).symm)
    hundec

end

end Adian
