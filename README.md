# Formalization of the Adian–Rabin Theorem in Lean 4

A complete, unconditional formalization of the **Adian–Rabin theorem** (Adian 1955, Rabin 1958) and the **Novikov–Boone theorem** (Novikov 1955, Boone 1958) in [Lean 4](https://lean-lang.org/) (`v4.36.0`) using [Mathlib](https://github.com/leanprover-community/mathlib4), with **zero `sorry`s** and **zero custom axioms**.

> **Adian–Rabin Theorem.** No Markov property of finitely presented groups is algorithmically decidable.

Everything is built from Mathlib's uncomputability of the halting problem (`ComputablePred.halting_problem 0`) down to Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

---

## Main Theorems

### Novikov–Boone Theorem ([`Adian/NovikovBoone.lean`](Adian/NovikovBoone.lean))
```lean
theorem Adian.novikov_boone :
    ∃ P : FinPres,
      ¬ ComputablePred (fun w : List (Fin P.numGens × Bool) => P.mkWord w = 1)
```
There exists a concrete finite group presentation `P : FinPres` whose word problem is undecidable.

### Adian–Rabin Theorem ([`Adian/AdianRabin.lean`](Adian/AdianRabin.lean))
```lean
structure Adian.IsMarkovProperty (P : GroupProp) : Prop where
  abstract : P.IsAbstract
  exists_pos : ∃ F₁ : FinPres, P F₁.Group
  exists_neg : ∃ F₂ : FinPres,
    ∀ (G : Type) [Group G], Group.IsFinitelyPresented G →
      (∃ f : F₂.Group →* G, Function.Injective f) → ¬ P G

theorem Adian.adian_rabin (P : GroupProp) (hP : IsMarkovProperty P) :
    ¬ ComputablePred (fun F : FinPres => P F.Group)
```
Also provided in conditional form as `Adian.adian_rabin_of_undecidable_word_problem`, reducing the word problem of any finite presentation `H` to deciding `P` on `FinPres`.

### Concrete Undecidability Corollaries ([`Adian/AdianRabin.lean`](Adian/AdianRabin.lean))

Given a finite group presentation `F : FinPres`, each of the following properties is proved undecidable:

| Corollary | Property of `F.Group` | Positive witness `F₁` | Negative witness `F₂` |
|---|---|---|---|
| `Adian.undecidable_trivial` | `Subsingleton F.Group` (trivial) | `⟨ \| ⟩` | `ℤ` |
| `Adian.undecidable_finite` | `Finite F.Group` (finite) | `⟨ \| ⟩` | `ℤ` |
| `Adian.undecidable_abelian` | `∀ x y, x * y = y * x` (abelian) | `⟨ \| ⟩` | `F₂` |
| `Adian.undecidable_torsionFree` | Torsion-free | `⟨ \| ⟩` | `ℤ / 2ℤ` |
| `Adian.undecidable_free` | `∃ ι, Nonempty (F.Group ≃* FreeGroup ι)` (free) | `⟨ \| ⟩` | `ℤ / 2ℤ` |
| `Adian.undecidable_cyclic` | `IsCyclic F.Group` (cyclic) | `⟨ \| ⟩` | `F₂` |
| `Adian.undecidable_solvable` | `Group.IsSolvable F.Group` (solvable) | `⟨ \| ⟩` | `S₅` |
| `Adian.undecidable_nilpotent` | `Group.IsNilpotent F.Group` (nilpotent) | `⟨ \| ⟩` | `S₅` |
| `Adian.undecidable_decidableWordProblem` | Decidable word problem | `⟨ \| ⟩` | Novikov–Boone group `H` |

---

## Proof Architecture

```text
ComputablePred.halting_problem 0  (Mathlib)
        │
        ▼   Adian/TMHalting.lean
Binary TM0 halting on a blank tape (exists_undecidable_blank_tm0)
        │
        ▼   Adian/ModularMachine.lean
Deterministic modular machine M on ℤ × ℤ halting at (0, 0) (exists_undecidable_modularMachine)
        │
        ▼   Adian/NovikovBoone.lean  +  Adian/MultiHNN.lean  +  Adian/FreeProductLemmas.lean
Aanderaa–Cohen 2-layer HNN group ModGroup M ≃* (modPres M).Group
  • Layer 1: MultiHNN over ModBase = ℤ² ∗ ℤ (one stable letter r_i per quadruple)
  • Layer 2: HNN extension with stable letter k commuting with t and all r_i
  • Multi-Letter Britton's Lemma + free kernel basis ⟹ [k, t_(α,β)] = 1 ↔ (α, β) ∈ ReachesZero M
        │
        ▼   novikov_boone
Finite presentation H with undecidable word problem
        │
        ▼   Adian/Rabin.lean  +  Adian/FreeProductLemmas.lean  +  Adian/MultiHNN.lean
Rabin's primitive-recursive presentation rabinPres K w
  • K.mkWord w = 1  ⟹  (rabinPres K w).Group collapses to the trivial group
  • K.mkWord w ≠ 1  ⟹  K.Group embeds into (rabinPres K w).Group via
                       K ↪ K∗ℤ ↪ (K∗ℤ)∗AffQ ↪ HNN_d ↪ (HNN_d)∗ℤ ↪ HNN_e ↪ AmalgamTarget A B
        │
        ▼   Adian/AdianRabin.lean
Given Markov property P (witnesses F₁, F₂), K := H ∗ F₂, Ψ(w) := rabinPres K w ∗ F₁:
  • H.mkWord w = 1  ⟹  (Ψ w).Group ≃* F₁.Group  ⟹  P (Ψ w).Group
  • H.mkWord w ≠ 1  ⟹  F₂.Group ↪ (Ψ w).Group   ⟹  ¬ P (Ψ w).Group
        │
        ▼
Adian.adian_rabin  &  9 concrete corollaries
```

---

## Repository Structure

| File | Description |
|---|---|
| [`Adian.lean`](Adian.lean) | Root module importing the full formalization |
| [`Adian/FinPres.lean`](Adian/FinPres.lean) | Concrete `FinPres`, `Primcodable FinPres`, free-product presentations `FinPres.coprod` / `coprodEquiv`, equivalence with `Group.IsFinitelyPresented`, and many-one reduction lemmas |
| [`Adian/MultiHNN.lean`](Adian/MultiHNN.lean) | Amalgamated free product embedding target `AmalgamTarget` and iterated `MultiHNN` with Multi-Letter Britton's Lemma (`exists_pinch_of_mem_of_range`) |
| [`Adian/FreeProductLemmas.lean`](Adian/FreeProductLemmas.lean) | Free-group retracts, `ModBase = ℤ² ∗ ℤ` with free kernel basis `kerProjBasis`, affine Baumslag–Solitar model `AffQ`, commutator infinite order, Rabin's free subgroups `rabinP`/`rabinQ`, and rank-2 free pairs in HNN extensions |
| [`Adian/TMHalting.lean`](Adian/TMHalting.lean) | Compiles `ComputablePred.halting_problem 0` through Mathlib's `Partrec → TM2 → TM1 → TM0` stack and wraps it into a binary `TM0` that erases its tape before halting |
| [`Adian/ModularMachine.lean`](Adian/ModularMachine.lean) | Deterministic modular machines on `ℤ × ℤ` and exact simulation of blank-halting binary `TM0` |
| [`Adian/NovikovBoone.lean`](Adian/NovikovBoone.lean) | Aanderaa–Cohen modular machine group, presentation isomorphism, word problem characterization, and `novikov_boone` |
| [`Adian/Rabin.lean`](Adian/Rabin.lean) | Rabin's `rabinPres`, primitive recursiveness (`primrec_rabinPres`), collapse (`rabinPres_subsingleton_of_eq_one`), and embedding (`rabinIncl_injective_of_ne_one`) |
| [`Adian/AdianRabin.lean`](Adian/AdianRabin.lean) | `IsMarkovProperty`, `adian_rabin_of_undecidable_word_problem`, `adian_rabin`, and 9 undecidability corollaries |

---

## Building and Verifying

Requires [elan](https://github.com/leanprover/elan) (toolchain `leanprover/lean4:v4.36.0` is pinned in [`lean-toolchain`](lean-toolchain)).

```bash
# Download precompiled Mathlib oleans (recommended)
lake exe cache get

# Build the entire formalization
lake build
```

### Axiom Audit

You can verify that every main theorem depends exclusively on Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`):

```bash
printf 'import Adian
#print axioms Adian.novikov_boone
#print axioms Adian.adian_rabin
#print axioms Adian.undecidable_trivial
#print axioms Adian.undecidable_finite
#print axioms Adian.undecidable_abelian
#print axioms Adian.undecidable_torsionFree
#print axioms Adian.undecidable_free
#print axioms Adian.undecidable_cyclic
#print axioms Adian.undecidable_solvable
#print axioms Adian.undecidable_nilpotent
#print axioms Adian.undecidable_decidableWordProblem
' | lake env lean --stdin
```
