/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Finset.Sups
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.UpperLower.Basic

/-!
# Set family certificates

This file defines the certificator of two families of sets. If we consider set families `𝒜` and `ℬ`
as probabilistic events, the size of the certificator `𝒜 □ ℬ` corresponds to the probability that
`𝒜` and `ℬ` occur "disjointly".

## Main declarations

* `finset.certificator`: Certificator of two elements of a Boolean algebra
* `finset.card_certificator_le`: The Van den Berg-Kesten-Reimer inequality: The probability that `𝒜`
  and `ℬ` occur "disjointly" is less than the product of their probabilities.

## References

* D. Reimer, *Proof of the Van den Berg–Kesten Conjecture*
-/

@[expose] public section

open scoped FinsetFamily

variable {α : Type*}

namespace Finset
section BooleanAlgebra
variable [BooleanAlgebra α] (s t u : Finset α) {a : α}

noncomputable def certificator : Finset α :=
  open scoped Classical in
  {a ∈ s ∩ t | ∃ x y, IsCompl x y ∧ (∀ ⦃b⦄, a ⊓ x = b ⊓ x → b ∈ s) ∧ ∀ ⦃b⦄, a ⊓ y = b ⊓ y → b ∈ t}

scoped[FinsetFamily] infixl:70 " □ " => Finset.certificator

variable {s t u}

@[simp] lemma mem_certificator :
    a ∈ s □ t ↔
      ∃ x y, IsCompl x y ∧ (∀ ⦃b⦄, a ⊓ x = b ⊓ x → b ∈ s) ∧ ∀ ⦃b⦄, a ⊓ y = b ⊓ y → b ∈ t := by
  classical
  rw [certificator, mem_filter, and_iff_right_of_imp]
  rintro ⟨u, v, _, hu, hv⟩
  exact mem_inter.2 ⟨hu rfl, hv rfl⟩

lemma certificator_subset_inter [DecidableEq α] : s □ t ⊆ s ∩ t := by
  unfold certificator; convert filter_subset ..

open scoped Classical in
lemma certificator_subset_disjSups : s □ t ⊆ s ○ t := by
  simp_rw [subset_iff, mem_certificator, mem_disjSups]
  rintro x ⟨u, v, huv, hu, hv⟩
  refine ⟨x ⊓ u, hu (inf_right_idem _ _).symm, x ⊓ v, hv (inf_right_idem _ _).symm,
    huv.disjoint.mono inf_le_right inf_le_right, ?_⟩
  rw [← inf_sup_left, huv.codisjoint.eq_top, inf_top_eq]

variable (s t u)

lemma certificator_comm : s □ t = t □ s := by
  ext s; rw [mem_certificator, exists_comm]; simp [isCompl_comm, and_comm]

lemma IsUpperSet.certificator_eq_inter [DecidableEq α] (hs : IsUpperSet (s : Set α))
    (ht : IsLowerSet (t : Set α)) : s □ t = s ∩ t := by
  refine
    certificator_subset_inter.antisymm fun a ha ↦ mem_certificator.2 ⟨a, aᶜ, isCompl_compl, ?_⟩
  rw [mem_inter] at ha
  simp only [@eq_comm _ ⊥, ← sdiff_eq, inf_idem, right_eq_inf, _root_.sdiff_self, sdiff_eq_bot_iff]
  exact ⟨fun b hab ↦ hs hab ha.1, fun b hab ↦ ht hab ha.2⟩

lemma IsLowerSet.certificator_eq_inter [DecidableEq α] (hs : IsLowerSet (s : Set α))
    (ht : IsUpperSet (t : Set α)) : s □ t = s ∩ t := by
  refine certificator_subset_inter.antisymm fun a ha ↦
    mem_certificator.2 ⟨aᶜ, a, isCompl_compl.symm, ?_⟩
  rw [mem_inter] at ha
  simp only [@eq_comm _ ⊥, ← sdiff_eq, inf_idem, right_eq_inf, _root_.sdiff_self, sdiff_eq_bot_iff]
  exact ⟨fun b hab ↦ hs hab ha.1, fun b hab ↦ ht hab ha.2⟩

open scoped Classical in
lemma IsUpperSet.certificator_eq_disjSups (hs : IsUpperSet (s : Set α))
    (ht : IsUpperSet (t : Set α)) : s □ t = s ○ t := by
  refine certificator_subset_disjSups.antisymm fun a ha ↦ mem_certificator.2 ?_
  obtain ⟨x, hx, y, hy, hxy, rfl⟩ := mem_disjSups.1 ha
  refine ⟨x, xᶜ, isCompl_compl, ?_⟩
  simp only [inf_of_le_right, le_sup_left, right_eq_inf, ← sdiff_eq, hxy.sup_sdiff_cancel_left]
  exact ⟨fun b hab ↦ hs hab hx, fun b hab ↦ ht (hab.trans_le sdiff_le) hy⟩

end BooleanAlgebra

open scoped FinsetFamily

variable [DecidableEq α] [Fintype α] {𝒜 ℬ 𝒞 : Finset (Finset α)}

/-- The **Van den Berg-Kesten-Reimer Inequality**: The probability that `𝒜` and `ℬ` occur
"disjointly" is less than the product of their probabilities. -/
lemma card_certificator_le : 2 ^ Fintype.card α * #(𝒜 □ ℬ) ≤ #𝒜 * #ℬ := sorry

end Finset
