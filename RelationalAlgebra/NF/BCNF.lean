import RelationalAlgebra.RelationalModel
import RelationalAlgebra.RA.RelationalAlgebra
import RelationalAlgebra.NF.FuncDep
import RelationalAlgebra.NF.Closure
import RelationalAlgebra.NF.Superkey

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Finset.Powerset

namespace RM

namespace NF

variable {α μ : Type} [DecidableEq α]

def is_BCNF (R : Finset α) (F : Finset (FunctionalDependency α)) : Prop :=
    ∀ {f}, implies_proj F R f → f.is_trivial ∨ is_superkey f.lhs R F

def is_BCNF_syn (R : Finset α) (F : Finset (FunctionalDependency α)) : Prop :=
    ∀ {X}, X ⊆ R → attr_closure_proj F X R = R ∨ attr_closure_proj F X R = X

lemma BCNF_sem_eq_syn {R : Finset α} {F : Finset (FunctionalDependency α)} :
  is_BCNF R F ↔ is_BCNF_syn R F := by
  rw [is_BCNF, is_BCNF_syn]
  constructor
  · intro h_sem X h_X
    have h_imp : implies_proj F R (X -> attr_closure_proj F X R) := by
      rw [implies_proj, attr_closure_proj]
      constructor
      · apply armstrong_sound
        exact Derives.transitivity attr_closure_sound (Derives.reflexivity Finset.inter_subset_left)
      · constructor
        · trivial
        · simp
    apply h_sem at h_imp
    simp [FunctionalDependency.is_trivial, is_superkey, implies_proj] at h_imp
    rcases h_imp with h_trivial | h_superkey
    · right
      rw [subset_antisymm_iff]
      constructor
      · trivial
      · exact Finset.subset_inter attr_closure_subset_impl h_X
    · left
      rcases h_superkey with ⟨_, ⟨h_imp, _⟩⟩
      rw [attr_closure_proj, Finset.inter_eq_right]
      apply attr_closure_complete
      apply armstrong_complete
      exact h_imp
  · intro h_syn f h_imp
    rw [implies_proj] at h_imp
    rcases h_imp with ⟨h_imp, ⟨h_lhs, h_rhs⟩⟩
    rcases h_syn h_lhs with h_rhs_eq_R | h_rhs_eq_lhs
    · right
      rw [is_superkey]
      constructor
      · trivial
      · constructor
        · rw [attr_closure_proj, Finset.inter_eq_right] at h_rhs_eq_R
          apply armstrong_sound
          apply Derives.transitivity attr_closure_sound (Derives.reflexivity h_rhs_eq_R)
        · simp
          trivial
    · left
      rw [attr_closure_proj] at h_rhs_eq_lhs
      apply armstrong_complete at h_imp
      apply attr_closure_complete at h_imp
      have h_rhs_inter_r : f.rhs ∩ R = f.rhs := by
        rw [Finset.inter_eq_left]
        trivial
      have h_rhs_r_sub_ac_r : f.rhs ∩ R ⊆ attr_closure_impl F f.lhs ∩ R := Finset.inter_subset_inter_right h_imp
      rw [h_rhs_inter_r, h_rhs_eq_lhs] at h_rhs_r_sub_ac_r
      trivial

def is_violator (X R : Finset α) (F : Finset (FunctionalDependency α)) : Prop :=
    X ⊆ R ∧ attr_closure_proj F X R ≠ R ∧ attr_closure_proj F X R ≠ X

instance decidable_is_violator (X R : Finset α) (F : Finset (FunctionalDependency α)) :
  Decidable (is_violator X R F) := by
  unfold is_violator
  infer_instance

def find_bcnf_violators (R : Finset α) (F : Finset (FunctionalDependency α)) : Finset (Finset α) :=
    R.powerset.filter (fun X => is_violator X R F)

inductive SchemaTree (α) where
  | leaf (R : Finset α) : SchemaTree α
  | node (R R₁ R₂ : Finset α) (left right : SchemaTree α) : SchemaTree α
deriving Nonempty

def SchemaTree.leaves : SchemaTree α → Finset (Finset α)
  | leaf R => {R}
  | node _ _ _ left right => left.leaves ∪ right.leaves

lemma R1_card_lt_R {X R : Finset α} {F : Finset (FunctionalDependency α)}
  (h_violator : is_violator X R F) :
  (attr_closure_proj F X R).card < R.card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · exact attr_closure_proj_subset
  · rw [is_violator] at h_violator
    rcases h_violator with ⟨_, h_xp_ne_R, _⟩
    trivial

lemma R2_card_lt_R {X R : Finset α} {F : Finset (FunctionalDependency α)}
  (h_violator : is_violator X R F) :
  ((R \ attr_closure_proj F X R) ∪ X).card < R.card := by
  apply Finset.card_lt_card
  rw [is_violator] at h_violator
  rcases h_violator with ⟨h_X, _, h_xp_ne_X⟩
  rw [← Finset.sdiff_sdiff_eq_sdiff_union]
  · apply Finset.sdiff_ssubset
    · exact Finset.Subset.trans Finset.sdiff_subset attr_closure_proj_subset
    · rw [Finset.sdiff_nonempty]
      have h : X ⊂ attr_closure_proj F X R := by
        rw [Finset.ssubset_iff_subset_ne]
        constructor
        · exact subset_attr_closure_proj h_X
        · symm at h_xp_ne_X
          trivial
      rw [Finset.ssubset_def] at h
      rcases h with ⟨_, h⟩
      trivial
  · exact h_X

def BCNF_decompose
  (R : Finset α) (F : Finset (FunctionalDependency α))
  (picker : Finset (Finset α) → Option (Finset α)) : SchemaTree α :=
    let violators := find_bcnf_violators R F
    if violators = ∅ then SchemaTree.leaf R
    else match picker violators with
      | none => SchemaTree.leaf R
      | some X =>
        if h_X : X ∈ violators then
          have h_violator : is_violator X R F := by
            dsimp [violators, find_bcnf_violators] at h_X
            exact (Finset.mem_filter.mp h_X).2
          let R₁ := attr_closure_proj F X R
          let R₂ := (R \ attr_closure_proj F X R) ∪ X
          SchemaTree.node R R₁ R₂ (BCNF_decompose R₁ F picker) (BCNF_decompose R₂ F picker)
        else SchemaTree.leaf R
termination_by R.card
decreasing_by
  · exact R1_card_lt_R h_violator
  · exact R2_card_lt_R h_violator

end NF

end RM
