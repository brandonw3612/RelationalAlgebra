import RelationalAlgebra.RelationalModel
import RelationalAlgebra.RA.RelationalAlgebra
import RelationalAlgebra.NF.FuncDep
import RelationalAlgebra.NF.Closure
import RelationalAlgebra.NF.Superkey

import Mathlib.Data.Finset.Basic
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

end NF

end RM
