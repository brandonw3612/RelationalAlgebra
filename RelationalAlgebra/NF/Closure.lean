import RelationalAlgebra.NF.FuncDep
import RelationalAlgebra.NF.Misc

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Lattice.Fold

namespace RM

namespace NF

variable {α μ : Type} [DecidableEq α]

section Implication

/-- A functional dependency `f` is implied by a set of functional dependencies `F` if every relation instance that satisfies all dependencies in `F` also satisfies `f`. -/
def implies (F : Finset (FunctionalDependency α)) (f : FunctionalDependency α) : Prop :=
  ∀ {μ : Type} (r : RelationInstance α μ), r.satisfies F → f.holds r

/-- Notation for implication of functional dependencies. -/
infix:50 " ⊨ " => implies

end Implication

section Armstrong

/-- Armstrong's axioms for functional dependencies. -/
inductive Derives (F : Finset (FunctionalDependency α)) : FunctionalDependency α → Prop where
  /-- a₀: If a functional dependency is in the set, then it can be derived. -/
  | member : ∀ f ∈ F, Derives F f
  /-- a₁ (Reflexivity): if Y is a subset of X, then X -> Y. -/
  | reflexivity : ∀ (X Y : Finset α), Y ⊆ X → Derives F (X -> Y)
  /-- a₂ (Augmentation): if X -> Y, then XZ -> YZ for any Z. -/
  | augmentation : ∀ (X Y Z : Finset α), Derives F (X -> Y) → Derives F (X ∪ Z -> Y ∪ Z)
  /-- a₃ (Transitivity): if X -> Y and Y -> Z, then X -> Z. -/
  | transitivity : ∀ (X Y Z : Finset α), Derives F (X -> Y) → Derives F (Y -> Z) → Derives F (X -> Z)

/-- Notation for derivation of functional dependencies. -/
infix:50 " ⊢ " => Derives

/-- Soundness of Armstrong's Axioms: if F ⊢ f, then F ⊨ f. -/
theorem armstrong_sound {F : Finset (FunctionalDependency α)} {f : FunctionalDependency α} :
  F ⊢ f → F ⊨ f := by
  intro h_der μ r h_sat
  induction h_der with
  | member f h_in => exact h_sat f h_in
  | reflexivity X Y h_y_subset_x =>
    intro t₁ t₂ h_t₁ h_t₂ h_eq_x s h_s_in_y
    have h_s_in_x : s ∈ X := h_y_subset_x h_s_in_y
    exact h_eq_x s h_s_in_x
  | augmentation X Y Z h_der_xy h_xy_holds =>
    intro t₁ t₂ h_t₁ h_t₂ h_eq_xz s h_s_in_yz
    cases Finset.mem_union.mp h_s_in_yz with
    | inl h_s_in_y =>
      have h_eq_x : ∀ a ∈ X, t₁ a = t₂ a := by
        intro a h_a_in_x
        have h_a_in_xz : a ∈ X ∪ Z := by simp [h_a_in_x]
        exact h_eq_xz a h_a_in_xz
      exact h_xy_holds t₁ t₂ h_t₁ h_t₂ h_eq_x s h_s_in_y
    | inr h_s_in_z =>
      have h_s_in_xz : s ∈ X ∪ Z := by simp [h_s_in_z]
      exact h_eq_xz s h_s_in_xz
  | transitivity X Y Z h_der_xy h_der_yz h_xy_holds h_yz_holds =>
    intro t₁ t₂ h_t₁ h_t₂ h_eq_x s h_s_in_z
    have h_eq_y : ∀ a ∈ Y, t₁ a = t₂ a := by
      intro a h_a_in_y
      exact h_xy_holds t₁ t₂ h_t₁ h_t₂ h_eq_x a h_a_in_y
    exact h_yz_holds t₁ t₂ h_t₁ h_t₂ h_eq_y s h_s_in_z

theorem armstrong_complete {F : Finset (FunctionalDependency α)} {f : FunctionalDependency α} :
  F ⊨ f → F ⊢ f := by
  sorry

/-- b₁ (Union): if X -> Y and X -> Z, then X -> YZ. -/
theorem derives_union {F : Finset (FunctionalDependency α)} {X Y Z : Finset α} :
  F ⊢ (X -> Y) → F ⊢ (X -> Z) → F ⊢ (X -> Y ∪ Z) := by
  intro h_der_x_y h_der_x_z
  have h_der_x_xx_xy : F ⊢ (X -> Y ∪ X) := by simpa using Derives.augmentation X Y X h_der_x_y
  have h_der_x_xy_yz : F ⊢ (Y ∪ X -> Y ∪ Z) := by
    apply Derives.augmentation X Z Y at h_der_x_z
    rw [Finset.union_comm X Y, Finset.union_comm Z Y] at h_der_x_z
    exact h_der_x_z
  exact Derives.transitivity X (Y ∪ X) (Y ∪ Z) h_der_x_xx_xy h_der_x_xy_yz

/-- b₂ (Decomposition): if X -> YZ, then X -> Y and X -> Z. -/
theorem derives_decomposition {F : Finset (FunctionalDependency α)} {X Y Z : Finset α} :
  F ⊢ (X -> Y ∪ Z) → F ⊢ (X -> Y) ∧ F ⊢ (X -> Z) := by
  intro h_der_x_yz
  constructor
  · have h_der_yz_y : F ⊢ (Y ∪ Z -> Y) := by simpa using Derives.reflexivity (Y ∪ Z) Y
    exact Derives.transitivity X (Y ∪ Z) Y h_der_x_yz h_der_yz_y
  · have h_der_yz_z : F ⊢ (Y ∪ Z -> Z) := by simpa using Derives.reflexivity (Y ∪ Z) Z
    exact Derives.transitivity X (Y ∪ Z) Z h_der_x_yz h_der_yz_z

/-- b₃ (Pseudotransitivity): if X -> Y and YZ -> W, then XZ -> W. -/
theorem derives_pseudotransitivity {F : Finset (FunctionalDependency α)} {X Y Z W : Finset α} :
  F ⊢ (X -> Y) → F ⊢ (Y ∪ Z -> W) → F ⊢ (X ∪ Z -> W) := by
  intro h_der_x_y h_der_yz_w
  have h_der_xz_yz : F ⊢ (X ∪ Z -> Y ∪ Z) := by simpa using Derives.augmentation X Y Z h_der_x_y
  exact Derives.transitivity (X ∪ Z) (Y ∪ Z) W h_der_xz_yz h_der_yz_w

end Armstrong

section FuncDepClosure

/-- F⁺: Closure of a FD set. -/
def FuncDepClosure (F : Finset (FunctionalDependency α)) : Set (FunctionalDependency α) :=
  {f | F ⊨ f}

/--
  F⁺ contains **all** FDs implied by F.
  Correctness = Soundness (f ∈ F⁺ → F ⊨ f) + Completeness (F ⊨ f → f ∈ F⁺)
-/
theorem func_dep_closure_correct {F : Finset (FunctionalDependency α)} {f : FunctionalDependency α} :
  ∀ f : FunctionalDependency α, f ∈ FuncDepClosure F ↔ F ⊨ f := by
  sorry

end FuncDepClosure

section AttrClosure

/-- X⁺: Closure of an attribute set X with respect to a FD set, F. -/
def AttrClosure (F : Finset (FunctionalDependency α)) (X : Finset α) : Set α :=
  {a | (X -> {a} : FunctionalDependency α) ∈ FuncDepClosure F}

/--
  Single step iteration for computing the attribute set closure.
  If α -> β is in F and α ⊆ X, then we can add β to X.
-/
def _attrClosureStep (F : Finset (FunctionalDependency α)) (X : Finset α) : Finset α :=
  have f_filtered := {fd ∈ F | fd.lhs ⊆ X}
  X ∪ f_filtered.sup (λ fd => fd.rhs)

/-- Implementation of attribute set closure, where we iterate the single step |F| times (in the worst case). -/
def AttrClosureImpl (F : Finset (FunctionalDependency α)) (X : Finset α) : Finset α :=
  (_attrClosureStep F)^[F.card] X

lemma attr_closure_step_sound {F : Finset (FunctionalDependency α)} {X : Finset α} :
  F ⊢ (X -> _attrClosureStep F X) := by
  simp [_attrClosureStep]
  apply derives_union
  · apply Derives.reflexivity
    simp
  · set s := {fd ∈ F | fd.lhs ⊆ X}
    have h_s_subset_F : s ⊆ F := by simp [s]
    have h_s'_sup : ∀ s' ⊆ s, F ⊢ (X -> s'.sup (λ fd => fd.rhs)) := by
      intro s' h_s'_sub_s
      induction s' using Finset.induction with
      | empty => simp [Derives.reflexivity]
      | insert fd s'' h_fd_not_in_s'' h_ih =>
        simp [Finset.sup_insert]
        obtain ⟨h_fd, h_s''⟩ := Finset.insert_subset_iff.mp h_s'_sub_s
        apply derives_union
        · apply Derives.transitivity X fd.lhs fd.rhs
          · apply Derives.reflexivity
            simp [Finset.mem_filter.mp h_fd]
          · apply Derives.member
            have h_fd_in_F : fd ∈ F := by apply Finset.mem_of_subset h_s_subset_F h_fd
            exact h_fd_in_F
        · exact h_ih h_s''
    apply h_s'_sup s
    simp

lemma attr_closure_iterate_sound {F : Finset (FunctionalDependency α)} {X : Finset α} (n : ℕ) :
  F ⊢ (X -> (_attrClosureStep F)^[n] X) := by
  induction n with
  | zero => simp [Derives.reflexivity]
  | succ n ih =>
    apply Derives.transitivity X ((_attrClosureStep F)^[n] X) ((_attrClosureStep F)^[n + 1] X)
    · exact ih
    · rw [Function.iterate_succ_apply']
      set Y := (_attrClosureStep F)^[n] X
      exact attr_closure_step_sound

lemma attr_closure_sound {F : Finset (FunctionalDependency α)} {X : Finset α} :
  F ⊢ (X -> AttrClosureImpl F X) := by
  simp [AttrClosureImpl]
  exact attr_closure_iterate_sound F.card

lemma attr_closure_complete {F : Finset (FunctionalDependency α)} {X : Finset α} (a : α) :
  F ⊢ (X -> Y) → Y ⊆ AttrClosureImpl F X := by
  sorry

/--
  X⁺ is the maximal β such that X -> β is in F⁺.
  Correctness = Validity (X -> X⁺ ∈ F⁺) + Maximality (∀ β, X -> β ∈ F⁺ → β ⊆ X⁺)
-/
theorem attr_closure_correct {F : Finset (FunctionalDependency α)} {X : Finset α} :
  AttrClosureImpl F X = AttrClosure F X := by
  sorry

/-- Syntactic superkey: a set of attributes K is a superkey with respect to a set of functional dependencies F if F implies K -> r.schema. -/
def isStructSuperkey (F : Finset (FunctionalDependency α)) (r : RelationInstance α μ) (K : Finset α) : Prop :=
  F ⊨ (K -> r.schema)

/--
  Application 1: Testing superkeys
  ∀ K ⊆ R.schema, K is a (syntactic) superkey **iff** K⁺ = R.schema.
-/
theorem superKeyViaAttrClosure {r : RelationInstance α μ} {F : Finset (FunctionalDependency α)} {K : Finset α} :
  K ⊆ r.schema → isStructSuperkey F r K ↔ AttrClosure F K = r.schema := by
  sorry

/--
  Application 1.1: A syntactic superkey implies a semantic superkey.
-/
theorem structSuperkeyImpliesSemanticSuperkey {r : RelationInstance α μ} {F : Finset (FunctionalDependency α)} {K : Finset α} :
  r.satisfies F → isStructSuperkey F r K → isSuperkey r K := by
  sorry

/--
  Application 2: Testing FDs
  ∀ S,T ⊆ R.schema, S -> T ∈ F⁺ **iff** T ⊆ S⁺.
  We simplify the left-hand side using f ∈ F⁺ ↔ F ⊨ f.
-/
theorem funcDepValidityViaAttrClosure {r : RelationInstance α μ} {F : Finset (FunctionalDependency α)} {S T : Finset α} :
  S ⊆ r.schema → T ⊆ r.schema → F ⊨ (S -> T) ↔ T ⊆ AttrClosureImpl F S := by
  sorry

end AttrClosure

end NF

end RM
