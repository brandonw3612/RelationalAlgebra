import RelationalAlgebra.NF.FuncDep
import RelationalAlgebra.NF.Misc

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Lattice.Fold

import Mathlib.Data.PFun

namespace RM

namespace NF

variable {α μ : Type} [DecidableEq α]

/-- A functional dependency `f` is implied by a set of functional dependencies `F` if every relation instance that satisfies all dependencies in `F` also satisfies `f`. -/
def implies (F : Finset (FunctionalDependency α)) (f : FunctionalDependency α) : Prop :=
  ∀ {μ : Type} (r : RelationInstance α μ), r.satisfies F → f.holds r

/-- Notation for implication of functional dependencies. -/
infix:50 " ⊨ " => implies

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

/-- F⁺: Closure of a FD set. -/
def func_dep_closure (F : Finset (FunctionalDependency α)) : Set (FunctionalDependency α) :=
  {f | F ⊨ f}

/-- X⁺: Closure of an attribute set X with respect to a FD set, F. (Weak definition.) -/
def attr_closure_weak (F : Finset (FunctionalDependency α)) (X : Finset α) : Set α :=
  {a | (X -> {a} : FunctionalDependency α) ∈ func_dep_closure F}

/-- Filtered set of FDs where lhs should be a subset of X.  -/
def left_filter (F : Finset (FunctionalDependency α)) (X : Finset α) : Finset (FunctionalDependency α) :=
  {fd ∈ F | fd.lhs ⊆ X}

/--
  Single step iteration for computing the attribute set closure.
  If α -> β is in F and α ⊆ X, then we can add β to X.
-/
def attr_closure_impl_step (F : Finset (FunctionalDependency α)) (X : Finset α) : Finset α :=
  have f_filtered := left_filter F X
  X ∪ f_filtered.sup (λ fd => fd.rhs)

/-- Auxiliary definition for iterating the closure step. -/
def ac_seq (F : Finset (FunctionalDependency α)) (X : Finset α) (n : ℕ) : Finset α :=
  (attr_closure_impl_step F)^[n] X

/-- Simply unfold the iteration by one layer. -/
lemma ac_seq_succ (F : Finset (FunctionalDependency α)) (X : Finset α) (n : ℕ) :
  ac_seq F X (n + 1) = attr_closure_impl_step F (ac_seq F X n) := by
  simp [ac_seq, Function.iterate_succ_apply']

/-- Implementation of attribute set closure, where we iterate the single step |F| times (in the worst case). -/
def attr_closure_impl (F : Finset (FunctionalDependency α)) (X : Finset α) : Finset α :=
  ac_seq F X F.card

/-- Soundness of a single step of the attribute set closure computation. -/
lemma attr_closure_step_sound {F : Finset (FunctionalDependency α)} {X : Finset α} :
  F ⊢ (X -> attr_closure_impl_step F X) := by
  simp [attr_closure_impl_step]
  apply derives_union
  · apply Derives.reflexivity
    simp
  · set s := left_filter F X
    have h_s_subset_F : s ⊆ F := by simp [left_filter, s]
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
            exact Finset.mem_of_subset h_s_subset_F h_fd
        · exact h_ih h_s''
    apply h_s'_sup s
    simp

/-- Soundness of the attribute closure implementation, induced by iterating the single step. -/
lemma attr_closure_sound {F : Finset (FunctionalDependency α)} {X : Finset α} :
  F ⊢ (X -> attr_closure_impl F X) := by
  simp [attr_closure_impl]
  induction F.card with
  | zero => simp [ac_seq, Derives.reflexivity]
  | succ n ih =>
    apply Derives.transitivity X (ac_seq F X n) (ac_seq F X (n + 1))
    · exact ih
    · simp [ac_seq_succ,attr_closure_step_sound]

/-- Subset property of a single step of the attribute set closure computation. -/
lemma attr_closure_subset_step {F : Finset (FunctionalDependency α)} {X : Finset α} :
  X ⊆ attr_closure_impl_step F X := by
  intro a ha
  simp [attr_closure_impl_step]
  exact Or.inl ha

/-- Subset property of the attribute set closure implementation. -/
lemma attr_closure_subset_impl {F : Finset (FunctionalDependency α)} {X : Finset α} :
  X ⊆ attr_closure_impl F X := by
  rw [attr_closure_impl]
  induction F.card with
    | zero => exact fun a ha => ha
    | succ n ih =>
      intro a ha
      simp [ac_seq_succ]
      exact attr_closure_subset_step (ih ha)

/-- X is a subset of the result for a single step. -/
lemma subset_step (F : Finset (FunctionalDependency α)) (X : Finset α) :
  X ⊆ attr_closure_impl_step F X := by
  simp [attr_closure_impl_step]

/-- left-filter is monotone with respect to the attribute set. -/
lemma filtered_mono {F : Finset (FunctionalDependency α)} {X Y : Finset α} (h : X ⊆ Y) :
  left_filter F X ⊆ left_filter F Y := by
  intro fd hfd
  simp [left_filter, Finset.mem_filter] at hfd ⊢
  exact ⟨hfd.1, fun a ha => h (hfd.2 ha)⟩

/-- When left-filter reaches the fixed point, the single step also does. -/
lemma fixed_of_filtered_eq {F : Finset (FunctionalDependency α)} {X : Finset α}
  (h : left_filter F X = left_filter F (attr_closure_impl_step F X)) :
  attr_closure_impl_step F (attr_closure_impl_step F X) = attr_closure_impl_step F X := by
  rw [attr_closure_impl_step, ← h, attr_closure_impl_step]
  simp

/-- The closure extends monotonically with respect to the number of iterations. -/
lemma seq_mono_step {F : Finset (FunctionalDependency α)} {X : Finset α} {n : ℕ} :
  ac_seq F X n ⊆ ac_seq F X (n + 1) := by
    simp [ac_seq_succ]
    exact subset_step F (ac_seq F X n)

/-- The left-filter with respect to the clusure set is monotone with respect to the number of iterations. -/
lemma seq_filtered_mono {F : Finset (FunctionalDependency α)} {X : Finset α} {n : ℕ} :
  left_filter F (ac_seq F X n) ⊆ left_filter F (ac_seq F X (n + 1)) :=
  filtered_mono seq_mono_step

/-- When the closure set stablizes at some point, it remains the same for all subsequent iterations. -/
lemma seq_fixed_of_eq {F : Finset (FunctionalDependency α)} {X : Finset α} {k n : ℕ}
  (h : ac_seq F X (k + 1) = ac_seq F X k) (hn : k ≤ n) :
  ac_seq F X n = ac_seq F X k := by
  have h_step : attr_closure_impl_step F (ac_seq F X k) = ac_seq F X k := by
    rw [← ac_seq_succ]
    exact h
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction d with
  | zero => rfl
  | succ d ih =>
    have heq : k + (d + 1) = k + d + 1 := by omega
    simp [heq, ac_seq_succ, ih, h_step]

/-- Lower bound for strict monotonicity. -/
lemma filtered_card_ge_succ (F : Finset (FunctionalDependency α)) (X : Finset α) (k : ℕ)
  (h_strict : ∀ i < k, left_filter F (ac_seq F X i) ⊂ left_filter F (ac_seq F X (i + 1)))
  (h_pos : 0 < (left_filter F (ac_seq F X 0)).card) :
  k + 1 ≤ (left_filter F (ac_seq F X k)).card := by
  induction k with
  | zero => exact h_pos
  | succ k ih =>
    have h_sub : left_filter F (ac_seq F X k) ⊂ left_filter F (ac_seq F X (k + 1)) := h_strict k (Nat.lt_succ_self k)
    have h_lt : (left_filter F (ac_seq F X k)).card < (left_filter F (ac_seq F X (k + 1))).card := Finset.card_lt_card h_sub
    have h_prev : ∀ i < k, left_filter F (ac_seq F X i) ⊂ left_filter F (ac_seq F X (i + 1)) := fun i hi => h_strict i (Nat.lt_trans hi (Nat.lt_succ_self k))
    have ih_val := ih h_prev
    omega

/-- The set of filtered dependencies cannot grow indefinitely. -/
lemma exists_filtered_eq (F : Finset (FunctionalDependency α)) (X : Finset α)
  (h_pos : 0 < (left_filter F (ac_seq F X 0)).card) :
  ∃ k < F.card, left_filter F (ac_seq F X k) = left_filter F (ac_seq F X (k + 1)) := by
  by_contra h_contra
  push_neg at h_contra
  have h_strict : ∀ i < F.card, left_filter F (ac_seq F X i) ⊂ left_filter F (ac_seq F X (i + 1)) := by
    intro i hi
    have h_ne := h_contra i hi
    rw [Finset.ssubset_iff_subset_ne]
    exact ⟨seq_filtered_mono, h_ne⟩
  have h_bound := filtered_card_ge_succ F X F.card h_strict h_pos
  have h_le : (left_filter F (ac_seq F X F.card)).card ≤ F.card := Finset.card_le_card (Finset.filter_subset _ _)
  omega

/-- The closure reaches a fixed point at step `|F|`. -/
lemma seq_stabilizes (F : Finset (FunctionalDependency α)) (X : Finset α) :
  ac_seq F X (F.card + 1) = ac_seq F X F.card := by
  by_cases h_zero : (left_filter F (ac_seq F X 0)).card = 0
  · have h_empty : left_filter F (ac_seq F X 0) = ∅ := Finset.card_eq_zero.mp h_zero
    have h_eq : ac_seq F X 1 = ac_seq F X 0 := by
      change attr_closure_impl_step F X = X
      rw [ac_seq, Function.iterate_zero, id, left_filter] at h_empty
      simp [attr_closure_impl_step, left_filter, h_empty]
    have h_all : ∀ n ≥ 0, ac_seq F X n = ac_seq F X 0 := fun n hn => seq_fixed_of_eq h_eq hn
    rw [h_all (F.card + 1) (Nat.zero_le _), h_all F.card (Nat.zero_le _)]
  · have h_pos : 0 < (left_filter F (ac_seq F X 0)).card := Nat.pos_of_ne_zero h_zero
    obtain ⟨k, hk_lt, hk_eq⟩ := exists_filtered_eq F X h_pos
    rw [ac_seq_succ] at hk_eq
    have h_eq : ac_seq F X (k + 2) = ac_seq F X (k + 1) := by
      simp [ac_seq_succ]
      exact fixed_of_filtered_eq hk_eq
    have h_all : ∀ n ≥ k + 1, ac_seq F X n = ac_seq F X (k + 1) := fun n hn => seq_fixed_of_eq h_eq hn
    have h1 : k + 1 ≤ F.card := hk_lt
    have h2 : k + 1 ≤ F.card + 1 := by omega
    rw [h_all (F.card + 1) h2, h_all F.card h1]

/-- The computed closure is closed under `F`: if an FD's LHS is in the closure, its RHS is also included. -/
lemma impl_closed {F : Finset (FunctionalDependency α)} {X : Finset α} :
  (attr_closure_impl F X).is_closed_under F := by
  set XP := attr_closure_impl F X
  intro fd hfd h_lhs
  have h_fixed_point : attr_closure_impl_step F XP = XP := by
    simp [XP, attr_closure_impl, ← ac_seq_succ]
    exact seq_stabilizes F X
  have h_step : fd.rhs ⊆ attr_closure_impl_step F XP := by
    intro a ha
    simp [attr_closure_impl_step, left_filter, Finset.mem_union, Finset.mem_sup]
    exact Or.inr ⟨fd, ⟨hfd, h_lhs⟩, ha⟩
  rw [h_fixed_point] at h_step
  exact h_step

/-- All attributes in the tuple are true. -/
def t_all_true (U : Finset α) : α →. Bool :=
  fun a => {
    Dom := a ∈ U
    get := fun _ => true
  }

/-- Only attributes in the closure S are true. -/
def t_closure (U S : Finset α) : α →. Bool :=
  fun a => {
    Dom := a ∈ U
    get := fun _ => decide (a ∈ S)
  }

/-- A counterexample relation instance that satisfies all FDs in F but violates the FD X -> Y when Y is not a subset of the closure of X. -/
def counterexample_relation (U S : Finset α) : RelationInstance α Bool where
  schema := U
  tuples := {t_all_true U, t_closure U S}
  validSchema := by
    intro t ht
    simp [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    ext x
    rcases ht with rfl | rfl
    · rfl
    · rfl

/-- If F is a set of FDs such that all FDs in F have their attributes contained in U, and S is closed under F, then the counterexample relation instance satisfies all FDs in F. -/
lemma counterexample_sat_F {U S : Finset α} {F : Finset (FunctionalDependency α)}
  (h_F_sub_U : ∀ fd ∈ F, fd.lhs ⊆ U ∧ fd.rhs ⊆ U) (h_closed : S.is_closed_under F) :
  (counterexample_relation U S).satisfies F := by
  intro fd hfd
  have hU := h_F_sub_U fd hfd
  intro t1 t2 ht1 ht2 h_agree_lhs
  simp [counterexample_relation, Set.mem_insert_iff, Set.mem_singleton_iff] at ht1 ht2
  rcases ht1 with rfl | rfl <;> rcases ht2 with rfl | rfl
  -- Case 1: t1 = t_all_true, t2 = t_all_true
  · simp
  -- Case 2: t1 = t_all_true, t2 = t_closure
  · have h_lhs_sub_S : fd.lhs ⊆ S := by
      intro a ha
      have h_eq := h_agree_lhs a ha
      simp [t_all_true, t_closure] at h_eq
      have h_val := congr_fun h_eq (hU.1 ha)
      exact of_decide_eq_true h_val.symm
    have h_rhs_sub_S : fd.rhs ⊆ S := h_closed fd hfd h_lhs_sub_S
    intro a ha
    simp [t_all_true, t_closure, h_rhs_sub_S ha]
  -- Case 3: t1 = t_closure, t2 = t_all_true
  · have h_lhs_sub_S : fd.lhs ⊆ S := by
      intro a ha
      have h_eq := h_agree_lhs a ha
      simp [t_all_true, t_closure] at h_eq
      have h_val := congr_fun h_eq (hU.1 ha)
      exact of_decide_eq_true h_val
    have h_rhs_sub_S : fd.rhs ⊆ S := h_closed fd hfd h_lhs_sub_S
    intro a ha
    simp [t_all_true, t_closure, h_rhs_sub_S ha]
  -- Case 4: t1 = t_closure, t2 = t_closure
  · simp

/-- If the FD X -> Y holds on the counterexample relation instance, then Y must be a subset of S. -/
lemma subset_of_closure_if_holds {U X Y S : Finset α}
  (h_X_sub_S : X ⊆ S) (h_Y_sub_U : Y ⊆ U)
  (h_holds : (X -> Y : FunctionalDependency α).holds (counterexample_relation U S)) :
  Y ⊆ S := by
  let t₁ := t_all_true U
  let t₂ := t_closure U S
  have h_t₁ : t₁ ∈ (counterexample_relation U S).tuples := Set.mem_insert _ _
  have h_t₂ : t₂ ∈ (counterexample_relation U S).tuples := Set.mem_insert_of_mem _ (Set.mem_singleton _)
  have h_agree_on_x : ∀ a ∈ X, t₁ a = t₂ a := by
    intro a ha_in_x
    simp [t₁, t₂, t_all_true, t_closure, h_X_sub_S ha_in_x]
  have h_agree_on_y : ∀ b ∈ Y, t₁ b = t₂ b := h_holds t₁ t₂ h_t₁ h_t₂ h_agree_on_x
  intro y hy
  have h_y_in_u := h_Y_sub_U hy
  have h_eq := h_agree_on_y y hy
  simp [t₁, t₂, t_all_true, t_closure] at h_eq
  have h_val := congr_fun h_eq h_y_in_u
  exact of_decide_eq_true h_val.symm

/-- If F ⊢ X -> Y, then Y is a subset of the closure of X. -/
lemma attr_closure_complete {F : Finset (FunctionalDependency α)} {X Y : Finset α} :
  F ⊢ (X -> Y) → Y ⊆ attr_closure_impl F X := by
  intro h_der
  set S := attr_closure_impl F X
  set U := X ∪ Y ∪ F.sup (fun fd => fd.lhs ∪ fd.rhs)
  have h_Y_sub_U : Y ⊆ U := by
    intro a ha
    apply Finset.mem_union.mpr
    left; apply Finset.mem_union.mpr; right
    exact ha
  have h_F_sub_U : ∀ fd ∈ F, fd.lhs ⊆ U ∧ fd.rhs ⊆ U := by
    intro fd hfd
    constructor
    · intro a ha
      apply Finset.mem_union.mpr; right
      simp [Finset.mem_sup, Finset.mem_union]
      exact ⟨fd, hfd, Or.inl ha⟩
    · intro a ha
      apply Finset.mem_union.mpr; right
      simp [Finset.mem_sup, Finset.mem_union]
      exact ⟨fd, hfd, Or.inr ha⟩
  have h_implies : F ⊨ (X -> Y) := armstrong_sound h_der
  have h_sat : (counterexample_relation U S).satisfies F :=
    counterexample_sat_F h_F_sub_U impl_closed
  have h_holds : (X -> Y : FunctionalDependency α).holds (counterexample_relation U S) :=
    h_implies (counterexample_relation U S) h_sat
  exact subset_of_closure_if_holds attr_closure_subset_impl h_Y_sub_U h_holds

/-- Completeness of Armstrong's Axioms: if F ⊨ f, then F ⊢ f. -/
theorem armstrong_complete {F : Finset (FunctionalDependency α)} {f : FunctionalDependency α} :
  F ⊨ f → F ⊢ f := by
  intro h_implies
  -- Step 0: Rename f: X -> Y
  set X := f.lhs
  set Y := f.rhs
  -- Step 1: Let S be the attribute closure of f.lhs.
  set S := attr_closure_impl F X
  -- Prove that S is closed under F.
  have h_closed : S.is_closed_under F := impl_closed
  -- Step 2: Define a universe U that contains all attributes from f and F.
  set U := X ∪ Y ∪ F.sup (fun fd => fd.lhs ∪ fd.rhs)
  have h_Y_sub_U : Y ⊆ U := by
    intro a ha
    apply Finset.mem_union.mpr
    left
    apply Finset.mem_union.mpr
    right
    exact ha
  have h_F_sub_U : ∀ fd ∈ F, fd.lhs ⊆ U ∧ fd.rhs ⊆ U := by
    intro fd hfd
    constructor
    · intro a ha
      apply Finset.mem_union.mpr
      right
      simp [Finset.mem_sup, Finset.mem_union]
      exact ⟨fd, hfd, Or.inl ha⟩
    · intro a ha
      apply Finset.mem_union.mpr
      right
      simp [Finset.mem_sup, Finset.mem_union]
      exact ⟨fd, hfd, Or.inr ha⟩
  -- Step 3: Instantiate the counterexample relation.
  set r := counterexample_relation U S
  have h_sat : r.satisfies F := counterexample_sat_F h_F_sub_U h_closed
  -- Because F ⊨ f, the counterexample relation must satisfy f.
  have h_f_holds : f.holds r :=  h_implies r h_sat
  -- Step 4: Prove X is a subset of its own closure S.
  have h_X_sub_S : X ⊆ S := by
    have h_ref : F ⊢ (X -> X) := Derives.reflexivity X X (subset_refl X)
    exact attr_closure_complete h_ref
  -- Because f holds on the relation, and Y ⊆ S, it must be that Y ⊆ S.
  have h_Y_sub_S : Y ⊆ S := subset_of_closure_if_holds h_X_sub_S h_Y_sub_U h_f_holds
  -- Step 5: Derive f from the fact that its RHS is in the closure of its LHS.
  have h_S_sound : F ⊢ (X -> S) := attr_closure_sound
  have h_Y_ref : F ⊢ (S -> Y) := Derives.reflexivity S Y h_Y_sub_S
  exact Derives.transitivity X S Y h_S_sound h_Y_ref

/-- Armstrong's axioms are correct, given their soundness and completeness. -/
theorem armstrong_correct {F : Finset (FunctionalDependency α)} {f : FunctionalDependency α} :
  F ⊢ f ↔ F ⊨ f := by
  constructor
  · exact armstrong_sound
  · exact armstrong_complete

/-- Prove that the computed attribute closure is correct with respect to the semantic definition of attribute closure. -/
theorem attr_closure_impl_correct {F : Finset (FunctionalDependency α)} {X : Finset α} :
  attr_closure_impl F X = attr_closure_weak F X := by
  ext x
  simp [attr_closure_weak, func_dep_closure, Set.mem_setOf_eq]
  constructor
  · intro h_x_in_impl
    apply armstrong_sound
    apply Derives.transitivity X (attr_closure_impl F X) {x} attr_closure_sound
    apply Derives.reflexivity (attr_closure_impl F X) {x}
    simp [h_x_in_impl]
  · intro h_x_in_attr_closure
    rw [← Finset.singleton_subset_iff]
    exact attr_closure_complete (armstrong_complete h_x_in_attr_closure)

/-- A strong definition of attribute closure, which is a finite set. -/
def attr_closure (F : Finset (FunctionalDependency α)) (X : Finset α) : Finset α :=
  attr_closure_impl F X

/-- Prove that the strong definition of attribute closure is equivalent to the weak definition via the implementation. -/
theorem attr_closure_strong_correct {F : Finset (FunctionalDependency α)} {X : Finset α} :
  attr_closure F X = attr_closure_weak F X := by
  simp [attr_closure, attr_closure_impl_correct]

/-- Syntactic superkey: a set of attributes K is a superkey with respect to a set of functional dependencies F if F implies K -> r.schema. -/
def isStructSuperkey (F : Finset (FunctionalDependency α)) (r : RelationInstance α μ) (K : Finset α) : Prop :=
  F ⊨ (K -> r.schema)

/--
  Application 1: Testing superkeys
  ∀ K ⊆ R.schema, K is a (syntactic) superkey **iff** K⁺ = R.schema.
-/
theorem superKeyViaAttrClosure {r : RelationInstance α μ} {F : Finset (FunctionalDependency α)} {K : Finset α} :
  K ⊆ r.schema → isStructSuperkey F r K ↔ attr_closure F K = r.schema := by
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
  S ⊆ r.schema → T ⊆ r.schema → F ⊨ (S -> T) ↔ T ⊆ attr_closure_impl F S := by
  sorry

end NF

end RM
