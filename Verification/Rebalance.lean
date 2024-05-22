import Verification.Rotate
import Verification.Tree
import Verification.AVL
import Mathlib.Tactic.Group

namespace Implementation

open BST (AVLNode.mk')
open Tree (AVLTree.balancingFactor AVLTree.balancingFactor_eq AVLTree.isAVL AVLNode.left_of_mk AVLNode.right_of_mk AVLNode.val_of_mk)
open Primitives
open avl_verification

-- Here's a bad annoying example
-- #reduce AVLNode.rotate_right _ (AVLNode.mk' 0 (AVLNode.mk' 1 (AVLNode.mk' 2 none none) (AVLNode.mk' 3 none (AVLNode.mk' 4 none none))) (AVLNode.mk' 5 none none))

-- TODO: For mathlib:
lemma neg_max (a b: ℤ): max a b = -min (-a) (-b) := by 
  simp [Int.max_def, Int.min_def]
  split_ifs <;> simp <;> linarith

lemma neg_min {a b: ℤ}: min a b = -max (-a) (-b) := by
  simp [Int.max_def, Int.min_def]
  split_ifs <;> simp <;> linarith

@[pspec]
theorem AVLNode.balance_factor_spec (self: AVLNode T):
  ∃ f, self.balance_factor = .ok f ∧ f.val = AVLTree.balancingFactor (some self) := by sorry

-- Useful technical lemma for the height computations.
lemma one_add_max_sub_max_one_add_max_cancel (x y: ℤ): x ≥ 0 -> y ≥ 0 -> 1 + Max.max x y - Max.max y (1 + Max.max x y) = 0 := by
  by_cases Hxy : (x ≤ y)
  . simp [Hxy]
  . push_neg at Hxy
    have Hysucc : y < 1 + x := by linarith [Hxy]
    simp [(max_eq_left $ le_of_lt Hxy), (max_eq_right $ le_of_lt Hysucc)]

lemma AVLTree.structure_of_nonzero_height (t: Tree.AVLTree T): 1 ≤ Tree.AVLTree.height t -> ∃ x left right h, t = some (AVLNode.mk x left right h) := by
  intro Ht
  match t with 
  | none => simp [Tree.AVLTree.height] at Ht
  | some (AVLNode.mk x left right h) => refine' ⟨ x, left, right, h, rfl ⟩

lemma AVLTree.left_structure_of_nonzero_bf (t: Tree.AVLTree T): 1 ≤ AVLTree.balancingFactor t -> ∃ x left right h, t = some (AVLNode.mk x (some left) right h) := by 
  intro Ht
  match t with 
  | none => simp [Tree.AVLTree.balancingFactor] at Ht
  | some (AVLNode.mk x none right h) => 
    simp [Tree.AVLTree.balancingFactor, Tree.AVLTree.height] at Ht; linarith [Ht]
  | some (AVLNode.mk x (some left) right h) => refine' ⟨ x, left, right, h, rfl ⟩

lemma AVLTree.right_structure_of_nonzero_bf (t: Tree.AVLTree T): AVLTree.balancingFactor t ≤ -1 -> ∃ x left right h, t = some (AVLNode.mk x left (some right) h) := by 
  intro Ht
  match t with 
  | none => simp [Tree.AVLTree.balancingFactor] at Ht
  | some (AVLNode.mk x left none h) => 
    simp [Tree.AVLTree.balancingFactor, Tree.AVLTree.height] at Ht; linarith [Ht]
  | some (AVLNode.mk x left (some right) h) => refine' ⟨ x, left, right, h, rfl ⟩

lemma AVLTree.left_height_of_bf {left: AVLNode T}: AVLTree.balancingFactor (some left) ≥ 0 -> Tree.AVLTree.height (some left) = 1 + Tree.AVLTree.height (Tree.AVLNode.left left) := by 
  intro Hlbf
  match left with 
  | AVLNode.mk x left_left left_right h => 
    simp [AVLTree.balancingFactor] at Hlbf 
    simp [Tree.AVLTree.height, Hlbf]

@[pspec]
lemma AVLNode.rebalance_spec_positive (left right: Tree.AVLTree T):
  -- TODO: assume that subtrees are AVL.
  AVLTree.isAVL left -> AVLTree.isAVL right -> AVLTree.balancingFactor (some $ AVLNode.mk x left right h) = 2 
    -> ∃ t_new, (AVLNode.mk x left right h).rebalance = .ok (true, t_new) ∧ AVLTree.isAVL (some t_new) := by
  intro H_left_avl H_right_avl H_balancing
  simp [AVLNode.rebalance]
  progress with AVLNode.balance_factor_spec as ⟨ bf, Hbf ⟩
  cases bf; rw [H_balancing] at Hbf; simp_all
  rename_i bf_val Hbf_min Hbf_max
  obtain ⟨ _, left_node, _, _, H_structure ⟩ := AVLTree.left_structure_of_nonzero_bf _ (by rw [H_balancing]; norm_num)
  rw [Option.some.injEq, AVLNode.mk.injEq] at H_structure
  replace H_structure := H_structure.2.1
  simp only [H_structure]
  progress with AVLNode.balance_factor_spec as ⟨ lbf, Hlbf ⟩
  split_ifs with Hlbf_rel_one
  . obtain ⟨ y, left_left, left_right, h', H_left_structure ⟩ := AVLTree.right_structure_of_nonzero_bf (some left_node) (by rw [← Hlbf, Hlbf_rel_one]; norm_cast)
    rw [Option.some.injEq] at H_left_structure
    progress with AVLNode.rotate_left_spec as ⟨ rotated₁, t_new₁, H_left_rotation ⟩
    progress with AVLNode.rotate_right_spec as ⟨ rotated, t_new, H_right_rotation ⟩
    simp only [H_left_structure, AVLNode.right_of_mk, Option.isNone_some, not_false_eq_true,
      neq_imp, AVLNode.val_of_mk, AVLNode.left_of_mk, IsEmpty.forall_iff, forall_true_left,
      true_and] at H_left_rotation
    replace H_left_rotation := H_left_rotation.2
    simp only [H_left_rotation, AVLNode.left_of_mk, Option.isNone_some, not_false_eq_true, neq_imp,
      AVLNode.val_of_mk, AVLNode.right_of_mk, IsEmpty.forall_iff, forall_true_left, true_and] at H_right_rotation
    replace H_right_rotation := H_right_rotation.2
    simp [H_right_rotation, AVLTree.isAVL, AVLTree.balancingFactor]
    simp [AVLTree.balancingFactor, H_structure, H_left_structure] at H_balancing
    have Hlbf' := Hlbf
    simp [H_left_structure, AVLTree.balancingFactor, Hlbf_rel_one] at Hlbf'
    rw [Tree.AVLTree.height_node_eq left_right] at Hlbf'; push_cast at Hlbf'
    set hr := Tree.AVLTree.height right
    set hll := Tree.AVLTree.height left_left
    set hlr := Tree.AVLTree.height_node left_right with hlr_def
    have H_hlr : (hll: ℤ) ≤ (hlr: ℤ) := by 
      simp [H_left_structure, AVLTree.balancingFactor, Hlbf_rel_one] at Hlbf
      linarith [Hlbf]
    simp [max_eq_right H_hlr] at H_balancing
    rw [hlr_def, Tree.AVLTree.height_node_eq left_right] at H_balancing; push_cast at H_balancing
    set hlrr := Tree.AVLTree.height (Tree.AVLNode.right left_right)
    set hlrl := Tree.AVLTree.height (Tree.AVLNode.left left_right)
    rw [(neg_max hlrr hr), Int.sub_neg, ← min_add_add_left, ← sub_eq_add_neg, ← sub_eq_add_neg]
    have H_hr : (max hlrl hlrr: ℤ) = hr := by linarith [H_balancing]
    have H_hll : (max hlrl hlrr: ℤ) = hll := by linarith [Hlbf']
    -- For reference:
    -- bf = hl - hr
    --    = 1 + hlr - hr because lbf = hll - hlr = -1 ⇒ hll ≤ hlr
    --    = 1 + (1 + max hlrl hlrr) - hr
    --    = 2 + max hlrl hlrr - hr
    --    = 2
    -- max hlrl hlrr = hr
    -- hlr = 1 + hll
    -- 1 + max hlrl hlrr = 1 + hll
    -- max hlrl hlrr = hll
    -- max(hll, hlrl) = max(max(hlrl, hlrr), hlrl) = max(hlrl, hlrr)
    -- max(hll, hlrl) - hr = 0
    -- max(hlrl, hlrr) - hlrr = max(lbf, 0) = max(-1, 0) = 0
    -- min(0, 0) = 0
    -- Min(Max(hll, hlrl) - hlrr, Max(hll, hlrl) - hr)
    rw [← H_hll, Max.right_comm, max_self, sub_eq_add_neg _ (hlrr: ℤ), ← max_add_add_right, ← sub_eq_add_neg, ← sub_eq_add_neg, H_hr]
    simp
  . 
    -- key: isAVL left ∧ isAVL right ∧ lbf ≠ -1
    have : lbf.val = 0 ∨ lbf.val = 1 := by 
      suffices H_ineq : |lbf.val| ≤ 1 by 
        simp [Int.abs_le_one_iff] at H_ineq
        rcases H_ineq with (_ | (_ | H_absurd))
        left; assumption
        right; assumption
        scalar_tac
      rw [AVLTree.isAVL, H_structure] at H_left_avl
      rw [Hlbf]; assumption
    progress with AVLNode.rotate_right_spec as ⟨ rotated, t_new, H_right_rotation ⟩
    simp [forall_true_left] at H_right_rotation
    simp [H_right_rotation.2, AVLTree.isAVL, AVLTree.balancingFactor]
    set hr := Tree.AVLTree.height right
    set hlr := Tree.AVLTree.height (Tree.AVLNode.right left_node)
    set hll := Tree.AVLTree.height (Tree.AVLNode.left left_node)
    -- key: bf = 1 + hll - hr = 2
    have bf_eq : (hll: ℤ) - (hr: ℤ) = 1 := by
      simp [AVLTree.balancingFactor] at H_balancing
      rw [H_structure, AVLTree.left_height_of_bf (by cases this <;> linarith)] at H_balancing
      push_cast at H_balancing
      linarith
    rw [Int.add_comm, ← Int.sub_sub, (neg_max hlr hr), Int.sub_neg, ← min_add_add_left, ← sub_eq_add_neg, ← sub_eq_add_neg]
    simp only [AVLTree.balancingFactor_eq, Tree.AVLTree.left_of_some, Tree.AVLTree.right_of_some] at Hlbf
    rw [← Hlbf, bf_eq]
    rcases this with (Hlbf_eq | Hlbf_eq) <;> simp [Hlbf_eq]; norm_cast


@[pspec]
theorem AVLNode.rebalance_spec (self: AVLNode T):
  AVLTree.isAVL (Tree.AVLNode.left self) -> AVLTree.isAVL (Tree.AVLNode.right self) -> (AVLTree.balancingFactor (some self)) = 2 ∨ (AVLTree.balancingFactor (some self)) = -2 
  -> ∃ t_new, self.rebalance = .ok (true, t_new)
      ∧ AVLTree.isAVL (some t_new) := by
      intro H_avl_left H_avl_right
      rintro (H_balancing | H_balancing)
      . match self with 
        | AVLNode.mk x left right h => 
          exact AVLNode.rebalance_spec_positive _ _ H_avl_left H_avl_right H_balancing
      -- BF = -2.
      . -- Mirror mirror argument time!
        sorry



end Implementation
