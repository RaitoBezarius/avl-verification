import Verification.Rotate
import Verification.Tree
import Verification.AVL
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Tactic.Group
import Verification.Rebalance.BalanceFactor
import Verification.Rebalance.Structure

namespace Implementation

open BST (AVLNode.mk')
open Tree (AVLTree.balancingFactor AVLTree.balancingFactor_eq AVLTree.isAVL AVLNode.left_of_mk AVLNode.right_of_mk AVLNode.val_of_mk)
open Primitives
open avl_verification

-- TODO: inline them.
lemma neg_max (a b: ℤ): max a b = -min (-a) (-b) := by 
  convert (max_neg_neg (-a) (-b))
  all_goals simp

lemma neg_min {a b: ℤ}: min a b = -max (-a) (-b) := by 
  convert (min_neg_neg (-a) (-b))
  all_goals simp

-- Useful technical lemma for the height computations.
lemma one_add_max_sub_max_one_add_max_cancel (x y: ℤ): x ≥ 0 -> y ≥ 0 -> 1 + Max.max x y - Max.max y (1 + Max.max x y) = 0 := by
  by_cases Hxy : (x ≤ y)
  . simp [Hxy]
  . push_neg at Hxy
    have Hysucc : y < 1 + x := by linarith [Hxy]
    simp [(max_eq_left $ le_of_lt Hxy), (max_eq_right $ le_of_lt Hysucc)]

-- TODO: remake me using the pure rebalancing.
@[pspec]
lemma AVLNode.rebalance_spec_positive (left right: Tree.AVLTree T):
  -- TODO: assume that subtrees are AVL.
  AVLTree.isAVL left -> AVLTree.isAVL right -> AVLTree.balancingFactor (some $ AVLNode.mk x left right h) = 2 
    -> ∃ t_new, (AVLNode.mk x left right h).rebalance = .ok (true, t_new) ∧ AVLTree.isAVL (some t_new) := by
  intro H_left_avl H_right_avl H_balancing
  simp [AVLNode.rebalance]
  progress with AVLNode.balance_factor_spec as ⟨ bf, Hbf ⟩
  cases bf; rw [H_balancing] at Hbf; simp_all only [AVLNode.rebalance.match_2.eq_2]
  rename_i bf_val Hbf_min Hbf_max
  -- FIXME: simp lemma broke something here.
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
    replace H_left_rotation := (H_left_rotation left_right rfl).2
    simp only [H_left_rotation, AVLNode.left_of_mk, Option.isNone_some, not_false_eq_true, neq_imp,
      AVLNode.val_of_mk, AVLNode.right_of_mk, IsEmpty.forall_iff, forall_true_left, true_and] at H_right_rotation
    replace H_right_rotation := (H_right_rotation _ rfl).2
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

end Implementation
