import Verification.Rotate
import Verification.Tree
import Verification.AVL
import Mathlib.Tactic.Group

namespace Implementation

open Tree (AVLTree.balancingFactor AVLTree.isAVL AVLNode.left_of_mk AVLNode.right_of_mk AVLNode.val_of_mk)
open Primitives
open avl_verification

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

@[pspec]
theorem AVLNode.rebalance_spec (self: AVLNode T):
  (AVLTree.balancingFactor (some self)) = 2 ∨ (AVLTree.balancingFactor (some self)) = -2 
  -> ∃ t_new, self.rebalance = .ok (true, t_new)
      ∧ AVLTree.isAVL (some t_new) := by
      rintro (H_balancing | H_balancing)
      all_goals (simp [AVLNode.rebalance]; progress with AVLNode.balance_factor_spec as ⟨ bf, Hbf ⟩; cases bf; rw [H_balancing] at Hbf; simp_all)
      . -- there is a left_node because BF = 2.
        have H_structure: ∃ x left_node right h, self = AVLNode.mk x (some left_node) right h := by
          convert AVLTree.left_structure_of_nonzero_bf (some self) _
          . simp only [Option.some.injEq]
          . rw [H_balancing]; norm_num
        obtain ⟨ x, left_node, right, h, H_structure ⟩ := H_structure
        simp [H_structure]
        progress with AVLNode.balance_factor_spec as ⟨ lbf, Hlbf ⟩
        split_ifs with Hlbf'
        . -- destructure left_node because lbf = 1.
          -- left balancing factor (lbf)
          have H_left_structure: ∃ x' left_left left_right h', left_node = AVLNode.mk x' (some left_left) left_right h' := by
            convert AVLTree.left_structure_of_nonzero_bf (some left_node) _
            . simp only [Option.some.injEq]
            . rw [← Hlbf, Hlbf']; norm_cast
          obtain ⟨ x', left_left, left_right, h', H_left_structure ⟩ := H_left_structure
          rw [H_left_structure]
          -- TODO: here, we have an annoying problem
          -- the spec is ill-written, the "or" case should be a true "or" case
          -- with a ∃ v, AVLTree.right self = .some v instead of letting Lean unify that variable
          -- right now, it unifies it to left_left instead of left_right because this is the
          -- only legitimate unification.
          -- but it's completely wrong.
          -- as an hack, we could match over left_right before getting to that progress
          -- and perform a manual simp on rotate_left in case it's a none so we can bring ourself back
          -- to the case of a single rotation...
          progress with AVLNode.rotate_left_spec as ⟨ rotated₁, t_new₁, H_left_rotation ⟩
          progress with AVLNode.rotate_right_spec as ⟨ rotated, t_new, H_right_rotation ⟩
          rcases H_left_rotation with ⟨ H_none_left_rotation, H_some_left_rotation ⟩
          rcases H_right_rotation with ⟨ _, H_right_rotation ⟩
          simp only [Result.ok.injEq, Prod.mk.injEq, true_and, AVLTree.isAVL, exists_eq_left',
            ge_iff_le]
          simp only [AVLNode.left_of_mk, AVLNode.val_of_mk, AVLNode.right_of_mk,
            forall_true_left] at H_right_rotation
          simp only [AVLTree.balancingFactor, H_right_rotation.2, Tree.AVLTree.height_of_some,
            Tree.AVLTree.height_node_of_mk, Nat.cast_add, Nat.cast_one, Nat.cast_max]

          set hll := Tree.AVLTree.height_node left_left with H_hll
          set hl := Tree.AVLTree.height_node left_node with H_hl
          set hr := Tree.AVLTree.height right with H_hr

          match left_right with
          | none => 
            simp only [AVLNode.right_of_mk, Option.isNone_none, AVLNode.val_of_mk,
              AVLNode.left_of_mk, forall_true_left] at H_none_left_rotation
            simp [H_none_left_rotation.2]; rw [← H_hll]
            sorry
          | some left_right =>
            simp [forall_true_left] at H_some_left_rotation
            simp [H_some_left_rotation.2]
            suffices goal_eq_one: AVLTree.balancingFactor (some t_new) = 1 by 
              simp [goal_eq_one]; norm_cast
            -- outline:
            -- let's denote height lrl = height n.left.right.left, etc.
            -- we need to prove |1 + max(hll, hlrl) - (1 + max(hlrr, hr))| ≤ 1
            -- we will prove it's exactly zero.
            -- by lbf: hll = 1 + hlr
            -- by bf: hl = 2 + hr
            -- thus: max(hll, hlrl) = hll
            -- moreover: hr = 1 + max (hlrl, hlrr).
            -- thus, we are looking at |1 + hlr - max(hlrr, 1 + max(hlrl, hlrr))|
            -- but: hr = 1 + max(hlrl, hlrr)
            -- thus, |1 + max(hlrl, hlrr) - max(hlrr, 1 + max (hlrl, hlrr))|
            -- in general: |1 + max(x, y) - max(y, 1 + max (x, y))| = 0
            let hlr := Tree.AVLTree.height_node left_right
            set hlrl := Tree.AVLTree.height (Tree.AVLNode.left left_right)
            set hlrr := Tree.AVLTree.height (Tree.AVLNode.right left_right)
            have lbf_eq: hll = 1 + hlr := by
              simp [H_left_structure, AVLTree.balancingFactor, Hlbf'] at Hlbf
              zify; simp [Hlbf]
            have hlrl_leq_hll: (hlrl : ℤ) ≤ (hll : ℤ) := by
              norm_cast
              refine' le_of_lt (Tree.AVLTree.height_left_lt_tree' _)
              rw [lbf_eq]; linarith
            have hl_eq: hl = 1 + max hll hlr := by simp [H_hl, H_left_structure]
            -- TODO(repair): left_right is potentially none
            -- thus, hlr = 0 ∨ hlr = 1 + max hlrl hlrr (potentially = 1).
            have hlr_eq: hlr = 1 + max hlrl hlrr := sorry -- Tree.AVLTree.height_node_eq left_right
            have hr_eq: hr = 1 + max hlrl hlrr := by 
              simp [H_structure, AVLTree.balancingFactor] at H_balancing
              suffices hr_eq' : 1 + (1 + hr) = 1 + (1 + (1 + max hlrl hlrr)) by
                exact (Nat.add_left_cancel $ Nat.add_left_cancel hr_eq')
              have hlr_leq_hll : hlr ≤ hll := by
                rw [lbf_eq]; linarith
              calc
                  1 + (1 + hr) = hl := by group; zify; simp [H_balancing.symm]
                  _ = 1 + max hll hlr := by simp [hl_eq]
                  _ = 1 + hll := by simp [(max_eq_left hlr_leq_hll)]
                  _ = 1 + (1 + hlr) := by rw [lbf_eq]
                  _ = 1 + (1 + (1 + max hlrl hlrr)) := by simp [hlr_eq]
            rw [(max_eq_left hlrl_leq_hll), lbf_eq, hlr_eq, hr_eq]
            push_cast; rw [Int.add_sub_assoc, (one_add_max_sub_max_one_add_max_cancel (hlrl: ℤ) (hlrr: ℤ) (by scalar_tac) (by scalar_tac)), Int.add_zero]
          -- progress does not do deep destructuration.
          . progress with AVLNode.rotate_right_spec as ⟨ rotated, t_new, H_rotation ⟩
            rcases H_rotation with ⟨ _, H_rotation ⟩
            simp [AVLTree.isAVL]
            simp [Tree.AVLNode.left, forall_true_left] at H_rotation
            -- max (h left) (h right) = h left
            -- because bf = 2 => h left = h right + 2
            -- |bf| = |h left - (1 + max (h left) (h right))| = |1| = 1 ≤ 1.
            -- TODO: prove h left ≥ h right => max (h left) (h right) = h left.
            simp [H_rotation.2, AVLTree.balancingFactor, Tree.AVLTree.height, Tree.AVLTree.height_node, Tree.AVLTree.height, Tree.AVLNode.right]
            sorry
      -- BF = -2.
      . sorry



end Implementation
