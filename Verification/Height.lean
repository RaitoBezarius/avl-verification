import Verification.Extracted
import Verification.Tree
import Verification.BinarySearchTree

namespace Implementation

variable {T: Type}

open avl_verification
open Primitives
open Tree (AVLTree AVLNode.left AVLNode.right AVLTree.height_node AVLNode.memoized_height AVLNode.height_left_lt_tree AVLNode.height_right_lt_tree)
open BST (AVLNode.mk')

variable (t: AVLNode T) [O: LinearOrder T] (Tcopy: core.marker.Copy T) (H: avl_verification.Ord T)

@[pspec]
def max_spec {a b: T}: ∃ o, avl_verification.max _ H Tcopy a b = .ok o ∧ o = O.max a b := sorry

@[pspec]
def AVLNode.left_height_spec
  (left: AVLNode T): (AVLNode.mk x (some left) right h).left_height = left.height
  := by simp only [AVLNode.left_height]

@[pspec]
def AVLNode.right_height_spec
  (right: AVLNode T): (AVLNode.mk x left (some right) h).right_height = right.height
  := by simp only [AVLNode.right_height]

@[simp, norm_cast]
theorem coe_max {ty: ScalarTy} (a b: Scalar ty): Max.max a b = (Max.max a b: ℤ) := by
  -- TODO: redo me better because this is a bit weird.
  rw [max_def, max_def]
  split_ifs <;> simp_all
  refine' absurd _ (lt_irrefl a)
  exact lt_of_le_of_lt (by assumption) ((Scalar.lt_equiv _ _).2 (by assumption))

-- TODO:
@[pspec]
def AVLNode.height_spec (t: AVLNode T): AVLTree.height_node t ≤ Scalar.max .Usize -> ∃ v, t.height = .ok v ∧ v.val = AVLTree.height_node t
  := by
  intro Hbound
  simp [AVLNode.height]
  match t with 
  | AVLNode.mk x left right h =>
    rcases Hleft: left with _ | ⟨ a, left_left, left_right, h_left ⟩ <;> rcases Hright: right with _ | ⟨ b, right_left, right_right, h_right ⟩ <;> simp [AVLNode.right_height, AVLNode.left_height] <;> rw [AVLTree.height_node, AVLTree.height]
    -- (none, none) case.
    . progress with max_spec as ⟨ w, Hw ⟩
      rw [Hw]; use 1#usize; norm_cast
    -- (none, some .) case.
    . progress with height_spec as ⟨ w, Hw ⟩
      . push_cast
        refine' le_trans _ Hbound
        apply le_of_lt; rw [Hright]
        exact_mod_cast AVLNode.height_right_lt_tree _
      . progress with max_spec as ⟨ M, Hm ⟩
        rw [Hm, AVLTree.height]
        have: 1 + w.val ≤ Scalar.max .Usize := by
          rw [Hw]
          refine' le_trans _ Hbound
          conv =>
            rhs
            rw [Hright, AVLTree.height_node, AVLTree.height]
          push_cast
          refine' Int.add_le_add_left _ _
          exact Int.le_max_right _ _
        have Hmax: Max.max 0#usize w = w := by sorry
        rw [Hmax]
        progress with Usize.add_spec as ⟨ X, Hx ⟩
        simp [Hx, Hw]
        -- TODO: render invariant by commutativity.
    -- (some ., none) case, above.
    . sorry
    -- (some ., some .) case.
    . progress with height_spec as ⟨ c, Hc ⟩
      -- TODO: factor me out...
      push_cast
      refine' le_trans _ Hbound
      apply le_of_lt; rw [Hleft]
      exact_mod_cast AVLNode.height_left_lt_tree _
      progress with height_spec as ⟨ d, Hd ⟩
      push_cast
      refine' le_trans _ Hbound
      apply le_of_lt; rw [Hright]
      exact_mod_cast AVLNode.height_right_lt_tree _
      progress with max_spec as ⟨ M, Hm ⟩
      have: 1 + M.val ≤ Scalar.max .Usize := by
        rw [Hm]
        refine' le_trans _ Hbound
        rw [Hleft, Hright, AVLTree.height_node, AVLTree.height, AVLTree.height]
        push_cast
        rw [Hc, Hd]
      progress with Usize.add_spec as ⟨ X, Hx ⟩
      simp [Hx, Hm, Hc, Hd, AVLTree.height]
decreasing_by
  all_goals (simp_wf; try simp [Hleft]; try simp [Hright]; try linarith)

-- Under bounds, we keep the bounds?
@[pspec]
def AVLNode.update_height_spec (x: T) (h: Usize) (left right: AVLTree T): ∃ t_new, AVLNode.update_height _ (AVLNode.mk x left right h) = .ok t_new ∧ t_new = AVLNode.mk' x left right := by sorry

end Implementation
