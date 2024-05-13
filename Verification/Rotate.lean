import Verification.Tree
import Verification.AVL
import Verification.Extracted
import Verification.Height
import Verification.BinarySearchTree

namespace Implementation

open BST (AVLNode.mk')
open Tree (AVLNode.memoized_height AVLNode.val AVLNode.right AVLNode.left AVLTree.balancingFactor)
open Primitives
open avl_verification

variable (T: Type) (H: avl_verification.Ord T) [LinearOrder T] (Ospec: OrdSpecLinearOrderEq H)

-- prove rotate_left make balancingFactor t_new.left = balancingFactor t.left + 1 + max(balancingFactor(t_new.right), 0)
-- prove rotate_left make balancingFactor t_new.right = balancingFactor t.right + 1 - min(balancingFactor(t_new.left), 0)

-- prove rotate_right make balancingFactor t_new.left = balancingFactor t.left - 1 - max(balancingFactor(t.left), 0)
-- prove rotate_right make balancingFactor t_new.right = balancingFactor t.right - 1 + min(balancingFactor(t_new.right), 0)
-- t.left - t.left+ = -f.left-
-- rotate_right(t).left.bf = -(1 + t.left.bf-)
-- t.left.bf \in {-1, 0, 1} -> t.left.bf- \in {0, 1} -> rotate_right(t).left.bf ∈ {-(

@[pspec]
theorem AVLNode.rotate_right_spec (self: AVLNode T):
  ∃ rotated t_new, self.rotate_right = .ok (rotated, t_new) 
  ∧ ((AVLNode.left self).isNone -> rotated = false ∧ t_new = AVLNode.mk (AVLNode.val self) none (AVLNode.right self) (AVLNode.memoized_height self))
  ∧ ((AVLNode.left self) = .some self_left -> rotated = true
    ∧ t_new = 
      AVLNode.mk' (AVLNode.val self_left) (AVLNode.left self_left) 
        (AVLNode.mk' (AVLNode.val self) (AVLNode.right self_left) (AVLNode.right self))
    )
  := by 
  match self with 
  | AVLNode.mk a left right memoized_height => 
    match left with 
    | .none => simp [AVLNode.rotate_right, AVLNode.left, AVLNode.val, AVLNode.right, AVLNode.memoized_height]
    | .some (AVLNode.mk b left_left left_right h) => 
      simp only [AVLNode.rotate_right, Option.isNone_some, not_false_eq_true, neq_imp, ↓reduceIte,
        core.mem.replace, Option.take, core.mem.swap, Bool.exists_bool]
      right
      have := AVLNode.update_height_spec a h left_right right
      progress keep Hupdate₁ with AVLNode.update_height_spec as ⟨ t_new₁, H₁ ⟩
      progress keep Hupdate₂ with AVLNode.update_height_spec as ⟨ t_new, H₂ ⟩
      simp [AVLNode.left]
      intro Hleft
      simp [← Hleft, H₂, H₁, AVLNode.val, AVLNode.right]

@[pspec]
theorem AVLNode.rotate_left_spec (self: AVLNode T):
  ∃ added t_new, self.rotate_left = .ok (added, t_new) := by
  match self with 
  | AVLNode.mk a left right memoized_height => 
    match right with 
    | .none => simp [AVLNode.rotate_left]
    | .some (AVLNode.mk b right_left right_right h) => 
      simp only [AVLNode.rotate_left, Option.isNone_some, not_false_eq_true, neq_imp, ↓reduceIte,
        core.mem.replace, Option.take, core.mem.swap, Bool.exists_bool]
      right
      have := AVLNode.update_height_spec a h left right_right
      progress keep Hupdate₁ with AVLNode.update_height_spec as ⟨ t_new₁, Hheight₁ ⟩
      progress keep Hupdate₂ with AVLNode.update_height_spec as ⟨ t_new, Hheight ⟩
      simp

end Implementation
