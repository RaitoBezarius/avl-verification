import AvlVerification.Tree

namespace BST

open Primitives (Result)
open avl_verification (AVLNode Ordering)
open Tree (AVLTree AVLNode.left AVLNode.right AVLNode.val)

inductive ForallNode (p: T -> Prop): AVLTree T -> Prop
| none : ForallNode p none
| some (a: T) (left: AVLTree T) (right: AVLTree T) : ForallNode p left -> p a -> ForallNode p right -> ForallNode p (some (AVLNode.mk a left right))

theorem ForallNode.left {p: T -> Prop} {t: AVLTree T}: ForallNode p t -> ForallNode p t.left := sorry

theorem ForallNode.right {p: T -> Prop} {t: AVLTree T}: ForallNode p t -> ForallNode p t.right := sorry

theorem ForallNode.label {a: T} {p: T -> Prop} {left right: AVLTree T}: ForallNode p (AVLNode.mk a left right) -> p a := sorry

-- This is the binary search invariant.
inductive BST [LT T]: AVLTree T -> Prop
| none : BST none
| some (a: T) (left: AVLTree T) (right: AVLTree T) : 
  ForallNode (fun v => v < a) left -> ForallNode (fun v => a < v) right
  -> BST left -> BST right -> BST (some (AVLNode.mk a left right))

@[simp]
theorem singleton_bst [LT T] {a: T}: BST (some (AVLNode.mk a none none)) := by
  apply BST.some
  all_goals simp [ForallNode.none, BST.none] 

theorem left [LT T] {t: AVLTree T}: BST t -> BST t.left := by
  intro H
  induction H with 
  | none => exact BST.none
  | some _ _ _ _ _ _ _ _ _ => simp [AVLTree.left]; assumption

theorem right [LT T] {t: AVLTree T}: BST t -> BST t.right := by
  intro H
  induction H with 
  | none => exact BST.none
  | some _ _ _ _ _ _ _ _ _ => simp [AVLTree.right]; assumption

end BST
