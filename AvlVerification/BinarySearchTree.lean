import AvlVerification.Tree

namespace BST

open Primitives (Result)
open avl_verification (AVLNode Ordering)
open Tree (AVLTree AVLNode.left AVLNode.right AVLNode.val)

inductive ForallNode (p: T -> Prop): AVLTree T -> Prop
| none : ForallNode p none
| some (a: T) (left: AVLTree T) (right: AVLTree T) : ForallNode p left -> p a -> ForallNode p right -> ForallNode p (some (AVLNode.mk a left right))

theorem ForallNode.left {p: T -> Prop} {t: AVLTree T}: ForallNode p t -> ForallNode p t.left := by
  intro Hpt
  cases Hpt with 
  | none => simp [AVLTree.left, ForallNode.none]
  | some a left right f_pleft f_pa f_pright => simp [AVLTree.left, f_pleft]

theorem ForallNode.right {p: T -> Prop} {t: AVLTree T}: ForallNode p t -> ForallNode p t.right := by
  intro Hpt
  cases Hpt with 
  | none => simp [AVLTree.right, ForallNode.none]
  | some a left right f_pleft f_pa f_pright => simp [AVLTree.right, f_pright]

theorem ForallNode.label {a: T} {p: T -> Prop} {left right: AVLTree T}: ForallNode p (AVLNode.mk a left right) -> p a := by
  intro Hpt
  cases Hpt with 
  | some a left right f_pleft f_pa f_pright => exact f_pa

-- This is the binary search invariant.
inductive Invariant [LT T]: AVLTree T -> Prop
| none : Invariant none
| some (a: T) (left: AVLTree T) (right: AVLTree T) : 
  ForallNode (fun v => v < a) left -> ForallNode (fun v => a < v) right
  -> Invariant left -> Invariant right -> Invariant (some (AVLNode.mk a left right))

@[simp]
theorem singleton_bst [LT T] {a: T}: Invariant (some (AVLNode.mk a none none)) := by
  apply Invariant.some
  all_goals simp [ForallNode.none, Invariant.none] 

theorem left [LT T] {t: AVLTree T}: Invariant t -> Invariant t.left := by
  intro H
  induction H with 
  | none => exact Invariant.none
  | some _ _ _ _ _ _ _ _ _ => simp [AVLTree.left]; assumption

theorem right [LT T] {t: AVLTree T}: Invariant t -> Invariant t.right := by
  intro H
  induction H with 
  | none => exact Invariant.none
  | some _ _ _ _ _ _ _ _ _ => simp [AVLTree.right]; assumption

end BST
