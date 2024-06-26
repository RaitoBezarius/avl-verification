import Verification.Tree
import AvlVerification

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

theorem ForallNode.not_mem {a: T} (p: T -> Prop) (t: Option (AVLNode T)): ¬ p a -> ForallNode p t -> a ∉ AVLTree.set t := fun Hnpa Hpt => by
  cases t with 
  | none => simp [AVLTree.set]; tauto
  | some t =>
    cases Hpt with 
    | some b left right f_pbleft f_pb f_pbright =>
      simp [AVLTree.set_some]
      push_neg
      split_conjs
      . by_contra hab; rw [hab] at Hnpa; exact Hnpa f_pb
      . exact ForallNode.not_mem p left Hnpa f_pbleft
      . exact ForallNode.not_mem p right Hnpa f_pbright

theorem ForallNode.not_mem' {a: T} (p: T -> Prop) (t: Option (AVLNode T)): p a -> ForallNode (fun x =>  ¬p x) t -> a ∉ AVLTree.set t := fun Hpa Hnpt => by 
  refine' ForallNode.not_mem (fun x => ¬ p x) t _ _
  simp [Hpa]
  exact Hnpt

theorem ForallNode.imp {p q: T -> Prop} {t: AVLTree T}: (∀ x, p x -> q x) -> ForallNode p t -> ForallNode q t := fun Himp Hpt => by 
  induction Hpt
  . simp [ForallNode.none]
  . constructor
    . assumption
    . apply Himp; assumption
    . assumption

-- This is the binary search invariant.
variable [LinearOrder T]
inductive Invariant: AVLTree T -> Prop
| none : Invariant none
| some (a: T) (left: AVLTree T) (right: AVLTree T) : 
  ForallNode (fun v => v < a) left -> ForallNode (fun v => a < v) right
  -> Invariant left -> Invariant right -> Invariant (some (AVLNode.mk a left right))

@[simp]
theorem singleton_bst {a: T}: Invariant (some (AVLNode.mk a none none)) := by
  apply Invariant.some
  all_goals simp [ForallNode.none, Invariant.none] 

theorem left {t: AVLTree T}: Invariant t -> Invariant t.left := by
  intro H
  induction H with 
  | none => exact Invariant.none
  | some _ _ _ _ _ _ _ _ _ => simp [AVLTree.left]; assumption

theorem right {t: AVLTree T}: Invariant t -> Invariant t.right := by
  intro H
  induction H with 
  | none => exact Invariant.none
  | some _ _ _ _ _ _ _ _ _ => simp [AVLTree.right]; assumption

-- TODO: ask at most for LT + Irreflexive (lt_irrefl) + Trichotomy (le_of_not_lt)?
theorem left_pos {left right: Option (AVLNode T)} {a x: T}: BST.Invariant (some (AVLNode.mk a left right)) -> x ∈ AVLTree.set (AVLNode.mk a left right) -> x < a -> x ∈ AVLTree.set left := fun Hbst Hmem Hxa => by
   simp [AVLTree.set_some] at Hmem
   rcases Hmem with (Heq | Hleft) | Hright
   . rewrite [Heq] at Hxa; exact absurd Hxa (lt_irrefl _)
   . assumption
   . exfalso
 
     -- Hbst -> x ∈ right -> ForallNode (fun v => ¬ v < a)
     refine' ForallNode.not_mem' (fun v => v < a) right Hxa _ _
     simp [le_of_not_lt]
     cases Hbst with 
     | some _ _ _ _ Hforall _ =>
       refine' ForallNode.imp _ Hforall
       exact fun x => le_of_lt
     assumption
 
theorem right_pos {left right: Option (AVLNode T)} {a x: T}: BST.Invariant (some (AVLNode.mk a left right)) -> x ∈ AVLTree.set (AVLNode.mk a left right) -> a < x -> x ∈ AVLTree.set right := fun Hbst Hmem Hax => by
   simp [AVLTree.set_some] at Hmem
   rcases Hmem with (Heq | Hleft) | Hright
   . rewrite [Heq] at Hax; exact absurd Hax (lt_irrefl _)
   . exfalso
     refine' ForallNode.not_mem' (fun v => a < v) left Hax _ _
     simp [le_of_not_lt]
     cases Hbst with 
     | some _ _ _ Hforall _ _ =>
       refine' ForallNode.imp _ Hforall
       exact fun x => le_of_lt
     assumption  
   . assumption
 

end BST
