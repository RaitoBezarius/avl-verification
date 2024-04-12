import AvlVerification.Tree
import AvlVerification.BinarySearchTree
import AvlVerification.Specifications

namespace Implementation

open Primitives
open avl_verification
open Tree (AVLTree)
open Specifications (OrdSpec ordSpecOfTotalityAndDuality ordOfOrdSpec ltOfRustOrder gtOfRustOrder)

example: OrdSpec OrdU32 := ordSpecOfTotalityAndDuality _ 
  (by 
  -- Totality
  intro a b
  unfold Ord.cmp
  unfold OrdU32
  unfold OrdU32.cmp
  if hlt : a < b then 
    use .Less
    simp [hlt]
  else
    if heq: a = b
    then
    use .Equal
    simp [hlt]
    rw [heq]
    -- TODO: simp [hlt, heq] breaks everything???
    else
      use .Greater
      simp [hlt, heq]
  ) (by 
  -- Duality
  intro a b Hgt
  if hlt : b < a then
    unfold Ord.cmp
    unfold OrdU32
    unfold OrdU32.cmp
    simp [hlt]
  else
    unfold Ord.cmp at Hgt
    unfold OrdU32 at Hgt
    unfold OrdU32.cmp at Hgt
    have hnlt : ¬ (a < b) := sorry
    have hneq : ¬ (a = b) := sorry
    exfalso
    apply hlt
    -- I need a Preorder on U32 now.
    sorry)

variable (T: Type) (H: avl_verification.Ord T) (Ospec: @OrdSpec T H)

instance rustOrder {U: Type} {O: avl_verification.Ord U} (OSpec: OrdSpec O): _root_.Ord U := ordOfOrdSpec O OSpec
-- Why the TC fails if I don't specify the previous instance explicitly?
instance rustLt {U: Type} {O: avl_verification.Ord U} (OSpec: OrdSpec O): LT U := @ltOfOrd _ (ordOfOrdSpec O OSpec)

instance rustLt' : LT T := rustLt Ospec

@[pspec]
theorem AVLTreeSet.insert_loop_spec_local (p: T -> Prop)
  (Hcmp_spec: ∀ a b, ∃ o, H.cmp a b = Result.ok o)
  (a: T) (t: Option (AVLNode T)):
  ∃ added t_new, AVLTreeSet.insert_loop T H a t = Result.ok ⟨ added, t_new ⟩
--  ∧ AVLTree.set t'.2 = insert a (AVLTree.set t)
  ∧ (BST.ForallNode p t -> p a -> BST.ForallNode p t_new)
  := by match t with
  | none =>
    simp [AVLTreeSet.insert_loop, AVLTree.set, setOf]
    intros _ Hpa
    constructor; all_goals try simp [BST.ForallNode.none]
    exact Hpa
  | some (AVLNode.mk b left right) =>
    rw [AVLTreeSet.insert_loop]
    simp only []
    progress keep Hordering as ⟨ ordering ⟩
    cases ordering
    all_goals simp only []
    {
      progress keep Htree as ⟨ added₁, right₁, Hnode ⟩
      refine' ⟨ added₁, ⟨ some (AVLNode.mk b left right₁), _ ⟩ ⟩
      simp only [true_and]
      intros Hptree Hpa
      constructor
      exact Hptree.left
      exact Hptree.label
      exact Hnode Hptree.right Hpa
    }
    {
      simp; tauto
    }
    {
      -- TODO: investigate wlog.
      -- Symmetric case of left.
      progress keep Htree as ⟨ added₁, left₁, Hnode ⟩
      refine' ⟨ added₁, ⟨ some (AVLNode.mk b left₁ right), _ ⟩ ⟩
      simp only [true_and]
      intros Hptree Hpa
      constructor
      exact Hnode Hptree.left Hpa
      exact Hptree.label
      exact Hptree.right
    }

@[pspec]
lemma AVLTreeSet.insert_loop_spec_global
  (a: T) (t: Option (AVLNode T))
  :
  haveI : LT T := (rustLt Ospec)
  BST.Invariant t -> ∃ added t_new, AVLTreeSet.insert_loop T H a t = Result.ok ⟨ added, t_new ⟩
  ∧ BST.Invariant t_new := by 
  intro Hbst
  letI instOrd : _root_.Ord T := (rustOrder Ospec)
  letI instLt : LT T := (rustLt Ospec)
  match t with
  | none => simp [AVLTreeSet.insert_loop]
  | some (AVLNode.mk b left right) =>
    rw [AVLTreeSet.insert_loop]
    simp only []
    have : ∀ a b, ∃ o, H.cmp a b = .ok o := Ospec.infallible
    progress keep Hordering as ⟨ ordering ⟩
    cases ordering
    all_goals simp only []
    {
      have ⟨ added₂, right₂, ⟨ H_result, H_bst ⟩ ⟩ := AVLTreeSet.insert_loop_spec_global a right (BST.right Hbst)
      progress keep Htree with AVLTreeSet.insert_loop_spec_local as ⟨ added₁, right₁, Hnode ⟩
      exact (fun x => b < x)
      rewrite [Htree] at H_result; simp at H_result
      refine' ⟨ added₁, ⟨ some (AVLNode.mk b left right₁), _ ⟩ ⟩
      simp only [true_and]
      cases' Hbst with _ _ _ H_forall_left H_forall_right H_bst_left H_bst_right
      constructor
      exact H_forall_left
      apply Hnode; exact H_forall_right
      exact (ltOfRustOrder H b a Hordering)
      exact H_bst_left
      convert H_bst
      exact H_result.2
    }
    {
      simp; tauto
    }
    {
      have ⟨ added₂, left₂, ⟨ H_result, H_bst ⟩ ⟩ := AVLTreeSet.insert_loop_spec_global a left (BST.left Hbst)
      progress keep Htree with AVLTreeSet.insert_loop_spec_local as ⟨ added₁, left₁, Hnode ⟩
      exact (fun x => x < b)
      rewrite [Htree] at H_result; simp at H_result
      refine' ⟨ added₁, ⟨ some (AVLNode.mk b left₁ right), _ ⟩ ⟩
      simp only [true_and]
      cases' Hbst with _ _ _ H_forall_left H_forall_right H_bst_left H_bst_right
      constructor
      apply Hnode; exact H_forall_left
      exact (gtOfRustOrder H b a Hordering)
      exact H_forall_right
      convert H_bst
      exact H_result.2
      exact H_bst_right
    }

@[pspec]
def AVLTreeSet.insert_spec 
  (a: T) (t: AVLTreeSet T):
  haveI : LT T := (rustLt Ospec)
  BST.Invariant t.root -> (∃ t' added,t.insert _ H a = Result.ok (added, t')
  -- it's still a binary search tree.
  ∧ BST.Invariant t'.root)
  := by
  rw [AVLTreeSet.insert]; intro Hbst
  progress keep h as ⟨ t', Hset ⟩; 
  simp; assumption

end Implementation
