import AvlVerification.Tree
import AvlVerification.BinarySearchTree
import AvlVerification.Specifications

namespace Implementation

open Primitives
open avl_verification
open Tree (AVLTree)

variable {T: Type}

@[pspec]
theorem AVLTreeSet.insert_loop_spec_local (p: T -> Prop)
  (Hcmp_spec: ∀ a b, ∃ o, H.cmp a b = Result.ret o)
  (a: T) (t: Option (AVLNode T)):
  ∃ added t_new, AVLTreeSet.insert_loop T H a t = Result.ret ⟨ added, t_new ⟩
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

      sorry
    }

@[pspec]
def AVLTreeSet.insert_spec 
  {H: avl_verification.Ord T} 
  -- TODO: this can be generalized into `H.cmp` must be an equivalence relation.
  -- and insert works no longer on Sets but on set quotiented by this equivalence relation.
  (Hcmp_eq: ∀ a b, H.cmp a b = Result.ret Ordering.Equal -> a = b)
  (Hcmp_spec: ∀ a b, ∃ o, H.cmp a b = Result.ret o)
  (Hbs_search: @BSTree.searchInvariant _ H t)
  (a: T) (t: AVLTreeSet T):
  ∃ t', t.insert _ H a = Result.ret t' 
  -- set of values *POST* insertion is {a} \cup set of values of the *PRE* tree.
  ∧ AVLTree.setOf t'.2.root = insert a (AVLTree.setOf t.root) 
  -- it's still a binary search tree.
  ∧ @BSTree.searchInvariant _ H t'.2.root
  -- TODO(reinforcement): (t'.1 is false <=> a \in AVLTree.setOf t.root)
  := by
  rw [AVLTreeSet.insert]
  progress keep h as ⟨ t', Hset ⟩; simp
  rw [Hset]
  sorry


-- insert is infaillible, right?
-- instance [LT T] (o: avl_verification.Ord T): Insert T (AVLTreeSet T) where
--   insert x tree := (AVLTreeSet.insert T o tree x).map (fun (added, tree) => tree)

end Implementation

