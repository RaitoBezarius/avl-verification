import AvlVerification.Tree
import AvlVerification.BinarySearchTree
import AvlVerification.Specifications

namespace Implementation

open Primitives
open avl_verification
open Tree (AVLTree)
open Specifications (OrdSpec ordSpecOfInfaillible ordOfOrdSpec ltOfRustOrder)

-- TODO: OSpec should be proven.
variable (T: Type) (H: avl_verification.Ord T) (Ospec: @OrdSpec T H)

instance rustOrder {U: Type} {O: avl_verification.Ord U} (OSpec: OrdSpec O): _root_.Ord U := ordOfOrdSpec O OSpec
-- Why the TC fails if I don't specify the previous instance explicitly?
instance rustLt {U: Type} {O: avl_verification.Ord U} (OSpec: OrdSpec O): LT U := @ltOfOrd _ (ordOfOrdSpec O OSpec)

instance rustLt' : LT T := rustLt Ospec

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

@[pspec]
lemma AVLTreeSet.insert_loop_spec_global
  (a: T) (t: Option (AVLNode T))
  :
  haveI : LT T := (rustLt Ospec)
  BST.BST t -> ∃ added t_new, AVLTreeSet.insert_loop T H a t = Result.ret ⟨ added, t_new ⟩
  ∧ BST.BST t_new := by 
  intro Hbst
  letI instOrd : _root_.Ord T := (rustOrder Ospec)
  letI instLt : LT T := (rustLt Ospec)
  match t with
  | none => simp [AVLTreeSet.insert_loop]
  | some (AVLNode.mk b left right) =>
    rw [AVLTreeSet.insert_loop]
    simp only []
    have := Ospec.infallible; simp at this
    -- TODO: unbundle `this`...
    have : ∀ a b, ∃ o, H.cmp a b = .ret o := sorry
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

