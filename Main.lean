import «AvlVerification»
open Primitives

namespace Avl

-- synthesize inhabited?
-- synthesize type aliases
-- AVLTree T := Option<Box<AVLNode>> ~ AVLTree T := Option<AVLNode>

open avl_verification
variable {T: Type}

def AVL.nil: AVLTreeSet T := { root := none }


-- TODO: AVLTree T ou AVLNode T?
noncomputable def AVL.height' (tree: AVLNode T): Nat := AVLNode.rec tree
  (mk := fun _ _ _ ihl ihr => 1 + ihl + ihr)
  (none := 0)
  (some := fun _ ih => 1 + ih)

-- Otherwise, Lean cannot prove termination by itself.
@[reducible]
def AVLTree (U: Type) := Option (AVLNode U)

mutual
def AVL.height'' (tree: AVLNode T): Nat := match tree with
| AVLNode.mk y left right => 1 +  AVL.height left + AVL.height right

def AVL.height (tree: AVLTree T): Nat := match tree with 
| none => 0
| some node => 1 + AVL.height'' node
end


def AVLTree.mem (tree: AVLTree T) (x: T): Prop :=
  match tree with
  | none => false
  | some (AVLNode.mk y left right) => x = y ∨ AVLTree.mem left x ∨ AVLTree.mem right y

def AVLTree.setOf: AVLTree T -> Set T := AVLTree.mem

#check AVL.nil
#check U32.ofInt 0
#check 0#u32
-- TODO: créer une instance OfNat pour les Uxyz.
-- TODO: générer {} adéquatement... ?

#check (AVL.nil.insert _ _ 0#u32)


#check Primitives.bind (AVL.nil.insert _ _ 0#u32) (fun x => Result.ret (x.1, AVLTree.setOf x.2.root))
#check Primitives.bind (AVL.nil.insert _ _ 0#u32) (fun x => Result.ret (x.1, AVLTree.setOf x.2.root))
#check Primitives.bind (AVL.nil.insert _ _ 0#u32) (fun (added, tree)  => Result.ret (added, AVLTree.setOf tree.root))
#check Primitives.bind (AVL.nil.insert _ _ 0#u32) (fun x => Result.ret (x.1, AVLTree.setOf x.2.root))
#check Primitives.bind (AVL.nil.insert _ _ 0#u32) (fun (added, tree)  => Result.ret (added, AVLTree.setOf tree.root))
#check Primitives.bind (AVL.nil.insert _ _ 0#u32) (fun x => Result.ret (x.1, AVLTree.setOf x.2.root))

def AVLTreeSet.setOfInsert {H: avl_verification.Ord T} (a: T) (t: AVLTreeSet T) := Primitives.bind (t.insert _ H a) (fun (_, tree) => Result.ret (AVLTree.setOf tree.root))

-- TODO: derive from Ord an Lean Order instance.
-- TODO: oh no, H.cmp returns a Result!

@[pspec]
def AVLTreeSet.insert_loop_spec {H: avl_verification.Ord T} 
  (a: T) (t: Option (AVLNode T))
  (Hcmp_spec: ∀ a b, ∃ o, H.cmp a b = Result.ret o):
  ∃ t', AVLTreeSet.insert_loop T H a t = Result.ret t' := by
  match t with
  | none => simp [AVLTreeSet.insert_loop]
  | some (AVLNode.mk b left right) =>
    rw [AVLTreeSet.insert_loop]
    simp only []
    progress as ⟨ ordering ⟩
    cases ordering
    all_goals {
      simp only []
      try progress
      simp
    }

@[pspec]
def AVLTreeSet.insert_spec 
  {H: avl_verification.Ord T} 
  (Hcmp_spec: ∀ a b, ∃ o, H.cmp a b = Result.ret o)
  (a: T) (t: AVLTreeSet T):
  ∃ t', t.insert _ H x = Result.ret t' ∧ AVLTree.setOf t'.2.root = insert a (AVLTree.setOf t.root) := by
  rw [AVLTreeSet.insert]
  progress; simp

end Avl
