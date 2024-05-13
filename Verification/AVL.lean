import Verification.Extracted
import Verification.Tree

open Tree (AVLTree)

namespace Tree

variable {T: Type}

open avl_verification

def AVLTree.balancingFactor (t: AVLTree T): ℤ := match t with
| .none => 0
| .some (AVLNode.mk _ left right _) => AVLTree.height left - AVLTree.height right

def AVLTree.isAVL (t: AVLTree T): Prop := |t.balancingFactor| <= 1

end Tree
