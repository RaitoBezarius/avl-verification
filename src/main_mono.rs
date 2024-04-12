use std::cmp::Ordering;

struct AVLNode {
    value: u32,
    left: AVLTree,
    right: AVLTree,
}

type AVLTree = Option<Box<AVLNode>>;

struct AVLTreeSet<T: Ord> {
    root: AVLTree<T>,
}

impl<T: Ord> AVLTreeSet<T> {
    pub fn new() -> Self {
        Self { root: None }
    }

    pub fn insert(&mut self, value: T) -> bool {
        let mut current_tree = &mut self.root;

        while let Some(current_node) = current_tree {
            match current_node.value.cmp(&value) {
                Ordering::Less => current_tree = &mut current_node.right,
                Ordering::Equal => return false,
                Ordering::Greater => current_tree = &mut current_node.left,
            }
        }

        *current_tree = Some(Box::new(AVLNode {
            value,
            left: None,
            right: None,
        }));

        true
    }
}

fn main() {
    let mut tree = AVLTreeSet::new();
    tree.insert(3);
    tree.insert(2);
}
