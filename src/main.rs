use std::cmp::Ordering;

trait Ord {
    fn cmp(&self, other: &Self) -> Ordering;
}

struct AVLNode<T: Ord> {
    value: T,
    left: AVLTree<T>,
    right: AVLTree<T>,
}

type AVLTree<T> = Option<Box<AVLNode<T>>>;

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

impl Ord for u32 {
    fn cmp(&self, other: &Self) -> Ordering {
        if *self < *other {
            Ordering::Less
        } else if *self == *other {
            Ordering::Equal
        } else {
            Ordering::Greater
        }
    }
}

fn main() {
    let mut tree = AVLTreeSet::new();
    tree.insert(3);
    tree.insert(2);
}
