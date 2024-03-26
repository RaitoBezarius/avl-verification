fn max<'a, T: Ord>(a: &'a T, b: &'a T) -> &'a T {
    match a.cmp(b) {
        Ordering::Less => b,
        Ordering::Equal => b,
        Ordering::Greater => a,
    }
}

impl Ord for usize {
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

pub enum Ordering {
    Less,
    Equal,
    Greater,
}

trait Ord {
    fn cmp(&self, other: &Self) -> Ordering;
}

// TODO: la structure AVLNode est extrait comme un inductif à un cas
// au lieu d'être extrait comme une structure
struct AVLNode<T> {
    value: T,
    left: AVLTree<T>,
    right: AVLTree<T>,

    // Memoized height.
    height: usize,
}

impl<T> AVLNode<T> {
    fn update_height(&mut self) {
        self.height = 1 + max(&self.left_height(), &self.right_height());
    }

    fn height(&self) -> usize {
        return 1 + max(&self.left_height(), &self.right_height());
    }

    fn left_height(&self) -> usize {
        self.left.as_ref().map_or(0, |left| left.height())
    }

    fn right_height(&self) -> usize {
        self.right.as_ref().map_or(0, |right| right.height())
    }

    fn balance_factor(&self) -> i8 {
        let left_height = self.left_height();
        let right_height = self.right_height();

        if left_height >= right_height {
            (left_height - right_height) as i8
        } else {
            -((right_height - left_height) as i8)
        }
    }

    fn rotate_right(&mut self) -> bool {
        if self.left.is_none() {
            return false;
        }

        let left_node = self.left.as_mut().unwrap();
        let left_right_tree = left_node.right.take();
        let left_left_tree = left_node.left.take();

        let mut new_right_tree = std::mem::replace(&mut self.left, left_left_tree);
        std::mem::swap(&mut self.value, &mut new_right_tree.as_mut().unwrap().value);
        let right_tree = self.right.take();

        let new_right_node = new_right_tree.as_mut().unwrap();
        new_right_node.left = left_right_tree;
        new_right_node.right = right_tree;

        self.right = new_right_tree;

        if let Some(node) = self.right.as_mut() {
            node.update_height();
        }

        self.update_height();

        true
    }

    fn rotate_left(&mut self) -> bool {
        if self.right.is_none() {
            return false;
        }

        let right_node = self.right.as_mut().unwrap();
        let right_left_tree = right_node.left.take();
        let right_right_tree = right_node.right.take();

        let mut new_left_tree = std::mem::replace(&mut self.right, right_right_tree);
        std::mem::swap(&mut self.value, &mut new_left_tree.as_mut().unwrap().value);
        let left_tree = self.left.take();

        let new_left_node = new_left_tree.as_mut().unwrap();
        new_left_node.right = right_left_tree;
        new_left_node.left = left_tree;

        self.left = new_left_tree;

        if let Some(node) = self.left.as_mut() {
            node.update_height();
        }

        self.update_height();

        true
    }

    fn rebalance(&mut self) -> bool {
        match self.balance_factor() {
            -2 => {
                let right_node = self.right.as_mut().unwrap();

                if right_node.balance_factor() == 1 {
                    right_node.rotate_right();
                }

                self.rotate_left();

                true
            }
            2 => {
                let left_node = self.left.as_mut().unwrap();

                if left_node.balance_factor() == 1 {
                    left_node.rotate_left();
                }

                self.rotate_right();

                true
            }
            _ => false,
        }
    }
}

type AVLTree<T> = Option<Box<AVLNode<T>>>;

struct AVLTreeSet<T> {
    root: AVLTree<T>,
}

impl<T: Ord> AVLTreeSet<T> {
    pub fn new() -> Self {
        Self { root: None }
    }

    pub fn find(&self, value: T) -> bool {
        let mut current_tree = &self.root;

        while let Some(current_node) = current_tree {
            match current_node.value.cmp(&value) {
                Ordering::Less => current_tree = &current_node.right,
                Ordering::Equal => return true,
                Ordering::Greater => current_tree = &current_node.left,
            }
        }

        false
    }

    pub fn insert(&mut self, value: T) -> bool {
        let mut current_tree = &mut self.root;

        while let Some(current_node) = current_tree {
            let ordering = current_node.value.cmp(&value);
            match ordering {
                Ordering::Less => current_tree = &mut current_node.right,
                Ordering::Equal => return false,
                Ordering::Greater => current_tree = &mut current_node.left,
            }
        }

        *current_tree = Some(Box::new(AVLNode {
            value,
            left: None,
            right: None,
            height: 0,
        }));

        let mut current_tree = &mut self.root;

        while let Some(current_node) = current_tree {
            current_node.update_height();
            current_node.rebalance();
            current_tree = &mut current_node.left;
        }

        current_tree = &mut self.root;

        while let Some(current_node) = current_tree {
            current_node.update_height();
            current_node.rebalance();
            current_tree = &mut current_node.right;
        }

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

fn main() {}
