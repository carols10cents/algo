// Based on http://www.keithschwarz.com/interesting/code/?dir=fibonacci-heap

use std::mem;
use std::ptr;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::hash::Hash;
use std::fmt::Debug;

#[derive(Debug)]
pub struct FibonacciHeap<I: Eq + Hash + Copy + Debug, T: PartialOrd + Debug> {
    size: usize,
    min: Link<I, T>,
    lookup: HashMap<I, Link<I, T>>,
    tree_table: Vec<Link<I, T>>,
    to_visit: Vec<Link<I, T>>,
}

#[derive(Debug)]
struct Entry<I: Eq + Hash + Copy + Debug, T: PartialOrd + Debug> {
    pub id: I,
    pub value: T,
    pub degree: usize,
    pub is_marked: bool,
    pub parent: Link<I, T>,
    pub next: Link<I, T>,
    pub prev: Link<I, T>,
    pub child: Link<I, T>,
}

#[derive(Debug)]
struct Link<I: Eq + Hash + Copy + Debug, T: PartialOrd + Debug> {
    entry: *mut Entry<I, T>,
}

impl<I: Eq + Hash + Copy + Debug, T: PartialOrd + Debug> FibonacciHeap<I, T> {
    pub fn new() -> FibonacciHeap<I, T> {
        FibonacciHeap {
            size: 0,
            min: Link::none(),
            lookup: HashMap::new(),
            tree_table: Vec::new(),
            to_visit: Vec::new(),
        }
    }

    pub fn min(&self) -> Option<&T> {
        self.min.borrow()
    }

    pub fn is_empty(&self) -> bool {
        self.min.is_none()
    }

    pub fn size(&self) -> usize {
        self.size
    }

    pub fn push(&mut self, id: I, value: T) {
        let link = Link::new(id, value);

        let mut min = Link::none();
        mem::swap(&mut min, &mut self.min);

        self.lookup.insert(id, link.clone());
        self.min = FibonacciHeap::<I, T>::concat_into_root_list(min, link);
        self.size += 1;
    }

    pub fn pop(&mut self) -> Option<T> {
        // https://github.com/jgrapht/jgrapht/blob/master/jgrapht-core/src/main/java/org/jgrapht/util/FibonacciHeap.java#L237
        if self.is_empty() {
            return None;
        }

        let mut z = Link::none();
        mem::swap(&mut z, &mut self.min);
        // println!("popping z, is {:?}", z.borrow());

        let mut num_kids = z.get_degree();
        let mut x = z.get_child();
        // println!("x is {:?}", x.borrow());
        let mut temp_next;

        // for each child of z do...
        while num_kids > 0 {
            temp_next = x.get_next();

            // remove x from child list
            x.get_prev().set_next(&x.get_next());
            x.get_next().set_prev(&x.get_prev());

            // add x to root list of heap
            x.set_prev(&z);
            x.set_next(&z.get_next());
            z.set_next(&x);
            x.get_next().set_prev(&x);

            // set parent[x] to null
            x.set_parent(&Link::none());
            x = temp_next;
            // println!("next x is {:?}", x.borrow());
            num_kids -= 1;
        }

        // remove z from root list of heap
        z.get_prev().set_next(&z.get_next());
        z.get_next().set_prev(&z.get_prev());

        if z.get_next().are_same(&z) {
            self.min = Link::none();
        } else {
            // println!("temporarily setting min to {:?} and calling consolidate", z.get_next().borrow());
            self.min = z.get_next();
            self.consolidate();
        }

        // decrement size of heap
        self.size -= 1;

        if let Some(id) = z.get_id() {
            self.lookup.remove(&id);
        }
        z.into_value()
    }

    // https://github.com/jgrapht/jgrapht/blob/master/jgrapht-core/src/main/java/org/jgrapht/util/FibonacciHeap.java#L423
    fn consolidate(&mut self) {
        // println!("START CONSOLIDATE =============");
        let one_over_log_phi: f64 = 1.0 / ((1.0 + 5.0f64.sqrt()).ln() / 2.0);
        let array_size: usize = (((self.size as f64).ln() * one_over_log_phi).floor() as usize) + 1;
        // println!("array size is {}", array_size);
        let mut array = vec![Link::none(); array_size];

        // Find the number of root nodes.
        let mut num_roots = 0;
        let mut x = self.min.clone();
        // println!("x at start of consolidate is {:?}", x.borrow());

        if x.is_some() {
            num_roots += 1;
            x = x.get_next();
            // println!("x next is {:?}", x.borrow());
            while !x.are_same(&self.min) {
                num_roots += 1;
                x = x.get_next();
                // println!("x next in loop is {:?}", x.borrow());
            }
        }

        // println!("num_roots is initially {}", num_roots);

        // For each node in root list do...
        while num_roots > 0 {
            // Access this node's degree..
            let mut d = x.get_degree();
            // println!("set d to {}", d);
            let next = x.get_next();

            // ..and see if there's another of the same degree.
            loop {
                match array.get(d) {
                    None => {
                        // println!("array.get({}) is None", d);
                        break
                    }, // Nope.
                    Some(y) if y.is_none() => {
                        // println!("array.get({}) is_none", d);
                        break
                    }, // Nope.
                    Some(y) => {
                        // println!("collision at {} with {:?}, {:?}", d, x.borrow(), y.borrow());
                        // There is, make one of the nodes a child of the other.
                        // Do this based on the key value.
                        if x > *y {
                            // println!("setting x {:?} to child, y {:?} to parent", x.borrow(), y.borrow());
                            self.link(x.clone(), y.clone());
                            x = y.clone();
                            // println!("x, the new parent, is now {:?} with child {:?}", x.borrow(), x.get_child().borrow());
                        } else {
                            // println!("setting y {:?} to child, x {:?} to parent", y.borrow(), x.borrow());
                            self.link(y.clone(), x.clone());
                        }
                    },
                };
                // We've handled this degree, go to next one.
                // println!("setting array[{}] to Link::none", d);
                array[d] = Link::none();
                d += 1;
                // println!("d is now {}", d);
            }
            // Save this node for later when we might encounter another
            // of the same degree.
            // println!("saving parent in array[{}] = {:?}", d, x.borrow());
            array[d] = x;

            // Move forward through list.
            x = next;
            num_roots -= 1;
            // println!("num_roots is now {}", num_roots);
        }

        // Set min to null (effectively losing the root list) and
        // reconstruct the root list from the array entries in array[].
        self.min = Link::none();

        // println!("for i in {:?}", 0..array_size);

        for i in 0..array_size {
            match array.get(i) {
                None => {
                    // println!("array.get(i) for {} is None", i);
                    continue
                },
                Some(y) if y.is_none() => {
                    // println!("array.get(i) for {} is_none", i);
                    continue
                },
                Some(y) => {
                    // println!("array.get(i) for {} is {:?}", i, y.borrow());
                    // We've got a live one, add it to root list.
                    if self.min.is_some() {
                        // First remove node from root list.
                        y.get_prev().set_next(&y.get_next());
                        y.get_next().set_prev(&y.get_prev());

                        let mut min = Link::none();
                        mem::swap(&mut min, &mut self.min);

                        // println!("deciding on min between curr min {:?} and y {:?}", min.borrow(), y.borrow());

                        // Now add to root list, again.
                        self.min = FibonacciHeap::<I, T>::concat_into_root_list(min, y.clone());
                        // println!("min is now {:?}", self.min.borrow());
                    } else {
                        // println!("first min is {:?}", y.borrow());
                        self.min = y.clone();
                    }
                }
            }
        }
    }

    fn link(&mut self, mut child: Link<I, T>, mut parent: Link<I, T>) {
        // remove child from root list of heap
        child.get_prev().set_next(&child.get_next());
        child.get_next().set_prev(&child.get_prev());

        // make the child a child of the parent
        child.set_parent(&parent);
        let mut parent_current_child = parent.get_child();

        if parent_current_child.is_none() {
            parent.set_child(&child);
            child.convert_to_singleton();
        } else {
            child.set_prev(&parent_current_child);
            child.set_next(&parent_current_child.get_next());
            parent_current_child.set_next(&child);
            child.get_next().set_prev(&child);
        }

        // increase degree of the parent
        parent.inc_degree();

        // set mark of the child to false
        child.set_is_marked(false);
    }

    pub fn get(&self, id: I) -> Option<&T> {
        match self.lookup.get(&id) {
            Some(link) => link.get_value(),
            None => None
        }
    }

    pub fn decrease_key(&mut self, id: I, decreased_value: T) {
        let mut link = self.lookup.get(&id).expect("Could not find key to decrease").clone();
        link.set_value(decreased_value);

        let parent = link.get_parent();

        if parent.is_some() && link <= parent {
            self.cut_link(link.clone());
        }

        if link <= self.min {
            self.min = link;
        }
    }

    pub fn merge(x: FibonacciHeap<I, T>, y: FibonacciHeap<I, T>) -> FibonacciHeap<I, T> {
        let mut result = FibonacciHeap::new();

        result.min = FibonacciHeap::<I, T>::merge_entries(x.min, y.min);
        result.size = x.size + y.size;

        result
    }

    fn concat_into_root_list(mut min_node: Link<I, T>, mut node: Link<I, T>) -> Link<I, T> {
        // concatenate node into min list --
        // https://github.com/jgrapht/jgrapht/blob/master/jgrapht-core/src/main/java/org/jgrapht/util/FibonacciHeap.java#L195
        // left => prev
        // right => next
        if !min_node.is_none() {
            node.set_prev(&min_node);
            node.set_next(&min_node.get_next());

            min_node.set_next(&node);
            node.get_next().set_prev(&node);

            if node < min_node {
                node
            } else {
                min_node
            }
        } else {
            node
        }
    }

    fn merge_entries(mut x: Link<I, T>, mut y: Link<I, T>) -> Link<I, T> {
        if x.is_none() && y.is_none() {
            Link::none()
        } else if !x.is_none() && y.is_none() {
            x
        } else if x.is_none() && !y.is_none() {
            y
        } else {
            let mut x_next = x.get_next();
            let mut y_next = y.get_next();
            x.set_next(&y_next);
            y_next.set_prev(&x);
            y.set_next(&x_next);
            x_next.set_prev(&y);

            if x < y {
                x
            } else {
                y
            }
        }
    }

    fn cut_link(&mut self, mut link: Link<I, T>) {
        link.set_is_marked(false);

        // Base case: If the link has no parent, we're done.
        if link.get_parent().is_some() {
            // Rewire the link's siblings around it, if it has any siblings.
            if !link.get_next().are_same(&link) {
                let mut prev = link.get_prev();
                let mut next = link.get_next();
                prev.set_next(&next);
                next.set_prev(&prev);
            }

            // If the link is the one identified by its parent as its child,
            // we need to rewrite that pointer to point to some arbitrary other
            // child.
            let mut parent = link.get_parent();
            if parent.get_child().are_same(&link) {
                // If there are any other children, pick one of them arbitrarily.
                if !link.get_next().are_same(&link) {
                    parent.set_child(&link.get_next());
                } else {
                    // Otherwise, there aren't any children left and we should clear the
                    // pointer and drop the links's degree.
                    parent.set_child(&Link::none());
                }
            }

            // Decrease the degree of the parent, since it just lost a child.
            parent.dec_degree();

            link.convert_to_singleton();

            // Clear the relocated link's parent; it's now a root.
            link.set_parent(&Link::none());

            // Splice this link into the root list by merging
            let mut min = Link::none();
            mem::swap(&mut min, &mut self.min);
            self.min = FibonacciHeap::<I, T>::merge_entries(min, link);

            // Recursively cut the former parent if it's already been marked
            if parent.get_is_marked() {
                self.cut_link(parent);
            } else {
                // Otherwise, mark it
                parent.set_is_marked(true);
            }
        }
    }
}

impl<I: Eq + Hash + Copy + Debug, T: PartialOrd + Debug> Entry<I, T> {
    pub fn new(id: I, value: T) -> Entry<I, T> {
        Entry {
            id: id,
            value: value,
            degree: 0,
            is_marked: false,
            parent: Link::none(),
            next: Link::none(),
            prev: Link::none(),
            child: Link::none(),
        }
    }
}

impl<I: Eq + Hash + Copy + Debug, T: PartialOrd + Debug> Link<I, T> {
    #[inline]
    pub fn none() -> Link<I, T> {
        Link { entry: ptr::null_mut() }
    }

    #[inline]
    pub fn is_none(&self) -> bool {
        self.entry.is_null()
    }

    #[inline]
    pub fn is_some(&self) -> bool {
        !self.is_none()
    }

    pub fn new(id: I, value: T) -> Link<I, T> {
        let entry_box = Box::new(Entry::new(id, value));
        let entry = Box::into_raw(entry_box);
        let prev = entry.clone();
        let next = entry.clone();

        unsafe {
            (*entry).prev = Link { entry: prev };
            (*entry).next = Link { entry: next };
        }

        Link { entry: entry }
    }

    #[inline]
    pub fn get_degree(&self) -> usize {
        if self.is_none() {
            0
        } else {
            unsafe { (*self.entry).degree }
        }
    }

    #[inline]
    pub fn inc_degree(&mut self) {
        if self.is_some() {
            unsafe {
                (*self.entry).degree += 1;
            }
        }
    }

    #[inline]
    pub fn dec_degree(&mut self) {
        if self.is_some() {
            unsafe {
                (*self.entry).degree -= 1;
            }
        }
    }

    pub fn get_id(&self) -> Option<I> {
        if self.is_none() {
            None
        } else {
            unsafe {
                Some ((*self.entry).id)
            }
        }
    }

    pub fn into_value(mut self) -> Option<T> {
        if self.is_none() {
            None
        } else {
            let mut raw_entry: *mut Entry<I, T> = ptr::null_mut();
            mem::swap(&mut raw_entry, &mut self.entry);

            let entry: Entry<I, T>;
            unsafe {
                entry = *Box::from_raw(raw_entry);
            }

            Some(entry.value)
        }
    }

    pub fn get_value(&self) -> Option<&T> {
        if self.is_none() {
            None
        } else {
            unsafe {
                Some(&(*self.entry).value)
            }
        }
    }

    #[inline]
    pub fn borrow(&self) -> Option<&T> {
        if self.is_none() {
            None
        } else {
            unsafe { Some(&(*self.entry).value) }
        }
    }

    #[inline]
    pub fn are_same(&self, other: &Link<I, T>) -> bool {
        self.entry == other.entry
    }

    #[inline]
    pub fn get_child(&self) -> Link<I, T> {
        if self.is_none() {
            Link::<I, T>::none()
        } else {
            unsafe { (*self.entry).child.clone() }
        }
    }

    #[inline]
    pub fn get_next(&self) -> Link<I, T> {
        if self.is_none() {
            Link::<I, T>::none()
        } else {
            unsafe { (*self.entry).next.clone() }
        }
    }

    #[inline]
    pub fn get_prev(&self) -> Link<I, T> {
        if self.is_none() {
            Link::<I, T>::none()
        } else {
            unsafe { (*self.entry).prev.clone() }
        }
    }

    #[inline]
    pub fn set_child(&mut self, child: &Link<I, T>) {
        if self.is_some() {
            unsafe {
                (*self.entry).child = child.clone();
            }
        }
    }

    #[inline]
    pub fn set_parent(&mut self, parent: &Link<I, T>) {
        if self.is_some() {
            unsafe {
                (*self.entry).parent = parent.clone();
            }
        }
    }

    #[inline]
    pub fn get_parent(&self) -> Link<I, T> {
        if self.is_none() {
            Link::<I, T>::none()
        } else {
            unsafe { (*self.entry).parent.clone() }
        }
    }

    #[inline]
    pub fn set_next(&mut self, next: &Link<I, T>) {
        if self.is_some() {
            unsafe {
                (*self.entry).next = next.clone();
            }
        }
    }

    #[inline]
    pub fn set_prev(&mut self, prev: &Link<I, T>) {
        if self.is_some() {
            unsafe {
                (*self.entry).prev = prev.clone();
            }
        }
    }

    #[inline]
    pub fn set_value(&mut self, value: T) {
        if self.is_some() {
            unsafe {
                (*self.entry).value = value;
            }
        }
    }

    #[inline]
    pub fn convert_to_singleton(&mut self) {
        if self.is_some() {
            unsafe {
                (*self.entry).next = self.clone();
                (*self.entry).prev = self.clone();
            }
        }
    }

    #[inline]
    pub fn set_is_marked(&mut self, is_marked: bool) {
        if self.is_some() {
            unsafe { (*self.entry).is_marked = is_marked }
        }
    }

    #[inline]
    pub fn get_is_marked(&mut self) -> bool {
        if self.is_some() {
            unsafe { (*self.entry).is_marked }
        } else {
            false
        }
    }
}

impl<I: Eq + Hash + Copy + Debug, T: PartialOrd + Debug> Clone for Link<I, T> {
    #[inline]
    fn clone(&self) -> Self {
        Link { entry: self.entry.clone() }
    }
}

impl<I: Eq + Hash + Copy + Debug, T: PartialOrd + Debug> PartialEq for Link<I, T> {
    #[inline]
    fn eq(&self, other: &Link<I, T>) -> bool {
        if self.is_none() || other.is_none() {
            false
        } else {
            unsafe { (*self.entry).value.eq(&(*other.entry).value) }
        }
    }
}

impl<I: Eq + Hash + Copy + Debug, T: PartialOrd + Debug> PartialOrd for Link<I, T> {
    #[inline]
    fn partial_cmp(&self, other: &Link<I, T>) -> Option<Ordering> {
        if self.is_none() || other.is_none() {
            None
        } else {
            unsafe { (*self.entry).value.partial_cmp(&(*other.entry).value) }
        }
    }
}

#[test]
fn test_size() {
    let mut heap = FibonacciHeap::new();

    heap.push(100, 1);

    assert_eq!(1, heap.size);
}

#[test]
fn test_min() {
    let mut heap = FibonacciHeap::new();

    heap.push(100, 1);

    assert_eq!(1, *heap.min().unwrap());
}

#[test]
fn test_pop() {
    let mut heap = FibonacciHeap::new();

    heap.push(100, 1);

    assert_eq!(1, heap.pop().unwrap());
    assert_eq!(None, heap.get(100));
    assert_eq!(0, heap.size);
}

#[test]
fn test_order() {
    let mut heap = FibonacciHeap::new();

    heap.push(107, 7);
    heap.push(101, 1);
    heap.push(108, 8);
    heap.push(104, 4);
    heap.push(105, 5);
    heap.push(102, 2);
    heap.push(103, 3);
    heap.push(106, 6);

    assert_eq!(1, heap.pop().unwrap());
    assert_eq!(2, heap.pop().unwrap());
    assert_eq!(3, heap.pop().unwrap());
    assert_eq!(4, heap.pop().unwrap());
    assert_eq!(5, heap.pop().unwrap());
    assert_eq!(6, heap.pop().unwrap());
    assert_eq!(7, heap.pop().unwrap());
    assert_eq!(8, heap.pop().unwrap());
}

#[test]
fn test_decrease_key() {
    let mut heap = FibonacciHeap::new();

    heap.push(107, 7);
    heap.push(101, 1);
    heap.push(108, 8);

    heap.decrease_key(107, 4);

    assert_eq!(1, heap.pop().unwrap());
    assert_eq!(4, heap.pop().unwrap());
    assert_eq!(8, heap.pop().unwrap());
}

#[test]
fn test_get() {
    let mut heap = FibonacciHeap::new();
    heap.push(107, 7);
    assert_eq!(Some(&7), heap.get(107));
}

#[bench]
fn bench_push_pop(b: &mut ::test::Bencher) {
    b.iter(|| {
        // TODO: Optimize heap
        let mut heap = FibonacciHeap::new();

        for i in 1..10001 {
            heap.push(10001 - i, 10001 - i);
        }

        for _ in 1..10001 {
            heap.pop();
        }
    })
}

#[bench]
fn bench_decrease_key(b: &mut ::test::Bencher) {
    b.iter(|| {
        let mut heap = FibonacciHeap::new();

        for i in 1..10001 {
            heap.push(10001 - i, 10001 - i);
        }

        for i in 1..10001 {
            heap.decrease_key(10001 - i, 10001 - i - 1);
        }
    })
}
