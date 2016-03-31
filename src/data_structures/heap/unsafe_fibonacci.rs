// Based on http://www.keithschwarz.com/interesting/code/?dir=fibonacci-heap

use std::mem;
use std::ptr;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::hash::Hash;

pub struct FibonacciHeap<I: Eq + Hash + Copy, T: PartialOrd> {
    size: usize,
    min: Link<I, T>,
    lookup: HashMap<I, Link<I, T>>,
    tree_table: Vec<Link<I, T>>,
    to_visit: Vec<Link<I, T>>,
}

struct Entry<I: Eq + Hash + Copy, T: PartialOrd> {
    pub id: I,
    pub value: T,
    pub degree: usize,
    pub is_marked: bool,
    pub parent: Link<I, T>,
    pub next: Link<I, T>,
    pub prev: Link<I, T>,
    pub child: Link<I, T>,
}

struct Link<I: Eq + Hash + Copy, T: PartialOrd> {
    entry: *mut Entry<I, T>,
}

impl<I: Eq + Hash + Copy, T: PartialOrd> FibonacciHeap<I, T> {
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
        self.min = FibonacciHeap::<I, T>::merge_entries(min, link);
        self.size += 1;
    }

    pub fn pop(&mut self) -> Option<T> {
        if self.is_empty() {
            return None;
        }

        self.size -= 1;

        let mut min = Link::none();
        mem::swap(&mut min, &mut self.min);

        if !min.get_next().are_same(&min) {
            let mut min_prev = min.get_prev();
            let mut min_next = min.get_next();
            min_prev.set_next(&min_next);
            min_next.set_prev(&min_prev);
            self.min = min_next;
        }

        let min_child = min.get_child();
        if !min_child.is_none() {
            let mut current = min_child.clone();
            while {
                current.set_parent(&Link::none());
                current = current.get_next();

                !current.are_same(&min_child)
            } {}
        }

        let mut new_min = Link::none();
        mem::swap(&mut new_min, &mut self.min);

        self.min = FibonacciHeap::<I, T>::merge_entries(new_min, min_child);

        if self.size == 0 {
            if let Some(id) = min.get_id() {
                self.lookup.remove(&id);
            }
            return min.into_value();
        }

        let mut current = self.min.clone();
        while self.to_visit.is_empty() || !self.to_visit[0].are_same(&current) {
            let next = current.get_next();
            self.to_visit.push(current);
            current = next;
        }

        for link_to_visit in &self.to_visit {
            let mut link = link_to_visit.clone();

            loop {
                let link_degree = link.get_degree();

                while link_degree >= self.tree_table.len() {
                    self.tree_table.push(Link::none());
                }

                if self.tree_table[link_degree].is_none() {
                    self.tree_table[link_degree] = link.clone();
                    break;
                }

                self.tree_table.push(Link::none());
                let other = self.tree_table.swap_remove(link_degree);

                let (mut min_link, mut max) = if link < other {
                    (link, other)
                } else {
                    (other, link)
                };

                let mut max_next = max.get_next();
                let mut max_prev = max.get_prev();
                max_next.set_prev(&max_prev);
                max_prev.set_next(&max_next);

                let max_clone = max.clone();
                max.set_prev(&max_clone);
                max.set_next(&max_clone);

                max.set_parent(&min_link);

                let min_link_child = min_link.get_child();
                min_link.set_child(&FibonacciHeap::<I, T>::merge_entries(min_link_child, max));
                // max.is_marked = false;

                min_link.inc_degree();

                link = min_link;
            }

            if link <= self.min {
                self.min = link;
            }
        }

        self.to_visit.clear();
        self.tree_table.clear();

        if let Some(id) = min.get_id() {
            self.lookup.remove(&id);
        }
        min.into_value()
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

impl<I: Eq + Hash + Copy, T: PartialOrd> Entry<I, T> {
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

impl<I: Eq + Hash + Copy, T: PartialOrd> Link<I, T> {
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

impl<I: Eq + Hash + Copy, T: PartialOrd> Clone for Link<I, T> {
    #[inline]
    fn clone(&self) -> Self {
        Link { entry: self.entry.clone() }
    }
}

impl<I: Eq + Hash + Copy, T: PartialOrd> PartialEq for Link<I, T> {
    #[inline]
    fn eq(&self, other: &Link<I, T>) -> bool {
        if self.is_none() || other.is_none() {
            false
        } else {
            unsafe { (*self.entry).value.eq(&(*other.entry).value) }
        }
    }
}

impl<I: Eq + Hash + Copy, T: PartialOrd> PartialOrd for Link<I, T> {
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
