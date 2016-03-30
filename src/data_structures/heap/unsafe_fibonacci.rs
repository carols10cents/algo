// Based on http://www.keithschwarz.com/interesting/code/?dir=fibonacci-heap

use std::mem;
use std::ptr;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::hash::Hash;

pub struct FibonacciHeap<T: PartialOrd + Eq + Hash + Clone> {
    size: usize,
    min: Link<T>,
    lookup: HashMap<T, Link<T>>,
    tree_table: Vec<Link<T>>,
    to_visit: Vec<Link<T>>,
}

struct Entry<T: PartialOrd> {
    pub value: T,
    pub degree: usize,
    pub is_marked: bool,
    pub parent: Link<T>,
    pub next: Link<T>,
    pub prev: Link<T>,
    pub child: Link<T>,
}

struct Link<T: PartialOrd> {
    entry: *mut Entry<T>,
}

impl<T: PartialOrd + Eq + Hash + Clone> FibonacciHeap<T> {
    pub fn new() -> FibonacciHeap<T> {
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

    pub fn push(&mut self, value: T) {
        let lookup_value = value.clone();
        let link = Link::new(value);

        let mut min = Link::none();
        mem::swap(&mut min, &mut self.min);

        self.lookup.insert(lookup_value, link.clone());
        self.min = FibonacciHeap::<T>::merge_entries(min, link);
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

        self.min = FibonacciHeap::<T>::merge_entries(new_min, min_child);

        if self.size == 0 {
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
                min_link.set_child(&FibonacciHeap::<T>::merge_entries(min_link_child, max));
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

        min.into_value()
    }

    pub fn decrease_key(&mut self, previous_value: T, decreased_value: T) {
        let mut link = self.lookup.get(&previous_value).expect("Could not find key to decrease").clone();
        link.set_value(decreased_value);

        let parent = link.get_parent();

        if parent.is_some() && link <= parent {
            self.cut_link(link.clone());
        }

        if link <= self.min {
            self.min = link;
        }
    }

    pub fn merge(x: FibonacciHeap<T>, y: FibonacciHeap<T>) -> FibonacciHeap<T> {
        let mut result = FibonacciHeap::new();

        result.min = FibonacciHeap::<T>::merge_entries(x.min, y.min);
        result.size = x.size + y.size;

        result
    }

    fn merge_entries(mut x: Link<T>, mut y: Link<T>) -> Link<T> {
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

    fn cut_link(&mut self, mut link: Link<T>) {
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
            self.min = FibonacciHeap::<T>::merge_entries(min, link);

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

impl<T: PartialOrd> Entry<T> {
    pub fn new(value: T) -> Entry<T> {
        Entry {
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

impl<T: PartialOrd> Link<T> {
    #[inline]
    pub fn none() -> Link<T> {
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

    pub fn new(value: T) -> Link<T> {
        let entry_box = Box::new(Entry::new(value));
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

    pub fn into_value(mut self) -> Option<T> {
        if self.is_none() {
            None
        } else {
            let mut raw_entry: *mut Entry<T> = ptr::null_mut();
            mem::swap(&mut raw_entry, &mut self.entry);

            let entry: Entry<T>;
            unsafe {
                entry = *Box::from_raw(raw_entry);
            }

            Some(entry.value)
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
    pub fn are_same(&self, other: &Link<T>) -> bool {
        self.entry == other.entry
    }

    #[inline]
    pub fn get_child(&self) -> Link<T> {
        if self.is_none() {
            Link::<T>::none()
        } else {
            unsafe { (*self.entry).child.clone() }
        }
    }

    #[inline]
    pub fn get_next(&self) -> Link<T> {
        if self.is_none() {
            Link::<T>::none()
        } else {
            unsafe { (*self.entry).next.clone() }
        }
    }

    #[inline]
    pub fn get_prev(&self) -> Link<T> {
        if self.is_none() {
            Link::<T>::none()
        } else {
            unsafe { (*self.entry).prev.clone() }
        }
    }

    #[inline]
    pub fn set_child(&mut self, child: &Link<T>) {
        if self.is_some() {
            unsafe {
                (*self.entry).child = child.clone();
            }
        }
    }

    #[inline]
    pub fn set_parent(&mut self, parent: &Link<T>) {
        if self.is_some() {
            unsafe {
                (*self.entry).parent = parent.clone();
            }
        }
    }

    #[inline]
    pub fn get_parent(&self) -> Link<T> {
        if self.is_none() {
            Link::<T>::none()
        } else {
            unsafe { (*self.entry).parent.clone() }
        }
    }

    #[inline]
    pub fn set_next(&mut self, next: &Link<T>) {
        if self.is_some() {
            unsafe {
                (*self.entry).next = next.clone();
            }
        }
    }

    #[inline]
    pub fn set_prev(&mut self, prev: &Link<T>) {
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

impl<T: PartialOrd> Clone for Link<T> {
    #[inline]
    fn clone(&self) -> Self {
        Link { entry: self.entry.clone() }
    }
}

impl<T: PartialOrd> PartialEq for Link<T> {
    #[inline]
    fn eq(&self, other: &Link<T>) -> bool {
        if self.is_none() || other.is_none() {
            false
        } else {
            unsafe { (*self.entry).value.eq(&(*other.entry).value) }
        }
    }
}

impl<T: PartialOrd> PartialOrd for Link<T> {
    #[inline]
    fn partial_cmp(&self, other: &Link<T>) -> Option<Ordering> {
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

    heap.push(1);

    assert_eq!(1, heap.size);
}

#[test]
fn test_min() {
    let mut heap = FibonacciHeap::new();

    heap.push(1);

    assert_eq!(1, *heap.min().unwrap());
}

#[test]
fn test_pop() {
    let mut heap = FibonacciHeap::new();

    heap.push(1);

    assert_eq!(1, heap.pop().unwrap());
}

#[test]
fn test_order() {
    let mut heap = FibonacciHeap::new();

    heap.push(7);
    heap.push(1);
    heap.push(8);
    heap.push(4);
    heap.push(5);
    heap.push(2);
    heap.push(3);
    heap.push(6);

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

    heap.push(7);
    heap.push(1);
    heap.push(8);

    heap.decrease_key(7, 4);

    assert_eq!(1, heap.pop().unwrap());
    assert_eq!(4, heap.pop().unwrap());
    assert_eq!(8, heap.pop().unwrap());
}

#[bench]
fn bench_push_pop(b: &mut ::test::Bencher) {
    b.iter(|| {
        // TODO: Optimize heap
        let mut heap = FibonacciHeap::new();

        for i in 1..10001 {
            heap.push(10001 - i);
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
            heap.push(10001 - i);
        }

        for i in 1..10001 {
            heap.decrease_key(i, i - 1);
        }
    })
}
