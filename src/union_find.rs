use std::{collections::HashMap, cell::Cell};

pub trait Key : Clone + Copy + PartialEq  {
    fn to_key(x: usize) -> Self;
    fn from_key(self) -> usize;
}

pub struct UnionFind<K: Key,V> {
    roots: HashMap<K, (usize, V)>,
    nodes: Vec<Cell<K>>,
}

pub trait Union<K> {
    type Err;

    fn union(table: &mut UnionFind<K,Self>, l: Self, r: Self) -> Result<Self, Self::Err>;
}

impl<K: Key, V: Union<K>> UnionFind<K, V> {
    pub fn new() -> Self {
	UnionFind {
	    roots: HashMap::new(),
	    nodes: Vec::new(),
	}
    }

    pub fn make_set(&mut self, v: V) -> K {
	let key = self.nodes.len();
	self.roots.insert(key, (0, v));
	self.nodes.push(Cell::new(key));
	Key::to_key(key)
    }

    pub fn get(&self, k: K) -> &V {
	&self.roots[self.find(k).from_key()].1
    }

    pub fn find(&self, k: K) -> K {
	let mut key = k.from_key();

	let mut node = &self.nodes[key];
	let mut parent = node.get();

	while key != parent {
	    key = parent;
	    let new_node = &self.nodes[key];
	    parent = new_node.get();
	    node.set(parent);
	    node = new_node;
	}

	Key::to_key(key)
    }

    pub fn union(&mut self, x: K, y: K) -> Result<(), V::Err> {
	let k1 = self.find(x);
	let k2 = self.find(y);

	if k1 != k2 {
	    let (r1, v1) = self.roots.remove(k1).unwrap();
	    let (r2, v2) = self.roots.remove(k2).unwrap();

	    let v = V::union(self, v1, v2)?;
	    if r1 < r2 {
		self.nodes[k1.from_key()].set(k2);
		self.roots.insert(k2, (v, r2));
	    } if r1 == r2 {
		self.nodes[k1.from_key()].set(k2);
		self.roots.insert(k2, (v, r2 + 1))
	    } else {
		self.nodes[k2.from_key()].set(k1);
		self.roots.insert(k1, (v, r1));
	    }
	    Ok(())
	} else {
	    Ok(())
	}
    }
}
