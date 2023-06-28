// Procedure CycleEquiv (G)

// Given a strongly connected graph S , let U be the undirected
// multigraph formed by removing edge directions. Since U
// is connected, a depth-first traversal will yield a depth-first
// spanning tree, and the edges of U are divided into a set of
// tree edges and a set of backedges. Notice that any cycle in U
// must contain at least one backedge. We use this observation
// to recast the problem of cycle equivalence in terms of sets
// of backedges rather than sets of cycles.

// Definition 7 In any depth-first traversal of U , a bracket of
// a tree edge t is a backedge connecting a descendant of t to
// an ancestor of t.
// Now consider whether two edges in U are cycle equivalent.
// Two backedges cannot be cycle equivalent since the
// cycle formed from a backedge together with the tree path
// connecting its endpoints contains no other backedges. On
// the other hand, a tree edge and a backedge or two tree edges
// may be cycle equivalent. The following theorems establish
// conditions for detecting these equivalences.

// Theorem 4 A backedge b and a tree edge t are cycle equivalent
// if and only if b is the only bracket of t.

// Lemma 1 In a depth-first spanning tree of U , if tree edges
// s and t have any bracket in common then they are ordered
// by the ancestor relation in the tree.

// Theorem 5 Tree edges s and t are cycle equivalent in U
// if and only if they have the same set of brackets in any
// depth-first spanning tree of U.

// ...

// Finally, we must handle general depth-first spanning trees;
// an example is shown in Figure 3(c). When we encounter
// a node that has more than one child, the bracket sets of
// the children must be merged. Unfortunately, the notion of
// ‘innermost bracket’ is no longer well-defined. For example,
// at node e in Figure 3(c), it is not clear whether the most-
// recently added backedge should be edge (f d) or edge (h c).
// The resolution of this difficulty rests on the observation that
// only one of the subtrees below node e can contain any edges
// cycle equivalent to an ancestor of e. This is because an edge
// in a subtree of e can only have brackets originating in the
// same subtree; therefore, any ancestor of e having brackets
// from multiple subtrees of e cannot be cycle equivalent with
// any descendant of e. For example, edges between e and b
// cannot be cycle equivalent to any edge below e. However,
// edges between b and a can be cycle equivalent to edges
// between h and i.

// The solution therefore is to add an additional “capping”
// backedge whenever we need to merge two or more bracket
// sets. This backedge becomes the topmost bracket in the
// set, and the children’s bracket sets are then concatenated in
// arbitrary order. The new bracket originates from the node
// whose children are being merged, and extends up to the
// highest node whose brackets come from more than one of
// the branches. To add this new backedge requires keeping
// track (at each node in the tree) of the highest node reached
// by any backedge below this point. The destination of the
// new backedge from a node is the second-highest of the
// node’s children’s highest backedges. This could be found
// by examination of the bracket sets, but the highest-ending
// backedge is not necessarily related to the first bracket in each
// set (the highest-originating), so a full search of the bracket
// set would be necessary. Fortunately, we can simply compute
// this information independently in constant time for each
// node. In Figure 3(c), we would add a new backedge from e to
// b, as shown by the dotted edge. We must show that once this
// backedge is added, the pair < topmost bracket set size >
// identifies the equivalence class as before.

// Lemma 2 The capping backedges added by the algorithm
// do not alter the cycle equivalence relation for tree edges.

// Theorem 6 The compact bracket set names uniquely identify
// bracket sets.

// getting started...

// We use integers to identify cycle equivalence classes.
// Procedure new-class () returns a new integer each time it
// is called. This can be implemented using a static variable
// initialized to zero that is incremented and returned each time
// the procedure is called.
// We assume each node structure has the following fields:
// n.dfsnum — depth-first search number of node.
// n.blist — pointer to node’s bracketlist.
// n.hi — dfsnum of destination node closest to root of
// any edge originating from a descendant of node n.

// The edge data structure saves the equivalence class number
// and the size of the bracket list when the edge was most
// recently the topmost bracket of a bracket list. For example,
// in Figure 3(b), edge z is the topmost bracket for edges c, a
// and finally b. a is given the same equivalence class number
// as c because the size of the bracket list at a is the same as
// it was when z was previously the topmost bracket (at edge
// c). In contrast, a and b are given different equivalence class
// numbers. To access the values saved on brackets, each edge
// structure has the following fields:
// e.class — index of edge’s cycle equivalence class.
// e.recentSize — size of bracket set when e was most
// recently the topmost edge in a bracket set.
// e.recentClass — equivalence class number of tree edge
// for which e was most recently the topmost bracket.

// BracketList overview
// create () : — make an empty BracketList structure.
// size : — number of elements in BracketList structure.
// push :  — push e on top of bl.
// top : — topmost bracket in bl.
// delete — delete e from bl.
// concat  — concatenate bl1 and bl2 .


use petgraph::visit::Dfs;
use petgraph::Graph;
use petgraph::Undirected;
use petgraph::graph::NodeIndex;
//use petgraph::Direction::{Incoming, Outgoing};
use petgraph::visit::DfsEvent;

use dot_writer::{Color, DotWriter, Attributes, Shape, Style};

use std::fs::File;
use std::io::Write;
use std::process::Command;
use std::fmt;

use std::rc::Rc;
use std::cell::RefCell;
use linked_list::LinkedList;

#[derive(Clone,Debug)]
struct Node {
    id: usize, // external id -- not used in algorithm
    dfsnum: usize, // depth in DFS
    blist: BracketList, // list of bracket edges
    hi: usize, // highest dfsnum of any descendant
}

// display method for Node
impl fmt::Display for Node {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Node: id: {}, dfsnum: {}, hi: {}, blist: {}", self.id, self.dfsnum, self.hi, self.blist)
    }
}

#[derive(Clone,Debug)]
struct Edge {
    from: usize, // index of from node in graph
    to: usize, // index of to node in graph
    class: usize, // cycle equivalence class
    recent_size: usize, // size of bracket list when this edge was most recently the topmost bracket
    recent_class: usize, // equivalence class number of tree edge for which this edge was most recently the topmost bracket
    is_tree_edge: bool, // is this edge a tree edge?
    is_backedge: bool, // is this edge a backedge?
    is_capping: bool, // is this edge a capping backedge?
}

// implement default constructor for Edge that takes only from and to
impl Edge {
    fn new(_from: usize, _to: usize) -> Edge {
        Edge {
            from: _from,
            to: _to,
            class: 0,
            recent_size: 0,
            recent_class: 0,
            is_tree_edge: false,
            is_backedge: false,
            is_capping: false,
        }
    }
}

// display method for Edge that shows all attributes
impl fmt::Display for Edge {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Edge: from: {}, to: {}, class: {}, recent_size: {}, recent_class: {}, is_backedge: {}, is_capping: {}", self.from, self.to, self.class, self.recent_size, self.recent_class, self.is_backedge, self.is_capping)
    }
}

#[derive(Clone,Debug)]
struct BracketList {
    brackets: LinkedList<Rc<RefCell<Edge>>>,
}

// display method for BracketList
impl fmt::Display for BracketList {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut result = String::new();
        for bracket in self.brackets.iter() {
            result.push_str(&format!("{} ", bracket.borrow()));
        }
        write!(f, "{}", result)
    }
}

impl BracketList {
    fn new() -> Self {
        Self { brackets: LinkedList::new() }
    }

    fn push(&mut self, edge: Rc<RefCell<Edge>>) {
        self.brackets.push_back(edge);
    }

    fn top(&self) -> Option<Rc<RefCell<Edge>>> {
        self.brackets.back().cloned()
    }

    fn delete(&mut self, edge: &Rc<RefCell<Edge>>) {
        let mut cursor = self.brackets.cursor();
        while let Some(e) = cursor.peek_next() {
            if Rc::ptr_eq(e, edge) {
                cursor.remove();
                break;
            }
            cursor.next();
        }
    }
    
    fn concat(&mut self, other: &Self) {
        self.brackets.append(&mut other.brackets.clone());
    }
}

// function that writes the petgraph to a dot format file
fn write_dot(graph: &Graph<Rc<RefCell<Node>>, Rc<RefCell<Edge>>, Undirected>, file_name: &str) {
    let mut output_bytes = Vec::new();
    {
        let mut writer = DotWriter::from(&mut output_bytes);
        //writer.set_pretty_print(false);
        let mut agraph = writer.graph();
        for edge in graph.edge_references() {
            let e = edge.weight().borrow();
            let f = graph[NodeIndex::new(e.from)].borrow().id.to_string();
            let t = graph[NodeIndex::new(e.to)].borrow().id.to_string();
            // label the edge with a compact description of key attributes
            let mut label = String::new();
            //label.push('[');
            if e.is_tree_edge {
                // use tree emoji
                label.push('🌲');
            }
            if e.is_backedge {
                // use back emoji
                label.push('🔙');
            }
            if e.is_capping {
                // use hat emoji
                label.push('🎩');
            }
            if e.class > 0 {
                label.push_str(&e.class.to_string());
            }
            if e.recent_class > 0 {
                label.push_str(&e.recent_class.to_string());
            }
            if e.recent_size > 0 {
                label.push_str(&e.recent_size.to_string());
            }
            //label.push(']');
            agraph.edge(&f, &t).attributes().set("label", label.as_str(), true);
        }
        for node in graph.node_indices() {
            let n = graph[node].borrow();
            let id = n.id.to_string();
            // build a label that displays all attributes compactly
            // pretty print the blist so that it fits in the node
            let mut label = String::new();
            label.push_str(&format!("id: {}, dfsnum: {}, hi: {}\nblist: ", n.id, n.dfsnum, n.hi));
            let mut blist = String::new();
            for bracket in n.blist.brackets.iter() {
                blist.push_str(&format!("{} ", bracket.borrow()));
            }
            label.push_str(&format!("{{{}}}", blist));
            agraph.node_named(id)
                .set_shape(Shape::Rectangle)
                .set_label(label.as_str());
        }
    }
    let mut file = File::create(file_name).unwrap();
    file.write_all(&output_bytes).unwrap();
    // run dot to generate pdf
    Command::new("dot")
        .arg("-Tpdf")
        .arg(file_name)
        .arg("-o")
        .arg(file_name.to_owned() + ".pdf")
        .output()
        .expect("failed to execute process");
}


// 1: perform an undirected depth-fist search on G
// 2: for each node n in reverse depth-first order do
// 3: /* compute n.hi */
// 4:   hi_0 := min {t.dfsnum | (n, t) is a backedge }; // where t is a predecessor of n in the DFS tree
// 5:   hi_1 := min {c.hi | c is a child of n };
// 6:   n.hi := min {hi_0, hi_1};
// 7:   hichild := any child c of n having c.hi == hi_1;
// 8:   hi_2 := min {c.hi | c is a child of n other than hichild };
// 9:
// 10:  /* compute bracketlist */
// 11:  n.blist := create();
// 12:  for each child c of n do
// 13:    n.blist := concat(c.blist, n.blist);
// 14:  endfor
// 15:  for each capping backedge d from a descendant of n to n do
// 16:    delete(n.blist, d);
// 17:  endfor
// 18:  for each backedge b from a descendant of n to n do
// 19:    delete(n.blist, b);
// 20:    if b.class undefined then
// 21:      b.class := new_class();
// 22:    endif
// 23:  endfor
// 24:  for each backedge e from n to an ancestor of n do
// 25:    push(n.blist, e);
// 26:  endfor
// 27:  if hi_2 < hi_0 then
// 28:    /* create capping backedge */
// 29:    d := (n, node[hi_2]);
// 30:    push(n.blist, d);
// 31:  endif
// 32:
// 33:  /* determine class for edge from parent(n) to n */
// 34:  if n is not the root of dfs tree then
// 35:    let e be the tree edge from parent(n) to n;
// 36:    b := top(n.blist);
// 37:    if b.recentSize != size(n.blist) then
// 38:      b.recentSize := size(n.blist);
// 39:      b.recentClass := new_class();
// 40:    endif
// 41:    e.class := b.recentClass;
// 42:
// 43:    /* check for e,b equivalence */
// 44:    if b.recentSize == 1 then
// 45:      b.class := e.class;
// 46:    endif
// 47:  endif
// 48:endfor
// }

use petgraph::visit::depth_first_search;

fn dfs_tree(graph: &mut Graph<Rc<RefCell<Node>>, Rc<RefCell<Edge>>, Undirected>) -> Vec<NodeIndex> {
    // get the source node of the graph
    let source = graph.node_indices().next().unwrap();
    let mut dfs_order = Vec::new();
    //let mut back_edges = Vec::new();
    let mut tree_edges = Vec::new();
    
    // run a depth first search and use DfsEvent matching to mark tree edges and back edges
    // and record when we first encounter a node in the search in dfs_order
    depth_first_search(&*graph, Some(source), |event| {
        match event {
            DfsEvent::Discover(node, _) => {
                dfs_order.push(node);
            }
            DfsEvent::TreeEdge(from, to) => {
                tree_edges.push((from, to));
            }
            //DfsEvent::BackEdge(from, to) => {
            //    back_edges.push((from, to));
            //}
            _ => {}
        }
    });

    println!("dfs_order: {:?}", dfs_order);
    println!("tree_edges: {:?}", tree_edges);
    //println!("back_edges: {:?}", back_edges);
    for (from, to) in tree_edges {
        // modify the edge in the graph to be marked as a backedge
        let mut edge = graph.edge_weight_mut(graph.find_edge(from, to).unwrap()).unwrap().borrow_mut();
        edge.is_tree_edge = true;
        edge.is_backedge = false;
    }

    // for all edges that are not tree edges, mark them as backedges
    for e in graph.edge_weights_mut() {
        let mut edge = e.borrow_mut();
        //let mut edge = graph.edge_weight_mut(graph.find_edge(from, to).unwrap()).unwrap().borrow_mut();
        if !edge.is_tree_edge {
            edge.is_backedge = true;
        }
        //edge.is_backedge = true;
    }

    for (i, node) in dfs_order.clone().into_iter().enumerate() {
        let mut n = graph[node].borrow_mut();
        n.dfsnum = i;
        //n.hi = i;
    }

    dfs_order.reverse();
    dfs_order
}



fn main() {

    let mut graph = Graph::<Rc<RefCell<Node>>, Rc<RefCell<Edge>>, Undirected>::new_undirected();

    let a = graph.add_node(Rc::new(RefCell::new(Node { id: 0, dfsnum: 0, blist: BracketList::new(), hi: 0 })));
    let b = graph.add_node(Rc::new(RefCell::new(Node { id: 1, dfsnum: 0, blist: BracketList::new(), hi: 0 })));
    let c = graph.add_node(Rc::new(RefCell::new(Node { id: 2, dfsnum: 0, blist: BracketList::new(), hi: 0 })));
    let d = graph.add_node(Rc::new(RefCell::new(Node { id: 3, dfsnum: 0, blist: BracketList::new(), hi: 0 })));
    let e = graph.add_node(Rc::new(RefCell::new(Node { id: 4, dfsnum: 0, blist: BracketList::new(), hi: 0 })));

    // get node at a given index 0
    let node = graph[NodeIndex::new(0)].clone();
    //println!("got node and index 0 {}", node.borrow());

    graph.add_edge(a, b, Rc::new(RefCell::new(Edge::new(0, 1))));
    graph.add_edge(a, c, Rc::new(RefCell::new(Edge::new(0, 2))));
    graph.add_edge(b, d, Rc::new(RefCell::new(Edge::new(1, 3))));
    graph.add_edge(c, d, Rc::new(RefCell::new(Edge::new(2, 3))));
    graph.add_edge(d, e, Rc::new(RefCell::new(Edge::new(3, 4))));
    // add end to start
    graph.add_edge(e, a, Rc::new(RefCell::new(Edge::new(4, 0))));

    // write the graph to dot format to file
    //let mut f = File::create("graph.dot").unwrap();
    // use the dot_writer crate to write the graph to file
    // using square nodes and the default style
    write_dot(&graph, "graph.dot");
    
    //write!(f, "{:?}", Dot::with_config(&graph, &[Config::NodeShape(Shape::Square)])).unwrap();
    // call graphviz dot to render the file to graph.pdf
    //Command::new("dot").args(["-Tpdf", "graph.dot", "-o", "graph.pdf"]).status().unwrap();
    let dfs_rev_order = dfs_tree(&mut graph);
    write_dot(&graph, "graph2.dot");

    

}
