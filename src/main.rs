// Procedttre CycleEquiv (G)

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
// create () : BracketList — make an empty BracketList structure.
// size (bl : BracketList) : integer — number of elements in BracketList structure.
// push (bl : BracketList e : bracket) : BracketList — push e on top of bl.
// top (bl : BracketList) : bracket — topmost bracket in bl.
// delete (bl : BracketList e : bracket) : BracketList — delete e from bl.
// concat (bl1 bl2 : BracketList) : BracketList — concatenate bl1 and bl2 .

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

use petgraph::graph::NodeIndex;

fn main() {
    println!("Hello, world!");

    use petgraph::visit::Dfs;
    use petgraph::Graph;

    let mut graph = Graph::<usize, ()>::new();
    let a = graph.add_node(1);
    // print the node index for node a
    println!("{}", a.index());
    
    let b = graph.add_node(2);
    let c = graph.add_node(3);
    let d = graph.add_node(4);

    // get node at a given index 0
    let node = graph[NodeIndex::new(0)];
    println!("got node and index 0 {}", node);

    graph.add_edge(a, b, ());
    graph.add_edge(a, d, ());
    graph.add_edge(b, c, ());
    graph.add_edge(c, d, ());

    let mut dfs = Dfs::new(&graph, a);

    // print the dfs order
    println!("Dfs order starting from node {:?}:", a);
    while let Some(nx) = dfs.next(&graph) {
        println!("{} {:?}", nx.index(), graph[nx]);
    }
}
