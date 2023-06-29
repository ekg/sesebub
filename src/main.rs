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
//use std::collections::LinkedList;

//use std::collections::linked_list::{Cursor, CursorMut};

#[derive(Clone,Debug)]
struct Node {
    id: usize, // external id -- not used in algorithm
    dfsnum: usize, // depth in DFS
    blist: BracketList, // list of bracket edges
    hi: usize, // highest dfsnum of any descendant
}

// implement default constructor for Node that takes only the id
impl Node {
    fn new(id_: usize) -> Node {
        Node {
            id: id_,
            dfsnum: 0,
            blist: BracketList::new(),
            hi: usize::max_value(),
        }
    }
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
    // pointer to bracket list cell where this edge is stored
    //blist_cell: Option<CursorMut<EdgeList>>,
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
//            blist_cell: None,
        }
    }
}

// display method for Edge that shows all attributes
impl fmt::Display for Edge {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Edge: from: {}, to: {}, class: {}, recent_size: {}, recent_class: {}, is_backedge: {}, is_capping: {}", self.from, self.to, self.class, self.recent_size, self.recent_class, self.is_backedge, self.is_capping)
    }
}

type EdgeList = Vec<Rc<RefCell<Edge>>>;

#[derive(Clone,Debug)]
struct BracketList {
    brackets: EdgeList,
}

// display method for BracketList
impl fmt::Display for BracketList {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut result = String::new();
        for bracket in self.brackets.iter() {
            // show the to and from ids of the edges
            result.push_str(&format!("({}, {}), ", bracket.borrow().from, bracket.borrow().to));
        }
        write!(f, "{}", result)
    }
}

impl BracketList {
    fn new() -> Self {
        Self { brackets: EdgeList::new() }
    }

    fn size(&self) -> usize {
        self.brackets.len()
    }

    fn push(&mut self, edge: Rc<RefCell<Edge>>) {
        self.brackets.push(edge);
    }

    fn top(&self) -> Option<Rc<RefCell<Edge>>> {
        self.brackets.last().cloned()
    }

    fn delete(&mut self, edge: Rc<RefCell<Edge>>) {
        for (i, bracket) in self.brackets.iter().enumerate() {
            if Rc::ptr_eq(&edge, bracket) {
                self.brackets.remove(i);
                break;
            }
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
                label.push_str(" c:");
                label.push_str(&e.class.to_string());
            }
            if e.recent_class > 0 {
                label.push_str(" r:");
                label.push_str(&e.recent_class.to_string());
            }
            if e.recent_size > 0 {
                label.push_str(" s:");
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
            label.push_str(&format!("id: {}, dfsnum: {}, hi: {}\nblist: {}", n.id, n.dfsnum, n.hi, n.blist));
            //let mut blist = String::new();
            //for bracket in n.blist.brackets.iter() {
            //    blist.push_str(&format!("{} ", bracket.borrow()));
            //}
            //label.push_str(&format!("{{{}}}", blist));
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

fn cycle_equivalence(graph: &mut Graph<Rc<RefCell<Node>>, Rc<RefCell<Edge>>, Undirected>,
                     rev_order: &Vec<NodeIndex>) {
    let mut next_class = 1;
    // perform an undirected depth-fist search on G
    // for each node n in reverse depth-first order do
    // /* compute n.hi */
    //    hi_0 := min {t.dfsnum | (n, t) is a backedge }; // where t is a predecessor of n in the DFS tree
    //    hi_1 := min {c.hi | c is a child of n };
    //    n.hi := min {hi_0, hi_1};
    //    hichild := any child c of n having c.hi == hi_1;
    //    hi_2 := min {c.hi | c is a child of n other than hichild };
    for ni in rev_order {
        let node = graph[*ni].clone();
        let nid = node.borrow().id;
        let ndfsnum = node.borrow().dfsnum;
        println!("cycle_equivalence: node {}", nid);
        // undirected edges
        let mut edges = Vec::new(); // all edges
        let mut children = Vec::new(); // just children in dfs tree
        for edge in graph.edges(*ni) {
            let edge = edge.weight().clone();
            let e = edge.borrow();
            // the traversal is undirected, so set from equal to the other node index
            // use nid to check which is the other node
            let from = if graph[NodeIndex::new(e.from)].borrow().id == nid { e.to } else { e.from };
            println!("cycle_equivalence: edge {} -> {}", from, nid);
            let other = graph[NodeIndex::new(from)].clone();
            // collect children
            if e.is_tree_edge && other.clone().borrow().dfsnum == ndfsnum + 1 {
                children.push(graph[NodeIndex::new(from)].clone());
            }
            // collect all edges
            edges.push((edge.clone(), graph[NodeIndex::new(from)].clone(), from));
        }
        let mut hi_0 = usize::max_value();
        let mut hi_1 = usize::max_value();
        let mut hi_2 = usize::max_value();
        let mut hichild = 0;
        for (edge, other, _) in edges.iter() {
            let edge = edge.borrow();
            let other = other.borrow();
            // get min of hi_0
            if edge.is_backedge {
                // print the backedge and dfsnum
                println!("cycle_equivalence: backedge {} -> {} with dfsnum {}", edge.from, edge.to, other.dfsnum);
                hi_0 = hi_0.min(other.dfsnum);
            }
            // the other is a child of current node
            // the edge should be a tree edge no?
            if other.dfsnum == ndfsnum + 1 {
                // print the tree edge and other.hi
                println!("cycle_equivalence: tree edge {} -> {} with hi {}", edge.from, edge.to, other.hi);
                hi_1 = hi_1.min(other.hi);
            }
        }
        node.borrow_mut().hi = hi_0.min(hi_1);
        for child in children.iter() {
            let child = child.borrow();
            println!("cycle_equivalence: child {} with hi {}", child.id, child.hi);
            if child.hi == hi_1 {
                hichild = child.id;
            }
        }
        for child in children.iter() {
            let child = child.borrow();
            if child.id != hichild {
                println!("cycle_equivalence: child {} with hi {}", child.id, child.hi);
                hi_2 = hi_2.min(child.hi);
            }
        }
        println!("cycle_equivalence: hi_0: {}, hi_1: {}, hi_2: {}", hi_0, hi_1, hi_2);
        // /* compute bracketlist */
        // n.blist := create();
        // for each child c of n do
        //   n.blist := concat(c.blist, n.blist);
        // endfor
        for child in children.iter() {
            let child = child.borrow();
            println!("cycle_equivalence: child {} with blist {:?}", child.id, child.blist);
            node.borrow_mut().blist.concat(&child.blist.clone());
        }
        // XXX TODO should this be over the children? what is the distinction between children and descendents
        // for each capping backedge d from a descendent of n to n, delete backedge d from n.blist
        for (edge_, other, _) in edges.iter() {
            let edge = edge_.borrow();
            let other = other.borrow();
            if other.dfsnum > ndfsnum && edge.is_backedge && edge.is_capping {
                println!("cycle_equivalence: capping backedge {} -> {}", edge.from, edge.to);
                node.borrow_mut().blist.delete(edge_.clone());
            }
        }
        // for each backedge b from a descendant of n to n
        // delete it from the node bracketlist n.blist
        // if b.class is not defined (==0), then set b.class to be a new class
        for (edge_, other, _) in edges.iter() {
            let mut edge = edge_.borrow_mut();
            let other = other.borrow();
            if other.dfsnum > ndfsnum && edge.is_backedge {
                // delete it from the node bracketlist n.blist
                println!("cycle_equivalence: backedge {} -> {}", edge.from, edge.to);
                node.borrow_mut().blist.delete(edge_.clone());
                if edge.class == 0 {
                    edge.class = next_class;
                    next_class += 1;
                }
            }
        }
        // for each backedge e from n to an ancestor of n
        // push the edge onto the node bracketlist n.blist
        for (edge_, other, _) in edges.iter() {
            let edge = edge_.borrow();
            let other = other.borrow();
            if other.dfsnum < ndfsnum && edge.is_backedge {
                node.borrow_mut().blist.push(edge_.clone());
            }
        }
        // if hi_2 < hi_0 then we create a capping backedge and add it to the graph
        if hi_2 < hi_0 {
            println!("cycle_equivalence: hi_2 < hi_0");
            let mut e = Edge::new(nid, hi_2);
            e.is_backedge = true;
            e.is_capping = true;
            e.class = next_class;
            next_class += 1;
            let edge = Rc::new(RefCell::new(e));
            graph.add_edge(NodeIndex::new(hi_2), NodeIndex::new(nid), edge.clone());
            node.borrow_mut().blist.push(edge.clone());
        }
        // determine the class for edge from parent(n) to n
        // if n is not the root of dfs tree
        if ndfsnum != 0 {
            println!("cycle_equivalence: n is not the root of dfs tree");
            // find the parent, which will be a node with a tree edge to this node where the dfsnum is one less
            // let e be the tree edge from parent(n) to n
            let mut e = Rc::new(RefCell::new(Edge::new(0, 0)));
            for (edge_, other, _) in edges.iter() {
                let edge = edge_.borrow();
                let other = other.borrow();
                if edge.is_tree_edge && other.dfsnum == ndfsnum - 1 {
                    println!("cycle_equivalence: found parent {} -> {}", edge.from, edge.to);
                    e = edge_.clone();
                    break;
                }
            }
            println!("cycle_equivalence: e is {:?}", e);
            // set b to the top of the node blist
            let b = node.borrow().blist.top().unwrap();
            // if b recent size is not the size of the node blist
            println!("cycle_equivalence: b recent size {} node blist size {}", b.borrow().recent_size, node.borrow().blist.size());
            if b.borrow().recent_size != node.borrow().blist.size() {
                println!("cycle_equivalence: b recent size is not the size of the node blist");
                // set b.recent_size to the size of the node blist
                b.borrow_mut().recent_size = node.borrow().blist.size();
                // set b.class to a new class
                b.borrow_mut().recent_class = next_class;
                next_class += 1;
            }
            // set e.class to b.recent_class
            e.borrow_mut().class = b.borrow().recent_class;
            println!("cycle_equivalence: e.class is {}", e.borrow().class);
        }
        println!("cycle_equivalence: end");
    }
}

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

fn add_graph_node(graph: &mut Graph<Rc<RefCell<Node>>, Rc<RefCell<Edge>>, Undirected>, id: usize) -> NodeIndex {
    let node = Rc::new(RefCell::new(Node::new(id)));
    graph.add_node(node)
}

fn add_graph_edge(graph: &mut Graph<Rc<RefCell<Node>>, Rc<RefCell<Edge>>, Undirected>, from: NodeIndex, to: NodeIndex) -> Rc<RefCell<Edge>> {
    let edge = Rc::new(RefCell::new(Edge::new(from.index(), to.index())));
    graph.add_edge(from, to, edge.clone());
    edge
}

fn make_example_0() -> Graph<Rc<RefCell<Node>>, Rc<RefCell<Edge>>, Undirected> {

    let mut graph = Graph::<Rc<RefCell<Node>>, Rc<RefCell<Edge>>, Undirected>::new_undirected();

    let a = add_graph_node(&mut graph, 0);
    let b = add_graph_node(&mut graph, 1);
    let c = add_graph_node(&mut graph, 2);
    let d = add_graph_node(&mut graph, 3);
    let e = add_graph_node(&mut graph, 4);

    // get node at a given index 0
    //let node = graph[NodeIndex::new(0)].clone();
    //println!("got node and index 0 {}", node.borrow());

    add_graph_edge(&mut graph, a, b);
    add_graph_edge(&mut graph, a, c);
    add_graph_edge(&mut graph, b, d);
    add_graph_edge(&mut graph, c, d);
    add_graph_edge(&mut graph, d, e);
    // add end to start
    add_graph_edge(&mut graph, e, a);

    graph
}


fn make_example_a() -> Graph::<Rc<RefCell<Node>>, Rc<RefCell<Edge>>, Undirected> {
    let mut graph = Graph::<Rc<RefCell<Node>>, Rc<RefCell<Edge>>, Undirected>::new_undirected();
    let n0 = add_graph_node(&mut graph, 0);
    let n1 = add_graph_node(&mut graph, 1);
    let n2 = add_graph_node(&mut graph, 2);
    let n3 = add_graph_node(&mut graph, 3);
    let n4 = add_graph_node(&mut graph, 4);
    let n5 = add_graph_node(&mut graph, 5);
    let n6 = add_graph_node(&mut graph, 6);
    let n7 = add_graph_node(&mut graph, 7);
    // link them up in a line
    add_graph_edge(&mut graph, n0, n1);
    add_graph_edge(&mut graph, n1, n2);
    add_graph_edge(&mut graph, n2, n3);
    add_graph_edge(&mut graph, n3, n4);
    add_graph_edge(&mut graph, n4, n5);
    add_graph_edge(&mut graph, n5, n6);
    add_graph_edge(&mut graph, n6, n7);
    // add back edges
    // start to end
    add_graph_edge(&mut graph, n7, n0);
    // 1 to 4
    add_graph_edge(&mut graph, n1, n4);
    // 2 to 3
    add_graph_edge(&mut graph, n2, n3);
    // 5 to 6
    add_graph_edge(&mut graph, n5, n6);
    graph
}

fn main() {

    let mut graph = make_example_a();
    
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

    cycle_equivalence(&mut graph, &dfs_rev_order);
    write_dot(&graph, "graph3.dot");
    

}
