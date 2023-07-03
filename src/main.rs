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
        write!(f, "Node: id: {}, dfs: {}, hi: {}, blist: {}", self.id, self.dfsnum, self.hi, self.blist)
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
    // pointer to bracket list cell where this edge is stored, which in big-O would make deleting it faster
    // but now we're using a vector implementation and iterating over it to remove entries, which has other efficiencies
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

type FlowGraph = Graph::<Rc<RefCell<Node>>, Rc<RefCell<Edge>>, Undirected>;

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
fn write_dot(graph: &FlowGraph,
             file_name: &str,
             ftype: &str) {
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
                label.push('🌿');
            }
            if e.is_backedge {
                // use back emoji
                label.push('🙃');
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
            label.push_str(&format!("id: {}, dfs: {}, hi: {}\nblist: {}", n.id, n.dfsnum, n.hi, n.blist));
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
        .arg(format!("-T{}", ftype).as_str())
        .arg(file_name)
        .arg("-o")
        .arg(file_name.to_owned() + format!(".{}", ftype).as_str())
        .output()
        .expect("failed to execute process");
}

fn cycle_equivalence(graph: &mut FlowGraph,
                     rev_order: &Vec<NodeIndex>) {
    let mut curr_class = 1;
    //closure for next_class()
    let mut next_class = || {
        let result = curr_class;
        curr_class += 1;
        result
    };
    
    // perform an undirected depth-fist search on G
    // for each node n in reverse depth-first order do
    // /* compute n.hi */
    //    hi_0 := min {t.dfsnum | (n, t) is a backedge }; // where t is a predecessor of n in the DFS tree
    //    hi_1 := min {c.hi | c is a child of n };
    //    n.hi := min {hi_0, hi_1};
    //    hichild := any child c of n having c.hi == hi_1;
    //    hi_2 := min {c.hi | c is a child of n other than hichild };
    // print the graph
    //let mut iter = 0; // put iter in the file name
    //write_dot(graph, format!("graph_{}.ce.dot", iter).as_str(), "png");
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
            if e.is_tree_edge && other.borrow().dfsnum > ndfsnum {
                children.push(graph[NodeIndex::new(from)].clone());
            }
            // collect all edges
            edges.push((edge.clone(), graph[NodeIndex::new(from)].clone(), from));
        }
        //write_dot(graph, format!("graph_{}.ce.1.dot", iter).as_str(), "png");
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
            if other.dfsnum > ndfsnum && edge.is_tree_edge {
                // print the tree edge and other.hi
                println!("cycle_equivalence: tree edge {} -> {} with hi {}", edge.from, edge.to, other.hi);
                hi_1 = hi_1.min(other.hi);
            }
        }
        //write_dot(graph, format!("graph_{}.ce.2.dot", iter).as_str(), "png");
        println!("cycle_equivalence: hi_1 {}", hi_1);
        node.borrow_mut().hi = hi_0.min(hi_1);
        println!("cycle_equivalence: node {} hi {}", nid, node.borrow().hi);
        for child in children.iter() {
            let child = child.borrow();
            println!("cycle_equivalence: child {} with hi {}", child.id, child.hi);
            if child.hi == hi_1 {
                println!("cycle_equivalence: hichild {}", child.id);
                hichild = child.id;
                break;
            }
        }
        //write_dot(graph, format!("graph_{}.ce.3.dot", iter).as_str(), "png");
        for child in children.iter() {
            let child = child.borrow();
            if child.id != hichild {
                println!("cycle_equivalence: child {} with hi {}", child.id, child.hi);
                hi_2 = hi_2.min(child.hi);
            }
        }
        //write_dot(graph, format!("graph_{}.ce.4.dot", iter).as_str(), "png");
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
        //write_dot(graph, format!("graph_{}.ce.5.dot", iter).as_str(), "png");
        // for each capping backedge d from a descendent of n to n, delete backedge d from n.blist
        println!("cycle_equivalence: deleting capping backedges from descendents from blist");
        for (edge_, other, _) in edges.iter() {
            let edge = edge_.borrow();
            let other = other.borrow();
            if other.dfsnum > ndfsnum && edge.is_backedge && edge.is_capping {
                println!("cycle_equivalence: delete capping backedge {} -> {}", edge.from, edge.to);
                node.borrow_mut().blist.delete(edge_.clone());
            }
        }
        //write_dot(graph, format!("graph_{}.ce.6.dot", iter).as_str(), "png");
        // for each backedge b from a descendant of n to n
        // delete it from the node bracketlist n.blist
        // if b.class is not defined (==0), then set b.class to be a new class
        println!("cycle_equivalence: deleting backedges from descendents from blist");
        for (edge_, other, _) in edges.iter() {
            let mut edge = edge_.borrow_mut();
            let other = other.borrow();
            if other.dfsnum > ndfsnum && edge.is_backedge {
                // delete it from the node bracketlist n.blist
                println!("cycle_equivalence: delete backedge {} -> {}", edge.from, edge.to);
                node.borrow_mut().blist.delete(edge_.clone());
                if edge.class == 0 {
                    edge.class = next_class();
                }
                println!("cycle_equivalence: set edge class {}", edge.class);
            }
        }
        //write_dot(graph, format!("graph_{}.ce.7.dot", iter).as_str(), "png");
        // for each backedge e from n to an ancestor of n
        // push the edge onto the node bracketlist n.blist
        for (edge_, other, _) in edges.iter() {
            let edge = edge_.borrow();
            let other = other.borrow();
            if other.dfsnum < ndfsnum && edge.is_backedge {
                node.borrow_mut().blist.push(edge_.clone());
            }
        }
        //write_dot(graph, format!("graph_{}.ce.8.dot", iter).as_str(), "png");
        // if hi_2 < hi_0 then we create a capping backedge and add it to the graph
        if hi_2 < hi_0 {
            println!("cycle_equivalence: creating capping backedge because hi_2 = {} < hi_0 = {}", hi_2, hi_0);
            let mut e = Edge::new(nid, hi_2);
            e.is_backedge = true;
            e.is_capping = true;
            e.class = next_class();
            let edge = Rc::new(RefCell::new(e));
            graph.add_edge(NodeIndex::new(hi_2), NodeIndex::new(nid), edge.clone());
            node.borrow_mut().blist.push(edge.clone());
        }
        //write_dot(graph, format!("graph_{}.ce.9.dot", iter).as_str(), "png");
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
                if edge.is_tree_edge && other.dfsnum < ndfsnum {
                    println!("cycle_equivalence: found parent {} -> {}", edge.from, edge.to);
                    e = edge_.clone();
                    break;
                }
            }
            println!("cycle_equivalence: e is {:?}", e);
            println!("cycle_equivalence: node blist {:?}", node.borrow().blist);
            // set b to the top of the node blist
            let b = node.borrow().blist.top().unwrap();
            // if b recent size is not the size of the node blist
            println!("cycle_equivalence: b is {:?} b recent size {} node blist size {}", (b.borrow().from, b.borrow().to), b.borrow().recent_size, node.borrow().blist.size());
            if b.borrow().recent_size != node.borrow().blist.size() {
                println!("cycle_equivalence: b recent size is not the size of the node blist");
                // set b.recent_size to the size of the node blist
                b.borrow_mut().recent_size = node.borrow().blist.size();
                // set b.class to a new class
                b.borrow_mut().recent_class = next_class();
            }
            // set e.class to b.recent_class
            e.borrow_mut().class = b.borrow().recent_class;
            println!("cycle_equivalence: e.class is {}", e.borrow().class);
            if b.borrow().recent_size == 1 {
                b.borrow_mut().class = e.borrow().class;
            }
        }
        //iter += 1;
        //write_dot(graph, format!("graph_{}.ce.dot", iter).as_str(), "png");
    }
}

// region structure
#[derive(Debug)]
struct SeSeRegion {
    id: usize,
    parent: Option<Rc<RefCell<SeSeRegion>>>,
    children: Vec<Rc<RefCell<SeSeRegion>>>,
    backedges: Vec<Rc<RefCell<Edge>>>,
    nodes: Vec<Rc<RefCell<Node>>>,
    class: usize,
}

impl SeSeRegion {
    fn new(id_: usize, class_: usize) -> SeSeRegion {
        SeSeRegion {
            id: id_,
            parent: None,
            children: Vec::new(),
            backedges: Vec::new(),
            nodes: Vec::new(),
            class: class_,
        }
    }
}

// structuretree of regions
#[derive(Debug)]
struct StructureTree {
    root: Option<Rc<RefCell<SeSeRegion>>>,
}

impl StructureTree {
    fn new() -> StructureTree {
        StructureTree {
            root: None,
        }
    }
    // print the structure tree to dot format to the specified file
    // and write it to an image using graphviz
    fn print_dot(&self, _graph: &FlowGraph, filename: &str) {
        let mut dot = String::new();
        dot.push_str("digraph {\n");
        dot.push_str("node [shape=record];\n");
        //let mut iter = 0;
        let mut stack = Vec::new();
        if let Some(root) = &self.root {
            stack.push(root.clone());
        }
        while !stack.is_empty() {
            let node = stack.pop().unwrap();
            let node = node.borrow();
            // write the tree simply, using the format region_{} with the id for the graphviz node
            // edges correspond to parent -> child relationships
            dot.push_str(format!("region_{} [label=\"{{", node.id).as_str());
            dot.push_str(format!("id: {}", node.id).as_str());
            dot.push_str(format!("|class: {}", node.class).as_str());
            //dot.push_str(format!("|entry: {}", node.entry.index()).as_str());
            //dot.push_str(format!("|exit: {}", node.exit.index()).as_str());
            //dot.push_str(format!("|header: {}", node.header.index()).as_str());
            dot.push_str("}\"];\n");
            if let Some(parent) = &node.parent {
                let parent = parent.borrow();
                dot.push_str(format!("region_{} -> region_{};\n", parent.id, node.id).as_str());
            }
            for child in node.children.iter() {
                stack.push(child.clone());
            }
        }
        dot.push_str("}\n");
        let mut file = File::create(filename).unwrap();
        file.write_all(dot.as_bytes()).unwrap();
        // write the dot file to a PDF
        let mut command = Command::new("dot");
        command.arg("-Tpdf");
        command.arg(filename);
        command.arg("-o");
        command.arg(format!("{}.pdf", filename));
        command.output().unwrap();
    }
}

enum GraphEntity {
    Node(Rc<RefCell<Node>>),
    Edge(Rc<RefCell<Edge>>),
}

use std::collections::HashSet;

// write the above pseudocode as a rust function, assume we can use our annotations on the graph edges for cycle equivalence classes
fn build_structure_tree(graph: &mut FlowGraph) -> StructureTree  {

    write_dot(graph, "graph.dot", "pdf");
    let dfs_rev_order = dfs_tree(graph);
    write_dot(graph, "graph2.dot", "pdf");
    cycle_equivalence(&mut *graph, &dfs_rev_order);
    write_dot(graph, "graph3.dot", "pdf");

    //let dfs_order = dfs_rev_order.iter().rev();

    // remove the capping backedges from the graph
    let mut capping_edges = Vec::new();
    for edge_idx in graph.edge_indices() {
        let edge = graph.edge_weight_mut(edge_idx).unwrap();
        if edge.borrow().is_capping {
            capping_edges.push(edge_idx);
        }
    }
    for edge in capping_edges.iter() {
        graph.remove_edge(*edge);
    }

    // Perform depth-first traversal of the control flow graph
    // get the source node of the graph as the lowest node in the graph
    let source = NodeIndex::new(0);
    // run a depth first search and use DfsEvent matching to collect the edges in order of traversal

    // we will then store the ordered list of both edges and nodes that we encounter
    let mut dfs_order = Vec::<GraphEntity>::new();
    // run a depth first search and use DfsEvent matching to mark tree edges and back edges
    // and record when we first encounter a node in the search in dfs_order
    depth_first_search(&*graph, Some(source), |event| {
        match event {
            DfsEvent::Discover(node, _) => {
                let node = graph.node_weight(node).unwrap();
                dfs_order.push(GraphEntity::Node(node.clone()));
            }
            DfsEvent::TreeEdge(from, to) => {
                let edge = graph.edge_weight(graph.find_edge(from, to).unwrap()).unwrap();
                dfs_order.push(GraphEntity::Edge(edge.clone()));
            }
            DfsEvent::BackEdge(from, to) => {
                let edge = graph.edge_weight(graph.find_edge(from, to).unwrap()).unwrap();
                if edge.borrow().is_backedge { // avoid multiple counting of edges as we traverse back up them
                    dfs_order.push(GraphEntity::Edge(edge.clone()));
                }
            }
            _ => {}
        }
    });

    // Compute cycle equivalence classes for edges in O(E) time
    //cycle_equivalence(&*graph);
    // Initialize an empty stack to keep track of entered regions
    let mut stack = Vec::<Rc<RefCell<SeSeRegion>>>::new();
    // Initialize the root of the program structure tree
    let mut program_structure_tree = StructureTree::new();
    // closure to get the next region id
    let mut curr_id = 1;
    let mut next_region_id = || {
        let id = curr_id;
        curr_id += 1;
        id
    };

    /*
    Since cycle equivalent edges are totally ordered in the control flow graph by dominance and postdominance, each adjacent pair of edges in this order encloses a canonical SESE region.
    To find canonical regions, we first compute cycle equivalence classes for edges in O(E) time using the algorithm in Figure 4.
    Any depth-first traversal of the original control flow graph will visit edges in a given cycle equivalence class in order; during this traversal, entry and exit edges of canonical SESE regions are identified.
    Canonical regions can be organized into a program structure tree such that a region’s parent is the closest containing region and its children are all the regions immediately contained within the region.
    We discover the nesting relationship during the same depth-first traversal that determines canonical regions.
    The depth-first search keeps track of the most recently entered region (i.e. the current region).
    When a region is first entered, we set its parent to the current region and then update the current region to be the region just entered.
    When a region is exited, the current region is set to be the exited region’s parent.
    From Theorem 1, it follows that the pushing and popping follows a stack discipline.
    The topmost SESE region on this stack when DFS reaches the entry node of a SESE region R1 is the name of the smallest SESE region containing R1.
    Once the depth-first traversal is complete, the program structure tree has been built.
     */

    //let mut edge = Vec::new();
    // set to keep track of active cycle equivalency classes
    let mut seen_classes = HashSet::<usize>::new();
    let mut firsts = HashSet::<usize>::new();
    let mut lasts = HashSet::<usize>::new();

    for (i, entity) in dfs_order.iter().enumerate() {
        if let GraphEntity::Edge(edge) = entity {
            let edge = edge.borrow();
            if !seen_classes.contains(&edge.class) {
                seen_classes.insert(edge.class);
                firsts.insert(i);
            }
        }
    }

    seen_classes.clear();
    // in reverse order
    for (i, entity) in dfs_order.iter().rev().enumerate() {
        if let GraphEntity::Edge(edge) = entity {
            let edge = edge.borrow();
            if !seen_classes.contains(&edge.class) {
                seen_classes.insert(edge.class);
                lasts.insert(dfs_order.len()-1-i);
            }
        }
    }

    print!("traversal:");
    for (i, entity) in dfs_order.iter().enumerate() {
        match entity {
            GraphEntity::Node(node) => {
                print!(" n{}", node.borrow().id);
            }
            GraphEntity::Edge(edge_) => {
                let edge = edge_.borrow();
                print!(" e{}", edge.class);
                let is_sese_entry = !lasts.contains(&i);
                let is_sese_exit = !firsts.contains(&i);
                if is_sese_entry {
                    print!("+");
                }
                if is_sese_exit {
                    print!("-");
                }
            }
        }
    }
    println!();

    
    /*
    print!("edge_classes:");
    for c in edge_classes.iter() {
        print!(" {}", c);
    }
    println!();
    */

        /*
        // is the edge's class in the active classes set?
        let is_entry = if active_classes.contains(&edge.class) {
            false
        } else {
            active_classes.insert(edge.class);
            true
        };
        //let is_exit =
        println!("edge: {:?}", edge);

        // When a region is first entered, we set its parent to the current region and then update the current region to be the region just entered.
        if is_entry {
            // create a new region
            let region = Rc::new(RefCell::new(SeSeRegion::new(next_region_id(), edge.class)));
            // set the parent of the region to the current region
            region.borrow_mut().parent = current_region.clone();
            // push the region onto the stack
            stack.push(region.clone());
            // add the region to the program structure tree by adding it to the current region's children
            if let Some(ref mut current_region) = current_region {
                current_region.borrow_mut().children.push(region.clone());
            } else {
                // if there is no current region, then this is the root of the program structure tree
                program_structure_tree.root = Some(region.clone());
            }
            // set the current region to the new region
            current_region = Some(region.clone());
        } else {
            // When a region is exited, the current region is set to be the exited region’s parent.
            // pop the topmost region off the stack
            let popped_region = stack.pop().unwrap_or_else(|| panic!("stack underflow"));
            // set the current region to the popped region's parent
            current_region = popped_region.borrow().parent.clone();
            // remove from active classes
            active_classes.remove(&edge.class);
        }
    }
        */

    program_structure_tree.print_dot(&*graph, "structure_tree.dot");

    // Return the built program structure tree
    program_structure_tree
}

use petgraph::visit::depth_first_search;

fn dfs_tree(graph: &mut FlowGraph) -> Vec<NodeIndex> {
    // get the source node of the graph as the lowest node in the graph
    let source = NodeIndex::new(0);
    let mut dfs_order = Vec::new();
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

fn add_graph_node(graph: &mut FlowGraph, id: usize) -> NodeIndex {
    let node = Rc::new(RefCell::new(Node::new(id)));
    graph.add_node(node)
}

fn add_graph_edge(graph: &mut FlowGraph, from: NodeIndex, to: NodeIndex) -> Rc<RefCell<Edge>> {
    let edge = Rc::new(RefCell::new(Edge::new(from.index(), to.index())));
    graph.add_edge(from, to, edge.clone());
    edge
}

fn make_example_0() -> FlowGraph {

    let mut graph = FlowGraph::new_undirected();

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


fn make_example_a() -> FlowGraph {
    let mut graph = FlowGraph::new_undirected();
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

fn make_example_fig1() -> FlowGraph {
    let mut graph = FlowGraph::new_undirected();
    let n0 = add_graph_node(&mut graph, 0);
    let n1 = add_graph_node(&mut graph, 1);
    let n2 = add_graph_node(&mut graph, 2);
    let n3 = add_graph_node(&mut graph, 3);
    let n4 = add_graph_node(&mut graph, 4);
    let n5 = add_graph_node(&mut graph, 5);
    let n6 = add_graph_node(&mut graph, 6);
    let n7 = add_graph_node(&mut graph, 7);
    let n8 = add_graph_node(&mut graph, 8);
    let n9 = add_graph_node(&mut graph, 9);
    let n10 = add_graph_node(&mut graph, 10);
    let n11 = add_graph_node(&mut graph, 11);
    let n12 = add_graph_node(&mut graph, 12);
    let n13 = add_graph_node(&mut graph, 13);
    let n14 = add_graph_node(&mut graph, 14);
    let n15 = add_graph_node(&mut graph, 15);
    // 0 -> 1 and 2
    add_graph_edge(&mut graph, n0, n1);
    add_graph_edge(&mut graph, n0, n2);
    // 1 -> 3 and 13
    add_graph_edge(&mut graph, n1, n3);
    add_graph_edge(&mut graph, n1, n13);
    // 2 -> 4
    add_graph_edge(&mut graph, n2, n4);
    // 4 -> 6 and 8
    add_graph_edge(&mut graph, n4, n6);
    add_graph_edge(&mut graph, n4, n8);
    // 3 -> 5
    add_graph_edge(&mut graph, n3, n5);
    // 5 -> 7 and 9
    add_graph_edge(&mut graph, n5, n7);
    add_graph_edge(&mut graph, n5, n9);
    // 7 -> 11
    add_graph_edge(&mut graph, n7, n11);
    // 9 -> 11
    add_graph_edge(&mut graph, n9, n11);
    // 6 -> 10
    add_graph_edge(&mut graph, n6, n10);
    // 8 -> 10 and 12
    add_graph_edge(&mut graph, n8, n10);
    add_graph_edge(&mut graph, n8, n12);
    // 10 -> 12
    add_graph_edge(&mut graph, n10, n12);
    // 11 -> 13
    add_graph_edge(&mut graph, n11, n13);
    // 12 -> 14
    add_graph_edge(&mut graph, n12, n14);
    // 13 -> 15
    add_graph_edge(&mut graph, n13, n15);
    // 14 -> 15
    add_graph_edge(&mut graph, n14, n15);
    graph
}

fn make_example_diamond() -> FlowGraph {
    let mut graph = FlowGraph::new_undirected();
    let n0 = add_graph_node(&mut graph, 0);
    let n1 = add_graph_node(&mut graph, 1);
    let n2 = add_graph_node(&mut graph, 2);
    let n3 = add_graph_node(&mut graph, 3);
    let n4 = add_graph_node(&mut graph, 4);
    let n5 = add_graph_node(&mut graph, 5);
    // 0 -> 1
    add_graph_edge(&mut graph, n0, n1);
    // 1 -> 2 and 3
    add_graph_edge(&mut graph, n1, n2);
    add_graph_edge(&mut graph, n1, n3);
    // 2 -> 4
    add_graph_edge(&mut graph, n2, n4);
    // 3 -> 4
    add_graph_edge(&mut graph, n3, n4);
    // 4 -> 5
    add_graph_edge(&mut graph, n4, n5);
    // 5 -> 0
    add_graph_edge(&mut graph, n5, n0);
    graph
}

fn main() {

    let mut graph = make_example_a();
    //let mut graph = make_example_fig1();
    //let mut graph = make_example_diamond();
    let _tree = build_structure_tree(&mut graph);

}
