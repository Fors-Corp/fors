use std::env;

struct Node {
    left: Option<Box<Node>>,
    right: Option<Box<Node>>,
}

fn make_tree(depth: i32) -> Box<Node> {
    if depth == 0 {
        Box::new(Node { left: None, right: None })
    } else {
        Box::new(Node {
            left: Some(make_tree(depth - 1)),
            right: Some(make_tree(depth - 1)),
        })
    }
}

fn check_tree(n: &Node) -> i64 {
    match (&n.left, &n.right) {
        (Some(l), Some(r)) => 1 + check_tree(l) + check_tree(r),
        _ => 1,
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let mut max_depth: i32 = args[1].parse().expect("integer depth");
    let min_depth: i32 = 4;
    if max_depth < min_depth + 2 {
        max_depth = min_depth + 2;
    }

    let stretch_depth = max_depth + 1;
    let stretch_tree = make_tree(stretch_depth);
    println!("stretch tree of depth {}\t check: {}", stretch_depth, check_tree(&stretch_tree));
    drop(stretch_tree);

    let long_lived_tree = make_tree(max_depth);

    let mut depth = min_depth;
    while depth <= max_depth {
        let iterations: i64 = 1i64 << (max_depth - depth + min_depth);
        let mut check_sum: i64 = 0;
        for _ in 0..iterations {
            let t = make_tree(depth);
            check_sum += check_tree(&t);
        }
        println!("{}\t trees of depth {}\t check: {}", iterations, depth, check_sum);
        depth += 2;
    }

    println!("long lived tree of depth {}\t check: {}", max_depth, check_tree(&long_lived_tree));
}
