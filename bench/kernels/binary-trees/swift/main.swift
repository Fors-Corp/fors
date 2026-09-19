import Foundation

final class Node {
    var left: Node?
    var right: Node?
    init(left: Node?, right: Node?) {
        self.left = left
        self.right = right
    }
}

func makeTree(_ depth: Int) -> Node {
    if depth == 0 {
        return Node(left: nil, right: nil)
    }
    return Node(left: makeTree(depth - 1), right: makeTree(depth - 1))
}

func checkTree(_ n: Node) -> Int64 {
    guard let l = n.left, let r = n.right else {
        return 1
    }
    return 1 + checkTree(l) + checkTree(r)
}

let args = CommandLine.arguments
var maxDepth = Int(args[1]) ?? 4
let minDepth = 4
if maxDepth < minDepth + 2 {
    maxDepth = minDepth + 2
}

let stretchDepth = maxDepth + 1
let stretchTree = makeTree(stretchDepth)
print("stretch tree of depth \(stretchDepth)\t check: \(checkTree(stretchTree))")

let longLivedTree = makeTree(maxDepth)

var depth = minDepth
while depth <= maxDepth {
    let iterations: Int64 = Int64(1) << Int64(maxDepth - depth + minDepth)
    var checkSum: Int64 = 0
    var i: Int64 = 0
    while i < iterations {
        let t = makeTree(depth)
        checkSum += checkTree(t)
        i += 1
    }
    print("\(iterations)\t trees of depth \(depth)\t check: \(checkSum)")
    depth += 2
}

print("long lived tree of depth \(maxDepth)\t check: \(checkTree(longLivedTree))")
