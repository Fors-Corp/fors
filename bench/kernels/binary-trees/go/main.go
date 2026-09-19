package main

import (
	"fmt"
	"os"
	"strconv"
)

type Node struct {
	left  *Node
	right *Node
}

func makeTree(depth int) *Node {
	n := &Node{}
	if depth > 0 {
		n.left = makeTree(depth - 1)
		n.right = makeTree(depth - 1)
	}
	return n
}

func checkTree(n *Node) int64 {
	if n.left == nil {
		return 1
	}
	return 1 + checkTree(n.left) + checkTree(n.right)
}

func main() {
	maxDepth, _ := strconv.Atoi(os.Args[1])
	const minDepth = 4
	if maxDepth < minDepth+2 {
		maxDepth = minDepth + 2
	}

	stretchDepth := maxDepth + 1
	stretchTree := makeTree(stretchDepth)
	fmt.Printf("stretch tree of depth %d\t check: %d\n", stretchDepth, checkTree(stretchTree))

	longLivedTree := makeTree(maxDepth)

	for depth := minDepth; depth <= maxDepth; depth += 2 {
		iterations := int64(1) << uint(maxDepth-depth+minDepth)
		var checkSum int64
		for i := int64(0); i < iterations; i++ {
			t := makeTree(depth)
			checkSum += checkTree(t)
		}
		fmt.Printf("%d\t trees of depth %d\t check: %d\n", iterations, depth, checkSum)
	}

	fmt.Printf("long lived tree of depth %d\t check: %d\n", maxDepth, checkTree(longLivedTree))
}
