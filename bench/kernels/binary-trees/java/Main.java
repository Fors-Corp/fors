public class Main {
    static final class Node {
        Node left;
        Node right;
        Node(Node left, Node right) {
            this.left = left;
            this.right = right;
        }
    }

    static Node makeTree(int depth) {
        if (depth == 0) {
            return new Node(null, null);
        }
        return new Node(makeTree(depth - 1), makeTree(depth - 1));
    }

    static long checkTree(Node n) {
        if (n.left == null) {
            return 1;
        }
        return 1 + checkTree(n.left) + checkTree(n.right);
    }

    public static void main(String[] args) {
        int maxDepth = Integer.parseInt(args[0]);
        final int minDepth = 4;
        if (maxDepth < minDepth + 2) {
            maxDepth = minDepth + 2;
        }

        int stretchDepth = maxDepth + 1;
        Node stretchTree = makeTree(stretchDepth);
        System.out.println("stretch tree of depth " + stretchDepth + "\t check: " + checkTree(stretchTree));

        Node longLivedTree = makeTree(maxDepth);

        for (int depth = minDepth; depth <= maxDepth; depth += 2) {
            long iterations = 1L << (maxDepth - depth + minDepth);
            long checkSum = 0;
            for (long i = 0; i < iterations; i++) {
                Node t = makeTree(depth);
                checkSum += checkTree(t);
            }
            System.out.println(iterations + "\t trees of depth " + depth + "\t check: " + checkSum);
        }

        System.out.println("long lived tree of depth " + maxDepth + "\t check: " + checkTree(longLivedTree));
    }
}
