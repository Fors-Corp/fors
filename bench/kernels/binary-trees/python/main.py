import sys


class Node:
    __slots__ = ("left", "right")

    def __init__(self, left, right):
        self.left = left
        self.right = right


def make_tree(depth):
    if depth == 0:
        return Node(None, None)
    return Node(make_tree(depth - 1), make_tree(depth - 1))


def check_tree(n):
    if n.left is None:
        return 1
    return 1 + check_tree(n.left) + check_tree(n.right)


def main():
    max_depth = int(sys.argv[1])
    min_depth = 4
    if max_depth < min_depth + 2:
        max_depth = min_depth + 2

    stretch_depth = max_depth + 1
    stretch_tree = make_tree(stretch_depth)
    print(f"stretch tree of depth {stretch_depth}\t check: {check_tree(stretch_tree)}")
    del stretch_tree

    long_lived_tree = make_tree(max_depth)

    depth = min_depth
    while depth <= max_depth:
        iterations = 1 << (max_depth - depth + min_depth)
        check_sum = 0
        for _ in range(iterations):
            t = make_tree(depth)
            check_sum += check_tree(t)
        print(f"{iterations}\t trees of depth {depth}\t check: {check_sum}")
        depth += 2

    print(f"long lived tree of depth {max_depth}\t check: {check_tree(long_lived_tree)}")


if __name__ == "__main__":
    main()
