class Node {
    constructor(left, right) {
        this.left = left;
        this.right = right;
    }
}

function makeTree(depth) {
    if (depth === 0) {
        return new Node(null, null);
    }
    return new Node(makeTree(depth - 1), makeTree(depth - 1));
}

function checkTree(n) {
    if (n.left === null) {
        return 1;
    }
    return 1 + checkTree(n.left) + checkTree(n.right);
}

function main() {
    const args = process.argv.slice(2);
    let maxDepth = parseInt(args[0], 10);
    const minDepth = 4;
    if (maxDepth < minDepth + 2) {
        maxDepth = minDepth + 2;
    }

    const stretchDepth = maxDepth + 1;
    const stretchTree = makeTree(stretchDepth);
    console.log(`stretch tree of depth ${stretchDepth}\t check: ${checkTree(stretchTree)}`);

    const longLivedTree = makeTree(maxDepth);

    for (let depth = minDepth; depth <= maxDepth; depth += 2) {
        const iterations = 2 ** (maxDepth - depth + minDepth);
        let checkSum = 0;
        for (let i = 0; i < iterations; i++) {
            const t = makeTree(depth);
            checkSum += checkTree(t);
        }
        console.log(`${iterations}\t trees of depth ${depth}\t check: ${checkSum}`);
    }

    console.log(`long lived tree of depth ${maxDepth}\t check: ${checkTree(longLivedTree)}`);
}

main();
