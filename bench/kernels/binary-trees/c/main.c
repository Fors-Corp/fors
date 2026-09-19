#include <stdio.h>
#include <stdlib.h>

typedef struct Node {
    struct Node *left;
    struct Node *right;
} Node;

static Node *make_tree(int depth) {
    Node *n = (Node *)malloc(sizeof(Node));
    if (depth == 0) {
        n->left = NULL;
        n->right = NULL;
    } else {
        n->left = make_tree(depth - 1);
        n->right = make_tree(depth - 1);
    }
    return n;
}

static long check_tree(Node *n) {
    if (n->left == NULL) {
        return 1;
    }
    return 1 + check_tree(n->left) + check_tree(n->right);
}

static void free_tree(Node *n) {
    if (n->left != NULL) {
        free_tree(n->left);
        free_tree(n->right);
    }
    free(n);
}

int main(int argc, char **argv) {
    if (argc < 2) {
        fprintf(stderr, "usage: %s <max-depth>\n", argv[0]);
        return 1;
    }
    int max_depth = atoi(argv[1]);
    const int min_depth = 4;
    if (max_depth < min_depth + 2) {
        max_depth = min_depth + 2;
    }

    int stretch_depth = max_depth + 1;
    Node *stretch_tree = make_tree(stretch_depth);
    printf("stretch tree of depth %d\t check: %ld\n", stretch_depth, check_tree(stretch_tree));
    free_tree(stretch_tree);

    Node *long_lived_tree = make_tree(max_depth);

    for (int depth = min_depth; depth <= max_depth; depth += 2) {
        long iterations = 1L << (max_depth - depth + min_depth);
        long check_sum = 0;
        for (long i = 0; i < iterations; i++) {
            Node *t = make_tree(depth);
            check_sum += check_tree(t);
            free_tree(t);
        }
        printf("%ld\t trees of depth %d\t check: %ld\n", iterations, depth, check_sum);
    }

    printf("long lived tree of depth %d\t check: %ld\n", max_depth, check_tree(long_lived_tree));
    free_tree(long_lived_tree);

    return 0;
}
