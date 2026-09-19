package main

import (
	"fmt"
	"os"
	"strconv"
)

func main() {
	n, _ := strconv.Atoi(os.Args[1])

	perm := make([]int, n)
	perm1 := make([]int, n)
	count := make([]int, n)
	for i := 0; i < n; i++ {
		perm1[i] = i
	}

	r := n
	checksum := 0
	maxflips := 0
	sign := 1

	for {
		for r != 1 {
			count[r-1] = r
			r--
		}
		copy(perm, perm1)

		flips := 0
		for {
			k := perm[0]
			if k == 0 {
				break
			}
			k2 := (k + 1) >> 1
			for i := 0; i < k2; i++ {
				perm[i], perm[k-i] = perm[k-i], perm[i]
			}
			flips++
		}

		checksum += sign * flips
		if flips > maxflips {
			maxflips = flips
		}

		done := false
		for {
			if r == n {
				done = true
				break
			}
			perm0 := perm1[0]
			for i := 0; i < r; i++ {
				perm1[i] = perm1[i+1]
			}
			perm1[r] = perm0
			count[r]--
			if count[r] > 0 {
				break
			}
			r++
		}
		if done {
			break
		}
		sign = -sign
	}

	fmt.Println(checksum)
	fmt.Printf("Pfannkuchen(%d) = %d\n", n, maxflips)
}
