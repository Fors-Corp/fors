package main

import (
	"fmt"
	"os"
	"strconv"
	"sync"
)

func main() {
	n, _ := strconv.Atoi(os.Args[1])
	r, _ := strconv.Atoi(os.Args[2])
	threads, _ := strconv.Atoi(os.Args[3])
	if threads < 1 {
		threads = 1
	}
	if threads > n {
		threads = n
	}

	a := make([]float64, n)
	b := make([]float64, n)
	c := make([]float64, n)
	s := 3.0

	base := n / threads
	rem := n % threads
	bounds := make([]int, threads+1)
	idx := 0
	for t := 0; t < threads; t++ {
		count := base
		if t < rem {
			count++
		}
		idx += count
		bounds[t+1] = idx
	}

	var wg sync.WaitGroup
	for t := 0; t < threads; t++ {
		start := bounds[t]
		end := bounds[t+1]
		wg.Add(1)
		go func(start, end int) {
			defer wg.Done()
			// Block slices let the compiler prove the index range once per block,
			// not once per element, for each of a/b/c.
			aBlock := a[start:end]
			bBlock := b[start:end]
			cBlock := c[start:end]
			for i := range bBlock {
				bBlock[i] = float64((start+i)%7 + 1)
				cBlock[i] = float64((start+i)%5 + 1)
				aBlock[i] = 0.0
			}
			for rep := 0; rep < r; rep++ {
				for i := range aBlock {
					aBlock[i] = bBlock[i] + s*cBlock[i]
				}
			}
		}(start, end)
	}
	wg.Wait()

	sum := 0.0
	for i := 0; i < n; i++ {
		sum += a[i]
	}
	fmt.Printf("%.0f\n", sum)
}
