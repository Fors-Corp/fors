package main

import (
	"fmt"
	"os"
	"strconv"
	"sync"
)

func main() {
	n, _ := strconv.Atoi(os.Args[1])
	threads, _ := strconv.Atoi(os.Args[2])
	if threads < 1 {
		threads = 1
	}
	if threads > n {
		threads = n
	}

	a := make([]float64, n*n)
	b := make([]float64, n*n)
	c := make([]float64, n*n)

	for i := 0; i < n; i++ {
		for j := 0; j < n; j++ {
			a[i*n+j] = float64(((i*j)%7)+1)
			b[i*n+j] = float64(((i+j)%5)+1)
		}
	}

	base := n / threads
	rem := n % threads
	bounds := make([]int, threads+1)
	row := 0
	bounds[0] = 0
	for t := 0; t < threads; t++ {
		count := base
		if t < rem {
			count++
		}
		row += count
		bounds[t+1] = row
	}

	var wg sync.WaitGroup
	for t := 0; t < threads; t++ {
		rowStart := bounds[t]
		rowEnd := bounds[t+1]
		wg.Add(1)
		go func(rowStart, rowEnd int) {
			defer wg.Done()
			for i := rowStart; i < rowEnd; i++ {
				// Row slices let the compiler prove the indexes in range once per row.
				cRow := c[i*n : (i+1)*n]
				for j := range cRow {
					cRow[j] = 0.0
				}
				for k := 0; k < n; k++ {
					av := a[i*n+k]
					bRow := b[k*n : (k+1)*n]
					for j := range cRow {
						cRow[j] += float64(av * bRow[j])
					}
				}
			}
		}(rowStart, rowEnd)
	}
	wg.Wait()

	sum := 0.0
	trace := 0.0
	for i := 0; i < n; i++ {
		for j := 0; j < n; j++ {
			sum += c[i*n+j]
		}
		trace += c[i*n+i]
	}

	fmt.Printf("%.0f\n", sum)
	fmt.Printf("%.0f\n", trace)
}
