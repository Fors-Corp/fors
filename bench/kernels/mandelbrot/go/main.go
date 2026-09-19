package main

import (
	"fmt"
	"os"
	"strconv"
	"sync"
)

func countRows(n int64, rowStart, rowEnd int64) int64 {
	var count int64
	for py := rowStart; py < rowEnd; py++ {
		ci0 := 2.0*float64(py)/float64(n) - 1.0
		for px := int64(0); px < n; px++ {
			cr := 2.0*float64(px)/float64(n) - 1.5
			var zr, zi float64 = 0.0, 0.0
			iter := 0
			for iter < 50 && zr*zr+zi*zi <= 4.0 {
				tr := float64(zr*zr) - float64(zi*zi) + cr
				ti := float64(2.0*zr)*zi + ci0
				zr = tr
				zi = ti
				iter++
			}
			if iter == 50 {
				count++
			}
		}
	}
	return count
}

func main() {
	n, _ := strconv.ParseInt(os.Args[1], 10, 64)
	numThreads, _ := strconv.ParseInt(os.Args[2], 10, 64)
	if numThreads < 1 {
		numThreads = 1
	}

	counts := make([]int64, numThreads)
	var wg sync.WaitGroup
	for t := int64(0); t < numThreads; t++ {
		wg.Add(1)
		rowStart := n * t / numThreads
		rowEnd := n * (t + 1) / numThreads
		go func(idx, rs, re int64) {
			defer wg.Done()
			counts[idx] = countRows(n, rs, re)
		}(t, rowStart, rowEnd)
	}
	wg.Wait()

	var total int64
	for _, c := range counts {
		total += c
	}
	fmt.Println(total)
}
