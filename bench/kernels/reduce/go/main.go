package main

import (
	"fmt"
	"os"
	"strconv"
	"sync"
)

func lowbias32(x uint32) uint32 {
	x ^= x >> 16
	x = x * 0x7feb352d
	x ^= x >> 15
	x = x * 0x846ca68b
	x ^= x >> 16
	return x
}

func partialSum(start, end int64) uint64 {
	var sum uint64
	for i := start; i < end; i++ {
		x := uint32(i)
		x = lowbias32(x)
		x = lowbias32(x)
		x = lowbias32(x)
		x = lowbias32(x)
		sum += uint64(x % 1000)
	}
	return sum
}

func main() {
	n, _ := strconv.ParseInt(os.Args[1], 10, 64)
	numThreads, _ := strconv.ParseInt(os.Args[2], 10, 64)
	if numThreads < 1 {
		numThreads = 1
	}

	partials := make([]uint64, numThreads)
	var wg sync.WaitGroup
	for t := int64(0); t < numThreads; t++ {
		wg.Add(1)
		start := n * t / numThreads
		end := n * (t + 1) / numThreads
		go func(idx, s, e int64) {
			defer wg.Done()
			partials[idx] = partialSum(s, e)
		}(t, start, end)
	}
	wg.Wait()

	var total uint64
	for _, p := range partials {
		total += p
	}
	fmt.Println(total)
}
