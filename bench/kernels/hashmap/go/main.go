package main

import (
	"fmt"
	"os"
	"strconv"
)

func main() {
	n, _ := strconv.ParseInt(os.Args[1], 10, 64)

	countsInt := make(map[int64]int64)
	countsStr := make(map[string]int64)

	var x uint64 = 42
	mod1 := n/4 + 1
	for i := int64(0); i < n; i++ {
		x = (x * 48271) % 2147483647
		key := int64(x % uint64(mod1))
		countsInt[key]++
	}

	n2 := n / 4
	mod2 := n/16 + 1
	for i := int64(0); i < n2; i++ {
		x = (x * 48271) % 2147483647
		num := int64(x % uint64(mod2))
		key := "k" + strconv.FormatInt(num, 10)
		countsStr[key]++
	}

	const modulo int64 = 1000000007
	var checksum int64 = 0
	for k, c := range countsInt {
		checksum = (checksum + (k%modulo)*(c%modulo)) % modulo
	}
	for k, c := range countsStr {
		num, _ := strconv.ParseInt(k[1:], 10, 64)
		checksum = (checksum + (num%modulo)*(c%modulo)) % modulo
	}

	fmt.Println(len(countsInt))
	fmt.Println(len(countsStr))
	fmt.Println(checksum)
}
