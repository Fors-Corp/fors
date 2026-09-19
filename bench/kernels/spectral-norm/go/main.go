package main

import (
	"fmt"
	"math"
	"os"
	"strconv"
)

func evalA(i, j int64) float64 {
	ij := i + j
	return 1.0 / float64((ij*(ij+1))/2+i+1)
}

func evalATimesU(n int64, u, au []float64) {
	for i := int64(0); i < n; i++ {
		sum := 0.0
		for j := int64(0); j < n; j++ {
			sum += float64(evalA(i, j) * u[j])
		}
		au[i] = sum
	}
}

func evalAtTimesU(n int64, u, au []float64) {
	for i := int64(0); i < n; i++ {
		sum := 0.0
		for j := int64(0); j < n; j++ {
			sum += float64(evalA(j, i) * u[j])
		}
		au[i] = sum
	}
}

func evalAtATimesU(n int64, u, atAu, tmp []float64) {
	evalATimesU(n, u, tmp)
	evalAtTimesU(n, tmp, atAu)
}

func main() {
	n, _ := strconv.ParseInt(os.Args[1], 10, 64)

	u := make([]float64, n)
	v := make([]float64, n)
	tmp := make([]float64, n)

	for i := int64(0); i < n; i++ {
		u[i] = 1.0
	}

	for i := 0; i < 10; i++ {
		evalAtATimesU(n, u, v, tmp)
		evalAtATimesU(n, v, u, tmp)
	}

	vBv := 0.0
	vv := 0.0
	for i := int64(0); i < n; i++ {
		vBv += float64(u[i] * v[i])
		vv += float64(v[i] * v[i])
	}

	fmt.Printf("%.9f\n", math.Sqrt(vBv/vv))
}
