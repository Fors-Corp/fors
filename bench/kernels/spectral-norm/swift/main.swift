import Foundation

func evalA(_ i: Int, _ j: Int) -> Double {
    let ij = i + j
    return 1.0 / Double((ij * (ij + 1)) / 2 + i + 1)
}

func evalATimesU(_ n: Int, _ u: [Double], _ au: inout [Double]) {
    for i in 0..<n {
        var sum = 0.0
        for j in 0..<n {
            sum += evalA(i, j) * u[j]
        }
        au[i] = sum
    }
}

func evalAtTimesU(_ n: Int, _ u: [Double], _ au: inout [Double]) {
    for i in 0..<n {
        var sum = 0.0
        for j in 0..<n {
            sum += evalA(j, i) * u[j]
        }
        au[i] = sum
    }
}

func evalAtATimesU(_ n: Int, _ u: [Double], _ atAu: inout [Double], _ tmp: inout [Double]) {
    evalATimesU(n, u, &tmp)
    evalAtTimesU(n, tmp, &atAu)
}

let args = CommandLine.arguments
let n = Int(args[1])!

var u = [Double](repeating: 1.0, count: n)
var v = [Double](repeating: 0.0, count: n)
var tmp = [Double](repeating: 0.0, count: n)

for _ in 0..<10 {
    evalAtATimesU(n, u, &v, &tmp)
    evalAtATimesU(n, v, &u, &tmp)
}

var vBv = 0.0
var vv = 0.0
for i in 0..<n {
    vBv += u[i] * v[i]
    vv += v[i] * v[i]
}

print(String(format: "%.9f", (vBv / vv).squareRoot()))
