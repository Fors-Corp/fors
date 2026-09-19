import Foundation
#if canImport(Dispatch)
import Dispatch
#endif

let args = CommandLine.arguments
let n = Int(args[1])!
var threads = Int(args[2])!
if threads < 1 { threads = 1 }
if threads > n { threads = n }

var a = [Double](repeating: 0.0, count: n * n)
var b = [Double](repeating: 0.0, count: n * n)
var c = [Double](repeating: 0.0, count: n * n)

for i in 0..<n {
    for j in 0..<n {
        a[i * n + j] = Double(((i * j) % 7) + 1)
        b[i * n + j] = Double(((i + j) % 5) + 1)
    }
}

let base = n / threads
let rem = n % threads
var bounds = [Int](repeating: 0, count: threads + 1)
var row = 0
bounds[0] = 0
for t in 0..<threads {
    var count = base
    if t < rem { count += 1 }
    row += count
    bounds[t + 1] = row
}

a.withUnsafeBufferPointer { aBuf in
    b.withUnsafeBufferPointer { bBuf in
        c.withUnsafeMutableBufferPointer { cBuf in
            DispatchQueue.concurrentPerform(iterations: threads) { t in
                let rowStart = bounds[t]
                let rowEnd = bounds[t + 1]
                for i in rowStart..<rowEnd {
                    // Rebased row views: the overflow-checked index arithmetic (i * n + j) leaves
                    // the inner loop, which is what was blocking vectorization.
                    let cRow = UnsafeMutableBufferPointer(rebasing: cBuf[i * n ..< (i + 1) * n])
                    for j in 0..<n {
                        cRow[j] = 0.0
                    }
                    for k in 0..<n {
                        let av = aBuf[i * n + k]
                        let bRow = UnsafeBufferPointer(rebasing: bBuf[k * n ..< (k + 1) * n])
                        for j in 0..<n {
                            cRow[j] += av * bRow[j]
                        }
                    }
                }
            }
        }
    }
}

var sum = 0.0
var trace = 0.0
for i in 0..<n {
    for j in 0..<n {
        sum += c[i * n + j]
    }
    trace += c[i * n + i]
}

print(String(format: "%.0f", sum))
print(String(format: "%.0f", trace))
