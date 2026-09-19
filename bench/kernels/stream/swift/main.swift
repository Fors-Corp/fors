import Foundation
#if canImport(Dispatch)
import Dispatch
#endif

let args = CommandLine.arguments
let n = Int(args[1])!
let r = Int(args[2])!
var threads = Int(args[3])!
if threads < 1 { threads = 1 }
if threads > n { threads = n }

var a = [Double](repeating: 0.0, count: n)
var b = [Double](repeating: 0.0, count: n)
var c = [Double](repeating: 0.0, count: n)
let s = 3.0

let base = n / threads
let rem = n % threads
var bounds = [Int](repeating: 0, count: threads + 1)
var idx = 0
bounds[0] = 0
for t in 0..<threads {
    var count = base
    if t < rem { count += 1 }
    idx += count
    bounds[t + 1] = idx
}

a.withUnsafeMutableBufferPointer { aBuf in
    b.withUnsafeMutableBufferPointer { bBuf in
        c.withUnsafeMutableBufferPointer { cBuf in
            DispatchQueue.concurrentPerform(iterations: threads) { t in
                let start = bounds[t]
                let end = bounds[t + 1]
                let len = end - start
                // Rebased block views: the overflow-checked index arithmetic (start + i)
                // leaves the inner loop, once per block instead of once per element.
                let aBlock = UnsafeMutableBufferPointer(rebasing: aBuf[start..<end])
                let bBlock = UnsafeMutableBufferPointer(rebasing: bBuf[start..<end])
                let cBlock = UnsafeMutableBufferPointer(rebasing: cBuf[start..<end])
                for i in 0..<len {
                    bBlock[i] = Double((start + i) % 7 + 1)
                    cBlock[i] = Double((start + i) % 5 + 1)
                    aBlock[i] = 0.0
                }
                for _ in 0..<r {
                    for i in 0..<len {
                        aBlock[i] = bBlock[i] + s * cBlock[i]
                    }
                }
            }
        }
    }
}

var sum = 0.0
for v in a { sum += v }
print(String(format: "%.0f", sum))
