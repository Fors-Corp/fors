import Dispatch
import Foundation

let args = CommandLine.arguments
let n = Int64(args[1])!
var numThreads = Int64(args[2])!
if numThreads < 1 { numThreads = 1 }

func lowbias32(_ x0: UInt32) -> UInt32 {
    var x = x0
    x ^= x >> 16
    x = x &* 0x7feb352d
    x ^= x >> 15
    x = x &* 0x846ca68b
    x ^= x >> 16
    return x
}

func partialSum(start: Int64, end: Int64) -> UInt64 {
    var sum: UInt64 = 0
    var i = start
    while i < end {
        var x = UInt32(truncatingIfNeeded: i)
        x = lowbias32(x)
        x = lowbias32(x)
        x = lowbias32(x)
        x = lowbias32(x)
        sum += UInt64(x % 1000)
        i += 1
    }
    return sum
}

var partials = [UInt64](repeating: 0, count: Int(numThreads))
partials.withUnsafeMutableBufferPointer { buf in
    DispatchQueue.concurrentPerform(iterations: Int(numThreads)) { t in
        let tl = Int64(t)
        let start = n * tl / numThreads
        let end = n * (tl + 1) / numThreads
        buf[t] = partialSum(start: start, end: end)
    }
}

let total = partials.reduce(0, +)
print(total)
