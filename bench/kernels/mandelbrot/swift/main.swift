import Dispatch
import Foundation

let args = CommandLine.arguments
let n = Int64(args[1])!
var numThreads = Int64(args[2])!
if numThreads < 1 { numThreads = 1 }

func countRows(n: Int64, rowStart: Int64, rowEnd: Int64) -> Int64 {
    var count: Int64 = 0
    var py = rowStart
    while py < rowEnd {
        let ci0 = 2.0 * Double(py) / Double(n) - 1.0
        var px: Int64 = 0
        while px < n {
            let cr = 2.0 * Double(px) / Double(n) - 1.5
            var zr = 0.0
            var zi = 0.0
            var iter = 0
            while iter < 50 && zr * zr + zi * zi <= 4.0 {
                let tr = zr * zr - zi * zi + cr
                let ti = 2.0 * zr * zi + ci0
                zr = tr
                zi = ti
                iter += 1
            }
            if iter == 50 {
                count += 1
            }
            px += 1
        }
        py += 1
    }
    return count
}

var counts = [Int64](repeating: 0, count: Int(numThreads))
counts.withUnsafeMutableBufferPointer { buf in
    DispatchQueue.concurrentPerform(iterations: Int(numThreads)) { t in
        let tl = Int64(t)
        let rowStart = n * tl / numThreads
        let rowEnd = n * (tl + 1) / numThreads
        buf[t] = countRows(n: n, rowStart: rowStart, rowEnd: rowEnd)
    }
}

let total = counts.reduce(0, +)
print(total)
