import Foundation

let n = Int(CommandLine.arguments[1])!

var perm = [Int](repeating: 0, count: n)
var perm1 = [Int](repeating: 0, count: n)
var count = [Int](repeating: 0, count: n)
for i in 0..<n { perm1[i] = i }

var r = n
var checksum = 0
var maxflips = 0
var sign = 1

while true {
    while r != 1 {
        count[r - 1] = r
        r -= 1
    }
    for i in 0..<n { perm[i] = perm1[i] }

    var flips = 0
    while true {
        let k = perm[0]
        if k == 0 { break }
        let k2 = (k + 1) >> 1
        var i = 0
        while i < k2 {
            perm.swapAt(i, k - i)
            i += 1
        }
        flips += 1
    }

    checksum += sign * flips
    if flips > maxflips { maxflips = flips }

    var done = false
    while true {
        if r == n {
            done = true
            break
        }
        let perm0 = perm1[0]
        for i in 0..<r {
            perm1[i] = perm1[i + 1]
        }
        perm1[r] = perm0
        count[r] -= 1
        if count[r] > 0 { break }
        r += 1
    }
    if done { break }
    sign = -sign
}

print(checksum)
print("Pfannkuchen(\(n)) = \(maxflips)")
