import Foundation

let args = CommandLine.arguments
let n: Int64 = Int64(args[1])!

var countsInt: [Int64: Int64] = [:]
var countsStr: [String: Int64] = [:]

var x: UInt64 = 42
let mod1: Int64 = n / 4 + 1
var i: Int64 = 0
while i < n {
    x = (x * 48271) % 2147483647
    let key = Int64(x % UInt64(mod1))
    countsInt[key, default: 0] += 1
    i += 1
}

let n2 = n / 4
let mod2: Int64 = n / 16 + 1
i = 0
while i < n2 {
    x = (x * 48271) % 2147483647
    let num = Int64(x % UInt64(mod2))
    let key = "k" + String(num)
    countsStr[key, default: 0] += 1
    i += 1
}

let modulo: Int64 = 1_000_000_007
var checksum: Int64 = 0
for (k, c) in countsInt {
    checksum = (checksum + (k % modulo) * (c % modulo)) % modulo
}
for (k, c) in countsStr {
    let numStr = String(k.dropFirst())
    let num = Int64(numStr)!
    checksum = (checksum + (num % modulo) * (c % modulo)) % modulo
}

print(countsInt.count)
print(countsStr.count)
print(checksum)
