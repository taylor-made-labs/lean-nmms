/-
  LeanNmms.Wire

  What the command-line checker needs to bind a response to its request:
  SHA-256 and the canonical JSON encoding that Python callers hash.

  * `canonical` writes JSON exactly as Python's
    `json.dumps(v, sort_keys=True, separators=(",", ":"), ensure_ascii=False)`
    does for the values callers send: object keys in code-point order, no
    whitespace, non-ASCII characters as themselves, Python's escapes for `"`,
    `\`, and control characters. Numbers must be integers (a fraction or an
    exponent is refused, since Python would print a float differently).
  * `sha256Hex` is FIPS 180-4 SHA-256 over the UTF-8 bytes, as lowercase hex.

  Neither is part of a proof: they are the unverified shell's transport
  check (README, "What is trusted"). A wrong hash can only make the checker
  refuse a request, never accept a different one: the decision is computed
  from the request's own fields, and the hash only ties the answer to them.
-/
import Lean.Data.Json

namespace NMMS.Wire

open Lean

/-- Python's `json.dumps` string escape with `ensure_ascii=False`. -/
def escapeChar (c : Char) : String :=
  if c == '"' then "\\\""
  else if c == '\\' then "\\\\"
  else if c == '\n' then "\\n"
  else if c == '\r' then "\\r"
  else if c == '\t' then "\\t"
  else if c.toNat == 8 then "\\b"
  else if c.toNat == 12 then "\\f"
  else if c.toNat < 0x20 then
    let hex := "0123456789abcdef".toList
    "\\u00" ++ String.singleton (hex.getD (c.toNat / 16) '0') ++
      String.singleton (hex.getD (c.toNat % 16) '0')
  else String.singleton c

def quote (s : String) : String :=
  "\"" ++ s.foldl (fun acc c => acc ++ escapeChar c) "" ++ "\""

/-- The canonical encoding (see the module header). -/
partial def canonical : Json → Except String String
  | .null => pure "null"
  | .bool true => pure "true"
  | .bool false => pure "false"
  | .num n =>
    if n.exponent == 0 then pure (toString n.mantissa)
    else throw "only integer numbers can be hashed canonically"
  | .str s => pure (quote s)
  | .arr xs => do
    let parts ← xs.toList.mapM canonical
    pure ("[" ++ ",".intercalate parts ++ "]")
  | .obj kvs => do
    let parts ← kvs.toList.mapM fun (k, v) => do
      pure (quote k ++ ":" ++ (← canonical v))
    pure ("{" ++ ",".intercalate parts ++ "}")

/-- SHA-256 round constants. -/
def roundK : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

def rotr (x : UInt32) (n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

/-- SHA-256 of a byte string. -/
def sha256 (msg : ByteArray) : Array UInt32 := Id.run do
  let bitLen : UInt64 := msg.size.toUInt64 * 8
  let mut m := msg.push 0x80
  while m.size % 64 != 56 do
    m := m.push 0
  for i in [0:8] do
    m := m.push (bitLen >>> (8 * (7 - i)).toUInt64).toUInt8
  let mut h : Array UInt32 := #[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
    0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]
  for chunk in [0:m.size / 64] do
    let mut w : Array UInt32 := Array.replicate 64 0
    for t in [0:16] do
      let b := chunk * 64 + 4 * t
      w := w.set! t ((m.get! b).toUInt32 <<< 24 ||| (m.get! (b + 1)).toUInt32 <<< 16 |||
        (m.get! (b + 2)).toUInt32 <<< 8 ||| (m.get! (b + 3)).toUInt32)
    for t in [16:64] do
      let x := w[t - 15]!
      let y := w[t - 2]!
      let s0 := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)
      let s1 := rotr y 17 ^^^ rotr y 19 ^^^ (y >>> 10)
      w := w.set! t (w[t - 16]! + s0 + w[t - 7]! + s1)
    let mut a := h[0]!
    let mut b := h[1]!
    let mut c := h[2]!
    let mut d := h[3]!
    let mut e := h[4]!
    let mut f := h[5]!
    let mut g := h[6]!
    let mut hh := h[7]!
    for t in [0:64] do
      let S1 := rotr e 6 ^^^ rotr e 11 ^^^ rotr e 25
      let ch := (e &&& f) ^^^ ((~~~e) &&& g)
      let t1 := hh + S1 + ch + roundK[t]! + w[t]!
      let S0 := rotr a 2 ^^^ rotr a 13 ^^^ rotr a 22
      let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
      let t2 := S0 + maj
      hh := g
      g := f
      f := e
      e := d + t1
      d := c
      c := b
      b := a
      a := t1 + t2
    h := #[h[0]! + a, h[1]! + b, h[2]! + c, h[3]! + d, h[4]! + e, h[5]! + f,
      h[6]! + g, h[7]! + hh]
  return h

def hexWord (x : UInt32) : String := Id.run do
  let digits := "0123456789abcdef".toList
  let mut out := ""
  for i in [0:8] do
    let nib := ((x >>> (4 * (7 - i)).toUInt32) &&& 0xf).toNat
    out := out.push (digits.getD nib '0')
  return out

/-- Lowercase hex SHA-256 of a string's UTF-8 bytes. -/
def sha256Hex (s : String) : String :=
  (sha256 s.toUTF8).foldl (fun acc w => acc ++ hexWord w) ""

/-- The binding hash of a JSON value: SHA-256 of its canonical encoding. -/
def digest (j : Json) : Except String String := do
  return sha256Hex (← canonical j)

end NMMS.Wire
