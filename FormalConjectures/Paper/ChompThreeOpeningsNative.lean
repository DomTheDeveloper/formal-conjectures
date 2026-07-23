import FormalConjecturesUtil

namespace ChompThreeOpeningsNative

/-- Mutable state for the exact retrograde search. -/
structure Engine where
  k : Nat
  n : Nat
  cols : Nat
  choose : Array Nat
  offsets : Array Nat
  words : Array Nat
  bits : Array UInt64
  x : Array Nat
  counts : Array Nat

private def buildChoose (k n : Nat) : Array Nat := Id.run do
  let rows := n + k + 3
  let cols := k + 3
  let mut c := Array.replicate (rows * cols) 0
  let mut a := 0
  while a < rows do
    c := c.set! (a * cols) 1
    let mut b := 1
    while b ≤ min a (k + 1) do
      let v := c[((a - 1) * cols) + (b - 1)]! + c[((a - 1) * cols) + b]!
      c := c.set! (a * cols + b) v
      b := b + 1
    a := a + 1
  return c

private def chooseAt (e : Engine) (a b : Nat) : Nat :=
  e.choose[a * e.cols + b]!

private def buildLayout (k n cols : Nat) (choose : Array Nat) : Array Nat × Array Nat × Nat :=
  Id.run do
    let mut offsets := Array.replicate (k - 1) 0
    let mut words := Array.replicate (k - 1) 0
    let mut total := 0
    let mut i := 0
    while i < k - 1 do
      let suffixLen := k - i - 1
      let nbits := choose[(n + suffixLen) * cols + suffixLen]!
      let count := (nbits + 63) / 64 + 1
      offsets := offsets.set! i total
      words := words.set! i count
      total := total + count
      i := i + 1
    return (offsets, words, total)

private def mkEngine (k n : Nat) : Engine :=
  let cols := k + 3
  let choose := buildChoose k n
  let (offsets, words, totalWords) := buildLayout k n cols choose
  { k, n, cols, choose, offsets, words,
    bits := Array.replicate totalWords 0,
    x := Array.replicate k 0,
    counts := Array.replicate (n + 1) 0 }

private def getBit (e : Engine) (shadow rank : Nat) : Bool :=
  let wi := e.offsets[shadow]! + rank / 64
  let word := e.bits[wi]!
  let mask : UInt64 := 1 <<< (rank % 64)
  (word &&& mask) != 0

private def setBit (e : Engine) (shadow rank : Nat) : Engine :=
  let wi := e.offsets[shadow]! + rank / 64
  let mask : UInt64 := 1 <<< (rank % 64)
  { e with bits := e.bits.set! wi (e.bits[wi]! ||| mask) }

private partial def clearWords (i stop : Nat) (bits : Array UInt64) : Array UInt64 :=
  if i < stop then clearWords (i + 1) stop (bits.set! i 0) else bits

private def clearShadow (shadow : Nat) (e : Engine) : Engine :=
  let first := e.offsets[shadow]!
  let stop := first + e.words[shadow]!
  { e with bits := clearWords first stop e.bits }

private partial def rankSuffixLoop (pos acc : Nat) (e : Engine) : Nat :=
  if pos < e.k then
    let j := e.k - pos
    rankSuffixLoop (pos + 1) (acc + chooseAt e (e.x[pos]! + j - 1) j) e
  else acc

private def rankSuffix (start : Nat) (e : Engine) : Nat := rankSuffixLoop start 0 e

mutual
  private partial def enumerateShadow
      (moveRow pos equalEnd upper lower : Nat) (e : Engine) : Engine :=
    if equalEnd < pos then
      setBit e moveRow (rankSuffix (moveRow + 1) e)
    else
      let old := e.x[pos]!
      let e := enumerateValues moveRow pos equalEnd lower upper lower e
      { e with x := e.x.set! pos old }

  private partial def enumerateValues
      (moveRow pos equalEnd value upper lower : Nat) (e : Engine) : Engine :=
    if value ≤ upper then
      let e := { e with x := e.x.set! pos value }
      let e := enumerateShadow moveRow (pos + 1) equalEnd value lower e
      enumerateValues moveRow pos equalEnd (value + 1) upper lower e
    else e
end

private partial def equalBlockEnd (m t : Nat) (e : Engine) : Nat :=
  if m + 1 < e.k then
    if e.x[m + 1]! = t then equalBlockEnd (m + 1) t e else m
  else m

private partial def addShadowRows (i : Nat) (e : Engine) : Engine :=
  if i < e.k - 1 then
    let t := e.x[i]!
    let m := equalBlockEnd i t e
    let upper := if i = 0 then e.n else e.x[i - 1]!
    let e := if t < upper then enumerateShadow i (i + 1) m upper t e else e
    addShadowRows (i + 1) e
  else e

private def addShadowOfCurrentP (e : Engine) : Engine := addShadowRows 0 e

private partial def allEqBefore (i r width : Nat) (e : Engine) : Bool :=
  if i < r then decide (e.x[i]! = width) && allEqBefore (i + 1) r width e else true

private partial def allEqAfter (i value : Nat) (e : Engine) : Bool :=
  if i < e.k then decide (e.x[i]! = value) && allEqAfter (i + 1) value e else true

private partial def hasTwoLevelAt (r width : Nat) (e : Engine) : Bool :=
  if r < e.k then
    let lower := e.x[r]!
    if decide (lower < width) && allEqBefore 0 r width e && allEqAfter r lower e then
      true
    else hasTwoLevelAt (r + 1) width e
  else false

private def recordIfRectangleChild (e : Engine) : Engine :=
  let width := e.x[0]!
  if hasTwoLevelAt 1 width e then
    { e with counts := e.counts.set! width (e.counts[width]! + 1) }
  else e

private partial def hasPOptionAt (i v : Nat) (base : Array Nat) (e : Engine) : Bool :=
  if i < e.k - 1 then getBit e i (base[i]! + v) || hasPOptionAt (i + 1) v base e else false

private partial def findChosen (v bottom : Nat) (base : Array Nat) (e : Engine) : Nat :=
  if v ≤ bottom then
    if hasPOptionAt 0 v base e then findChosen (v + 1) bottom base e else v
  else bottom + 1

private partial def buildBaseDown
    (pos acc : Nat) (base : Array Nat) (e : Engine) : Array Nat :=
  if pos = 0 then base
  else
    let j := e.k - pos
    let acc := acc + chooseAt e (e.x[pos]! + j - 1) j
    buildBaseDown (pos - 1) acc (base.set! (pos - 1) acc) e

private def processPrefix (target : Nat) (e : Engine) : Bool × Engine :=
  let bottom := e.x[e.k - 2]!
  let base := buildBaseDown (e.k - 2) 0 (Array.replicate (e.k - 1) 0) e
  let chosen := findChosen 0 bottom base e
  if bottom < chosen then (false, e)
  else
    let e := { e with x := e.x.set! (e.k - 1) chosen }
    let e := recordIfRectangleChild e
    let found := decide (target ≤ e.counts[e.x[0]!]!)
    let e := addShadowOfCurrentP e
    (found, e)

mutual
  private partial def dfs (pos bound target : Nat) (e : Engine) : Bool × Engine :=
    if pos = e.k - 1 then processPrefix target e else dfsValues pos 0 bound target e

  private partial def dfsValues
      (pos value bound target : Nat) (e : Engine) : Bool × Engine :=
    if value ≤ bound then
      let e := { e with x := e.x.set! pos value }
      let e := if pos + 1 < e.k - 1 then clearShadow (pos + 1) e else e
      let (found, e) := dfs (pos + 1) value target e
      if found then (true, e) else dfsValues pos (value + 1) bound target e
    else (false, e)
end

private partial def runTops (top target : Nat) (e : Engine) : Bool :=
  if top ≤ e.n then
    let e := { e with x := e.x.set! 0 top }
    let e := if 2 < e.k then clearShadow 1 e else e
    let (found, e) := dfs 1 top target e
    if found then true else runTops (top + 1) target e
  else false

/-- Exact retrograde search for a rectangle with at least `target` losing children. -/
def exactSearch (rows maxWidth target : Nat) : Bool :=
  if rows < 2 then false else runTops 1 target (mkEngine rows maxWidth)

example : exactSearch 6 13 2 = true := by native_decide

end ChompThreeOpeningsNative
