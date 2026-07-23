import FormalConjecturesUtil

namespace ChompThreeOpeningsNative

/-- Smoke test for the mutable-array primitives used by the exact checker. -/
private def arraySmoke : Bool := Id.run do
  let mut a : Array UInt64 := Array.replicate 16 0
  a := a.set! 3 5
  let x := a[3]!
  return x == 5

example : arraySmoke = true := by
  native_decide

end ChompThreeOpeningsNative
