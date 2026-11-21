import Lean
import Lean.Replay
import ParseExport33
import RH17.S09_Reflection
import RH17.S16_TwoArithmeticInputs

namespace UpperTheory.LiteratureTheorems
end UpperTheory.LiteratureTheorems

open Lean Elab Command

elab "#prepare_arithmetic_interfaces" : command => do
  let base ← getEnv
  let data ← Export.parseStream (.ofHandle (← IO.FS.Handle.mk "/dev/stdin" .read))
  let missing := data.constMap.filter fun n _ => !base.contains n
  IO.eprintln s!"Type-interface development context contributes {missing.size} declarations."
  let context ← base.replay missing
  let path := (← IO.getEnv "RH_INTERFACE_OUTPUT").get!
  writeModule (context.setMainModule `RHChapterContext) path (writeIR := false)

#prepare_arithmetic_interfaces
