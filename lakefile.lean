import Lake
open System Lake DSL

package theorems
lean_lib lake

@[default_target]
lean_exe theorems where
  root := `Int
  supportInterpreter := true
