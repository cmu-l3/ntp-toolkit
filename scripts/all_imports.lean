/-
Prints all imports of a module, in order
-/

import Mathlib.Lean.CoreM
import Batteries.Lean.Util.Path

open Lean Meta

def main (args : List String) : IO UInt32 := do
  let options := Options.empty.insert `maxHeartbeats (0 : Nat)
  let modules := match args with
  | [] => #[`Mathlib]
  | args => args.toArray.map fun s => s.toName
  searchPathRef.set compile_time_search_path%
  CoreM.withImportModules modules (options := options) do
    let env ← getEnv
    let allModules := env.allImportedModuleNames
    for module in allModules do
      IO.println (Json.str s!"{module}").compress
  return 0
