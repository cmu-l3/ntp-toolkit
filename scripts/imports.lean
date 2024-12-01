/-
Prints all (transitively) imported modules of a module.
-/

import Mathlib.Lean.CoreM
import Lean.Util.SearchPath

open Lean Meta

/-- Extracts modules imported (directly and transitively) by a lean module -/
def main (args : List String) : IO UInt32 := do
  let options := Options.empty.insert `maxHeartbeats (0 : Nat)
  let modules := match args with
  | [] => #[`Mathlib]
  | args => args.toArray.map fun s => s.toName
  searchPathRef.set compile_time_search_path%
  CoreM.withImportModules modules (options := options) do
    let env ← getEnv
    let allModulesSorted := env.allImportedModuleNames.qsort (·.toString < ·.toString)
    let directlyImportedModules := env.imports.map (·.module)
    for module in allModulesSorted do
      let json := Json.mkObj [
        ("name", Json.str s!"{module}"),
        ("isDirect", Json.bool (directlyImportedModules.contains module))
      ]
      IO.println json.compress
  return 0
