/-
Prints all imported modules of a project, in order. Takes as input the base module name(s).
-/

import Mathlib.Lean.CoreM
import Lean.Util.SearchPath

open Lean Meta System.FilePath

/-- Extracts modules imported by a lean module (eg Mathlib) that starts with this name (eg Mathlib.*) -/
def main (args : List String) : IO UInt32 := do
  let options := Options.empty.insert `maxHeartbeats (0 : Nat)
  let modules := match args with
  | [] => #[`Mathlib]
  | args => args.toArray.map fun s => s.toName
  searchPathRef.set compile_time_search_path%
  CoreM.withImportModules modules (options := options) do
    let env ← getEnv
    let allModules := env.allImportedModuleNames.filter fun module =>
      modules.contains module.components.head!
    let allModulesSorted := allModules.qsort (·.toString < ·.toString)
    for module in allModulesSorted do
      let json := Json.mkObj [
        ("name", Json.str s!"{module}")
      ]
      IO.println json.compress
  return 0

-- /--
-- This alternative implementation (basically `getAllModulesSorted`) extracts all **/*.lean files.
-- We did not use it because it also extracts tests/, scripts/ etc.
-- -/
-- def main' (args : List String) : IO UInt32 := do
--   for path in args do
--     let moduleFiles := (← walkDir path).filter (·.extension == some "lean")
--     let moduleNames ← moduleFiles.filterMapM fun f => do
--       if ← f.pathExists then
--         return some (← moduleNameOfFileName f (some path)).toString
--       else
--         return none
--     let moduleNamesSorted := moduleNames.qsort (· < ·)
--     for module in moduleNamesSorted do
--       IO.println (Json.str s!"{module}").compress
--   return 0

-- -- #eval main' [".lake/packages/mathlib"]
