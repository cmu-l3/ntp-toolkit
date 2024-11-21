/-
Prints all imported modules of a project, in order. Takes as input the base module name(s).
-/

import Lean
import Batteries

open Lean Meta System.FilePath Core

/--
Copied from mathlib (not importing mathlib, so we can extract from non-mathlib-dependent Lean):
Run a `CoreM α` in a fresh `Environment` with specified `modules : List Name` imported.
-/
def CoreM.withImportModules' {α : Type} (modules : Array Name) (run : CoreM α)
    (searchPath : Option SearchPath := none) (options : Options := {})
    (trustLevel : UInt32 := 0) (fileName := "") :
    IO α := unsafe do
  if let some sp := searchPath then searchPathRef.set sp
  Lean.withImportModules (modules.map (Import.mk · false)) options trustLevel fun env =>
    let ctx := {fileName, options, fileMap := default}
    let state := {env}
    Prod.fst <$> (CoreM.toIO · ctx state) do
      run

/-- Extracts modules imported by a lean module (eg Mathlib) that starts with this name (eg Mathlib.*) -/
def main (args : List String) : IO UInt32 := do
  let options := Options.empty.insert `maxHeartbeats (0 : Nat)
  let modules := match args with
  | [] => #[`Mathlib]
  | args => args.toArray.map fun s => s.toName
  searchPathRef.set compile_time_search_path%
  CoreM.withImportModules' modules (options := options) do
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
