import Lean

open Lean Core Meta

/-- This is copied from doc-gen4 (the ' is to disambiguate). -/
def envOfImports' (imports : Array Name) : IO Environment := do
  -- needed for modules which use syntax registered with `initialize add_parser_alias ..`
  unsafe enableInitializersExecution
  importModules (imports.map (Import.mk · false true)) Options.empty (leakEnv := true) (loadExts := true)

/-- The ' is to disambiguate with the definition in Mathlib.
This definition is copied from the `load` function in doc-gen4.
Apparently, this allows notations to be printed normally (why?), which the Lean/Mathlib `withImportModules` can't do. -/
def CoreM.withImportModules' {α} (imports : Array Name) (x : CoreM α) (options : Options := .empty) : IO α := do
  initSearchPath (← findSysroot)
  let env ← envOfImports' imports
  let options := options.set `Elab.async false
  let config := {
    maxHeartbeats := 0,
    options,
    fileName := "<ntp-toolkit>",
    fileMap := default,
  }
  Prod.fst <$> CoreM.toIO x config { env }

def MetaM.withImportModules' {α} (imports : Array Name) (x : MetaM α) (options : Options := .empty) : IO α := do
  CoreM.withImportModules' imports x.run' options
