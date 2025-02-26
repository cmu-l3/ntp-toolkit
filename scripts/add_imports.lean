import TrainingData.Frontend
import TrainingData.InfoTree.ToJson
import TrainingData.InfoTree.TacticInvocation.Basic
import Mathlib.Control.Basic
import Mathlib.Tactic.Common
import Mathlib.Tactic.Change
import Cli

open Lean Elab IO Meta Cli System

def addImportsToModule (module : ModuleName) (importPkgs : List Name) : IO UInt32 := do
  let fileName := (← findLean module).toString
  let src ← moduleSource module
  let inputCtx := Parser.mkInputContext src fileName
  let (header, _parserState, messages) ← Parser.parseHeader inputCtx
  let (env, _messages) ← processHeader header {} messages inputCtx
  let mut additionalImports := ""
  for pkg in importPkgs do
    if !env.header.moduleNames.contains pkg then
      additionalImports := additionalImports ++ s!"import {pkg}\n"
  let out := additionalImports ++ src
  IO.println out
  return 0

/-- Like `addImportsToModule` but doesn't worry about potentially duplicating imports. -/
def addImportsToModuleWithoutChecking (module : ModuleName) (importPkgs : List Name) : IO UInt32 := do
  let src ← moduleSource module
  let mut additionalImports := ""
  for pkg in importPkgs do
    additionalImports := additionalImports ++ s!"import {pkg}\n"
  let out := additionalImports ++ src
  IO.println out
  return 0

def addImports (args : Cli.Parsed) : IO UInt32 := do
  searchPathRef.set compile_time_search_path%
  let module := args.positionalArg! "module" |>.as! ModuleName
  let mut needToCheck := false -- Only bother checking for duplicate imports if that is possible
  let mut importPkgs := []
  if args.hasFlag "hammer" then importPkgs := `Hammer :: importPkgs
  if args.hasFlag "querySMT" then importPkgs := `QuerySMT :: importPkgs
  if args.hasFlag "aesop" then
    importPkgs := `Aesop :: importPkgs
    needToCheck := true
  if args.hasFlag "duper" && !args.hasFlag "querySMT" && !args.hasFlag "hammer" then importPkgs := `Duper :: importPkgs
  if importPkgs.isEmpty then
    importPkgs := [`Hammer] -- Default behavior if no flags are included
  if needToCheck then addImportsToModule module importPkgs
  else addImportsToModuleWithoutChecking module importPkgs

/-- Setting up command line options and help text for `lake exe add_imports`. -/
def add_imports : Cmd := `[Cli|
  add_imports VIA addImports; ["0.0.1"]
"Modify a Lean file by inserting an import at the beginning of the file (if the file
 does not already contain said import). Prints the modified source code to stdout."

  FLAGS:
    "duper";  "Add `import Duper` if the file does not already import Duper"
    "aesop"; "Add `import Aesop` if the file does not already import Aesop"
    "querySMT"; "Add `import QuerySMT` if the file does not already import QuerySMT"
    "hammer"; "Add `import Hammer` if the file does not already import Hammer. " ++
              "This flag is included by default if no other flags are added"

  ARGS:
    module : ModuleName; "Lean module to add the import to."
]

/-- `lake exe add_imports` -/
def main (args : List String) : IO UInt32 :=
  add_imports.validate args

-- #eval addImportToModule `temp [`Aesop, `Duper]
