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
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header {} messages inputCtx
  let mut additionalImports := ""
  for pkg in importPkgs do
    if !env.header.moduleNames.contains pkg then
      additionalImports := additionalImports ++ s!"import {pkg}\n"
  let out := additionalImports ++ src
  IO.println out
  return 0

def addImports (args : Cli.Parsed) : IO UInt32 := do
  searchPathRef.set compile_time_search_path%
  let module := args.positionalArg! "module" |>.as! ModuleName
  let mut importPkgs := []
  if args.hasFlag "querySMT" then importPkgs := `QuerySMT :: importPkgs
  if args.hasFlag "aesop" then importPkgs := `Aesop :: importPkgs
  if args.hasFlag "duper" && !args.hasFlag "querySMT" then importPkgs := `Duper :: importPkgs
  if importPkgs.isEmpty then
    importPkgs := [`QuerySMT] -- Default behavior if no flags are included
  addImportsToModule module importPkgs

/-- Setting up command line options and help text for `lake exe add_imports`. -/
def add_imports : Cmd := `[Cli|
  add_imports VIA addImports; ["0.0.1"]
"Modify a Lean file by inserting an import at the beginning of the file (if the file
 does not already contain said import). Prints the modified source code to stdout."

  FLAGS:
    "duper";  "Add `import Duper` if the file does not already import Duper"
    "aesop"; "Add `import Aesop` if the file does not already import Aesop"
    "querySMT"; "Add `import QuerySMT` if the file does not already import QuerySMT. " ++
                "This flag is included by default if no other flags are added"

  ARGS:
    module : ModuleName; "Lean module to add the import to."
]

/-- `lake exe add_imports` -/
def main (args : List String) : IO UInt32 :=
  add_imports.validate args

-- #eval addImportToModule `temp [`Aesop, `Duper]
