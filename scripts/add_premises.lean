import Lean.Util.SearchPath
import Mathlib.Lean.CoreM
import PremiseSelection

open Lean PremiseSelection Cloud

def getModuleNameFor (env : Environment) (name : Name) : Name :=
  match env.getModuleIdxFor? name with
    | none => env.header.mainModule
    | some idx => env.header.moduleNames[idx.toNat]!

def addPremise (name : Name) : CoreM Unit := do
  let env ← getEnv
  let premise ← Premise.fromName name
  let moduleName := getModuleNameFor env name
  let apiBaseUrl := getApiBaseUrl (← getOptions)

  let apiUrl := apiBaseUrl ++ "/add-premise"
  let data := Json.mkObj [
    ("name", toJson name),
    ("decl", toJson premise.decl),
    ("module", toJson moduleName),
  ]
  let curlArgs := #[
    "-X", "POST",
    "--header", "Content-Type: application/json",
    "--user-agent", "LeanProver (https://leanprover-community.github.io/)",
    -- We put data in stdin rather than command argument, because the data may be too long
    "--data", "@-",
    apiUrl
  ]

  let child ← IO.Process.spawn { cmd := "curl", args := curlArgs, stdin := .piped, stdout := .piped, stderr := .piped }
  let (stdin, child) ← child.takeStdin
  stdin.putStr data.compress
  let exitCode ← child.wait
  let _stdout ← child.stdout.readToEnd

  if exitCode != 0 then
    let stderr ← child.stderr.readToEnd
    IO.throwServerError <|
      "Could not send API request to select premises. " ++
      s!"curl exited with code {exitCode}:\n{stderr}"

/-- Adds all premises from all modules imported (directly and transitively) by a lean module to a server endpoint
(Currently this is for test only!)
-/
def main (args : List String) : IO UInt32 := do
  let options := Options.empty.insert `maxHeartbeats (0 : Nat)
  let modules := match args with
  | [] => #[`Mathlib]
  | args => args.toArray.map fun s => s.toName
  searchPathRef.set compile_time_search_path%
  CoreM.withImportModules modules (options := options) do
    let indexedModules ← getIndexedModules (getApiBaseUrl (← getOptions))
    let newNames ← Premise.getNames indexedModules
    for name in newNames do
      addPremise name
  return 0
