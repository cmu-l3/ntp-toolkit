-- TODO

def main (args : List String) : IO UInt32 := do return 1

-- import Lean.Util.SearchPath
-- import Mathlib.Lean.CoreM
-- -- import PremiseSelection
-- import Mathlib.Data.Prod.Basic /- c/f TrainingData.Utils.TheoremPrettyPrinting -/

-- open Lean PremiseSelection Cloud

-- def getModuleNameFor (env : Environment) (name : Name) : Name :=
--   match env.getModuleIdxFor? name with
--     | none => env.header.mainModule
--     | some idx => env.header.moduleNames[idx.toNat]!

-- def addPremise (premise : Premise) : CoreM Unit := do
--   let env ← getEnv
--   let moduleName := getModuleNameFor env premise.name
--   let apiBaseUrl := getApiBaseUrl (← getOptions)

--   let apiUrl := apiBaseUrl ++ "/add-premise"
--   let data := Json.mkObj [
--     ("name", toJson premise.name),
--     ("decl", toJson premise.decl),
--     ("module", toJson moduleName),
--   ]
--   let curlArgs := #[
--     "-X", "POST",
--     "--header", "Content-Type: application/json",
--     "--user-agent", "LeanProver (https://leanprover-community.github.io/)",
--     -- We put data in stdin rather than command argument, because the data may be too long
--     "--data", "@-",
--     apiUrl
--   ]

--   let child ← IO.Process.spawn { cmd := "curl", args := curlArgs, stdin := .piped, stdout := .piped, stderr := .piped }
--   let (stdin, child) ← child.takeStdin
--   stdin.putStr data.compress
--   let exitCode ← child.wait
--   let _stdout ← child.stdout.readToEnd

--   if exitCode != 0 then
--     let stderr ← child.stderr.readToEnd
--     IO.throwServerError <|
--       "Could not send API request to select premises. " ++
--       s!"curl exited with code {exitCode}:\n{stderr}"

-- /-- Adds all premises from all modules imported (directly and transitively) by a lean module to a server endpoint
-- (Currently this is for test only!)
-- -/
-- def main (args : List String) : IO UInt32 := do
--   let modules := match args with
--   | [] => #[`Mathlib]
--   | args => args.toArray.map fun s => s.toName
--   CoreM.withImportModules' modules do
--     let env ← getEnv
--     let indexedModules ← Cloud.getIndexedModules
--     let newPremises ← Cloud.getUnindexedPremises
--     for premise in newPremises do
--       unless indexedModules.contains (getModuleNameFor env premise.name) do
--         logInfo m!"adding premise {premise.name}"
--         addPremise premise
--   return 0
