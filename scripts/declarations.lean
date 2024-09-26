/-
Adapted from lean-training-data/scripts/premises.lean
(Changed: output declarations restricted to the input module(s).)

Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Lean.CoreM
import Mathlib.Control.Basic
import Mathlib.Lean.Expr.Basic
import Std.Lean.HashMap
import Std.Lean.Util.Path

-- import Mathlib.Tactic.Positivity

import DocGen4.Process

/-!
Generate declaration names and types.
-/

open Lean Meta DocGen4.Process

def argToString (arg : Arg) : String :=
  let (l, r) := match arg.binderInfo with
  | BinderInfo.default => ("(", ")")
  | BinderInfo.implicit => ("{", "}")
  | BinderInfo.strictImplicit => ("⦃", "⦄")
  | BinderInfo.instImplicit => ("[", "]")
  let n := match arg.name with
    | some name => s!"{name.toString} : "
    | none => ""
  s!"{l}{n}{arg.type.stripTags}{r}"

/-- Fix for Lean v4.7 -/
def computeEquations? (v : DefinitionVal) : MetaM (Array Widget.CodeWithInfos) := do
  let eqs? ← getEqnsFor? v.name
  match eqs? with
  | some eqs =>
    let eqs ← eqs.mapM processEq
    return eqs
  | none =>
    let equations := #[← stripArgs (← valueToEq v) prettyPrintTerm]
    return equations

/--
Modified version of `DocInfo.ofConstant`:
* Removed custom isBlackListed check
  (blacklisting is relegated to name.isBlackListed)
* Suppressed WARNING to stdout
* Don't ignore recursors or quot
-/
def DocInfo.ofConstant' (info : ConstantInfo) : MetaM (Option DocInfo) := do
  match ← findDeclarationRanges? info.name with
  | none => return none
  | some _ =>
    match info with
    | ConstantInfo.axiomInfo i => return some <| .axiomInfo (← AxiomInfo.ofAxiomVal i)
    | ConstantInfo.thmInfo i => return some <| .theoremInfo (← TheoremInfo.ofTheoremVal i)
    | ConstantInfo.opaqueInfo i => return some <| .opaqueInfo (← OpaqueInfo.ofOpaqueVal i)
    | ConstantInfo.defnInfo i =>
      if ← DocInfo.isProjFn i.name then
        let info ← Info.ofConstantVal i.toConstantVal
        let isUnsafe := i.safety == DefinitionSafety.unsafe
        let isNonComputable := isNoncomputable (← getEnv) i.name
        let equations ←
          tryCatch
            (.some <$> computeEquations? i)
            (fun _ => return none)
        return some <| .definitionInfo { info with isUnsafe, hints := i.hints, equations, isNonComputable }
      else
        if ← DocGen4.Process.isInstance i.name then
          let info ← InstanceInfo.ofDefinitionVal i
          return some <| .instanceInfo info
        else
          let info ← DefinitionInfo.ofDefinitionVal i
          return some <| .definitionInfo info
    | ConstantInfo.inductInfo i =>
      let env ← getEnv
      if isStructure env i.name then
        if isClass env i.name then
          return some <| .classInfo (← ClassInfo.ofInductiveVal i)
        else
          return some <| .structureInfo (← StructureInfo.ofInductiveVal i)
      else
        if isClass env i.name then
          return some <| .classInductiveInfo (← ClassInductiveInfo.ofInductiveVal i)
        else
          return some <| .inductiveInfo (← InductiveInfo.ofInductiveVal i)
    | ConstantInfo.ctorInfo i =>
      let info ← Info.ofConstantVal i.toConstantVal
      return some <| .ctorInfo { info with render := false }
    | ConstantInfo.recInfo i | ConstantInfo.quotInfo i =>
      let info ← Info.ofConstantVal i.toConstantVal
        let isNonComputable := isNoncomputable (← getEnv) i.name
      return some <| .definitionInfo
        { info with isUnsafe := false, hints := default, equations := none, isNonComputable, render := false }

def ppConstantInfo (cinfo : ConstantInfo) : MetaM (Option String) := do
  if let some info ← DocInfo.ofConstant' cinfo then
    -- let docString := info.getDocString.getD ""
    let kind := info.getKind
    -- I opted not to use this and instead use the simpler `kind`
    -- because information in it (eg unsafe def vs def) is unnecessary
    -- let kindDescription := info.getKindDescription
    let name := info.getName.toString
    -- let declarationRange := info.getDeclarationRange
    -- let line := info.getDeclarationRange.pos.line
    let args := info.getArgs.map argToString
    let type := info.getType.stripTags
    let declaration := kind ++ " " ++ name ++ " " ++ " ".intercalate args.toList ++ " : " ++ type
    match info.getDocString with
    | some docString => return "/-- " ++ docString ++ "-/\n" ++ declaration
    | none => return declaration
  else
    return none

/--
Traverse all constants from imported files,
collecting prettified declarations
-/
def allConstantDeclarations (moduleNames : Array Name) :
    MetaM (NameMap String) := do
  let constantsMap := (← getEnv).constants.map₁
  let const2ModIdx := (← getEnv).const2ModIdx
  let moduleIdxs := moduleNames.filterMap (← getEnv).getModuleIdx?
  let mut result : NameMap String := ∅
  for (n, c) in constantsMap do
    -- We omit all internally generated auxiliary statements.
    -- We restrict to declarations in the module
    if let some modIdx := const2ModIdx.find? n then
      if moduleIdxs.contains modIdx && ! (← n.isBlackListed) then
        if let some d ← ppConstantInfo c then
          result := result.insert n d
  return result

-- #eval show MetaM Unit from do
--   let constantsMap := (← getEnv).constants.map₁
--   let name := ``Mathlib.Meta.Positivity.evalAscFactorial
--   let cinfo := constantsMap.find! name
--   IO.println <| (← ppConstantInfo cinfo).get!
--   return ()

-- #check Lean.LevelMVarId.mk
-- #eval show MetaM Unit from do
--   let mut cnt := 0
--   let constantsMap := (← getEnv).constants.map₁
--   IO.println <| (← ppConstantInfo (constantsMap.find! `Nat)).get!
--   for (name, cinfo) in constantsMap do
--     if cnt > 100 then return ()
--     if !(← name.isBlackListed) && !(`injEq).isSuffixOf name then
--       match ← findDeclarationRanges? name with
--       | some _ => continue
--       | none =>
--           cnt := cnt + 1
--           IO.println name

-- #eval show MetaM Unit from do
--   let env ← getEnv
--   IO.println env.allImportedModuleNames

def main (args : List String) : IO UInt32 := do
  let options := Options.empty.insert `maxHeartbeats (0 : Nat)
  let modules := match args with
  | [] => #[`Mathlib]
  | args => args.toArray.map fun s => s.toName
  searchPathRef.set compile_time_search_path%
  CoreM.withImportModules modules (options := options) do
    let allDeclarations ← MetaM.run' (allConstantDeclarations modules)
    for (n, d) in allDeclarations do
      let json := Json.mkObj [
        ("name", Json.str n.toString),
        ("declaration", Json.str d)
      ]
      IO.println json.compress
  return 0
