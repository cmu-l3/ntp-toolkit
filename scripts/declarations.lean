/-
Adapted from lean-training-data/scripts/premises.lean
(Changed: output declarations restricted to the input module(s).)

Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Lean.CoreM
import Mathlib.Control.Basic
import Mathlib.Lean.Expr.Basic
import Batteries.Lean.HashMap
import Batteries.Lean.Util.Path

import Mathlib.Tactic.Positivity

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

namespace DocGen4.Process

open DocGen4 DocGen4.Process DocGen4.Process.DocInfo

-- #check ofConstant
/--
Modified version of `Info.ofConstantVal`:
* Suppressed error when declaration range is none
-/
def Info.ofConstantVal' (v : ConstantVal) : MetaM Info := do
  argTypeTelescope v.type fun args type => do
    let args ← args.mapM (fun (n, e, b) => do return Arg.mk n (← prettyPrintTerm e) b)
    let nameInfo ← NameInfo.ofTypedName v.name type
    let range := (← findDeclarationRanges? v.name).getD default
    -- TODO: Maybe selection range is more relevant? Figure this out in the future
    return {
      toNameInfo := nameInfo,
      args,
      declarationRange := range.range,
      attrs := ← getAllAttributes v.name
    }

-- #check DocInfo.getKindDescription
/--
Returns kind (string) and Info given constant.
Simplified version of `DocInfo.getKind`, `DocInfo.ofConstant`.
-/
def infoOfConstant (cinfo : ConstantInfo) : MetaM (String × Info) := do
  let env ← getEnv
  let kind : String :=
    match cinfo with
    | .axiomInfo _ => "axiom"
    | .thmInfo _ => "theorem"
    | .opaqueInfo _ => "opaque"
    | .defnInfo i =>
      if isInstanceCore env i.name then
        "instance"
      else
        "def"
    | .inductInfo i =>
      if isClass env i.name then
        "class"
      else if isStructure env i.name then
        "structure"
      else
        "inductive"
    | .ctorInfo _ => "def"
    | .recInfo _ => "def"
    | .quotInfo _ => "def"
  return (kind, ← Info.ofConstantVal' cinfo.toConstantVal)

end DocGen4.Process

/-- Pretty-prints a constant to JSON -/
def constantInfoToJson (cinfo : ConstantInfo) : MetaM Json := do
  let (kind, info) ← infoOfConstant cinfo
  return Json.mkObj [
    ("name", Json.str cinfo.name.toString),
    ("kind", Json.str kind),
    ("args", Json.arr <| info.args.map argToString |>.map Json.str),
    ("type", Json.str info.type.stripTags),
    ("doc", match info.doc with
      | some doc => Json.str doc
      | none => Json.null),
    ("pos", match info.declarationRange.pos.line with
      -- if 0, probably generated from the getD default in Info.ofConstantVal'
      -- so we don't know the position
      | 0 => Json.null
      | l => l)
  ]

/--
Traverse all constants from imported files,
collecting prettified declarations
-/
def allConstantDeclarations (moduleNames : Array Name) :
    MetaM (Array Json) := do
  let env ← getEnv
  let constantsMap := env.constants.map₁
  let const2ModIdx := env.const2ModIdx
  let moduleIdxs := moduleNames.filterMap env.getModuleIdx?
  let mut result : Array Json := ∅
  for (n, c) in constantsMap do
    -- We omit all internal details (Name.isInternalDetail)
    -- We restrict to declarations in the module
    if let some modIdx := const2ModIdx.find? n then
      if moduleIdxs.contains modIdx && !n.isInternalDetail then
        let json ← constantInfoToJson c
        result := result.push json
  return result

-- #check Mathlib.Meta.NormNum.invertibleOfMul'
-- #eval show MetaM Unit from do
--   let name := ``Mathlib.Meta.NormNum.invertibleOfMul'
--   if let some cinfo := (← getEnv).constants.find? name then
--     IO.println <| cinfo.getUsedConstantsAsSet.toList

-- #eval show MetaM Unit from do
--   IO.withStderr (← IO.getStdin) <| do
--   let constantsMap := (← getEnv).constants.map₁
--   let name := ``Mathlib.Meta.Positivity.evalAscFactorial
--   let cinfo := constantsMap.find! name
--   IO.println <| ← constantInfoToJson cinfo

-- #check Nat.casesAuxOn
-- #eval show MetaM Unit from do
--   let mut cnt := 0
--   let constantsMap := (← getEnv).constants.map₁
--   IO.println <| ← (``Nat.casesAuxOn).isBlackListed
--   for (name, cinfo) in constantsMap do
--     if cnt > 100 then return ()
--     -- if !(← name.isBlackListed) && !(`injEq).isSuffixOf name then
--     --   match ← findDeclarationRanges? name with
--     --   | some _ => continue
--     --   | none =>
--     if !name.isInternalDetail && (← findDeclarationRanges? name).isNone then
--           cnt := cnt + 1
--           IO.println name

def main (args : List String) : IO UInt32 := do
  let options := Options.empty.insert `maxHeartbeats (0 : Nat)
  let modules := match args with
  | [] => #[`Mathlib]
  | args => args.toArray.map fun s => s.toName
  searchPathRef.set compile_time_search_path%
  CoreM.withImportModules modules (options := options) do
    let allDeclarations ← MetaM.run' (allConstantDeclarations modules)
    for json in allDeclarations do
      IO.println json.compress
  return 0
