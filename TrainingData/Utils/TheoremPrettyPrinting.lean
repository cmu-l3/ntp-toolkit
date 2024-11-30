import DocGen4.Process
import Batteries.Data.String.Basic

open Lean IO Meta System DocGen4 Process

namespace TheoremPrettyPrinting

def argToString (arg : DocGen4.Process.Arg) : String :=
  let (l, r) := match arg.binderInfo with
  | BinderInfo.default => ("(", ")")
  | BinderInfo.implicit => ("{", "}")
  | BinderInfo.strictImplicit => ("⦃", "⦄")
  | BinderInfo.instImplicit => ("[", "]")
  let n := match arg.name with
    | some name => s!"{name.toString} : "
    | none => ""
  s!"{l}{n}{arg.type.stripTags}{r}"

/-- Wrapper around `Lean.findDeclarationRanges?` that tries harder to find a range -/
def findDeclarationRanges! [Monad m] [MonadEnv m] [MonadLiftT BaseIO m]
    (name : Name) : m DeclarationRanges := do
  match ← findDeclarationRanges? name with
  | some range => pure range
  | none =>
    match name with
    | .str p _ | .num p _ =>
      -- If declaration range of e.g. `Nat.noConfusionType` could not be found, try prefix `Nat` instead.
      findDeclarationRanges! p
    | .anonymous =>
      -- If a declaration range could not be found with recursion above, use the default range (all 0)
      pure default

/-- Modified version of `Info.ofConstantVal`:
    * Suppressed error when declaration range is none
    * Changed `findDeclarationRanges?` to `ConstantPrettyPrinting.findDeclarationRanges!` -/
def Info.ofConstantVal' (v : ConstantVal) : MetaM Info := do
  argTypeTelescope v.type fun args type => do
    let args ← args.mapM (fun (n, e, b) => do return Arg.mk n (← prettyPrintTerm e) b)
    let nameInfo ← NameInfo.ofTypedName v.name type
    let range ← findDeclarationRanges! v.name
    return {
      toNameInfo := nameInfo,
      args,
      declarationRange := range.range,
      attrs := ← getAllAttributes v.name
    }

end TheoremPrettyPrinting
