import DocGen4.Process
import Batteries.Data.String.Basic
/- Without this import, declarations.lean raises uncaught exception when pretty printing some theorems with `Prod.fst`.
  (To reproduce: remove this import and run `lake exe declarations Mathlib.Data.Fin.Tuple.Basic`).
  This is likely because of the option `Prod.PrettyPrinting.pp.numericProj.prod` in `Mathlib.Data.Prod.Basic`
  cannot be both defined by and accessed in `Lean.withImports`.
  TODO: is there a better fix? -/
import Mathlib.Data.Prod.Basic
import Mathlib.Util.PPOptions

open Lean IO Meta System DocGen4 Process

namespace TheoremPrettyPrinting

/--
Pretty prints a `Lean.Parser.Term.bracketedBinder`.
-/
private def prettyPrintBinder (stx : Syntax) (infos : SubExpr.PosMap Elab.Info) : MetaM RenderedCode := do
  let fmt ← PrettyPrinter.format Parser.Term.bracketedBinder.formatter stx
  let tt := Widget.TaggedText.prettyTagged fmt
  let ctx := {
    env := ← getEnv
    mctx := ← getMCtx
    options := ← getOptions
    currNamespace := ← getCurrNamespace
    openDecls := ← getOpenDecls
    fileMap := default,
    ngen := ← getNGen
  }
  return renderTagged (← Widget.tagCodeInfos ctx infos tt)

private def prettyPrintTermStx (stx : Term) (infos : SubExpr.PosMap Elab.Info) : MetaM RenderedCode := do
  let fmt ← PrettyPrinter.formatTerm stx
  let tt := Widget.TaggedText.prettyTagged fmt
  let ctx := {
    env := ← getEnv
    mctx := ← getMCtx
    options := ← getOptions
    currNamespace := ← getCurrNamespace
    openDecls := ← getOpenDecls
    fileMap := default,
    ngen := ← getNGen
  }
  return renderTagged (← Widget.tagCodeInfos ctx infos tt)

private def findDeclarationRanges! [Monad m] [MonadEnv m] [MonadLiftT BaseIO m] (name : Name) : m DeclarationRanges := do
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

def Info.ofTypedName (n : Name) (t : Expr) : MetaM Info := do
  -- Use the main signature delaborator. We need to run sanitization, parenthesization, and formatting ourselves
  -- to be able to extract the pieces of the signature right before they are formatted
  -- and then format them individually.
  let (sigStx, infos) ← withTheReader Core.Context ({ · with currNamespace := n.getPrefix }) <|
    PrettyPrinter.delabCore t (delab := PrettyPrinter.Delaborator.delabForallParamsWithSignature fun binders type =>
      -- Use `declSig` as a data structure so that the binders and type can be put through the sanitizer all together.
      `(declSig| $binders* : $type))
  let sigStx := (sanitizeSyntax sigStx).run' { options := (← getOptions) }
  let sigStx ← PrettyPrinter.parenthesize Parser.Command.declSig.parenthesizer sigStx
  let `(declSig| $binders* : $type) := sigStx
    | throwError "signature pretty printer failure for {n}"
  let args ← binders.mapM fun binder => do
    let fmt ← prettyPrintBinder binder infos
    return Arg.mk fmt (!binder.isOfKind ``Parser.Term.explicitBinder)
  let type ← prettyPrintTermStx type infos
  let range ← findDeclarationRanges! n
  return {
    toNameInfo := { name := n, type, doc := ← getDocString? (← getEnv) n},
    args,
    declarationRange := range.range,
    attrs := ← getAllAttributes n
  }

/-- This is identical to DocGen4's `Info.ofConstantVal` except it does not panic if it fails to find the declationRange.
    It simply uses `declarationRange := default`. The critical change is in `Info.ofTypedName` -/
def Info.ofConstantVal' (v : ConstantVal) : MetaM Info := do
  let e := Expr.const v.name (v.levelParams.map mkLevelParam)
  ofTypedName v.name (← inferType e)

def numArgsOfConstantVal (v : ConstantVal) : MetaM Nat := do
  try
    let thmInfo ← Info.ofConstantVal' v
    return thmInfo.args.size
  catch _ =>
    return getIntrosSize v.type

def withHammerPPOptions {m α} [MonadWithOptions m] (x : m α) : m α :=
  withOptions (fun o => (o.set `pp.notation false).set `pp.fullNames true) x

end TheoremPrettyPrinting
