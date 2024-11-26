import Lean
open Lean Meta Elab

-- Note that this exists as well https://github.com/leanprover-community/mathlib4/blob/5ad34c033417c6e6efd3fcd9062fa1764d240209/Mathlib/Tactic/ToAdditive/Frontend.lean

def replace_name : Name → Option Name
| Name.str `mul other => some (Name.str `add other)
| Name.str `Mul other => some (Name.str `Add other)
| Name.str `inv other => some (Name.str `neg other)
| Name.str `Inv other => some (Name.str `Neg other)
| Name.str `one other => some (Name.str `zero other)
| Name.str `One other => some (Name.str `Zero other)
| Name.str `HMul "hMul" => some (Name.str `HAdd "hAdd")
| Name.str Name.anonymous "instHMul" => some (Name.str Name.anonymous "instHAdd")
| Name.str Name.anonymous "HMul" => some (Name.str Name.anonymous "HAdd")
| Name.str (Name.str `Mul "Group") "toMul" => some (Name.str (Name.str `Add "Group") "toAdd")
| Name.str value inner => (fun x => Name.str x inner) <$> replace_name value
| _ => none

def replace_name' : Name → Name := fun n => (replace_name n).getD n

def change_expr : Expr → Expr
| .const (declName : Name) (us : List Level) =>
  .const (replace_name' declName: Name) (us : List Level)
| .app (fn : Expr) (arg : Expr) =>
  .app (change_expr fn: Expr) (change_expr arg: Expr)
| .lam (binderName : Name) (binderType : Expr) (body : Expr) (binderInfo : BinderInfo) =>
  .lam (binderName : Name) (change_expr binderType : Expr) (change_expr body : Expr) (binderInfo : BinderInfo)
| .mdata (data : MData) (expr : Expr) =>
  .mdata (data : MData) (change_expr expr : Expr)
| .proj (typeName : Name) (idx : Nat) (struct : Expr) =>
  .proj (replace_name' typeName: Name) (idx : Nat) (change_expr struct : Expr)
| .forallE (binderName : Name) (binderType : Expr) (body : Expr) (binderInfo : BinderInfo) =>
  .forallE (binderName : Name) (change_expr binderType : Expr) (change_expr body : Expr) (binderInfo : BinderInfo)
| .letE (declName : Name) (type : Expr) (value : Expr) (body : Expr) (nonDep : Bool) =>
  .letE (declName : Name) (change_expr type : Expr) (change_expr value : Expr) (change_expr body : Expr) (nonDep : Bool)
| .lit (.natVal 1) => .lit (.natVal 0)
| expr => expr

syntax (name := toAdditive) "to_additive" : attr

-- inv -> neg, mul -> add
initialize registerBuiltinAttribute {
  name := `toAdditive
  descr := "Converts multiplicative theorems to their additive kind"
  applicationTime := .afterTypeChecking
  add := fun src ref kind => match ref with
  | `(attr| to_additive) => MetaM.run' do
    -- Something about only on
    if (kind != AttributeKind.global) then
      throwError f!"`to_additive` can only be used as a global attribute. not {kind}"

    -- logInfo f!"Finding {src}"

    let env ← getEnv
    match (env.find? src) with
    | some (.thmInfo thm) => {
      let name := thm.name
      let value := thm.value

      -- TODO inline `.or_else_error`
      match replace_name name with
      | none => throwError "doesn't start with prefix"
      | some new_name => {
        -- THIS `do` is incredible import here
        do

        let ranges: DeclarationRanges := {
          range := ← getDeclarationRange (← getRef)
          selectionRange := ← getDeclarationRange ref
        }
        addDeclarationRanges new_name ranges

        let new_value := change_expr value
        -- logInfo f!"Before={value}"
        -- logInfo f!"After={new_value}"

        let (levels, pf) ← Term.TermElabM.run' do
          let pf ← Elab.Term.levelMVarToParam new_value
          return (← Term.getLevelNames, pf)
        let pf ← instantiateMVars pf

        let stmt := .thmDecl {
          name := new_name,
          levelParams := levels,
          type := (← inferType pf),
          value := new_value
        }
        -- logInfo f!"Output {pf}"
        addAndCompile stmt
      }
    }
    | some (.inductInfo _) => {
        throwError "TODO"
      -- let stmt := Declaration.inductDecl i.all i.all.length i.ctors;
      -- logInfo f!"Output {stmt}"
      -- addAndCompile stmt
    }
    | _ => throwError "to_additive not on theorem (at least not in env)"

  | _ => throwUnsupportedSyntax }
