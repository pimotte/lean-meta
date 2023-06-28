import Lean

open Lean Lean.Expr Lean.Meta

#eval show MetaM Unit from do
  let oneExpr := Expr.app (Expr.const `Nat.succ []) (Expr.const ``Nat.zero [])
  let twoExpr := Expr.app (Expr.const `Nat.succ []) oneExpr

  -- Create `mvar1` with type `Nat`
  let mvar1 ← mkFreshExprMVar (some (.const ``Nat []))
  -- Create `mvar2` with type `Nat`
  let mvar2 ← mkFreshExprMVar (some (.const ``Nat []))
  -- Create `mvar3` with type `Nat`
  let mvar3 ← mkFreshExprMVar (some (.const ``Nat []))

  -- Assign `mvar1` to `2 + ?mvar2 + ?mvar3`
  mvar1.mvarId!.assign (mkAppN (.const ``Nat.add []) #[.lit (.natVal 2), mkAppN (.const ``Nat.add []) #[mvar2, mvar3]])

  -- Assign `mvar3` to `1`
  mvar3.mvarId!.assign (.lit (.natVal 1))

  -- Instantiate `mvar1`, which should result in expression `2 + ?mvar2 + 1`
  IO.println s!"  meta1: {← instantiateMVars mvar1}"


elab "explore" : tactic => do
  let mvarId : MVarId ← Lean.Elab.Tactic.getMainGoal
  let metavarDecl : MetavarDecl ← mvarId.getDecl

  IO.println "Our metavariable"
  IO.println s!"  Goal username: { metavarDecl.userName }"
  IO.println s!"  Goal type: { metavarDecl.type }"

  IO.println "All of its local declarations"
  for ldecl in ← getLCtx do
    if ldecl.isImplementationDetail then
      continue
    IO.println s!"  Local username: { ldecl.userName }"
    IO.println s!"  Local type: { ldecl.type }"
    if (← isDefEq metavarDecl.type ldecl.type) then
      mvarId.assign ldecl.toExpr
      return ()
  
  return ()

theorem red (hA : 1 = 1) (hB : 2 = 2) : 2 = 2 := by
  explore

def checkExpr (e1 : Expr) (e2 : Expr) : MetaM Unit := do
  IO.println s!"  isDefEq: { ← isDefEq e1 e2}"

#eval show MetaM Unit from do
  let litExp := Expr.lit (Lean.Literal.natVal 1)
  let compExp := Expr.app (Expr.const ``Nat.succ []) (Expr.const ``Nat.zero [])

  checkExpr litExp compExp

#eval show MetaM Unit from do
  let litExp := Expr.lit (Lean.Literal.natVal 5)
  let compExp := Expr.app (.lam `x (.const ``Nat []) (.lit (.natVal 5)) .default) 
    (.app (.lam `y (← mkArrow (.const ``Nat []) (.const ``Nat [])) (.bvar 0) .default) 
      (.lam `z (.const ``Nat []) (.bvar 0) .default))

  checkExpr litExp compExp
-- (fun x => 5) ((fun y : Nat → Nat => y) (fun z : Nat => z))
#eval show MetaM Unit from do
  let litExp := .lit (.natVal 5)
  let compExp := Expr.app (.lam `x (.const ``Nat []) (.lit (.natVal 5)) .default) 
    (.app (.lam `y (← mkArrow (.const ``Nat []) (.const ``Nat [])) (.bvar 0) .default) 
      (.lam `z (.const ``Nat []) (.bvar 0) .default))

  checkExpr litExp compExp