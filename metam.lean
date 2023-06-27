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
  -- ...

  IO.println "All of its local declarations"
  -- ...

theorem red (hA : 1 = 1) (hB : 2 = 2) : 2 = 2 := by
  explore
  sorry