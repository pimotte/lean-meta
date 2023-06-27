import Lean

open Lean Lean.Expr Lean.Meta

#eval show MetaM Unit from do
  let oneExpr := Expr.app (Expr.const `Nat.succ []) (Expr.const ``Nat.zero [])
  let twoExpr := Expr.app (Expr.const `Nat.succ []) oneExpr

  -- Create `mvar1` with type `Nat`
  -- let mvar1 ← ...
  -- Create `mvar2` with type `Nat`
  -- let mvar2 ← ...
  -- Create `mvar3` with type `Nat`
  -- let mvar3 ← ...

  -- Assign `mvar1` to `2 + ?mvar2 + ?mvar3`
  -- ...

  -- Assign `mvar3` to `1`
  -- ...

  -- Instantiate `mvar1`, which should result in expression `2 + ?mvar2 + 1`
  -- ...