import Lean

open Lean

def zero := Expr.const ``Nat.zero []

def one := Expr.app (.const ``Nat.succ []) zero

def two := Expr.app (Expr.app (.const ``Nat.succ []) zero) zero


def one_plus_two := Expr.app (Expr.app (.const ``Nat.add []) one) two

def one_plus_two' := mkAppN (.const ``Nat.add []) #[one, two]

def fun_add_one : Expr := .lam `x (.const ``Nat []) (mkAppN (.const ``Nat.add []) #[one , .bvar 0]) BinderInfo.default

def fun_fun : Expr := 
  .lam `a (.const ``Nat []) (
  .lam `b (.const ``Nat []) (
  .lam `c (.const ``Nat []) (mkAppN (.const ``Nat.add []) #[ mkAppN (.const ``Nat.mul []) #[.bvar 1, .bvar 2], .bvar 0])
  BinderInfo.default) BinderInfo.default) BinderInfo.default

