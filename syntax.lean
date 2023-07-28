import Lean

-- notation:80 l:80 " 💀 " r:79 => l - r

-- set_option quotPrecheck false in
-- infixr:80 " 💀 " => fun l r => l - r
open Lean Elab Command

namespace c
  scoped syntax:71 term:50 " 💀 " term:72 : term
  scoped macro_rules | `($l:term 💀 $r:term) => `($l - $r)

  scoped syntax "goodmorning" : term
  scoped macro_rules | `("good morning") => `(1337)

  scoped syntax (name := hello_c) "hello" : command
  @[command_elab hello_c] def helloElab : CommandElab :=
    fun stx => Lean.logInfo "hello!"

  -- scoped syntax (name := yellow_t)"yellow" : tactic
  -- @[command_elab yellow_t] def yellowElab : TacticElab :=
  --   fun stx => do
  --     Lean.logInfo "yellowee"
  elab "yellow" : tactic => do
    Lean.logInfo "yellowee"
  
    -- red red red 4
    -- blue 7
    -- blue blue blue blue blue 18

  syntax color := "red" <|> "blue"
  syntax (("red"+) <|> ("blue"+)) num : term

  #check red red red 4
  #check red blue 4
  #check blue blue blue 12
end c

namespace d 
  
end d
open c
open d
#check 5 * 8 💀 4
#check 8 💀 6 💀 1

#eval 5 * 8 💀 4
#eval 8 💀 6 💀 1

#eval goodmorning
hello

def testFun : True := by 
  yellow
  trivial

