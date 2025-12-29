import LambdaCalc.Basic

/-!
  Lambda Calculus REPL
-/

namespace LambdaCalc.REPL

open Term

/-!
## Pretty Printer
-/

def indexToName (n : Nat) : String :=
  let letters := #["x", "y", "z", "w", "v", "u", "t", "s", "r", "q", "p", "n", "m"]
  if n < letters.size then
    letters[n]!
  else
    s!"x{n}"

partial def prettyPrint (t : Term) : String :=
  go t 0 0
where
  go (t : Term) (depth prec : Nat) : String :=
    match t with
    | var n =>
      if n < depth then indexToName (depth - 1 - n) else s!"#{n - depth}"
    | lam body =>
      let s := s!"λ{indexToName depth}. {go body (depth + 1) 0}"
      if prec > 0 then s!"({s})" else s
    | app t1 t2 =>
      let s := s!"{go t1 depth 1} {go t2 depth 2}"
      if prec > 1 then s!"({s})" else s

partial def prettyPrintDB (t : Term) : String :=
  match t with
  | var n => s!"var({n})"
  | lam body => s!"λ.{prettyPrintDB body}"
  | app t1 t2 => s!"({prettyPrintDB t1} {prettyPrintDB t2})"

/-!
## Simple Parser using String.Iterator
-/

def builtins : List (String × Term) := [
  ("I", idCombinator), ("K", kCombinator), ("S", sCombinator),
  ("B", bCombinator), ("C", cCombinator), ("W", wCombinator),
  ("true", churchTrue), ("false", churchFalse),
  ("and", churchAnd), ("or", churchOr), ("not", churchNot), ("if", churchIf),
  ("succ", churchSucc), ("pred", churchPred),
  ("add", churchAdd), ("mul", churchMult), ("exp", churchExp), ("sub", churchSub),
  ("zero?", churchIsZero), ("leq", churchLeq),
  ("pair", churchPair), ("fst", churchFst), ("snd", churchSnd),
  ("Y", yCombinator), ("Z", zCombinator), ("theta", thetaCombinator),
  ("nil", scottNil), ("cons", scottCons),
  ("null?", scottIsNil), ("head", scottHead), ("tail", scottTail),
  ("length", scottLength), ("append", scottAppend), ("map", scottMap),
  ("foldr", scottFoldr), ("reverse", scottReverse),
  ("sum", scottSum), ("product", scottProduct), ("nth", scottNth),
  ("omega", omega)
]

def lookupBuiltin (name : String) : Option Term :=
  builtins.find? (·.1 == name) |>.map (·.2)

def lookupVar (ctx : List String) (name : String) : Option Nat :=
  ctx.findIdx? (· == name)

structure PS where
  s : String
  i : Nat
  ctx : List String

namespace PS
def curr (p : PS) : Option Char := p.s.get? ⟨p.i⟩
def adv (p : PS) : PS := { p with i := p.i + 1 }
def done (p : PS) : Bool := p.i >= p.s.length

partial def skip (p : PS) : PS :=
  match p.curr with
  | some ' ' | some '\n' | some '\t' => p.adv.skip
  | _ => p

def readWhile (p : PS) (pred : Char → Bool) : PS × String :=
  go p.s.length p ""
where go (fuel : Nat) (p : PS) (acc : String) : PS × String :=
  match fuel with
  | 0 => (p, acc)
  | fuel' + 1 =>
    match p.curr with
    | some c => if pred c then go fuel' p.adv (acc.push c) else (p, acc)
    | none => (p, acc)
end PS

def isAlpha (c : Char) : Bool := ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z')
def isDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'
def isIdent (c : Char) : Bool := isAlpha c || isDigit c || c == '_' || c == '\'' || c == '?'

mutual
partial def pTerm (p : PS) : Except String (PS × Term) := pApp p

partial def pApp (p : PS) : Except String (PS × Term) := do
  let (p, t) ← pAtom p
  pAppRest p t

partial def pAppRest (p : PS) (acc : Term) : Except String (PS × Term) :=
  let p := p.skip
  match p.curr with
  | some '\\' | some 'λ' | some '(' =>
    match pAtom p with
    | .ok (p', t') => pAppRest p' (app acc t')
    | .error _ => .ok (p, acc)
  | some c =>
    if isAlpha c || isDigit c then
      match pAtom p with
      | .ok (p', t') => pAppRest p' (app acc t')
      | .error _ => .ok (p, acc)
    else .ok (p, acc)
  | none => .ok (p, acc)

partial def pAtom (p : PS) : Except String (PS × Term) :=
  let p := p.skip
  match p.curr with
  | some '\\' | some 'λ' => pLam p.adv
  | some '(' =>
    match pTerm p.adv.skip with
    | .error e => .error e
    | .ok (p', t) =>
      let p' := p'.skip
      match p'.curr with
      | some ')' => .ok (p'.adv, t)
      | _ => .error "Expected ')'"
  | some c =>
    if isAlpha c then
      let (p', name) := p.readWhile isIdent
      match lookupBuiltin name with
      | some t => .ok (p', t)
      | none =>
        match lookupVar p.ctx name with
        | some idx => .ok ({ p' with ctx := p.ctx }, var idx)
        | none => .error s!"Unbound variable: {name}"
    else if isDigit c then
      let (p', ns) := p.readWhile isDigit
      let n := ns.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0
      .ok (p', churchNum n)
    else .error s!"Unexpected: {c}"
  | none => .error "Unexpected end"

partial def pLam (p : PS) : Except String (PS × Term) :=
  let p := p.skip  -- skip spaces after λ or \
  match p.curr with
  | some c =>
    if isAlpha c then
      let (p', name) := p.readWhile isIdent
      let p' := p'.skip
      match p'.curr with
      | some '.' =>
        match pTerm { p'.adv with ctx := name :: p.ctx } with
        | .error e => .error e
        | .ok (p'', body) => .ok ({ p'' with ctx := p.ctx }, lam body)
      | some c' =>
        if isAlpha c' then
          match pLam { p' with ctx := name :: p.ctx } with
          | .error e => .error e
          | .ok (p'', body) => .ok ({ p'' with ctx := p.ctx }, lam body)
        else .error "Expected '.' or variable"
      | _ => .error "Unexpected end in λ"
    else .error "Expected variable after λ"
  | none => .error "Unexpected end after λ"
end

def parse (input : String) : Except String Term :=
  match pTerm { s := input, i := 0, ctx := [] } with
  | .error e => .error e
  | .ok (p, t) => if p.skip.done then .ok t else .error "Extra characters"

/-!
## REPL Commands
-/

inductive Cmd | reduce (t : String) | step (t : String) | trace (t : String)
             | show (t : String) | showType (n : String) | list | help | quit | eval (t : String)

def parseCmd (s : String) : Cmd :=
  let s := s.trim
  if s.startsWith ":reduce " then .reduce (s.drop 8)
  else if s.startsWith ":step " then .step (s.drop 6)
  else if s.startsWith ":trace " then .trace (s.drop 7)
  else if s.startsWith ":parse " then .show (s.drop 7)
  else if s.startsWith ":type " then .showType (s.drop 6)
  else if s == ":list" then .list
  else if s == ":help" || s == ":h" then .help
  else if s == ":quit" || s == ":q" then .quit
  else .eval s

def recognizeNum (t : Term) : Option Nat := churchToNat t
def recognizeBool (t : Term) : Option Bool :=
  if t == churchTrue then some true else if t == churchFalse then some false else none

def execCmd (c : Cmd) : IO String := do
  match c with
  | .reduce ts =>
    match parse ts with
    | .error e => return s!"Parse error: {e}"
    | .ok t => return prettyPrint (reduce 1000 t)
  | .step ts =>
    match parse ts with
    | .error e => return s!"Parse error: {e}"
    | .ok t =>
      match betaReduceStep t with
      | none => return s!"{prettyPrint t}  (normal form)"
      | some t' => return s!"{prettyPrint t}\n→ {prettyPrint t'}"
  | .trace ts =>
    match parse ts with
    | .error e => return s!"Parse error: {e}"
    | .ok t => return String.intercalate "\n→ " ((reduceWithTrace 100 t).map prettyPrint)
  | .show ts =>
    match parse ts with
    | .error e => return s!"Parse error: {e}"
    | .ok t => return s!"Pretty: {prettyPrint t}\nDe Bruijn: {prettyPrintDB t}"
  | .showType n =>
    match lookupBuiltin n with
    | some t => return s!"{n} = {prettyPrint t}"
    | none => return s!"Unknown: {n}"
  | .list => return "Built-ins:\n  Combinators: I K S B C W\n  Booleans: true false and or not if\n  Arithmetic: succ pred add mul exp sub zero? leq\n  Pairs: pair fst snd\n  Fixed-point: Y Z theta\n  Lists: nil cons null? head tail length append map foldr reverse sum product nth\n  Other: omega\n  Numerals: 0, 1, 2, ..."
  | .help => return "Lambda Calculus REPL\n\nSyntax:\n  λx. body  or  \\x. body\n  f x (application)\n  (term)\n\nCommands:\n  :reduce <term>  Reduce to normal form\n  :step <term>    Single step\n  :trace <term>   Show trace\n  :parse <term>   Show de Bruijn\n  :type <name>    Show built-in\n  :list           List built-ins\n  :help           This help\n  :quit           Exit\n\nExamples:\n  (\\x. x) I\n  add 2 3\n  :trace K I omega"
  | .quit => return ""
  | .eval ts =>
    if ts.isEmpty then return ""
    else match parse ts with
    | .error e => return s!"Parse error: {e}"
    | .ok t =>
      let r := reduce 1000 t
      let pp := prettyPrint r
      match recognizeNum r, recognizeBool r with
      | some n, _ => return s!"{pp}  (= {n})"
      | _, some b => return s!"{pp}  (= {b})"
      | _, _ => return pp

partial def repl : IO Unit := do
  IO.println "Lambda Calculus REPL\nType :help for help, :quit to exit\n"
  loop
where
  loop : IO Unit := do
    IO.print "λ> "
    (← IO.getStdout).flush
    let line := (← (← IO.getStdin).getLine).trim
    if line.isEmpty then loop
    else
      let cmd := parseCmd line
      if let .quit := cmd then IO.println "Goodbye!"
      else do
        let r ← execCmd cmd
        if !r.isEmpty then IO.println r
        loop

end LambdaCalc.REPL

def main : IO Unit := LambdaCalc.REPL.repl
