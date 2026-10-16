import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Dissertation.PaperSpec
import Dissertation.Acceptance

/-!
Probe of `tools/acceptance.py`. Reads the query file named by `ACCEPTANCE_QUERY`, one request per
line (`SPEC <spec>`, `ACC <theorem> <spec>`, `REF <theorem> <spec>`), and prints one verdict line
per request together with the definition closure of every specification. Not part of the library.
-/

open Lean Meta

namespace AcceptanceProbe

def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def erase (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  transform e (pre := fun x => do
    if x.isFVar || x.isBVar || x.isSort then return .continue
    let p ← try isProof x catch _ => pure false
    if p then return .done (mkConst `«erased proof»)
    return .continue)

def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => `«this file»

def inScope (env : Environment) (n : Name) : Bool :=
  let r := (moduleOf env n).getRoot
  r == `Dissertation || r == `LevyStochCalc

def kindOf : ConstantInfo → String
  | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "ctor" | .opaqueInfo _ => "opaque" | .recInfo _ => "rec"
  | .axiomInfo _ => "axiom" | .quotInfo _ => "quot"

/-- A 64-bit structural hash of an expression, blind to binder names and metadata. -/
partial def deepHash (e : Expr) : StateM (Std.HashMap Expr UInt64) UInt64 := do
  if let some h := (← get)[e]? then return h
  let h ← match e with
    | .bvar i => pure (mixHash 11 (hash i))
    | .fvar i => pure (mixHash 13 (hash i.name.toString))
    | .mvar i => pure (mixHash 17 (hash i.name.toString))
    | .sort l => pure (mixHash 19 (hash (toString l)))
    | .const n ls => pure (mixHash 23 (mixHash (hash n.toString) (hash (toString ls))))
    | .lit (.natVal k) => pure (mixHash 29 (hash k))
    | .lit (.strVal t) => pure (mixHash 31 (hash t))
    | .mdata _ b => deepHash b
    | .app f a => do pure (mixHash 37 (mixHash (← deepHash f) (← deepHash a)))
    | .lam _ t b bi => do
      pure (mixHash 41 (mixHash (hash (toString (repr bi)))
        (mixHash (← deepHash t) (← deepHash b))))
    | .forallE _ t b bi => do
      pure (mixHash 43 (mixHash (hash (toString (repr bi)))
        (mixHash (← deepHash t) (← deepHash b))))
    | .letE _ t v b _ => do
      pure (mixHash 47 (mixHash (← deepHash t) (mixHash (← deepHash v) (← deepHash b))))
    | .proj s i b => do
      pure (mixHash 53 (mixHash (hash s.toString) (mixHash (hash i) (← deepHash b))))
  modify (·.insert e h)
  return h

def hex (h : UInt64) : String :=
  let s := String.ofList (Nat.toDigits 16 h.toNat)
  "".pushn '0' (16 - s.length) ++ s

/-- The hash of a constant with its proofs erased: its type, and its value if it is a
definition. -/
def constHash (ci : ConstantInfo) : MetaM (String × Array Name) := do
  let ty ← erase ci.type
  let mut used := ty.getUsedConstants
  let mut vh : UInt64 := 0
  match ci with
  | .defnInfo d =>
    let v ← erase d.value
    vh := (deepHash v).run' {}
    used := used ++ v.getUsedConstants
  | .inductInfo i => used := used ++ i.ctors.toArray
  | .ctorInfo c => used := used.push c.induct
  | _ => pure ()
  return (hex ((deepHash ty).run' {}) ++ hex vh, used)

def axiomsOf (n : Name) : MetaM (Array Name) := do
  let axs ← collectAxioms n
  return axs.filter fun a => !standardAxioms.contains a

def checkSpec (spec : Name) : MetaM Unit := do
  let env ← getEnv
  let some ci := env.find? spec | IO.println s!"SPEC {spec} ERR:missing"; return
  let mut errs : Array String := #[]
  unless ci matches .defnInfo _ do errs := errs.push "not-a-def"
  unless ci.type == .sort .zero do errs := errs.push "type-not-Prop"
  unless (`Dissertation.PaperSpec).isPrefixOf (moduleOf env spec) do
    errs := errs.push "outside-PaperSpec"
  let bad ← axiomsOf spec
  unless bad.isEmpty do errs := errs.push s!"axioms={bad.toList}"
  let (h, used) ← constHash ci
  let verdict := if errs.isEmpty then "ok" else "ERR:" ++ ",".intercalate errs.toList
  IO.println s!"SPEC {spec} {verdict} {h} {moduleOf env spec}"
  let mut seen : NameSet := {}
  let mut stack := used
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if seen.contains n || n == spec then continue
    seen := seen.insert n
    unless inScope env n do continue
    let some c := env.find? n | continue
    let (hc, more) ← constHash c
    let line := match ← findDeclarationRanges? n with
      | some r => r.range.pos.line
      | none => 0
    IO.println s!"CLOS {spec} {n} {kindOf c} {hc} {moduleOf env n} {line}"
    stack := stack ++ more

/-- A definition the manuscript's statements are built from: its hash and closure. -/
def checkDef (n : Name) : MetaM Unit := do
  let env ← getEnv
  let some ci := env.find? n | IO.println s!"DEF {n} ERR:missing"; return
  let (h, used) ← constHash ci
  let verdict := if inScope env n then "ok" else "ERR:outside-project"
  IO.println s!"DEF {n} {verdict} {h} {moduleOf env n}"
  let mut seen : NameSet := {}
  let mut stack := used
  while !stack.isEmpty do
    let m := stack.back!
    stack := stack.pop
    if seen.contains m || m == n then continue
    seen := seen.insert m
    unless inScope env m do continue
    let some c := env.find? m | continue
    let (hc, more) ← constHash c
    let line := match ← findDeclarationRanges? m with
      | some r => r.range.pos.line
      | none => 0
    IO.println s!"CLOS {n} {m} {kindOf c} {hc} {moduleOf env m} {line}"
    stack := stack ++ more

def levelsMatch (ls : List Level) (params : List Name) : Bool :=
  let ps := ls.filterMap fun l => match l with | .param p => some p | _ => none
  ps.length == ls.length && ps.eraseDups.length == ps.length && ps.length == params.length
    && params.all ps.contains

def checkProof (tag : String) (thm spec : Name) : MetaM Unit := do
  let env ← getEnv
  let some ci := env.find? thm | IO.println s!"{tag} {thm} {spec} ERR:missing -"; return
  let mut errs : Array String := #[]
  unless ci matches .thmInfo _ do errs := errs.push "not-a-theorem"
  unless (`Dissertation.Acceptance).isPrefixOf (moduleOf env thm) do
    errs := errs.push "outside-Acceptance"
  if tag == "ACC" then
    match ci.type with
    | .const c ls =>
      unless c == spec && levelsMatch ls ci.levelParams do errs := errs.push "type-not-spec"
    | _ => errs := errs.push "type-not-spec"
  else if tag == "REF" then
    match ci.type with
    | .app (.const ``Not []) (.const c _) =>
      unless c == spec do errs := errs.push "type-not-negated-spec"
    | .forallE _ (.const c _) (.const ``False []) _ =>
      unless c == spec do errs := errs.push "type-not-negated-spec"
    | _ => errs := errs.push "type-not-negated-spec"
  let axs ← collectAxioms thm
  let bad := axs.filter fun a => !standardAxioms.contains a
  unless bad.isEmpty do errs := errs.push s!"axioms={bad.toList}"
  let verdict := if errs.isEmpty then "ok" else "ERR:" ++ ",".intercalate errs.toList
  let axl := if axs.isEmpty then "-" else ",".intercalate (axs.toList.map toString)
  let lv := if ci.levelParams.isEmpty then "-" else ",".intercalate (ci.levelParams.map toString)
  IO.println s!"{tag} {thm} {spec} {verdict} {axl} {lv}"

/-- No module of the specification layer imports a module of the acceptance layer. -/
def checkLayering : CoreM Unit := do
  let env ← getEnv
  let names := env.header.moduleNames
  for i in [:names.size] do
    let mod := names[i]!
    unless (`Dissertation.PaperSpec).isPrefixOf mod do continue
    let mut seen : NameSet := {}
    let mut stack : Array Name := #[mod]
    while !stack.isEmpty do
      let m := stack.back!
      stack := stack.pop
      if seen.contains m then continue
      seen := seen.insert m
      if (`Dissertation.Acceptance).isPrefixOf m then
        IO.println s!"LAYER {mod} imports {m}"
      let some idx := env.getModuleIdx? m | continue
      for imp in env.header.moduleData[idx.toNat]!.imports do
        stack := stack.push imp.module
    IO.println s!"SPECMODULE {mod}"

end AcceptanceProbe

open AcceptanceProbe in
#eval show MetaM Unit from do
  let some path ← IO.getEnv "ACCEPTANCE_QUERY" | throwError "ACCEPTANCE_QUERY unset"
  checkLayering
  -- Each request runs with its own heartbeat budget: the budget of one command is otherwise
  -- shared by every request of the query.
  for line in ← IO.FS.lines path do
    withCurrHeartbeats <| match line.splitOn " " with
    | ["SPEC", s] => checkSpec s.toName
    | ["DEF", s] => checkDef s.toName
    | ["ACC", t, s] => checkProof "ACC" t.toName s.toName
    | ["REF", t, s] => checkProof "REF" t.toName s.toName
    | ["WIT", t, s] => checkProof "WIT" t.toName s.toName
    | _ => pure ()
  IO.println "DONE"
