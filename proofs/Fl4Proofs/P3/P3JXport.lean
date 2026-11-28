/-
P3 (line p3J, gen 2): **the kernel-checked constant transport for the narrowed path premises**
(IrqFixXport's staged transport, with a fresh target family).

Names: `Fl4Proofs.X` ↦ `Fl4ProofsJ.X`, a private name `p` ↦ `Fl4ProofsJ.priv ++ p`. Every copy goes through
`addDecl` (the kernel re-checks it): no axiom, no trusted step.

Collapse A (N, I, Q): the `Fl4ProofsN` / `Fl4ProofsI` / `Fl4ProofsQ` layers are written back into the base
records, so this transport walks the base constants only (its former `…N` / `…I` / `…Q` ↦ `…JN` / `…JI` / `…JQ`
branches are gone). IrqFixXport is removed with Q; its `depsOf` (StallNarrowGen's, used here and by P3KXport)
lives in this module under its old name.
-/
import Fl4Proofs.P3.XTopJointKEntryU30
import Fl4Proofs.P3.P3JLook
open Lean Meta Elab Command

namespace Fl4Proofs.P3.StallNarrow

/-- The constants a constant's type, value and (for an inductive) constructors use. -/
def depsOf (env : Environment) (n : Name) : Array Name :=
  match env.find? n with
  | none => #[]
  | some ci =>
    let v := match ci.value? (allowOpaque := true) with | some v => v.getUsedConstants | none => #[]
    let k := match ci with
      | .inductInfo ii => ii.ctors.toArray.flatMap (fun c => match env.find? c with
          | some cc => cc.type.getUsedConstants | none => #[])
      | _ => #[]
    ci.type.getUsedConstants ++ v ++ k

end Fl4Proofs.P3.StallNarrow

namespace Fl4Proofs.P3.P3JX

/-- A constant of this development reachable by the transport. -/
def ours (n : Name) : Bool :=
  (`Fl4Proofs).isPrefixOf n ||
    (isPrivateName n && (n.toString.startsWith "_private.Fl4Proofs."))

/-- A staged transport: records renamed by prefix, definitions renamed by exact name (both seed the
copied set), single constants replaced by hand-proved ones (not seeds). -/
structure Spec where
  recMap : List (Name × Name)
  defMap : List (Name × Name)
  constMap : List (Name × Name)

def mapName (σ : Spec) (n : Name) : Name := Id.run do
  for (a, b) in σ.constMap do
    if n == a then return b
  for (a, b) in σ.defMap do
    if n == a then return b
  for (a, b) in σ.recMap do
    if a.isPrefixOf n then return n.replacePrefix a b
  if (`Fl4Proofs).isPrefixOf n then return n.replacePrefix `Fl4Proofs `Fl4ProofsJ
  return `Fl4ProofsJ.priv ++ n

/-- Whether `n` is renamed to a hand-written constant (not copied). -/
def isFixed (σ : Spec) (n : Name) : Bool :=
  σ.constMap.any (·.1 == n) || σ.defMap.any (·.1 == n) || σ.recMap.any (·.1.isPrefixOf n)

def trE (σ : Spec) (tr : NameSet) (e : Expr) : CoreM Expr :=
  Core.transform e (post := fun x => pure <| match x with
    | .const n ls => if tr.contains n || isFixed σ n then .done (.const (mapName σ n) ls) else .done x
    | .proj s i b => if tr.contains s || isFixed σ s then .done (.proj (mapName σ s) i b) else .done x
    | _ => .done x)

def stamp (msg : String) : IO Unit := do
  if let some f ← IO.getEnv "FL4_TRANSPORT_LOG" then
    let h ← IO.FS.Handle.mk f .append
    h.putStrLn s!"{← IO.monoMsNow} {msg}"
    h.flush

/-- Copy the constants of `Tr` reached from `roots`, in dependency order; returns (copied, reused). -/
def transport (σ : Spec) (roots : List Name) : CoreM (Nat × Nat) := do
  let env ← getEnv
  stamp "start"
  let mut cone : NameSet := {}
  let mut wl : List Name := roots
  let mut deps : Std.HashMap Name (Array Name) := {}
  repeat
    match wl with
    | [] => break
    | n :: rest =>
      wl := rest
      if cone.contains n then continue
      cone := cone.insert n
      -- a replaced constant's own proof is not copied: do not walk into it
      let ds := if σ.constMap.any (·.1 == n) then #[] else
        (Fl4Proofs.P3.StallNarrow.depsOf env n).filter ours
      deps := deps.insert n ds
      for d in ds do
        if !cone.contains d then wl := d :: wl
  stamp s!"cone {cone.size}"
  let coneL := cone.toList
  let mut rev : Std.HashMap Name (List Name) := {}
  for n in coneL do
    for d in deps.getD n #[] do
      rev := rev.insert d (n :: rev.getD d [])
  let mut tr : NameSet := {}
  let mut wl2 : List Name := coneL.filter (fun n =>
    σ.recMap.any (fun (a, _) => a.isPrefixOf n) || σ.defMap.any (fun (a, _) => a == n))
  repeat
    match wl2 with
    | [] => break
    | n :: more =>
      wl2 := more
      if tr.contains n then continue
      tr := tr.insert n
      for u in rev.getD n [] do
        if !tr.contains u then wl2 := u :: wl2
  stamp s!"tr {tr.size}"
  let mut done : NameSet := {}
  let mut seen : NameSet := {}
  let mut order : Array Name := #[]
  for n0 in tr.toList do
    if done.contains n0 then continue
    let mut stack : List (Name × Bool) := [(n0, false)]
    repeat
      match stack with
      | [] => break
      | (n, exp) :: rest =>
        stack := rest
        if exp then
          if !done.contains n then
            done := done.insert n
            order := order.push n
        else if !seen.contains n then
          seen := seen.insert n
          stack := (n, true) :: stack
          for d in deps.getD n #[] do
            if tr.contains d && !seen.contains d then stack := (d, false) :: stack
  let mut cnt := 0
  let mut reused := 0
  stamp s!"order {order.size}"
  for n in order do
    if σ.constMap.any (·.1 == n) || σ.defMap.any (·.1 == n) then continue
    let n' := mapName σ n
    -- a record's own constants (constructor, projections, …) exist in its replacement
    if σ.recMap.any (·.1.isPrefixOf n) && (← getEnv).contains n' then continue
    let some ci := (← getEnv).find? n | throwError "transport: missing {n}"
    if let some ci' := (← getEnv).find? n' then
      -- a copy from an earlier run: it must have the type this run gives
      let same ← withCurrHeartbeats do pure (ci'.type == (← trE σ tr ci.type))
      unless same do
        throwError "transport: {n'} exists with another type than this run's copy of {n}"
      reused := reused + 1
      continue
    stamp s!"{cnt} {n}"
    withCurrHeartbeats do
      match ci with
      | .thmInfo v =>
        addDecl (.thmDecl (⟨⟨n', v.levelParams, (← trE σ tr v.type)⟩, (← trE σ tr v.value), [n']⟩ : TheoremVal))
      | .defnInfo v =>
        addDecl (.defnDecl (mkDefinitionValEx n' v.levelParams (← trE σ tr v.type) (← trE σ tr v.value) v.hints v.safety [n']))
      | .opaqueInfo v =>
        addDecl (.opaqueDecl (⟨⟨n', v.levelParams, (← trE σ tr v.type)⟩, (← trE σ tr v.value), v.isUnsafe, [n']⟩ : OpaqueVal))
      | .inductInfo v =>
        unless v.all.length == 1 do throwError "transport: mutual inductive {n}"
        let ctors ← v.ctors.mapM fun k => do
          let some kc := (← getEnv).find? k | throwError "transport: missing constructor {k}"
          pure (⟨mapName σ k, (← trE σ tr kc.type)⟩ : Constructor)
        addDecl (.inductDecl v.levelParams v.numParams [(⟨n', (← trE σ tr v.type), ctors⟩ : InductiveType)] v.isUnsafe)
      | .ctorInfo _ | .recInfo _ => pure ()
      | _ => throwError "transport: unsupported constant {n}"
    cnt := cnt + 1
  return (cnt, reused)

end Fl4Proofs.P3.P3JX
