/-
Declaration manifest for the blueprint coverage check.

Walks the compiled environment of the root `KVAC` library and prints every
public, source-backed declaration with its module, one per line, as
`module<TAB>name`. Auto-generated machinery (projections, constructors,
recursors, match/proof auxiliaries) and private declarations are excluded.
Consumed by the blueprint docs coverage check; run from the repo root with
`lake env lean --run scripts/blueprint_decl_manifest.lean`.
-/
import KVAC

open Lean

def isGenerated (ci : ConstantInfo) : Bool :=
  match ci with
  | .ctorInfo _ | .recInfo _ => true
  | _ => false

def hasAuxComponent (n : Name) : Bool :=
  (n.toString.splitOn ".").any fun s =>
    s.startsWith "proof_" || s.startsWith "match_" || s == "eq_def"
    || s == "sizeOf_spec" || s == "injEq" || s.startsWith "noConfusion"
    || s == "casesOn" || s == "rec" || s == "recOn" || s == "brecOn"
    || s == "below" || s == "ibelow" || s == "ndrec" || s == "mk"
    || s == "ctorIdx" || s == "ctorElim" || s == "ctorElimType"
    || s == "elim" || s == "inj" || s == "congr_simp" || s == "decEq"
    || s == "proxyType" || s == "proxyTypeEquiv"

def isExcluded (env : Environment) (n : Name) (ci : ConstantInfo) : Bool :=
  n.isInternal || n.isInternalDetail
  || (`_private).isPrefixOf n
  || n.components.any (fun c => c.toString.startsWith "_private")
  || isGenerated ci
  || env.isProjectionFn n
  || hasAuxComponent n

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{module := `KVAC}] {} (trustLevel := 1024)
  let mut rows : Array (String × String) := #[]
  for (n, ci) in env.constants.toList do
    match env.getModuleIdxFor? n with
    | none => pure ()
    | some idx =>
      let mod := env.header.moduleNames[idx.toNat]!
      if (`KVAC).isPrefixOf mod && !isExcluded env n ci then
        rows := rows.push (mod.toString, n.toString)
  let sorted := rows.qsort (fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 < b.2))
  for (m, n) in sorted do
    IO.println s!"{m}\t{n}"
