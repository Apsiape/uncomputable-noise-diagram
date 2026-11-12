/-
# The axiom-audit commands

Copied from the forgetting core (`FixedNoiseErgodicity/AuditCommand.lean`, same authors) with the
namespace `FNE.Audit` → `UND.Audit`, plus `#audit_prefix`.

* `#audit_axioms c`: prints the axioms of `c`; `propext`, `Classical.choice`, `Quot.sound` are
  allowed; `sorryAx` is a warning (an unfinished proof, counted in `STATUS.md`); any other axiom is
  an error.
* `#audit_axioms_strict c`: as above, and `sorryAx` is an error too (finished leaves).
* `#audit_prefix P`: every declaration whose name starts with `P` (including private and
  generated ones) is checked: a disallowed axiom is an error; the declarations that depend on
  `sorryAx` are listed (warning); a summary line counts the checked declarations.
-/
import Lean

set_option autoImplicit false

open Lean Elab Command

namespace UND.Audit

/-- The axioms allowed in the finished core. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Shared implementation of the two single-constant audit commands. -/
def runAudit (id : Syntax) (strict : Bool) : CommandElabM Unit := do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let axs ← liftCoreM <| collectAxioms n
  let bad := axs.filter fun a => !(allowedAxioms.contains a) && a != ``sorryAx
  let hasSorry := axs.contains ``sorryAx
  logInfo m!"{n} depends on axioms: {axs.toList}"
  unless bad.isEmpty do
    logError m!"{n} depends on disallowed axioms: {bad.toList}"
  if hasSorry then
    if strict then logError m!"{n} depends on sorryAx"
    else logWarning m!"{n} depends on sorryAx (unfinished proof)"

/-- `#audit_axioms c`: allowed axioms only, `sorryAx` tolerated with a warning. -/
elab "#audit_axioms " id:ident : command => runAudit id false

/-- `#audit_axioms_strict c`: allowed axioms only, `sorryAx` is an error. -/
elab "#audit_axioms_strict " id:ident : command => runAudit id true

/-- `#audit_prefix P`: audit every constant whose name has the prefix `P`. -/
elab "#audit_prefix " id:ident : command => do
  let pre := id.getId
  let env ← getEnv
  let names := env.constants.fold (init := #[]) fun acc n _ =>
    if pre.isPrefixOf n then acc.push n else acc
  let names := names.qsort Name.lt
  let mut withSorry : Array Name := #[]
  let mut nBad : Nat := 0
  for n in names do
    let axs ← liftCoreM <| collectAxioms n
    let bad := axs.filter fun a => !(allowedAxioms.contains a) && a != ``sorryAx
    unless bad.isEmpty do
      logError m!"{n} depends on disallowed axioms: {bad.toList}"
      nBad := nBad + 1
    if axs.contains ``sorryAx then withSorry := withSorry.push n
  unless withSorry.isEmpty do
    logWarning m!"declarations depending on sorryAx: {withSorry.toList}"
  logInfo m!"audit_prefix {pre}: {names.size} declarations checked, {nBad} with disallowed axioms, {withSorry.size} depending on sorryAx"

end UND.Audit
