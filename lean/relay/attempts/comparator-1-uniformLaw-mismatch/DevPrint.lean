import UncomputableNoiseDiagram.Statements
set_option pp.all true

set_option autoImplicit false
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for n in [``UND.CA.uniformLaw, ``UND.CA.Sym, ``UND.CA.numSymbols] do
    let some ci := env.find? n | throwError "missing {n}"
    let hints := match ci with
      | .defnInfo d => (match d.hints with | .opaque => "opaque" | .abbrev => "abbrev" | .regular h => s!"regular {h}")
      | _ => "-"
    logInfo m!"NAME {n} levels={ci.levelParams} hints={hints}"
    logInfo m!"TYPE {ci.type}"
    if let some v := ci.value? then logInfo m!"VALUE {v}"
