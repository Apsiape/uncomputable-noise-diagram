import Lake
open Lake DSL
-- Release pin: Lean v4.35.0 (eb6cafb7290e8bd5f2937522d8d804f58f02bafc),
-- Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679, vendored as path packages under vendor/.
-- The two reused cores are vendored as sources (vendor/FixedNoiseErgodicity,
-- vendor/UndecidablePhaseDiagram); scripts/replay.py compiles the modules of them that this package
-- imports, and this package, into this package's build directory (serial, -j1 -M5000, memory floor
-- and process-tree cap). The targets below call it, so that `lake comparator` never rebuilds
-- dependencies.
package UncomputableNoiseDiagram where
  moreLeanArgs := #["-j1", "-M5000"]
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]
require plausible from "vendor/plausible"
require LeanSearchClient from "vendor/LeanSearchClient"
require importGraph from "vendor/importGraph"
require proofwidgets from "vendor/proofwidgets"
require aesop from "vendor/aesop"
require Qq from "vendor/Qq"
require batteries from "vendor/batteries"
require Cli from "vendor/Cli"
require mathlib from "vendor/mathlib"
lean_lib UncomputableNoiseDiagram where
  globs := #[`UncomputableNoiseDiagram, `UncomputableNoiseDiagram.+]

target Challenge pkg : Unit := do
  Job.async do
    proc { cmd := if System.Platform.isWindows then "python" else "python3"
           args := #["-I", "-B", (pkg.dir / "scripts" / "replay.py").toString, "--resume"]
           cwd := some pkg.dir }

target Solution pkg : Unit := do
  Job.async do
    proc { cmd := if System.Platform.isWindows then "python" else "python3"
           args := #["-I", "-B", (pkg.dir / "scripts" / "replay.py").toString, "--resume"]
           cwd := some pkg.dir }

target Audit pkg : Unit := do
  Job.async do
    proc { cmd := if System.Platform.isWindows then "python" else "python3"
           args := #["-I", "-B", (pkg.dir / "scripts" / "replay.py").toString, "--resume"]
           cwd := some pkg.dir }

@[default_target]
target core pkg : Unit := do
  Job.async do
    proc { cmd := if System.Platform.isWindows then "python" else "python3"
           args := #["-I", "-B", (pkg.dir / "scripts" / "replay.py").toString, "--resume"]
           cwd := some pkg.dir }
