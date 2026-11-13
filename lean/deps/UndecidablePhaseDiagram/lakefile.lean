import Lake
open Lake DSL

package UndecidablePhaseDiagram where
  moreLeanArgs := #["-j1", "-M6144"]
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

require mathlib from git "https://github.com/leanprover-community/mathlib4" @
  "56a005855ea17e0b0958f73ec801ae140b0a1679"

-- Only this frozen statement module needs the Lean 4.35 compatibility option.
@[default_target]
lean_lib UPDStatements where
  roots := #[`UndecidablePhaseDiagram.Statements]
  moreLeanArgs := #["-Dbackward.isDefEq.respectTransparency=false"]

-- Together these two libraries preserve the original root/submodule coverage.
@[default_target]
lean_lib UndecidablePhaseDiagram where
  roots := #[]
  globs := #[.one `UndecidablePhaseDiagram.Background.BgMap, .one `UndecidablePhaseDiagram.Background.Computation, .one `UndecidablePhaseDiagram.Background.Construct, .one `UndecidablePhaseDiagram.Background.Freeze, .one `UndecidablePhaseDiagram.Background.Grids, .one `UndecidablePhaseDiagram.Background.Line, .one `UndecidablePhaseDiagram.Background.Machine, .one `UndecidablePhaseDiagram.Background.Markers, .one `UndecidablePhaseDiagram.Background.Routing, .one `UndecidablePhaseDiagram.Background.Run, .one `UndecidablePhaseDiagram.Background.Split, .one `UndecidablePhaseDiagram.Background.Unique, .one `UndecidablePhaseDiagram.Compiler.Encode, .one `UndecidablePhaseDiagram.Compiler.Fold, .one `UndecidablePhaseDiagram.Compiler.OneSided, .one `UndecidablePhaseDiagram.Compiler.Universal, .one `UndecidablePhaseDiagram.Gibbs.Hard, .one `UndecidablePhaseDiagram.Gibbs.Site, .one `UndecidablePhaseDiagram.Gibbs.Weights, .one `UndecidablePhaseDiagram.Hypotheses, .one `UndecidablePhaseDiagram.Interaction.Basic, .one `UndecidablePhaseDiagram.Scaffold.Desub, .one `UndecidablePhaseDiagram.Scaffold.Frames, .one `UndecidablePhaseDiagram.Scaffold.Haar, .one `UndecidablePhaseDiagram.Scaffold.Legal, .one `UndecidablePhaseDiagram.Scaffold.Phase, .one `UndecidablePhaseDiagram.Scaffold.QuarterPhase, .one `UndecidablePhaseDiagram.Scaffold.Quarters, .one `UndecidablePhaseDiagram.Scaffold.Red, .one `UndecidablePhaseDiagram.Scaffold.Substitution, .one `UndecidablePhaseDiagram.Scaffold.TILaw, .one `UndecidablePhaseDiagram.Scaffold.Tables, .one `UndecidablePhaseDiagram.Scaffold.Tower, .one `UndecidablePhaseDiagram.Scaffold.Typical, .one `UndecidablePhaseDiagram.Scaffold.Walls]
