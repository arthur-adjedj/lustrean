import Lustrean.Elaboration.Reify
import Lustrean.Elaboration.Inline
import Lustrean.Elaboration.Indicise
import Lustrean.Elaboration.Normalize
import Lustrean.Elaboration.Compile
import Lustrean.Elaboration.Options
import Lustrean.Interpreter
import Lustrean.Domain.Interval
import Lustrean.Domain.Sign
import Misc.Graphviz

open Lean
open Elab (liftMacroM TermElabM)
open Elab.Command (liftCoreM liftTermElabM CommandElabM )

namespace Lustrean.Elaboration

def elabNodes (nodes : TSyntaxArray `lustre_node) : CoreM (Array &Compile.Node) := do
    Compile.elabLustre <|
    ← Normalize.elabLustre <|
    ← Indicise.elabLustre <|
    ← Inline.elabLustre <|
    ← Reify.elabLustre <|
    nodes

def shouldPrintDot : CoreM Bool := do
  getBoolOption `trace.Lustrean.Elab.DOT

def elabLustre (nodes : TSyntaxArray `lustre_node) : ReaderT Options CommandElabM Unit := do
  let nodes ← liftCoreM (elabNodes nodes)
  for ⟨out@⟨n, vertices, output_vars⟩,ref⟩ in nodes do
      -- trace[Lustrean.Elab] s!"{out.toDot}\n# To visualize DOT diagrams, use https://magjac.com/graphviz-visual-editor/"
      if ← liftCoreM shouldPrintDot then
        mkHtmlDotStx ref out.toDot
      let some cfg := Cfg.new vertices.toList | continue
      let opts ← read
      match opts.dom with
      | .UndefinedInterval =>
        let state ← liftTermElabM <| withRef ref do State.run (m := CoreM) (α := NonRelational (Undefined (Interval [])) n) cfg
        let some env := state.node_env.back? | continue
        for ⟨var, ref⟩ in output_vars do
          let val := env.get var
          if val.may_be_nil then
            logErrorAt ref s!"variable {ref.getId} could be nil"
      | .Sign =>
        let state ← withRef ref do State.run (α := NonRelational (Lustrean.Sign) n) cfg
        let some env := state.node_env.back? | continue
        logWarning s!"final environment: {env}"

elab_rules : command
  | `(command| lustre $[($opts)]? $nodes:lustre_node*) => do
    let opts: Options ←
      if let some opts := opts then
        Options.ofSyntax opts
      else
        pure {}
    let nodes ← nodes.mapM fun nod => do
      let nod ← liftMacroM <| expandMacros nod.raw
      return .mk nod
    (elabLustre nodes).run opts
end Lustrean.Elaboration

initialize
  registerTraceClass `Lustrean.Elab.DOT  (inherited := true)
  registerTraceClass `Lustrean.Elab  (inherited := true)
