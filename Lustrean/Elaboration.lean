import Lustrean.Elaboration.Reify
import Lustrean.Elaboration.Inline
import Lustrean.Elaboration.Indicise
import Lustrean.Elaboration.Normalize
import Lustrean.Elaboration.Compile
import Lustrean.Elaboration.Options
import Lustrean.Interpreter
import Lustrean.Domain.Interval
import Lustrean.Domain.Sign
import Lustrean.Domain.NonRelational
import Lustrean.Domain.Undefined

open Lean
open Elab (liftMacroM)
open Elab.Command (liftTermElabM)

namespace Lustrean.Elaboration

def elabLustre (nodes : TSyntaxArray `lustre_node) : ReaderT Options CoreM Unit := do
  let nodes :=
    ← Compile.elabLustre <|
    ← Normalize.elabLustre <|
    ← Indicise.elabLustre <|
    ← Inline.elabLustre <|
    ← Reify.elabLustre <|
    nodes
  for ⟨out@⟨n, vertices, output_vars⟩,ref⟩ in nodes do
      trace[Lustrean.Elab] s!"{out.toDot}\n# To visualize DOT diagrams, use https://magjac.com/graphviz-visual-editor/"
      let some cfg := Cfg.new vertices.toList | continue
      -- println! s!"{cfg.arcs}"
      let opts ← read
      match opts.dom with
      | .UndefinedInterval =>
        let state ← withRef ref do State.run (m := CoreM) (α := NonRelational (Undefined (Interval [])) n) cfg
        -- println! "Step ∞"
        -- for (env, i) in state.node_env.zipIdx do
        --   dbg_trace s!" {i}) {env}"
        let some env := state.node_env.back? | continue
        for ⟨var, ref⟩ in output_vars do
          let val := env.get var
          -- println! s!"Checking {i}-th variable {var}: {val}..."
          if val.may_be_nil then
            logErrorAt ref s!"variable {ref.getId} could be nil"
            -- println! s!"  The {i}-th output variable can be nil."
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
    liftTermElabM <| (elabLustre nodes).run opts
end Lustrean.Elaboration

initialize
  registerTraceClass `Lustrean.Elab  (inherited := true)
