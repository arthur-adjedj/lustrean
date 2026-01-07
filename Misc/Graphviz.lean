import ProofWidgets.Component.HtmlDisplay
import Lean
open Lean
open ProofWidgets.Jsx

open Elab.Command (CommandElabM liftCoreM)
open ProofWidgets ProofWidgets.HtmlEval ProofWidgets.HtmlCommand
open Lean.Server.RpcEncodable (rpcEncode)

def mkHtmlDotStx (ref : Syntax) (toDot : Std.Format) : Elab.Command.CommandElabM Unit := do
  let html ← `(term|<embed type="text/html" src={"https://quickchart.io/graphviz?graph=" ++ $(Syntax.mkStrLit toDot.pretty)}> </embed>)
  let htX ← Elab.Command.liftTermElabM <| evalCommandMHtml <| ← ``(ProofWidgets.HtmlEval.eval $html)
  let ht ← htX
  liftCoreM <| Widget.savePanelWidgetInfo
      (hash HtmlDisplayPanel.javascript)
      (return json% { html: $(← rpcEncode ht) })
      ref
